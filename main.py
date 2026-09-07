#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
PERPETUAL PRINCIPAL — BTC / ETH / HYPE
=====================================

Identidade do robô:
  - Nome operacional: ASTER_PERPETUAL_PRINCIPAL
  - Estratégias ativas: RANGE local em 4 subgrids + MACD.
  - Não possui motor PYRAMID ativo.

RANGE:
  - Quatro subgrids locais por ativo, fases padrão 0 / 0,25% / 0,50% / 0,75%.
  - Gatilho por deslocamento de preço de 1%, TP de 1%, stop de 2%.
  - Recovery RANGE 4x com déficit de recuperação persistente e proteção.
  - Migração segura de eventual cesta RANGE legada: a cesta antiga é drenada antes
    de liberar os quatro subgrids do mesmo ativo.

MACD:
  - BTC/ETH/HYPE em 5m e 15m.
  - MACD 7/21/9 em candle fechado.
  - Stop loss de 2%, trailing após +2% com distância de 2%.
  - Recovery 2x e proteção após a sequência configurada de perdas.

Risco e execução:
  - Hedge Mode obrigatório, margem ISOLATED, Single-Asset.
  - Estratégias podem coexistir no mesmo símbolo.
  - Leverage é tratada como configuração compartilhada do símbolo: com posição
    aberta o robô não tenta alterá-la; apenas adota uma leverage válida e recalcula margem.
  - FillLedger SQLite + state.json + posição física da Aster são reconciliados em conjunto.
  - Ordens com resultado de execução desconhecido (HTTP 503/timeout de transporte)
    são marcadas como UNKNOWN e reconciliadas por clientOrderId, sem reenvio cego.
  - Proteções nativas são verificadas em modo fail-closed.
  - Se uma nova posição RANGE/MACD não puder receber a proteção obrigatória,
    a exposição recém-aberta é encerrada.

Sizing:
  - Bankroll é contabilidade lógica de risco, não reserva física de caixa.
  - AUTO_SCALE_NOTIONAL_WITH_EQUITY=0 por padrão.
  - O sizing respeita saldo/margem livre real, caps e regras do símbolo.

Persistência:
  - BOT_DIR/state.json
  - BOT_DIR/fill_ledger.sqlite3
  - BOT_DIR/trades.jsonl
  - BOT_DIR/order_journal.jsonl

Segurança:
  - LIVE_TRADING=0 por padrão.
  - SOFT kill bloqueia novas entradas e continua gerenciando posições.
  - HARD kill cancela ordens e tenta encerrar posições do robô.
  - Notícias de alto impacto bloqueiam novas entradas conforme configuração.
  - Nunca use seed phrase/chave privada da carteira principal; use somente a API Wallet.
"""


from __future__ import annotations

import hashlib
import fcntl
import json
import logging
import math
import os
import queue
import re
import signal
import sqlite3
import uuid
import sys
import threading
import time
import traceback
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from decimal import Decimal, ROUND_DOWN, ROUND_UP, getcontext
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import urlencode

import requests
from eth_account import Account
from eth_account.messages import encode_typed_data

try:
    import websocket
except Exception:
    websocket = None

try:
    from bs4 import BeautifulSoup
except Exception:
    BeautifulSoup = None

getcontext().prec = 28
D = Decimal
UTC = timezone.utc

# -----------------------------------------------------------------------------
# CONFIG
# -----------------------------------------------------------------------------

VERSION = "5.38.0-v53-state-ledger-orphan-repair"
BOT_NAME = "ASTER_PERPETUAL_PRINCIPAL"
BASE_URL = os.getenv("ASTER_BASE_URL", "https://fapi.asterdex.com").rstrip("/")
WS_BASE = os.getenv("ASTER_WS_BASE", "wss://fstream.asterdex.com").rstrip("/")
USER_ADDRESS = os.getenv("ASTER_USER_ADDRESS", "").strip()
SIGNER_ADDRESS = os.getenv("ASTER_API_WALLET_ADDRESS", "").strip()
SIGNER_PRIVATE_KEY = os.getenv("ASTER_API_WALLET_PRIVATE_KEY", "").strip()
LIVE_TRADING = os.getenv("LIVE_TRADING", "0") == "1"
VALIDATE_API_ONLY = os.getenv("VALIDATE_API_ONLY", "0") == "1"
EMERGENCY_CLOSE_ALL_AND_RESET = os.getenv("EMERGENCY_CLOSE_ALL_AND_RESET", "0") == "1"
FULL_FACTORY_RESET_ON_STARTUP = os.getenv("FULL_FACTORY_RESET_ON_STARTUP", "1") == "1"
RETIRE_LEGACY_PYRAMID_ON_STARTUP = os.getenv("RETIRE_LEGACY_PYRAMID_ON_STARTUP", "1") == "1"
RETIRE_LEGACY_RANGE_ON_STARTUP = os.getenv("RETIRE_LEGACY_RANGE_ON_STARTUP", "1") == "1"
RESET_INHERITED_RANGE_PROTECT_ON_STARTUP = os.getenv("RESET_INHERITED_RANGE_PROTECT_ON_STARTUP", "1") == "1"
RESET_INHERITED_MACD_PROTECT_ON_STARTUP = os.getenv("RESET_INHERITED_MACD_PROTECT_ON_STARTUP", "1") == "1"
EMERGENCY_RESET_ID = os.getenv("EMERGENCY_RESET_ID", "reset-20260830-01").strip()
FULL_FACTORY_RESET_ID = os.getenv("FULL_FACTORY_RESET_ID", "principal-full-reset-v52-20260906").strip()
BOT_DIR = Path(os.getenv("BOT_DIR", "/data"))
BOT_DIR.mkdir(parents=True, exist_ok=True)
STATE_FILE = BOT_DIR / "state.json"
STATE_BACKUP_FILE = BOT_DIR / "state.backup.json"
TRADES_FILE = BOT_DIR / "trades.jsonl"
NEWS_CACHE_FILE = BOT_DIR / "news_calendar_cache.json"
LOG_FILE = BOT_DIR / "aster_bot.log"
LEDGER_FILE = BOT_DIR / "fill_ledger.sqlite3"
ORDER_JOURNAL_FILE = BOT_DIR / "order_journal.jsonl"
INSTANCE_LOCK_FILE = BOT_DIR / ".aster_perpetual_bot_dir.instance.lock"
RATE_LIMIT_STATE_FILE = BOT_DIR / "rate_limit_cooldown.json"

SYMBOLS = tuple(s.strip().upper() for s in os.getenv("SYMBOLS", "BTCUSDT,ETHUSDT,HYPEUSDT").split(",") if s.strip())
if not SYMBOLS:
    raise RuntimeError("SYMBOLS vazio ou inválido")

INITIAL_BANKROLL_USD = D(os.getenv("INITIAL_BANKROLL_USD", "10"))
BTC_INITIAL_BANKROLL_USD = D(os.getenv("BTC_INITIAL_BANKROLL_USD", "20"))
INITIAL_OPERATION_NOTIONAL_USD = D(os.getenv(
    "INITIAL_OPERATION_NOTIONAL_USD",
    os.getenv("INITIAL_OPERATION_MARGIN_USD", "10"),
))
BTC_INITIAL_OPERATION_NOTIONAL_USD = D(os.getenv("BTC_INITIAL_OPERATION_NOTIONAL_USD", "100"))
MAX_INITIAL_NOTIONAL_OVERSHOOT_PCT = D(os.getenv("MAX_INITIAL_NOTIONAL_OVERSHOOT_PCT", "0.05"))
RECOVERY_MULTIPLIER = D(os.getenv("RECOVERY_MULTIPLIER", "4"))
MACD_RECOVERY_MULTIPLIER = D(os.getenv("MACD_RECOVERY_MULTIPLIER", "2"))
MAX_RECOVERY_FAILURES = int(os.getenv("MAX_RECOVERY_FAILURES", "2"))

MAX_REQUESTED_LEVERAGE = int(os.getenv("MAX_REQUESTED_LEVERAGE", "35"))
API_HARD_MAX_LEVERAGE = 125
BOT_HARD_MAX_LEVERAGE = 35
MIN_LEVERAGE = int(os.getenv("MIN_LEVERAGE", "1"))
LEVERAGE_HEADROOM = D(os.getenv("LEVERAGE_HEADROOM", "0.95"))
LIQUIDATION_BUFFER_PCT = D(os.getenv("LIQUIDATION_BUFFER_PCT", "0.005"))
ADVERSE_MOVE_SAFETY_MULTIPLIER = D(os.getenv("ADVERSE_MOVE_SAFETY_MULTIPLIER", "1.25"))
MIN_FREE_WALLET_BUFFER_USD = D(os.getenv("MIN_FREE_WALLET_BUFFER_USD", "1.00"))
MAX_MARGIN_FRACTION_PER_STRATEGY = D(os.getenv("MAX_MARGIN_FRACTION_PER_STRATEGY", "1.0"))

RANGE_SIGNAL_MODE = "VOLATILITY_ONLY"
RANGE_TRIGGER_PCT = D(os.getenv("RANGE_TRIGGER_PCT", "0.01"))
RANGE_TAKE_PROFIT_PCT = D(os.getenv("RANGE_TAKE_PROFIT_PCT", "0.01"))
RANGE_HARD_STOP_PCT = D(os.getenv("RANGE_HARD_STOP_PCT", "0.02"))
RANGE_REARM_PCT = D(os.getenv("RANGE_REARM_PCT", "0.03"))
RANGE_ENGINE_ENABLED = os.getenv("RANGE_ENGINE_ENABLED", "1") == "1"

# RANGE sub-grids are entirely local to this robot. They do not coordinate with another account.
RANGE_GRID_PHASES = tuple(
    D(x.strip()) for x in os.getenv("RANGE_GRID_PHASES", "0,0.0025,0.005,0.0075").split(",")
    if x.strip()
)
RANGE_GRID_COUNT = max(1, len(RANGE_GRID_PHASES))

# Logical risk bankroll per RANGE grid. This is separate from order notional.
RANGE_GRID_BANKROLL_USD = D(os.getenv("RANGE_GRID_BANKROLL_USD", "5"))
BTC_RANGE_GRID_BANKROLL_USD = D(os.getenv("BTC_RANGE_GRID_BANKROLL_USD", "10"))

# Initial exposure per RANGE grid.
RANGE_GRID_INITIAL_NOTIONAL_USD = D(os.getenv("RANGE_GRID_INITIAL_NOTIONAL_USD", "5"))
BTC_RANGE_GRID_INITIAL_NOTIONAL_USD = D(os.getenv("BTC_RANGE_GRID_INITIAL_NOTIONAL_USD", "100"))

# Extra bankroll is a risk/margin envelope, not an automatic position-size multiplier.
AUTO_SCALE_NOTIONAL_WITH_EQUITY = os.getenv("AUTO_SCALE_NOTIONAL_WITH_EQUITY", "0") == "1"

MACD_ENGINE_ENABLED = os.getenv("MACD_ENGINE_ENABLED", "1") == "1"
MACD_FAST = int(os.getenv("MACD_FAST", "7"))
MACD_SLOW = int(os.getenv("MACD_SLOW", "21"))
MACD_SIGNAL = int(os.getenv("MACD_SIGNAL", "9"))
MACD_TIMEFRAMES = tuple(x.strip() for x in os.getenv("MACD_TIMEFRAMES", "5m,15m").split(",") if x.strip())
if not MACD_TIMEFRAMES:
    MACD_TIMEFRAMES = ("5m", "15m")
MACD_REARM_PCT = D(os.getenv("MACD_REARM_PCT", "0.03"))
MACD_TRAILING_ACTIVATION_PCT = D(os.getenv("MACD_TRAILING_ACTIVATION_PCT", "0.02"))
MACD_TRAILING_DISTANCE_PCT = D(os.getenv("MACD_TRAILING_DISTANCE_PCT", "0.02"))
MACD_HARD_STOP_PCT = D(os.getenv("MACD_HARD_STOP_PCT", "0.02"))
MACD_NATIVE_TRAILING_ENABLED = os.getenv("MACD_NATIVE_TRAILING_ENABLED", "1") == "1"
PROTECTIVE_WATCHDOG_SECONDS = float(os.getenv("PROTECTIVE_WATCHDOG_SECONDS", "5"))

RECV_WINDOW = int(os.getenv("RECV_WINDOW", "5000"))
HTTP_TIMEOUT = float(os.getenv("HTTP_TIMEOUT", "10"))
ORDER_FILL_WAIT_SECONDS = float(os.getenv("ORDER_FILL_WAIT_SECONDS", "8"))
ORDER_POLL_SECONDS = float(os.getenv("ORDER_POLL_SECONDS", "0.4"))
MAIN_LOOP_SECONDS = float(os.getenv("MAIN_LOOP_SECONDS", "0.5"))
REST_PRICE_FALLBACK_SECONDS = float(os.getenv("REST_PRICE_FALLBACK_SECONDS", "5"))
HEARTBEAT_SECONDS = float(os.getenv("HEARTBEAT_SECONDS", "30"))
ACCOUNT_SYNC_SECONDS = float(os.getenv("ACCOUNT_SYNC_SECONDS", "10"))

ALLOW_MULTI_STRATEGY_SAME_SYMBOL = os.getenv("ALLOW_MULTI_STRATEGY_SAME_SYMBOL", "1") == "1"
NATIVE_PROTECTIVE_ORDERS = os.getenv("NATIVE_PROTECTIVE_ORDERS", "1") == "1"
PROTECTIVE_WORKING_TYPE = os.getenv("PROTECTIVE_WORKING_TYPE", "MARK_PRICE").strip().upper()
PROTECTIVE_PRICE_PROTECT = os.getenv("PROTECTIVE_PRICE_PROTECT", "0") == "1"

NEWS_FILTER_ENABLED = os.getenv("NEWS_FILTER_ENABLED", "1") == "1"
NEWS_FAIL_CLOSED = os.getenv("NEWS_FAIL_CLOSED", "1") == "1"
NEWS_WINDOW_BEFORE_MIN = int(os.getenv("NEWS_WINDOW_BEFORE_MIN", "15"))
NEWS_WINDOW_AFTER_MIN = int(os.getenv("NEWS_WINDOW_AFTER_MIN", "15"))
NEWS_REFRESH_SECONDS = int(os.getenv("NEWS_REFRESH_SECONDS", "900"))
NEWS_MAX_STALE_SECONDS = int(os.getenv("NEWS_MAX_STALE_SECONDS", "3600"))
NEWS_LOOKAHEAD_DAYS = int(os.getenv("NEWS_LOOKAHEAD_DAYS", "7"))
NEWS_MANUAL_EVENTS_UTC = os.getenv("NEWS_MANUAL_EVENTS_UTC", "").strip()

KILL_SWITCH_ON_API_ERRORS = int(os.getenv("KILL_SWITCH_ON_API_ERRORS", "8"))
HARD_KILL_ON_POSITION_MISMATCH = os.getenv("HARD_KILL_ON_POSITION_MISMATCH", "0") == "1"

MAX_RECOVERY_NOTIONAL_USD = D(os.getenv("MAX_RECOVERY_NOTIONAL_USD", "160"))
BTC_MAX_RECOVERY_NOTIONAL_USD = D(os.getenv("BTC_MAX_RECOVERY_NOTIONAL_USD", "1600"))
MAX_TOTAL_SYMBOL_NOTIONAL_USD = D(os.getenv("MAX_TOTAL_SYMBOL_NOTIONAL_USD", "300"))
BTC_MAX_TOTAL_SYMBOL_NOTIONAL_USD = D(os.getenv("BTC_MAX_TOTAL_SYMBOL_NOTIONAL_USD", "2500"))
MAX_PRICE_AGE_FOR_ENTRY_SECONDS = float(os.getenv("MAX_PRICE_AGE_FOR_ENTRY_SECONDS", "4"))
RECONCILE_INTERVAL_SECONDS = float(os.getenv("RECONCILE_INTERVAL_SECONDS", "10"))
STATE_LEDGER_MISMATCH_CONFIRMATIONS = int(os.getenv("STATE_LEDGER_MISMATCH_CONFIRMATIONS", "2"))
UNKNOWN_ORDER_QUERY_ATTEMPTS = int(os.getenv("UNKNOWN_ORDER_QUERY_ATTEMPTS", "12"))
UNKNOWN_ORDER_QUERY_DELAY_SECONDS = float(os.getenv("UNKNOWN_ORDER_QUERY_DELAY_SECONDS", "0.5"))
RATE_LIMIT_DEFAULT_COOLDOWN_SECONDS = float(os.getenv("RATE_LIMIT_DEFAULT_COOLDOWN_SECONDS", "60"))
RATE_LIMIT_MAX_COOLDOWN_SECONDS = float(os.getenv("RATE_LIMIT_MAX_COOLDOWN_SECONDS", "3600"))
CANCEL_CONFIRM_ATTEMPTS = int(os.getenv("CANCEL_CONFIRM_ATTEMPTS", "8"))
CANCEL_CONFIRM_DELAY_SECONDS = float(os.getenv("CANCEL_CONFIRM_DELAY_SECONDS", "0.25"))
LEDGER_RECONCILE_ON_STARTUP = os.getenv("LEDGER_RECONCILE_ON_STARTUP", "1") == "1"
SELF_TEST_ON_STARTUP = os.getenv("SELF_TEST_ON_STARTUP", "1") == "1"
AUTO_REPAIR_ZERO_PHYSICAL_LEDGER = os.getenv("AUTO_REPAIR_ZERO_PHYSICAL_LEDGER", "0") == "1"

LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO").upper()

def validate_runtime_config() -> None:
    """Fail fast on contradictory/unsafe environment configuration before network or trading."""
    errors: List[str] = []

    def require(cond: bool, message: str) -> None:
        if not cond:
            errors.append(message)

    require(1 <= MIN_LEVERAGE <= MAX_REQUESTED_LEVERAGE <= BOT_HARD_MAX_LEVERAGE <= API_HARD_MAX_LEVERAGE,
            f"leverage invalida: MIN={MIN_LEVERAGE} requested={MAX_REQUESTED_LEVERAGE} bot_cap={BOT_HARD_MAX_LEVERAGE} api_cap={API_HARD_MAX_LEVERAGE}")
    require(D(0) < LEVERAGE_HEADROOM <= D(1), f"LEVERAGE_HEADROOM deve estar em (0,1], atual={LEVERAGE_HEADROOM}")
    require(D(0) <= LIQUIDATION_BUFFER_PCT < D(1), f"LIQUIDATION_BUFFER_PCT invalido: {LIQUIDATION_BUFFER_PCT}")
    require(ADVERSE_MOVE_SAFETY_MULTIPLIER >= D(1), f"ADVERSE_MOVE_SAFETY_MULTIPLIER deve ser >=1, atual={ADVERSE_MOVE_SAFETY_MULTIPLIER}")
    require(MIN_FREE_WALLET_BUFFER_USD >= D(0), f"MIN_FREE_WALLET_BUFFER_USD nao pode ser negativo: {MIN_FREE_WALLET_BUFFER_USD}")
    require(D(0) < MAX_MARGIN_FRACTION_PER_STRATEGY <= D(1), f"MAX_MARGIN_FRACTION_PER_STRATEGY deve estar em (0,1], atual={MAX_MARGIN_FRACTION_PER_STRATEGY}")

    for name, value in (("INITIAL_BANKROLL_USD", INITIAL_BANKROLL_USD), ("BTC_INITIAL_BANKROLL_USD", BTC_INITIAL_BANKROLL_USD),
                        ("INITIAL_OPERATION_NOTIONAL_USD", INITIAL_OPERATION_NOTIONAL_USD), ("BTC_INITIAL_OPERATION_NOTIONAL_USD", BTC_INITIAL_OPERATION_NOTIONAL_USD),
                        ("RANGE_GRID_BANKROLL_USD", RANGE_GRID_BANKROLL_USD), ("BTC_RANGE_GRID_BANKROLL_USD", BTC_RANGE_GRID_BANKROLL_USD),
                        ("RANGE_GRID_INITIAL_NOTIONAL_USD", RANGE_GRID_INITIAL_NOTIONAL_USD), ("BTC_RANGE_GRID_INITIAL_NOTIONAL_USD", BTC_RANGE_GRID_INITIAL_NOTIONAL_USD),
                        ("MAX_RECOVERY_NOTIONAL_USD", MAX_RECOVERY_NOTIONAL_USD), ("BTC_MAX_RECOVERY_NOTIONAL_USD", BTC_MAX_RECOVERY_NOTIONAL_USD),
                        ("MAX_TOTAL_SYMBOL_NOTIONAL_USD", MAX_TOTAL_SYMBOL_NOTIONAL_USD), ("BTC_MAX_TOTAL_SYMBOL_NOTIONAL_USD", BTC_MAX_TOTAL_SYMBOL_NOTIONAL_USD)):
        require(value > 0, f"{name} deve ser >0, atual={value}")

    require(MAX_TOTAL_SYMBOL_NOTIONAL_USD >= RANGE_GRID_INITIAL_NOTIONAL_USD, "MAX_TOTAL_SYMBOL_NOTIONAL_USD menor que RANGE_GRID_INITIAL_NOTIONAL_USD")
    require(BTC_MAX_TOTAL_SYMBOL_NOTIONAL_USD >= BTC_RANGE_GRID_INITIAL_NOTIONAL_USD, "BTC_MAX_TOTAL_SYMBOL_NOTIONAL_USD menor que BTC_RANGE_GRID_INITIAL_NOTIONAL_USD")
    require(RECOVERY_MULTIPLIER >= D(1), f"RECOVERY_MULTIPLIER deve ser >=1, atual={RECOVERY_MULTIPLIER}")
    require(MACD_RECOVERY_MULTIPLIER >= D(1), f"MACD_RECOVERY_MULTIPLIER deve ser >=1, atual={MACD_RECOVERY_MULTIPLIER}")
    require(MAX_RECOVERY_FAILURES >= 1, f"MAX_RECOVERY_FAILURES deve ser >=1, atual={MAX_RECOVERY_FAILURES}")
    require(RANGE_TRIGGER_PCT > 0 and RANGE_TAKE_PROFIT_PCT > 0 and RANGE_HARD_STOP_PCT > 0 and RANGE_REARM_PCT > 0, "percentuais RANGE devem ser >0")
    require(MACD_FAST > 0 and MACD_SLOW > MACD_FAST and MACD_SIGNAL > 0, f"MACD invalido: fast={MACD_FAST} slow={MACD_SLOW} signal={MACD_SIGNAL}")
    require(MACD_REARM_PCT > 0 and MACD_TRAILING_ACTIVATION_PCT > 0 and MACD_TRAILING_DISTANCE_PCT > 0 and MACD_HARD_STOP_PCT > 0, "percentuais MACD devem ser >0")
    require(PROTECTIVE_WORKING_TYPE in ("MARK_PRICE", "CONTRACT_PRICE"), f"PROTECTIVE_WORKING_TYPE invalido: {PROTECTIVE_WORKING_TYPE}")

    for name, value in (("HTTP_TIMEOUT", HTTP_TIMEOUT), ("ORDER_FILL_WAIT_SECONDS", ORDER_FILL_WAIT_SECONDS), ("ORDER_POLL_SECONDS", ORDER_POLL_SECONDS),
                        ("MAIN_LOOP_SECONDS", MAIN_LOOP_SECONDS), ("REST_PRICE_FALLBACK_SECONDS", REST_PRICE_FALLBACK_SECONDS), ("HEARTBEAT_SECONDS", HEARTBEAT_SECONDS),
                        ("ACCOUNT_SYNC_SECONDS", ACCOUNT_SYNC_SECONDS), ("PROTECTIVE_WATCHDOG_SECONDS", PROTECTIVE_WATCHDOG_SECONDS),
                        ("MAX_PRICE_AGE_FOR_ENTRY_SECONDS", MAX_PRICE_AGE_FOR_ENTRY_SECONDS), ("RECONCILE_INTERVAL_SECONDS", RECONCILE_INTERVAL_SECONDS),
                        ("UNKNOWN_ORDER_QUERY_DELAY_SECONDS", UNKNOWN_ORDER_QUERY_DELAY_SECONDS)):
        require(value > 0, f"{name} deve ser >0, atual={value}")
    require(RECV_WINDOW > 0, f"RECV_WINDOW deve ser >0, atual={RECV_WINDOW}")
    require(STATE_LEDGER_MISMATCH_CONFIRMATIONS >= 1, f"STATE_LEDGER_MISMATCH_CONFIRMATIONS deve ser >=1, atual={STATE_LEDGER_MISMATCH_CONFIRMATIONS}")
    require(UNKNOWN_ORDER_QUERY_ATTEMPTS >= 1, f"UNKNOWN_ORDER_QUERY_ATTEMPTS deve ser >=1, atual={UNKNOWN_ORDER_QUERY_ATTEMPTS}")
    require(RATE_LIMIT_DEFAULT_COOLDOWN_SECONDS > 0, f"RATE_LIMIT_DEFAULT_COOLDOWN_SECONDS deve ser >0, atual={RATE_LIMIT_DEFAULT_COOLDOWN_SECONDS}")
    require(RATE_LIMIT_MAX_COOLDOWN_SECONDS >= RATE_LIMIT_DEFAULT_COOLDOWN_SECONDS,
            f"RATE_LIMIT_MAX_COOLDOWN_SECONDS deve ser >= default, atual={RATE_LIMIT_MAX_COOLDOWN_SECONDS}")
    require(CANCEL_CONFIRM_ATTEMPTS >= 1, f"CANCEL_CONFIRM_ATTEMPTS deve ser >=1, atual={CANCEL_CONFIRM_ATTEMPTS}")
    require(CANCEL_CONFIRM_DELAY_SECONDS > 0, f"CANCEL_CONFIRM_DELAY_SECONDS deve ser >0, atual={CANCEL_CONFIRM_DELAY_SECONDS}")
    require(NEWS_WINDOW_BEFORE_MIN >= 0 and NEWS_WINDOW_AFTER_MIN >= 0 and NEWS_REFRESH_SECONDS > 0 and NEWS_MAX_STALE_SECONDS > 0 and NEWS_LOOKAHEAD_DAYS >= 1, "configuracao NEWS invalida")

    require(len(set(RANGE_GRID_PHASES)) == len(RANGE_GRID_PHASES), f"RANGE_GRID_PHASES duplicadas: {RANGE_GRID_PHASES}")
    require(all(D(0) <= x < RANGE_TRIGGER_PCT for x in RANGE_GRID_PHASES), f"RANGE_GRID_PHASES fora de [0,RANGE_TRIGGER_PCT): {RANGE_GRID_PHASES}")
    if RANGE_GRID_COUNT > 1:
        require(ALLOW_MULTI_STRATEGY_SAME_SYMBOL, "RANGE subgrids requerem ALLOW_MULTI_STRATEGY_SAME_SYMBOL=1")

    if errors:
        raise RuntimeError("CONFIG INVALIDA | " + " | ".join(errors))

# -----------------------------------------------------------------------------
# LOGGING
# -----------------------------------------------------------------------------

logger = logging.getLogger(BOT_NAME)
logger.setLevel(getattr(logging, LOG_LEVEL, logging.INFO))
formatter = logging.Formatter("%(asctime)s | %(levelname)s | %(message)s")
sh = logging.StreamHandler(sys.stdout)
sh.setFormatter(formatter)
logger.addHandler(sh)
try:
    fh = logging.FileHandler(LOG_FILE)
    fh.setFormatter(formatter)
    logger.addHandler(fh)
except Exception:
    pass

# -----------------------------------------------------------------------------
# HELPERS
# -----------------------------------------------------------------------------

def now_ms() -> int:
    return int(time.time() * 1000)

def now_iso() -> str:
    return datetime.now(UTC).isoformat()

def dec(x: Any, default: str = "0") -> Decimal:
    try:
        return D(str(x))
    except Exception:
        return D(default)

def dstr(x: Decimal, places: int = 8) -> str:
    q = D(10) ** -places
    s = format(x.quantize(q), "f")
    return s.rstrip("0").rstrip(".") if "." in s else s

_JSONL_LOCK = threading.RLock()

def atomic_json_write(path: Path, data: Dict[str, Any]) -> None:
    """Durable atomic JSON write: fsync temp, replace, then fsync directory."""
    tmp = path.with_suffix(path.suffix + ".tmp")
    payload = json.dumps(data, indent=2, ensure_ascii=False)
    path.parent.mkdir(parents=True, exist_ok=True)
    with tmp.open("w", encoding="utf-8") as f:
        f.write(payload)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)
    try:
        dir_fd = os.open(str(path.parent), os.O_RDONLY)
        try:
            os.fsync(dir_fd)
        finally:
            os.close(dir_fd)
    except Exception:
        # Directory fsync is not available on every platform/filesystem.
        pass

def jsonl_append(path: Path, obj: Dict[str, Any]) -> bool:
    """Best-effort auxiliary audit log. Never changes order semantics after an exchange fill."""
    try:
        line = json.dumps(obj, ensure_ascii=False) + "\n"
        with _JSONL_LOCK:
            with path.open("a", encoding="utf-8") as f:
                f.write(line)
                f.flush()
        return True
    except Exception as e:
        logger.critical("JSONL AUDIT WRITE FAIL | %s | %s", path, e)
        return False

def floor_step(value: Decimal, step: Decimal) -> Decimal:
    if step <= 0:
        return value
    return (value / step).to_integral_value(rounding=ROUND_DOWN) * step

def ceil_step(value: Decimal, step: Decimal) -> Decimal:
    if step <= 0:
        return value
    return (value / step).to_integral_value(rounding=ROUND_UP) * step

def pct_change(a: Decimal, b: Decimal) -> Decimal:
    if a == 0:
        return D(0)
    return (b / a) - D(1)

def ema(values: List[Decimal], period: int) -> List[Decimal]:
    if len(values) < period:
        return []
    k = D(2) / D(period + 1)
    out = [sum(values[:period]) / D(period)]
    for v in values[period:]:
        out.append(v * k + out[-1] * (D(1) - k))
    return out

def macd_series(closes: List[Decimal], fast: int, slow: int, sig: int) -> Tuple[List[Decimal], List[Decimal]]:
    if len(closes) < slow + sig + 3:
        return [], []
    ef = ema(closes, fast)
    es = ema(closes, slow)
    offset = slow - fast
    ef2 = ef[offset:]
    n = min(len(ef2), len(es))
    m = [ef2[i] - es[i] for i in range(n)]
    s = ema(m, sig)
    if not s:
        return [], []
    m_aligned = m[sig - 1:]
    n2 = min(len(m_aligned), len(s))
    return m_aligned[-n2:], s[-n2:]

def get_macd_cross(closes: List[Decimal]) -> Optional[str]:
    m, s = macd_series(closes, MACD_FAST, MACD_SLOW, MACD_SIGNAL)
    if len(m) < 2 or len(s) < 2:
        return None
    if m[-2] <= s[-2] and m[-1] > s[-1]:
        return "LONG"
    if m[-2] >= s[-2] and m[-1] < s[-1]:
        return "SHORT"
    return None

# -----------------------------------------------------------------------------
# ASTER REST CLIENT
# -----------------------------------------------------------------------------

class AsterAPIError(RuntimeError):
    def __init__(self, message: str, code: Optional[int] = None, payload: Any = None):
        super().__init__(message)
        self.code = code
        self.payload = payload

class AsterClient:
    def __init__(self, user_address: str, signer_address: str, signer_private_key: str):
        self.user_address = user_address
        self.signer_address = signer_address
        self.signer_private_key = signer_private_key
        if self.signer_private_key:
            derived = Account.from_key(self.signer_private_key).address
            if self.signer_address and derived.lower() != self.signer_address.lower():
                raise AsterAPIError(
                    f"ASTER_API_WALLET_PRIVATE_KEY nao corresponde a ASTER_API_WALLET_ADDRESS "
                    f"(derivado={derived})"
                )
        self.s = requests.Session()
        self.s.headers.update({"User-Agent": f"{BOT_NAME}/{VERSION}"})
        self.time_offset_ms = 0
        # Only authenticated/account/trading calls participate in this streak. Public market-data
        # success must not erase a degraded authenticated API signal.
        self.api_error_streak = 0
        self._lock = threading.Lock()
        self._last_nonce = 0
        self._rate_limit_lock = threading.RLock()
        self._rate_limit_until = 0.0
        try:
            if RATE_LIMIT_STATE_FILE.exists():
                saved = json.loads(RATE_LIMIT_STATE_FILE.read_text(encoding="utf-8"))
                saved_until = float(saved.get("until_epoch", 0)) if isinstance(saved, dict) else 0.0
                if saved_until > time.time():
                    self._rate_limit_until = saved_until
                    logger.warning("RATE LIMIT COOLDOWN RESTORED | remaining=%.1fs", saved_until - time.time())
                else:
                    try:
                        RATE_LIMIT_STATE_FILE.unlink()
                    except Exception:
                        pass
        except Exception as e:
            logger.warning("RATE LIMIT STATE INVALID | ignorando arquivo %s | %s", RATE_LIMIT_STATE_FILE, e)

    def _ts(self) -> int:
        return now_ms() + self.time_offset_ms

    def _nonce(self) -> int:
        with self._lock:
            candidate = self._ts() * 1000
            self._last_nonce = max(candidate, self._last_nonce + 1)
            return self._last_nonce

    def sync_time(self) -> None:
        t0 = now_ms()
        r = self.s.get(BASE_URL + "/fapi/v3/time", timeout=HTTP_TIMEOUT)
        r.raise_for_status()
        server = int(r.json()["serverTime"])
        t1 = now_ms()
        midpoint = (t0 + t1) // 2
        self.time_offset_ms = server - midpoint
        logger.info(f"TIME SYNC | offset_ms={self.time_offset_ms}")

    def _request(self, method: str, path: str, params: Optional[Dict[str, Any]] = None,
                 signed: bool = False, api_key_only: bool = False, retry_unknown: bool = False) -> Any:
        params = dict(params or {})
        if signed:
            if not self.user_address or not self.signer_address or not self.signer_private_key:
                raise AsterAPIError("Credenciais da API Wallet V3 ausentes")
            params["nonce"] = self._nonce()
            params["signer"] = self.signer_address
            qs = urlencode([(k, str(v).lower() if isinstance(v, bool) else str(v)) for k, v in params.items()])
            typed_data = {"types": {"EIP712Domain": [{"name": "name", "type": "string"}, {"name": "version", "type": "string"}, {"name": "chainId", "type": "uint256"}, {"name": "verifyingContract", "type": "address"}], "Message": [{"name": "msg", "type": "string"}]}, "primaryType": "Message", "domain": {"name": "AsterSignTransaction", "version": "1", "chainId": 1666, "verifyingContract": "0x0000000000000000000000000000000000000000"}, "message": {"msg": qs}}
            signable = encode_typed_data(full_message=typed_data)
            params["signature"] = Account.sign_message(signable, private_key=self.signer_private_key).signature.hex()
        url = BASE_URL + path
        with self._rate_limit_lock:
            cooldown_left = self._rate_limit_until - time.time()
        if cooldown_left > 0:
            # This check occurs before the request try/except below, so account for the
            # authenticated failure here exactly once.
            if signed:
                self.api_error_streak += 1
            raise AsterAPIError(
                f"RATE LIMIT COOLDOWN ativo por mais {cooldown_left:.1f}s",
                429,
                {"cooldown_seconds": cooldown_left},
            )
        try:
            r = self.s.request(method, url, params=params, timeout=HTTP_TIMEOUT)
            if r.status_code in (418, 429):
                try:
                    retry_after = float(r.headers.get("Retry-After") or RATE_LIMIT_DEFAULT_COOLDOWN_SECONDS)
                except Exception:
                    retry_after = RATE_LIMIT_DEFAULT_COOLDOWN_SECONDS
                retry_after = max(1.0, min(retry_after, RATE_LIMIT_MAX_COOLDOWN_SECONDS))
                with self._rate_limit_lock:
                    self._rate_limit_until = max(self._rate_limit_until, time.time() + retry_after)
                    try:
                        atomic_json_write(RATE_LIMIT_STATE_FILE, {
                            "until_epoch": self._rate_limit_until,
                            "http_status": r.status_code,
                            "at": now_iso(),
                        })
                    except Exception as persist_error:
                        logger.critical("RATE LIMIT COOLDOWN PERSIST FAIL | %s", persist_error)
                raise AsterAPIError(
                    f"HTTP {r.status_code} RATE LIMIT | cooldown={retry_after}s",
                    r.status_code,
                    r.text,
                )
            if r.status_code == 503 and not retry_unknown:
                raise AsterAPIError("HTTP 503: status de execucao desconhecido; reconciliar por clientOrderId", 503, r.text)
            if r.status_code >= 400:
                try:
                    body = r.json()
                    code = body.get("code") if isinstance(body, dict) else None
                    msg = body.get("msg", r.text) if isinstance(body, dict) else r.text
                except Exception:
                    code, msg, body = None, r.text, r.text
                # Aster documents -1006 and -1007 as execution status UNKNOWN. For order POST,
                # route them through the same idempotent query-by-clientOrderId flow as HTTP 503.
                if method.upper() == "POST" and path == "/fapi/v3/order" and code in (-1006, -1007):
                    raise AsterAPIError(f"ORDER EXECUTION UNKNOWN | code={code} | {msg}", 503, body)
                raise AsterAPIError(f"HTTP {r.status_code} | {msg}", code, body)
            if signed:
                self.api_error_streak = 0
            return r.json() if r.text else {}
        except AsterAPIError:
            if signed:
                self.api_error_streak += 1
            raise
        except (requests.Timeout, requests.ConnectionError) as e:
            if signed:
                self.api_error_streak += 1
            if method.upper() == "POST" and path == "/fapi/v3/order":
                raise AsterAPIError(
                    f"TRANSPORT UNKNOWN EXECUTION | {type(e).__name__}: {e}",
                    503,
                    {"path": path, "method": method},
                ) from e
            raise AsterAPIError(str(e)) from e
        except Exception as e:
            if signed:
                self.api_error_streak += 1
            raise AsterAPIError(str(e)) from e

    def exchange_info(self) -> Dict[str, Any]:
        return self._request("GET", "/fapi/v3/exchangeInfo")

    def price(self, symbol: str) -> Decimal:
        x = self._request("GET", "/fapi/v3/ticker/price", {"symbol": symbol})
        return dec(x.get("price"))

    def mark(self, symbol: str) -> Decimal:
        x = self._request("GET", "/fapi/v3/premiumIndex", {"symbol": symbol})
        return dec(x.get("markPrice") or x.get("price"))

    def klines(self, symbol: str, interval: str, limit: int = 100) -> List[List[Any]]:
        return self._request("GET", "/fapi/v3/klines", {"symbol": symbol, "interval": interval, "limit": limit})

    def position_mode(self) -> bool:
        x = self._request("GET", "/fapi/v3/positionSide/dual", signed=True)
        return bool(x.get("dualSidePosition"))

    def multi_assets_mode(self) -> bool:
        x = self._request("GET", "/fapi/v3/multiAssetsMargin", signed=True)
        return bool(x.get("multiAssetsMargin"))

    def set_single_asset_mode(self) -> None:
        if not self.multi_assets_mode():
            return
        try:
            self._request("POST", "/fapi/v3/multiAssetsMargin",
                          {"multiAssetsMargin": "false"}, signed=True)
        except AsterAPIError as e:
            raise RuntimeError(
                "Aster esta em Multi-Assets Mode e nao permitiu mudar automaticamente para "
                "Single-Asset Mode. Cancele ordens e feche posicoes manuais na conta/subconta, "
                "desative Multi-Assets Mode na interface Aster e faca novo deploy. "
                f"Erro original: {e}"
            ) from e
        if self.multi_assets_mode():
            raise RuntimeError("Aster continuou em Multi-Assets Mode apos a solicitacao de desativacao")

    def set_hedge_mode(self) -> None:
        try:
            self._request("POST", "/fapi/v3/positionSide/dual", {"dualSidePosition": "true"}, signed=True)
        except AsterAPIError as e:
            if e.code not in (-4059,):
                raise

    def set_margin_type(self, symbol: str, isolated: bool = True) -> None:
        try:
            self._request("POST", "/fapi/v3/marginType",
                          {"symbol": symbol, "marginType": "ISOLATED" if isolated else "CROSSED"}, signed=True)
        except AsterAPIError as e:
            if e.code not in (-4046,):
                raise

    def set_leverage(self, symbol: str, leverage: int) -> Dict[str, Any]:
        return self._request("POST", "/fapi/v3/leverage", {"symbol": symbol, "leverage": int(leverage)}, signed=True)

    def leverage_bracket(self, symbol: str) -> Any:
        return self._request("GET", "/fapi/v3/leverageBracket", {"symbol": symbol}, signed=True)

    def balance(self) -> Any:
        return self._request("GET", "/fapi/v3/balance", signed=True)

    def account(self) -> Any:
        return self._request("GET", "/fapi/v3/accountWithJoinMargin", signed=True)

    def positions(self, symbol: Optional[str] = None) -> Any:
        p = {"symbol": symbol} if symbol else {}
        return self._request("GET", "/fapi/v3/positionRisk", p, signed=True)

    def open_orders(self, symbol: Optional[str] = None) -> Any:
        p = {"symbol": symbol} if symbol else {}
        return self._request("GET", "/fapi/v3/openOrders", p, signed=True)

    def query_order(self, symbol: str, client_id: str) -> Dict[str, Any]:
        return self._request("GET", "/fapi/v3/order", {"symbol": symbol, "origClientOrderId": client_id}, signed=True)

    def order(self, symbol: str, side: str, position_side: str, quantity: Decimal,
              client_id: str, order_type: str = "MARKET") -> Dict[str, Any]:
        p = {
            "symbol": symbol,
            "side": side,
            "positionSide": position_side,
            "type": order_type,
            "quantity": dstr(quantity, 12),
            "newClientOrderId": client_id[:36],
            "newOrderRespType": "RESULT",
        }
        try:
            return self._request("POST", "/fapi/v3/order", p, signed=True)
        except AsterAPIError as e:
            if e.code == 503:
                for _ in range(max(1, UNKNOWN_ORDER_QUERY_ATTEMPTS)):
                    time.sleep(max(0.05, UNKNOWN_ORDER_QUERY_DELAY_SECONDS))
                    try:
                        return self.query_order(symbol, client_id)
                    except Exception:
                        continue
            raise

    def conditional_order(self, symbol: str, side: str, position_side: str, quantity: Decimal,
                          stop_price: Decimal, client_id: str, order_type: str,
                          working_type: str = "MARK_PRICE", price_protect: bool = False) -> Dict[str, Any]:
        if order_type not in ("STOP_MARKET", "TAKE_PROFIT_MARKET"):
            raise ValueError(f"Tipo condicional invalido: {order_type}")
        p = {
            "symbol": symbol,
            "side": side,
            "positionSide": position_side,
            "type": order_type,
            "quantity": dstr(quantity, 12),
            "stopPrice": dstr(stop_price, 12),
            "workingType": working_type,
            "priceProtect": "TRUE" if price_protect else "FALSE",
            "newClientOrderId": client_id[:36],
            "newOrderRespType": "RESULT",
        }
        try:
            return self._request("POST", "/fapi/v3/order", p, signed=True)
        except AsterAPIError as e:
            if e.code == 503:
                for _ in range(max(1, UNKNOWN_ORDER_QUERY_ATTEMPTS)):
                    time.sleep(max(0.05, UNKNOWN_ORDER_QUERY_DELAY_SECONDS))
                    try:
                        return self.query_order(symbol, client_id)
                    except Exception:
                        continue
            raise

    def cancel_order(self, symbol: str, client_id: str) -> Any:
        try:
            return self._request("DELETE", "/fapi/v3/order",
                                 {"symbol": symbol, "origClientOrderId": client_id}, signed=True)
        except AsterAPIError as e:
            if e.code in (-2011, -2013):
                return {"status": "UNKNOWN_OR_GONE", "clientOrderId": client_id}
            raise

    def cancel_all(self, symbol: str) -> Any:
        return self._request("DELETE", "/fapi/v3/allOpenOrders", {"symbol": symbol}, signed=True)

    def cancel_all_confirmed(self, symbol: str, attempts: int = 5, delay_seconds: float = 0.20) -> bool:
        """Cancel all open orders and prove the symbol has none left.

        DELETE timeout/503 is treated as execution-unknown: verification decides the result.
        Other deterministic API errors fail closed.
        """
        try:
            self.cancel_all(symbol)
        except AsterAPIError as e:
            if e.code != 503:
                raise
            logger.warning("CANCEL ALL UNKNOWN | %s | verificando openOrders antes de decidir | %s", symbol, e)
        last: Any = None
        for _ in range(max(1, attempts)):
            last = self.open_orders(symbol)
            if isinstance(last, list) and not last:
                return True
            time.sleep(max(0.05, delay_seconds))
        raise RuntimeError(f"cancel_all nao confirmado para {symbol}; openOrders={last!r}")

    def income(self, symbol: Optional[str] = None, start_ms: Optional[int] = None, limit: int = 1000) -> Any:
        p: Dict[str, Any] = {"limit": limit}
        if symbol:
            p["symbol"] = symbol
        if start_ms:
            p["startTime"] = start_ms
        return self._request("GET", "/fapi/v3/income", p, signed=True)

    def user_trades(self, symbol: str, start_ms: Optional[int] = None, end_ms: Optional[int] = None,
                    limit: int = 1000) -> Any:
        p: Dict[str, Any] = {"symbol": symbol, "limit": limit}
        if start_ms is not None:
            p["startTime"] = int(start_ms)
        if end_ms is not None:
            p["endTime"] = int(end_ms)
        return self._request("GET", "/fapi/v3/userTrades", p, signed=True)

# -----------------------------------------------------------------------------
# EXCHANGE SYMBOL RULES
# -----------------------------------------------------------------------------

@dataclass
class SymbolRules:
    symbol: str
    tick_size: Decimal
    step_size: Decimal
    min_qty: Decimal
    max_qty: Decimal
    min_notional: Decimal

class RulesBook:
    def __init__(self, client: AsterClient):
        self.client = client
        self.rules: Dict[str, SymbolRules] = {}

    def refresh(self) -> None:
        info = self.client.exchange_info()
        out: Dict[str, SymbolRules] = {}
        for s in info.get("symbols", []):
            sym = str(s.get("symbol", "")).upper()
            if sym not in SYMBOLS:
                continue
            tick = step = min_qty = min_notional = D(0)
            max_qty = D("1e50")
            for f in s.get("filters", []):
                ft = f.get("filterType")
                if ft == "PRICE_FILTER":
                    tick = dec(f.get("tickSize"))
                elif ft in ("LOT_SIZE", "MARKET_LOT_SIZE"):
                    st = dec(f.get("stepSize"))
                    mn = dec(f.get("minQty"))
                    mx = dec(f.get("maxQty"), "1e50")
                    if st > step:
                        step = st
                    if mn > min_qty:
                        min_qty = mn
                    if mx < max_qty:
                        max_qty = mx
                elif ft in ("MIN_NOTIONAL", "NOTIONAL"):
                    min_notional = max(min_notional, dec(f.get("notional") or f.get("minNotional")))
            out[sym] = SymbolRules(sym, tick or D("0.00000001"), step or D("0.00000001"),
                                   min_qty, max_qty, min_notional)
        missing = [s for s in SYMBOLS if s not in out]
        if missing:
            raise RuntimeError(f"Simbolos nao disponiveis na Aster: {missing}")
        self.rules = out
        for r in out.values():
            logger.info(f"RULES | {r.symbol} | tick={r.tick_size} step={r.step_size} min_qty={r.min_qty} min_notional={r.min_notional}")

    def qty(self, symbol: str, raw: Decimal, price: Decimal) -> Decimal:
        r = self.rules[symbol]
        q = floor_step(raw, r.step_size)
        if q < r.min_qty:
            q = ceil_step(r.min_qty, r.step_size)
        if r.min_notional > 0 and q * price < r.min_notional:
            q = ceil_step(r.min_notional / price, r.step_size)
        if q > r.max_qty:
            raise RuntimeError(f"Quantidade acima maxQty {symbol}: {q}>{r.max_qty}")
        return q

    def trigger_price(self, symbol: str, raw: Decimal, direction: str) -> Decimal:
        r = self.rules[symbol]
        if direction == "UP":
            return ceil_step(raw, r.tick_size)
        if direction == "DOWN":
            return floor_step(raw, r.tick_size)
        return floor_step(raw, r.tick_size)

# -----------------------------------------------------------------------------
# MARKET DATA WEBSOCKET + REST FALLBACK
# -----------------------------------------------------------------------------

class MarketData:
    def __init__(self, client: AsterClient):
        self.client = client
        self.prices: Dict[str, Decimal] = {}
        self.price_ts: Dict[str, float] = {}
        self._lock = threading.Lock()
        self.stop = threading.Event()
        self.ws_thread: Optional[threading.Thread] = None
        self.rest_thread: Optional[threading.Thread] = None

    def start(self) -> None:
        if websocket is not None:
            self.ws_thread = threading.Thread(target=self._ws_loop, name="market-ws", daemon=True)
            self.ws_thread.start()
        else:
            logger.warning("websocket-client ausente; usando REST fallback")
        self.rest_thread = threading.Thread(target=self._rest_loop, name="market-rest", daemon=True)
        self.rest_thread.start()

    def age(self, symbol: str) -> float:
        with self._lock:
            ts = self.price_ts.get(symbol, 0)
        return max(0.0, time.time() - ts) if ts else float("inf")

    def is_fresh(self, symbol: str, max_age: float = MAX_PRICE_AGE_FOR_ENTRY_SECONDS) -> bool:
        return self.age(symbol) <= max_age

    def get(self, symbol: str, max_age: float = 4.0) -> Optional[Decimal]:
        with self._lock:
            p = self.prices.get(symbol)
            ts = self.price_ts.get(symbol, 0)
        if p is not None and time.time() - ts <= max_age:
            return p
        try:
            fresh = self.client.price(symbol)
            self._set(symbol, fresh)
            return fresh
        except Exception as e:
            age = max(0.0, time.time() - ts) if ts else float("inf")
            logger.warning(f"PRICE FALLBACK FAIL | {symbol} | age_s={age:.3f} | {e}")
            return None if age > max_age else p

    def _set(self, symbol: str, price: Decimal) -> None:
        if price <= 0:
            return
        with self._lock:
            self.prices[symbol] = price
            self.price_ts[symbol] = time.time()

    def _ws_loop(self) -> None:
        streams = "/".join(f"{s.lower()}@miniTicker" for s in SYMBOLS)
        url = f"{WS_BASE}/stream?streams={streams}"
        while not self.stop.is_set():
            try:
                def on_message(ws, message):
                    try:
                        j = json.loads(message)
                        data = j.get("data", j)
                        sym = str(data.get("s", "")).upper()
                        p = dec(data.get("c"))
                        if sym in SYMBOLS and p > 0:
                            self._set(sym, p)
                    except Exception:
                        pass

                def on_open(ws):
                    logger.info(f"MARKET WS | CONECTADO | {url}")

                def on_error(ws, error):
                    logger.warning(f"MARKET WS | erro={error}")

                def on_close(ws, code, msg):
                    logger.warning(f"MARKET WS | fechado code={code} msg={msg}")

                app = websocket.WebSocketApp(url, on_open=on_open, on_message=on_message,
                                             on_error=on_error, on_close=on_close)
                app.run_forever(ping_interval=120, ping_timeout=30)
            except Exception as e:
                logger.warning(f"MARKET WS LOOP | {e}")
            if self.stop.is_set():
                break
            self.stop.wait(3)

    def _rest_loop(self) -> None:
        while not self.stop.wait(REST_PRICE_FALLBACK_SECONDS):
            if self.stop.is_set():
                break
            for sym in SYMBOLS:
                with self._lock:
                    age = time.time() - self.price_ts.get(sym, 0)
                if age < REST_PRICE_FALLBACK_SECONDS:
                    continue
                try:
                    self._set(sym, self.client.price(sym))
                except Exception as e:
                    logger.warning(f"REST PRICE | {sym} | {e}")

# -----------------------------------------------------------------------------
# NEWS FILTER
# -----------------------------------------------------------------------------

class NewsFilter:
    def __init__(self):
        self.events: List[Dict[str, Any]] = []
        self.last_refresh = 0.0
        self.last_success = 0.0
        self.last_source = "NONE"
        self.stop = threading.Event()
        self.thread: Optional[threading.Thread] = None
        self._lock = threading.Lock()
        self._load_cache()
        self._load_manual()

    def _load_cache(self) -> None:
        try:
            j = json.loads(NEWS_CACHE_FILE.read_text(encoding="utf-8"))
            self.events = j.get("events", [])
            self.last_success = float(j.get("last_success", 0))
            self.last_source = str(j.get("source", "CACHE"))
        except Exception:
            pass

    def _load_manual(self) -> None:
        if not NEWS_MANUAL_EVENTS_UTC:
            return
        manual = []
        for item in NEWS_MANUAL_EVENTS_UTC.split(";"):
            if not item.strip():
                continue
            parts = item.split("|", 1)
            try:
                dt = datetime.fromisoformat(parts[0].replace("Z", "+00:00")).astimezone(UTC)
                manual.append({"ts": dt.timestamp(), "title": parts[1] if len(parts) > 1 else "MANUAL", "source": "MANUAL"})
            except Exception:
                continue
        if manual:
            self.events.extend(manual)

    def start(self) -> None:
        if not NEWS_FILTER_ENABLED:
            return
        self.thread = threading.Thread(target=self._loop, name="news", daemon=True)
        self.thread.start()

    def _loop(self) -> None:
        while not self.stop.is_set():
            try:
                self.refresh()
            except Exception as e:
                logger.warning(f"NEWS | refresh falhou | {e}")
            self.stop.wait(NEWS_REFRESH_SECONDS)

    def refresh(self) -> None:
        self.last_refresh = time.time()
        source = "INVESTING_3STAR"
        try:
            events = self._fetch_investing()
        except Exception as investing_error:
            logger.warning(f"NEWS | Investing indisponivel | {investing_error} | tentando ForexFactory")
            events = self._fetch_forexfactory()
            source = "FOREXFACTORY_HIGH"
        with self._lock:
            manual = [e for e in self.events if e.get("source") == "MANUAL"]
            self.events = events + manual
            self.last_success = time.time()
            self.last_source = source
            atomic_json_write(NEWS_CACHE_FILE, {
                "last_success": self.last_success,
                "source": self.last_source,
                "events": self.events,
            })
        logger.info(f"NEWS | cache atualizado | fonte={source} | eventos_high={len(events)}")

    def _parse_investing_rows(self, html_text: str) -> List[Dict[str, Any]]:
        if BeautifulSoup is None:
            raise RuntimeError("beautifulsoup4 ausente")
        soup = BeautifulSoup(html_text or "", "html.parser")
        events: List[Dict[str, Any]] = []
        now = datetime.now(UTC)
        horizon = now + timedelta(days=NEWS_LOOKAHEAD_DAYS)
        rows = soup.find_all("tr", attrs={"data-event-datetime": True})
        for row in rows:
            txt = " ".join(row.stripped_strings)
            row_html = str(row)[:8000]
            high = bool(re.search(r"bull3|High Volatility Expected|sentiment[-_ ]?3|importance[^>]*3", row_html, re.I))
            if not high:
                continue
            raw_dt = row.get("data-event-datetime")
            if not raw_dt:
                continue
            dt = self._parse_investing_dt(str(raw_dt))
            if not dt or dt < now - timedelta(hours=2) or dt > horizon:
                continue
            event_cell = row.find("td", class_=lambda c: c and "event" in (c if isinstance(c, list) else str(c)).split())
            title = " ".join(event_cell.stripped_strings)[:240] if event_cell else txt[:240]
            events.append({"ts": dt.timestamp(), "title": title, "source": "INVESTING_3STAR"})
        unique = {(round(float(e["ts"])), e["title"][:80]): e for e in events}
        return sorted(unique.values(), key=lambda x: x["ts"])

    def _fetch_investing(self) -> List[Dict[str, Any]]:
        if BeautifulSoup is None:
            raise RuntimeError("beautifulsoup4 ausente")
        base = "https://www.investing.com"
        calendar_url = base + "/economic-calendar/"
        service_url = base + "/economic-calendar/Service/getCalendarFilteredData"
        ua = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/152.0.0.0 Safari/537.36"
        common = {
            "User-Agent": ua,
            "Accept-Language": "en-US,en;q=0.9",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Cache-Control": "no-cache",
            "Pragma": "no-cache",
            "Connection": "keep-alive",
        }
        ajax = dict(common)
        ajax.update({
            "Accept": "application/json, text/javascript, */*; q=0.01",
            "X-Requested-With": "XMLHttpRequest",
            "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
            "Referer": calendar_url,
            "Origin": base,
        })

        today = datetime.now(UTC).date()
        end = today + timedelta(days=NEWS_LOOKAHEAD_DAYS)
        form = [
            ("importance[]", "3"),
            ("timeZone", "55"),
            ("timeFilter", "timeOnly"),
            ("currentTab", "custom"),
            ("limit_from", "0"),
            ("dateFrom", today.isoformat()),
            ("dateTo", end.isoformat()),
        ]
        errors: List[str] = []

        with requests.Session() as sess:
            sess.headers.update(common)
            try:
                warm = sess.get(calendar_url, timeout=20, allow_redirects=True)
                warm.raise_for_status()
                direct_events = self._parse_investing_rows(warm.text)
            except Exception as e:
                direct_events = []
                errors.append(f"warmup={type(e).__name__}:{e}")

            for attempt in range(1, 4):
                try:
                    r = sess.post(service_url, headers=ajax, data=form, timeout=25, allow_redirects=True)
                    if r.status_code in (403, 429) or r.status_code >= 500:
                        raise RuntimeError(f"HTTP {r.status_code}")
                    r.raise_for_status()
                    payload = r.json()
                    if not isinstance(payload, dict) or "data" not in payload:
                        raise RuntimeError("JSON sem campo data")
                    events = self._parse_investing_rows(str(payload.get("data", "")))
                    if events:
                        logger.info(f"NEWS INVESTING | service OK | tentativa={attempt} | eventos_3star={len(events)}")
                        return events
                    if direct_events:
                        logger.info(f"NEWS INVESTING | service vazio, usando pagina direta | eventos_3star={len(direct_events)}")
                        return direct_events
                    logger.info("NEWS INVESTING | service OK | nenhum evento 3-star no horizonte")
                    return []
                except Exception as e:
                    errors.append(f"service#{attempt}={type(e).__name__}:{e}")
                    if attempt < 3:
                        time.sleep(1.5 * attempt)
                        try:
                            sess.get(calendar_url, timeout=15, allow_redirects=True)
                        except Exception:
                            pass

            if direct_events:
                logger.warning(f"NEWS INVESTING | service falhou, pagina direta OK | eventos_3star={len(direct_events)}")
                return direct_events

        raise RuntimeError("Investing indisponivel apos retries: " + " | ".join(errors[-5:]))

    def _fetch_forexfactory(self) -> List[Dict[str, Any]]:
        url = "https://nfs.faireconomy.media/ff_calendar_thisweek.json"
        headers = {"User-Agent": f"{BOT_NAME}/{VERSION}", "Accept": "application/json"}
        r = requests.get(url, headers=headers, timeout=20)
        r.raise_for_status()
        payload = r.json()
        if not isinstance(payload, list):
            raise RuntimeError("resposta inesperada do calendario ForexFactory")
        now = datetime.now(UTC)
        horizon = now + timedelta(days=NEWS_LOOKAHEAD_DAYS)
        events: List[Dict[str, Any]] = []
        for item in payload:
            if str(item.get("impact", "")).strip().lower() != "high":
                continue
            try:
                dt = datetime.fromisoformat(str(item.get("date", "")).replace("Z", "+00:00"))
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=UTC)
                dt = dt.astimezone(UTC)
            except Exception:
                continue
            if dt < now - timedelta(hours=2) or dt > horizon:
                continue
            title = f"{item.get('country', '')} | {item.get('title', 'High-impact event')}"[:240]
            events.append({"ts": dt.timestamp(), "title": title, "source": "FOREXFACTORY_HIGH"})
        unique = {(round(float(e["ts"])), e["title"][:80]): e for e in events}
        return sorted(unique.values(), key=lambda x: x["ts"])

    @staticmethod
    def _parse_investing_dt(raw: str) -> Optional[datetime]:
        raw = raw.strip()
        fmts = ["%Y/%m/%d %H:%M:%S", "%Y-%m-%d %H:%M:%S", "%Y-%m-%dT%H:%M:%S%z"]
        for fmt in fmts:
            try:
                dt = datetime.strptime(raw, fmt)
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=UTC)
                return dt.astimezone(UTC)
            except Exception:
                pass
        try:
            dt = datetime.fromisoformat(raw.replace("Z", "+00:00"))
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=UTC)
            return dt.astimezone(UTC)
        except Exception:
            return None

    def blocked(self, when: Optional[datetime] = None) -> Tuple[bool, Optional[str]]:
        if not NEWS_FILTER_ENABLED:
            return False, None
        when = when or datetime.now(UTC)
        with self._lock:
            events = list(self.events)
            last_success = self.last_success
        stale = (time.time() - last_success) > NEWS_MAX_STALE_SECONDS if last_success else True
        if stale and NEWS_FAIL_CLOSED:
            return True, "NEWS_CACHE_STALE_FAIL_CLOSED"
        ts = when.timestamp()
        before = NEWS_WINDOW_BEFORE_MIN * 60
        after = NEWS_WINDOW_AFTER_MIN * 60
        for e in events:
            et = float(e.get("ts", 0))
            if et - before <= ts <= et + after:
                return True, f"{e.get('source')} | {e.get('title')}"
        return False, None

# -----------------------------------------------------------------------------
# STATE
# -----------------------------------------------------------------------------

def configured_bankroll(symbol: str) -> Decimal:
    return BTC_INITIAL_BANKROLL_USD if symbol.upper() == "BTCUSDT" else INITIAL_BANKROLL_USD

def configured_initial_notional(symbol: str) -> Decimal:
    return BTC_INITIAL_OPERATION_NOTIONAL_USD if symbol.upper() == "BTCUSDT" else INITIAL_OPERATION_NOTIONAL_USD

def configured_range_grid_bankroll(symbol: str) -> Decimal:
    return BTC_RANGE_GRID_BANKROLL_USD if symbol.upper() == "BTCUSDT" else RANGE_GRID_BANKROLL_USD

def configured_range_grid_initial_notional(symbol: str) -> Decimal:
    return BTC_RANGE_GRID_INITIAL_NOTIONAL_USD if symbol.upper() == "BTCUSDT" else RANGE_GRID_INITIAL_NOTIONAL_USD

def configured_strategy_bankroll(symbol: str, strategy_state: Dict[str, Any]) -> Decimal:
    if str(strategy_state.get("grid_id", "")).startswith("G"):
        return configured_range_grid_bankroll(symbol)
    return configured_bankroll(symbol)

def configured_strategy_initial_notional(symbol: str, strategy_state: Dict[str, Any]) -> Decimal:
    if str(strategy_state.get("grid_id", "")).startswith("G"):
        return configured_range_grid_initial_notional(symbol)
    return configured_initial_notional(symbol)

def configured_max_recovery_notional(symbol: str) -> Decimal:
    return BTC_MAX_RECOVERY_NOTIONAL_USD if symbol.upper() == "BTCUSDT" else MAX_RECOVERY_NOTIONAL_USD

def configured_max_total_symbol_notional(symbol: str) -> Decimal:
    return BTC_MAX_TOTAL_SYMBOL_NOTIONAL_USD if symbol.upper() == "BTCUSDT" else MAX_TOTAL_SYMBOL_NOTIONAL_USD

def empty_range_state(symbol: str) -> Dict[str, Any]:
    bankroll = configured_bankroll(symbol)
    return {
        "strategy": f"RANGE:{symbol}",
        "symbol": symbol,
        "equity": str(bankroll),
        "bankroll_config_base": str(bankroll),
        "anchor": None,
        "status": "IDLE",
        "basket": None,
        "recovery_deficit": "0",
        "failures": 0,
        "protect_anchor": None,
        "wins": 0,
        "losses": 0,
        "realized_pnl": "0",
        "last_result": "NONE",
        "last_update": now_iso(),
    }

def empty_range_grid_state(symbol: str, grid_id: str, phase: Decimal) -> Dict[str, Any]:
    bankroll = configured_range_grid_bankroll(symbol)
    return {
        "strategy": f"RANGE:{symbol}:{grid_id}",
        "symbol": symbol,
        "grid_id": grid_id,
        "grid_phase": str(phase),
        "equity": str(bankroll),
        "bankroll_config_base": str(bankroll),
        "anchor": None,
        "status": "IDLE",
        "basket": None,
        "recovery_deficit": "0",
        "failures": 0,
        "protect_anchor": None,
        "wins": 0,
        "losses": 0,
        "realized_pnl": "0",
        "last_result": "NONE",
        "last_update": now_iso(),
    }

def empty_macd_state(symbol: str, tf: str) -> Dict[str, Any]:
    bankroll = configured_bankroll(symbol)
    return {
        "strategy": f"MACD:{symbol}:{tf}",
        "symbol": symbol,
        "tf": tf,
        "equity": str(bankroll),
        "bankroll_config_base": str(bankroll),
        "position": None,
        "recovery_deficit": "0",
        "loss_streak": 0,
        "recovery_level": 0,
        "protect": False,
        "protect_anchor": None,
        "last_candle_close_ms": 0,
        "wins": 0,
        "losses": 0,
        "realized_pnl": "0",
        "last_result": "NONE",
        "last_update": now_iso(),
    }

def fresh_state() -> Dict[str, Any]:
    return {
        "version": VERSION,
        "bot_name": BOT_NAME,
        "created_at": now_iso(),
        "updated_at": now_iso(),
        "kill_switch": {"mode": "OFF", "reason": None, "at": None},
        "trade_gate": {"open_allowed": True, "reason": None, "at": now_iso()},
        "operational_blocks": {},
        "protection_blocks": {},
        "range": {s: empty_range_state(s) for s in SYMBOLS},
        "range_grids": {f"{sym}:G{i}": empty_range_grid_state(sym, f"G{i}", phase) for sym in SYMBOLS for i, phase in enumerate(RANGE_GRID_PHASES)},
        "macd": {f"{s}:{tf}": empty_macd_state(s, tf) for s in SYMBOLS for tf in MACD_TIMEFRAMES},
        "symbol_owner": {s: None for s in SYMBOLS},
        "last_wallet": {},
        "maintenance": {"completed_emergency_actions": [], "range_grid_v19_migrated": {}},
    }

def acquire_instance_lock():
    """Acquire a non-blocking process lock for this robot/BOT_DIR.

    The descriptor is intentionally kept open for the process lifetime; POSIX releases
    flock automatically on process exit/crash. A second live instance fails closed before
    it can read state or submit orders.
    """
    fh = open(INSTANCE_LOCK_FILE, "a+", encoding="utf-8")
    try:
        fcntl.flock(fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as e:
        try:
            fh.seek(0)
            owner = fh.read().strip()
        except Exception:
            owner = ""
        fh.close()
        raise RuntimeError(
            f"OUTRA INSTANCIA ATIVA | lock={INSTANCE_LOCK_FILE} | owner={owner or 'desconhecido'}"
        ) from e
    fh.seek(0)
    fh.truncate(0)
    fh.write(f"pid={os.getpid()} bot={BOT_NAME} version={VERSION} started={now_iso()}\n")
    fh.flush()
    os.fsync(fh.fileno())
    return fh

class StateStore:
    def __init__(self):
        self.lock = threading.RLock()
        self.loaded_fresh = False
        self.recovered_from_backup = False
        self.state = self._load()

    @staticmethod
    def _validate_state_shape(st: Any) -> Dict[str, Any]:
        if not isinstance(st, dict):
            raise ValueError("state root precisa ser objeto JSON")
        # Existing state must carry enough semantic identity to distinguish a legitimate
        # migration from a syntactically-valid but truncated file such as {}.
        if not st:
            raise ValueError("state vazio/truncado")
        if not isinstance(st.get("version"), str) or not str(st.get("version") or "").strip():
            raise ValueError("state sem version valida; possivel truncamento")
        legacy_version = str(st.get("version") or "")
        identity = str(st.get("bot_name") or "")
        if identity and identity != BOT_NAME:
            raise ValueError(f"state pertence a outro robo: bot_name={identity!r}, esperado={BOT_NAME!r}")
        # Legacy states created before BOT_NAME existed are identified by structure, not
        # by a version-number prefix. Version prefixes changed across historical builds and
        # must never be the sole reason to reject otherwise coherent production state.
        core_maps = ("range", "range_grids", "macd")
        if not any(k in st and isinstance(st.get(k), dict) for k in core_maps):
            raise ValueError(f"state sem mapas estrategicos esperados {core_maps}; possivel truncamento/arquivo errado")
        essential = ("created_at", "kill_switch", "trade_gate", "symbol_owner", "range", "macd")
        missing = [k for k in essential if k not in st]
        if missing:
            raise ValueError(f"state incompleto; chaves essenciais ausentes={missing}")
        if not isinstance(st.get("created_at"), str) or not str(st.get("created_at") or "").strip():
            raise ValueError("state sem created_at valido")
        for key in ("range", "macd"):
            mp = st.get(key)
            if not isinstance(mp, dict) or not mp:
                raise ValueError(f"state[{key!r}] vazio/invalido; possivel truncamento")
            if any(not isinstance(v, dict) for v in mp.values()):
                raise ValueError(f"state[{key!r}] contem entrada nao-objeto")
        required_maps = ("kill_switch", "trade_gate", "operational_blocks", "protection_blocks",
                         "symbol_owner", "last_wallet", "maintenance", "range", "macd", "pyramid", "pyramid_grids")
        for key in required_maps:
            if key in st and not isinstance(st.get(key), dict):
                raise ValueError(f"state[{key!r}] precisa ser objeto JSON")
        if "range_grids" in st and not isinstance(st.get("range_grids"), dict):
            raise ValueError("state['range_grids'] precisa ser objeto JSON")
        gate = st.get("trade_gate")
        if isinstance(gate, dict) and "open_allowed" in gate and not isinstance(gate.get("open_allowed"), bool):
            raise ValueError("state['trade_gate']['open_allowed'] precisa ser boolean")
        ks = st.get("kill_switch")
        if isinstance(ks, dict) and "mode" in ks and str(ks.get("mode")) not in ("OFF", "SOFT", "HARD"):
            raise ValueError("state['kill_switch']['mode'] invalido")
        return st

    @classmethod
    def _read_state_file(cls, path: Path) -> Dict[str, Any]:
        raw = path.read_text(encoding="utf-8")
        return cls._validate_state_shape(json.loads(raw))

    def _load(self) -> Dict[str, Any]:
        if not STATE_FILE.exists():
            if STATE_BACKUP_FILE.exists():
                try:
                    st = self._read_state_file(STATE_BACKUP_FILE)
                    self.recovered_from_backup = True
                    logger.critical("STATE RECOVERY | principal ausente; backup valido carregado | %s", STATE_BACKUP_FILE)
                    atomic_json_write(STATE_FILE, st)
                except Exception as backup_error:
                    raise RuntimeError(
                        f"STATE AUSENTE e backup invalido ({backup_error}). Startup interrompido."
                    ) from backup_error
            else:
                st = fresh_state()
                self.loaded_fresh = True
                logger.info("STATE | novo | principal e backup inexistentes")
        else:
            try:
                st = self._read_state_file(STATE_FILE)
                logger.info(f"STATE | carregado | {STATE_FILE}")
            except Exception as primary_error:
                logger.critical("STATE PRIMARY INVALID | %s | erro=%s", STATE_FILE, primary_error)
                if STATE_BACKUP_FILE.exists():
                    try:
                        st = self._read_state_file(STATE_BACKUP_FILE)
                        self.recovered_from_backup = True
                        logger.critical("STATE RECOVERY | backup valido carregado | %s", STATE_BACKUP_FILE)
                        atomic_json_write(STATE_FILE, st)
                        logger.critical("STATE RECOVERY | state.json restaurado atomicamente a partir do backup")
                    except Exception as backup_error:
                        raise RuntimeError(
                            f"STATE CORROMPIDO: principal invalido ({primary_error}) e backup invalido ({backup_error}). "
                            "Startup interrompido para nao perder ownership/posicoes persistidas."
                        ) from backup_error
                else:
                    raise RuntimeError(
                        f"STATE CORROMPIDO: {STATE_FILE} existe mas e invalido ({primary_error}) e nao ha backup valido. "
                        "Startup interrompido para nao substituir estado operacional por fresh_state()."
                    ) from primary_error
        st.setdefault("kill_switch", {"mode": "OFF", "reason": None, "at": None})
        st.setdefault("trade_gate", {"open_allowed": True, "reason": None, "at": now_iso()})
        st.setdefault("operational_blocks", {})
        st.setdefault("protection_blocks", {})
        st.setdefault("range", {})
        st.setdefault("range_grids", {})
        st.setdefault("macd", {})
        st.setdefault("symbol_owner", {})
        st.setdefault("last_wallet", {})
        st.setdefault("maintenance", {"completed_emergency_actions": []})
        st["maintenance"].setdefault("completed_emergency_actions", [])
        st["maintenance"].setdefault("range_grid_v19_migrated", {})
        for s in SYMBOLS:
            st["range"].setdefault(s, empty_range_state(s))
            for i, phase in enumerate(RANGE_GRID_PHASES):
                st["range_grids"].setdefault(f"{s}:G{i}", empty_range_grid_state(s, f"G{i}", phase))
            st["symbol_owner"].setdefault(s, None)
            for tf in MACD_TIMEFRAMES:
                key = f"{s}:{tf}"
                st["macd"].setdefault(key, empty_macd_state(s, tf))
                m = st["macd"][key]
                rd = dec(m.get("recovery_deficit"))
                streak = max(0, int(m.get("loss_streak", 0)))
                saved_level = max(0, int(m.get("recovery_level", 0)))
                if rd > 0:
                    repaired_level = min(
                        MAX_RECOVERY_FAILURES,
                        max(1, saved_level, streak),
                    )
                    if saved_level != repaired_level or streak == 0:
                        logger.warning(
                            f"STATE MIGRATION | {key} | RD={rd} streak={streak} recovery_level={saved_level}->{repaired_level}"
                        )
                    m["recovery_level"] = repaired_level
                    if streak == 0:
                        m["loss_streak"] = repaired_level
                else:
                    m["recovery_level"] = 0
                    if not m.get("protect"):
                        m["loss_streak"] = 0
        st["version"] = VERSION
        st["bot_name"] = BOT_NAME
        return st

    def save(self) -> None:
        with self.lock:
            self.state["updated_at"] = now_iso()
            # Mantem uma geracao anterior valida antes de substituir o estado principal.
            # Um arquivo existente so vira backup se puder ser parseado e validado.
            if STATE_FILE.exists():
                try:
                    previous = self._read_state_file(STATE_FILE)
                    atomic_json_write(STATE_BACKUP_FILE, previous)
                except Exception as e:
                    logger.error("STATE BACKUP SKIPPED | state atual invalido | %s", e)
            atomic_json_write(STATE_FILE, self.state)

    def kill(self, mode: str, reason: str) -> None:
        with self.lock:
            self.state["kill_switch"] = {"mode": mode, "reason": reason, "at": now_iso()}
            self.save()
        logger.error(f"KILL SWITCH | mode={mode} | reason={reason}")

    def killed(self) -> str:
        with self.lock:
            return self.state.get("kill_switch", {}).get("mode", "OFF")

    def set_trade_gate(self, allowed: bool, reason: Optional[str] = None) -> None:
        allowed = bool(allowed)
        normalized_reason = str(reason) if reason is not None else None
        with self.lock:
            current = self.state.get("trade_gate", {}) or {}
            if bool(current.get("open_allowed", True)) == allowed and current.get("reason") == normalized_reason:
                return
            self.state["trade_gate"] = {"open_allowed": allowed, "reason": normalized_reason, "at": now_iso()}
            self.save()

    def entry_allowed(self) -> Tuple[bool, Optional[str]]:
        with self.lock:
            operational = self.state.get("operational_blocks", {}) or {}
            if operational:
                first_key = sorted(operational)[0]
                return False, f"OPERATIONAL_BLOCK:{first_key}:{operational[first_key]}"
            blocks = self.state.get("protection_blocks", {}) or {}
            if blocks:
                first_key = sorted(blocks)[0]
                return False, f"PROTECTION_BLOCK:{first_key}:{blocks[first_key]}"
            g = self.state.get("trade_gate", {}) or {}
            return bool(g.get("open_allowed", True)), g.get("reason")

    def set_operational_block(self, block_id: str, reason: Optional[str]) -> None:
        key = str(block_id)
        normalized = str(reason) if reason else None
        changed = False
        with self.lock:
            blocks = self.state.setdefault("operational_blocks", {})
            previous = blocks.get(key)
            if normalized:
                if previous != normalized:
                    blocks[key] = normalized
                    changed = True
            elif key in blocks:
                blocks.pop(key, None)
                changed = True
            if changed:
                self.save()
        if changed:
            log = logger.warning if normalized else logger.info
            log("OPERATIONAL BLOCK | id=%s | active=%s | reason=%s", block_id, bool(normalized), normalized)

    def set_protection_block(self, strategy_id: str, reason: Optional[str]) -> None:
        key = str(strategy_id)
        normalized = str(reason) if reason else None
        changed = False
        with self.lock:
            blocks = self.state.setdefault("protection_blocks", {})
            previous = blocks.get(key)
            if normalized:
                if previous != normalized:
                    blocks[key] = normalized
                    changed = True
            elif key in blocks:
                blocks.pop(key, None)
                changed = True
            if changed:
                self.save()
        if changed:
            log = logger.warning if normalized else logger.info
            log("PROTECTION BLOCK | strategy=%s | active=%s | reason=%s", strategy_id, bool(normalized), normalized)

    def clear_soft_position_mismatch(self) -> bool:
        with self.lock:
            ks = self.state.get("kill_switch", {}) or {}
            if str(ks.get("mode")) != "SOFT":
                return False
            if not str(ks.get("reason") or "").startswith("POSITION_MISMATCH"):
                return False
            self.state["kill_switch"] = {"mode": "OFF", "reason": None, "at": now_iso()}
            self.save()
        logger.warning("KILL SWITCH AUTO-CLEAR | POSITION_MISMATCH reconciliado | novas entradas liberadas")
        return True

# -----------------------------------------------------------------------------
# DURABLE FILL LEDGER + EXCHANGE SNAPSHOT + ORDER STATE MACHINE
# -----------------------------------------------------------------------------

@dataclass
class ExchangeSnapshot:
    captured_ms: int
    positions: Dict[Tuple[str, str], Decimal]
    entry_prices: Dict[Tuple[str, str], Decimal]
    open_orders: List[Dict[str, Any]]

class FillLedger:
    def __init__(self, path: Path):
        self.path = path
        self.lock = threading.RLock()
        self.db = sqlite3.connect(str(path), check_same_thread=False, timeout=30)
        self.db.execute("PRAGMA journal_mode=WAL")
        self.db.execute("PRAGMA synchronous=FULL")
        check = self.db.execute("PRAGMA quick_check").fetchone()
        if not check or str(check[0]).lower() != "ok":
            raise RuntimeError(f"LEDGER SQLITE CORROMPIDO | quick_check={check}")
        self.db.executescript("""
        CREATE TABLE IF NOT EXISTS orders (
            client_id TEXT PRIMARY KEY,
            strategy_id TEXT NOT NULL,
            symbol TEXT NOT NULL,
            position_side TEXT NOT NULL,
            action TEXT NOT NULL,
            order_type TEXT NOT NULL,
            requested_qty TEXT NOT NULL,
            order_id TEXT,
            status TEXT NOT NULL,
            executed_qty TEXT NOT NULL DEFAULT '0',
            avg_price TEXT NOT NULL DEFAULT '0',
            commission TEXT NOT NULL DEFAULT '0',
            realized_pnl TEXT NOT NULL DEFAULT '0',
            reason TEXT,
            created_ms INTEGER NOT NULL,
            updated_ms INTEGER NOT NULL
        );
        CREATE TABLE IF NOT EXISTS lots (
            leg_id TEXT PRIMARY KEY,
            strategy_id TEXT NOT NULL,
            symbol TEXT NOT NULL,
            position_side TEXT NOT NULL,
            opened_qty TEXT NOT NULL,
            open_qty TEXT NOT NULL,
            entry_price TEXT NOT NULL,
            open_client_id TEXT,
            opened_ms INTEGER NOT NULL,
            closed_ms INTEGER,
            source TEXT NOT NULL DEFAULT 'BOT'
        );
        CREATE INDEX IF NOT EXISTS idx_lots_open ON lots(symbol, position_side, open_qty);
        CREATE INDEX IF NOT EXISTS idx_orders_oid ON orders(order_id);
        """)
        self.db.commit()

    def close(self) -> None:
        with self.lock:
            self.db.commit(); self.db.close()

    def reset(self) -> None:
        with self.lock:
            self.db.execute("DELETE FROM lots")
            self.db.execute("DELETE FROM orders")
            self.db.commit()
        logger.warning("LEDGER RESET | durable fill ledger cleared after confirmed emergency reset")

    def order_state(self, client_id: str, strategy_id: str, symbol: str, position_side: str,
                    action: str, order_type: str, requested_qty: Decimal, status: str,
                    order_id: Any = None, executed_qty: Decimal = D(0), avg_price: Decimal = D(0),
                    commission: Decimal = D(0), realized_pnl: Decimal = D(0), reason: str = "") -> None:
        with self.lock:
            t = now_ms()
            self.db.execute("""
                INSERT INTO orders(client_id,strategy_id,symbol,position_side,action,order_type,requested_qty,
                    order_id,status,executed_qty,avg_price,commission,realized_pnl,reason,created_ms,updated_ms)
                VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
                ON CONFLICT(client_id) DO UPDATE SET
                    order_id=excluded.order_id,status=excluded.status,executed_qty=excluded.executed_qty,
                    avg_price=excluded.avg_price,commission=excluded.commission,realized_pnl=excluded.realized_pnl,
                    reason=excluded.reason,updated_ms=excluded.updated_ms
            """, (client_id, strategy_id, symbol, position_side, action, order_type, str(requested_qty),
                  str(order_id or ""), status, str(executed_qty), str(avg_price), str(commission),
                  str(realized_pnl), reason, t, t))
            self.db.commit()
        jsonl_append(ORDER_JOURNAL_FILE, {"client_id": client_id, "strategy": strategy_id, "symbol": symbol,
            "position_side": position_side, "action": action, "order_type": order_type, "status": status,
            "executed_qty": str(executed_qty), "avg_price": str(avg_price), "commission": str(commission),
            "realized_pnl": str(realized_pnl), "at": now_iso()})

    def record_open_lot(self, leg_id: str, strategy_id: str, symbol: str, position_side: str,
                        qty: Decimal, entry_price: Decimal, client_id: str, source: str = "BOT") -> None:
        with self.lock:
            self.db.execute("""
                INSERT INTO lots(leg_id,strategy_id,symbol,position_side,opened_qty,open_qty,entry_price,
                                 open_client_id,opened_ms,source)
                VALUES(?,?,?,?,?,?,?,?,?,?)
                ON CONFLICT(leg_id) DO UPDATE SET strategy_id=excluded.strategy_id,symbol=excluded.symbol,
                    position_side=excluded.position_side,opened_qty=excluded.opened_qty,
                    open_qty=CASE WHEN CAST(lots.open_qty AS REAL)>0 THEN lots.open_qty ELSE excluded.open_qty END,
                    entry_price=excluded.entry_price,open_client_id=excluded.open_client_id,source=excluded.source
            """, (leg_id, strategy_id, symbol, position_side, str(qty), str(qty), str(entry_price), client_id, now_ms(), source))
            self.db.commit()

    def record_close_lot(self, leg_id: str, qty: Decimal) -> None:
        with self.lock:
            row = self.db.execute("SELECT open_qty FROM lots WHERE leg_id=?", (leg_id,)).fetchone()
            if not row:
                return
            remaining = max(D(0), dec(row[0]) - qty)
            self.db.execute("UPDATE lots SET open_qty=?, closed_ms=? WHERE leg_id=?",
                            (str(remaining), now_ms() if remaining <= 0 else None, leg_id))
            self.db.commit()

    def open_by_symbol_side(self) -> Dict[Tuple[str, str], Decimal]:
        out: Dict[Tuple[str, str], Decimal] = {}
        with self.lock:
            rows = self.db.execute("SELECT symbol,position_side,open_qty FROM lots WHERE CAST(open_qty AS REAL)>0").fetchall()
        for sym, side, q in rows:
            k = (str(sym).upper(), str(side).upper())
            out[k] = out.get(k, D(0)) + dec(q)
        return out

    def zero_open_lots_for_symbol_side(self, symbol: str, side: str, reason: str = "EXCHANGE_ZERO_SIDE_RECONCILE") -> int:
        """Mark open ledger lots closed only for one Hedge-Mode symbol/side.

        This is called only after Reconciler proves that the exchange reports this exact
        positionSide flat and that no open order for that side remains unaccounted for.
        Lots are preserved as history; only open_qty/closed_ms are updated.
        """
        symbol = str(symbol).upper(); side = str(side).upper()
        if side not in ("LONG", "SHORT"):
            raise ValueError(f"position_side invalido para ledger repair: {side!r}")
        with self.lock:
            rows = self.db.execute(
                "SELECT leg_id FROM lots WHERE symbol=? AND position_side=? AND CAST(open_qty AS REAL)>0",
                (symbol, side),
            ).fetchall()
            if not rows:
                return 0
            t = now_ms()
            self.db.execute(
                "UPDATE lots SET open_qty='0', closed_ms=? WHERE symbol=? AND position_side=? AND CAST(open_qty AS REAL)>0",
                (t, symbol, side),
            )
            self.db.commit()
        logger.warning(
            "LEDGER SIDE AUTO-REPAIR | symbol=%s side=%s | ghost_lots_closed=%s | reason=%s",
            symbol, side, len(rows), reason,
        )
        return len(rows)

    def open_strategy_qty(self, strategy_id: str, symbol: str, side: str) -> Decimal:
        with self.lock:
            row = self.db.execute("SELECT COALESCE(SUM(CAST(open_qty AS REAL)),0) FROM lots WHERE strategy_id=? AND symbol=? AND position_side=? AND CAST(open_qty AS REAL)>0",
                                  (strategy_id, symbol, side)).fetchone()
        return dec(row[0] if row else 0)

    def order_owner(self, client_id: str) -> Optional[str]:
        """Return durable strategy ownership for a known clientOrderId, if any."""
        cid = str(client_id or "")
        if not cid:
            return None
        with self.lock:
            row = self.db.execute(
                "SELECT strategy_id FROM orders WHERE client_id=? ORDER BY updated_ms DESC LIMIT 1",
                (cid,),
            ).fetchone()
        return str(row[0]) if row and row[0] else None

    def open_lots_for_symbol_side(self, symbol: str, side: str) -> List[Dict[str, Any]]:
        """Return all durable open lots for one exact Hedge-Mode symbol/side."""
        symbol = str(symbol).upper(); side = str(side).upper()
        with self.lock:
            rows = self.db.execute(
                """
                SELECT leg_id,strategy_id,symbol,position_side,open_qty,entry_price,source,opened_ms
                FROM lots
                WHERE symbol=? AND position_side=? AND CAST(open_qty AS REAL)>0
                ORDER BY opened_ms ASC, leg_id ASC
                """,
                (symbol, side),
            ).fetchall()
        out: List[Dict[str, Any]] = []
        for leg_id, strategy_id, sym, ps, open_qty, entry_price, source, opened_ms in rows:
            qty = dec(open_qty)
            if qty <= 0:
                continue
            out.append({
                "id": str(leg_id),
                "strategy_id": str(strategy_id),
                "symbol": str(sym).upper(),
                "side": str(ps).upper(),
                "qty": str(qty),
                "entry_price": str(dec(entry_price)),
                "source": str(source or "BOT"),
                "opened_ms": int(opened_ms or 0),
            })
        return out

    def open_strategy_breakdown(self, symbol: str, side: str) -> Dict[str, Decimal]:
        """Retorna ownership persistente do FillLedger para symbol/positionSide."""
        out: Dict[str, Decimal] = {}
        with self.lock:
            rows = self.db.execute(
                """
                SELECT strategy_id, COALESCE(SUM(CAST(open_qty AS REAL)),0)
                FROM lots
                WHERE symbol=? AND position_side=? AND CAST(open_qty AS REAL)>0
                GROUP BY strategy_id
                """,
                (str(symbol).upper(), str(side).upper()),
            ).fetchall()
        for strategy_id, raw_qty in rows:
            qty = dec(raw_qty)
            if qty > 0:
                out[str(strategy_id)] = qty
        return out

    def open_lots_by_strategy_prefix(self, prefix: str) -> List[Dict[str, Any]]:
        """Lots ainda abertos cujo strategy_id começa com prefix."""
        with self.lock:
            rows = self.db.execute(
                """
                SELECT leg_id,strategy_id,symbol,position_side,open_qty,entry_price,source
                FROM lots
                WHERE strategy_id LIKE ? AND CAST(open_qty AS REAL)>0
                ORDER BY opened_ms ASC, leg_id ASC
                """,
                (str(prefix) + "%",),
            ).fetchall()
        out: List[Dict[str, Any]] = []
        for leg_id, strategy_id, symbol, side, open_qty, entry_price, source in rows:
            qty = dec(open_qty)
            if qty <= 0:
                continue
            out.append({
                "id": str(leg_id),
                "strategy_id": str(strategy_id),
                "symbol": str(symbol).upper(),
                "side": str(side).upper(),
                "qty": str(qty),
                "entry_price": str(dec(entry_price)),
                "source": str(source or "BOT"),
            })
        return out

    def zero_open_lots_for_symbol(self, symbol: str, reason: str = "EXCHANGE_ZERO_RECONCILE") -> int:
        """Close only ledger lots for a symbol after exchange confirms BOTH hedge sides are zero."""
        with self.lock:
            rows = self.db.execute(
                "SELECT leg_id FROM lots WHERE symbol=? AND CAST(open_qty AS REAL)>0", (symbol,)
            ).fetchall()
            if not rows:
                return 0
            t = now_ms()
            self.db.execute(
                "UPDATE lots SET open_qty='0', closed_ms=? WHERE symbol=? AND CAST(open_qty AS REAL)>0",
                (t, symbol),
            )
            self.db.commit()
        logger.warning("LEDGER AUTO-REPAIR | symbol=%s | ghost_lots_closed=%s | reason=%s", symbol, len(rows), reason)
        return len(rows)

    def bootstrap_from_state(self, store: 'StateStore') -> int:
        with self.lock:
            existing = self.db.execute("SELECT COUNT(*) FROM lots").fetchone()[0]
        if existing:
            return 0
        seeded = 0
        with store.lock:
            for sym, st in store.state.get("range", {}).items():
                b = (st or {}).get("basket") or {}
                for leg in b.get("legs", []) or []:
                    q = dec(leg.get("qty")); ep = dec(leg.get("entry_price")); lid = str(leg.get("id") or uuid.uuid4().hex)
                    if q > 0 and ep > 0:
                        self.record_open_lot(lid, f"RANGE:{sym}", sym, str(leg.get("side")), q, ep, lid, "STATE_BOOTSTRAP"); seeded += 1
            for st in store.state.get("range_grids", {}).values():
                b = (st or {}).get("basket") or {}
                for leg in b.get("legs", []) or []:
                    q = dec(leg.get("qty")); ep = dec(leg.get("entry_price")); lid = str(leg.get("id") or uuid.uuid4().hex)
                    if q > 0 and ep > 0:
                        self.record_open_lot(lid, str(st.get("strategy")), str(st.get("symbol")), str(leg.get("side")), q, ep, lid, "STATE_BOOTSTRAP"); seeded += 1
            for st in store.state.get("macd", {}).values():
                pos = (st or {}).get("position") or {}; leg = pos.get("leg") or {}
                q = dec(leg.get("qty")); ep = dec(leg.get("entry_price")); lid = str(leg.get("id") or uuid.uuid4().hex)
                if q > 0 and ep > 0:
                    self.record_open_lot(lid, str(st.get("strategy")), str(st.get("symbol")), str(leg.get("side")), q, ep, lid, "STATE_BOOTSTRAP"); seeded += 1
        if seeded:
            logger.warning(f"LEDGER BOOTSTRAP | lots_seeded={seeded} from state.json")
        return seeded

class OrderManager:
    TERMINAL = {"FILLED", "CANCELED", "REJECTED", "EXPIRED"}
    def __init__(self, client: AsterClient, ledger: FillLedger):
        self.client = client
        self.ledger = ledger
        self.lock = threading.RLock()

    def submit_market(self, strategy_id: str, symbol: str, position_side: str, side: str,
                      qty: Decimal, client_id: str, reason: str) -> Dict[str, Any]:
        action = "OPEN" if side == ("BUY" if position_side == "LONG" else "SELL") else "CLOSE"
        self.ledger.order_state(client_id, strategy_id, symbol, position_side, action,
                                "MARKET", qty, "CREATED", reason=reason)
        try:
            resp = self.client.order(symbol, side, position_side, qty, client_id, "MARKET")
            self.ledger.order_state(client_id, strategy_id, symbol, position_side, action, "MARKET", qty,
                                    str(resp.get("status") or "SUBMITTED"), resp.get("orderId"),
                                    dec(resp.get("executedQty")), dec(resp.get("avgPrice")), reason=reason)
            return resp
        except AsterAPIError as e:
            status = "UNKNOWN" if e.code == 503 else "REJECTED"
            self.ledger.order_state(client_id, strategy_id, symbol, position_side, action, "MARKET", qty,
                                    status, reason=reason)
            if status == "UNKNOWN":
                logger.critical(
                    "ORDER EXECUTION UNKNOWN | strategy=%s symbol=%s side=%s posSide=%s qty=%s cid=%s",
                    strategy_id, symbol, side, position_side, qty, client_id,
                )
            raise
        except Exception:
            self.ledger.order_state(client_id, strategy_id, symbol, position_side, action, "MARKET", qty,
                                    "REJECTED", reason=reason)
            raise

    def submit_conditional(self, strategy_id: str, symbol: str, position_side: str, side: str,
                           qty: Decimal, stop_price: Decimal, client_id: str, order_type: str,
                           working_type: str, price_protect: bool, reason: str) -> Dict[str, Any]:
        self.ledger.order_state(client_id, strategy_id, symbol, position_side, "PROTECT", order_type,
                                qty, "CREATED", reason=reason)
        try:
            resp = self.client.conditional_order(symbol, side, position_side, qty, stop_price,
                                                client_id, order_type, working_type, price_protect)
            self.ledger.order_state(client_id, strategy_id, symbol, position_side, "PROTECT", order_type, qty,
                                    str(resp.get("status") or "SUBMITTED"), resp.get("orderId"),
                                    dec(resp.get("executedQty")), dec(resp.get("avgPrice")), reason=reason)
            return resp
        except AsterAPIError as e:
            status = "UNKNOWN" if e.code == 503 else "REJECTED"
            self.ledger.order_state(client_id, strategy_id, symbol, position_side, "PROTECT", order_type, qty,
                                    status, reason=reason)
            if status == "UNKNOWN":
                logger.critical(
                    "PROTECTIVE ORDER EXECUTION UNKNOWN | strategy=%s symbol=%s posSide=%s qty=%s cid=%s",
                    strategy_id, symbol, position_side, qty, client_id,
                )
            raise
        except Exception:
            self.ledger.order_state(client_id, strategy_id, symbol, position_side, "PROTECT", order_type, qty,
                                    "REJECTED", reason=reason)
            raise

# -----------------------------------------------------------------------------
# ACCOUNT / LEVERAGE / EXECUTION
# -----------------------------------------------------------------------------

class AccountManager:
    def __init__(self, client: AsterClient, rules: RulesBook, store: StateStore):
        self.client = client
        self.rules = rules
        self.store = store
        self.wallet_balance = D(0)
        self.available_balance = D(0)
        self.unrealized = D(0)
        self.last_sync = 0.0
        self.commission: Dict[str, Decimal] = {}
        self._lock = threading.RLock()

    def sync(self, force: bool = False) -> None:
        if not LIVE_TRADING and not VALIDATE_API_ONLY:
            strategy_count = (
                (len(SYMBOLS) if RANGE_ENGINE_ENABLED else 0)
                + (len(SYMBOLS) * len(MACD_TIMEFRAMES) if MACD_ENGINE_ENABLED else 0)
            )
            simulated_total = D(0)
            if RANGE_ENGINE_ENABLED:
                simulated_total += sum((configured_bankroll(s) for s in SYMBOLS), D(0))
            if MACD_ENGINE_ENABLED:
                simulated_total += sum((configured_bankroll(s) * D(len(MACD_TIMEFRAMES)) for s in SYMBOLS), D(0))
            if strategy_count == 0:
                simulated_total = INITIAL_BANKROLL_USD
            self.wallet_balance = simulated_total
            self.available_balance = simulated_total
            self.unrealized = D(0)
            self.last_sync = time.time()
            return
        if not force and time.time() - self.last_sync < ACCOUNT_SYNC_SECONDS:
            return
        with self._lock:
            acct = self.client.account()
            self.wallet_balance = dec(acct.get("totalWalletBalance") or acct.get("totalMarginBalance") or 0)
            self.available_balance = dec(acct.get("availableBalance") or 0)
            self.unrealized = dec(acct.get("totalUnrealizedProfit") or 0)
            self.last_sync = time.time()
            with self.store.lock:
                self.store.state["last_wallet"] = {
                    "wallet": str(self.wallet_balance),
                    "available": str(self.available_balance),
                    "unrealized": str(self.unrealized),
                    "at": now_iso(),
                }
            self.store.save()

    def free_margin(self, force: bool = False) -> Decimal:
        self.sync(force=force)
        return max(D(0), self.available_balance - MIN_FREE_WALLET_BUFFER_USD)

    def ensure_modes(self) -> None:
        if not LIVE_TRADING:
            logger.info("MODES | simulacao: nao altera Hedge/Isolated")
            return
        self.client.set_single_asset_mode()
        logger.info("MODES | Single-Asset Mode confirmado")
        self.client.set_hedge_mode()
        if not self.client.position_mode():
            raise RuntimeError("Conta nao esta em Hedge Mode")
        for s in SYMBOLS:
            self.client.set_margin_type(s, True)
        logger.info(f"MODES | Hedge Mode confirmado | ISOLATED solicitado em {','.join(SYMBOLS)}")

    def get_brackets(self, symbol: str) -> List[Dict[str, Any]]:
        if not LIVE_TRADING:
            return []
        try:
            x = self.client.leverage_bracket(symbol)
            if isinstance(x, list):
                if x and "brackets" in x[0]:
                    return x[0].get("brackets", [])
                return x
            if isinstance(x, dict):
                return x.get("brackets", [])
        except Exception as e:
            logger.warning(f"LEVERAGE BRACKET FAIL | {symbol} | {e}")
        return []

    def max_exchange_leverage(self, symbol: str, notional: Decimal) -> Tuple[int, Decimal]:
        brackets = self.get_brackets(symbol)
        max_lev = API_HARD_MAX_LEVERAGE
        mmr = D("0.005")
        if brackets:
            chosen = None
            for b in brackets:
                floor = dec(b.get("notionalFloor"))
                cap = dec(b.get("notionalCap"), "1e50")
                if floor <= notional < cap:
                    chosen = b
                    break
            if chosen is None:
                chosen = brackets[-1]
            max_lev = int(chosen.get("initialLeverage", max_lev))
            mmr = dec(chosen.get("maintMarginRatio"), "0.005")
        return max(1, min(max_lev, API_HARD_MAX_LEVERAGE, BOT_HARD_MAX_LEVERAGE,
                          MAX_REQUESTED_LEVERAGE)), mmr

    def safe_leverage_cap(self, symbol: str, notional: Decimal, adverse_distance_pct: Decimal) -> Tuple[int, Dict[str, Any]]:
        exch_max, mmr = self.max_exchange_leverage(symbol, notional)
        protected_move = adverse_distance_pct * ADVERSE_MOVE_SAFETY_MULTIPLIER
        denom = protected_move + mmr + LIQUIDATION_BUFFER_PCT
        liq_safe = int((D(1) / denom).to_integral_value(rounding=ROUND_DOWN)) if denom > 0 else exch_max
        cap = max(MIN_LEVERAGE, min(exch_max, liq_safe, API_HARD_MAX_LEVERAGE,
                                    BOT_HARD_MAX_LEVERAGE, MAX_REQUESTED_LEVERAGE))
        return cap, {"exchange_max": exch_max, "bot_hard_max": BOT_HARD_MAX_LEVERAGE,
                     "mmr": str(mmr), "protected_move": str(protected_move),
                     "liq_safe_max": liq_safe, "denom": str(denom)}

    def current_symbol_notional(self, symbol: str) -> Decimal:
        if not LIVE_TRADING:
            return D(0)
        total = D(0)
        try:
            for p in self.client.positions(symbol):
                q = abs(dec(p.get("positionAmt"))); mark = dec(p.get("markPrice") or p.get("entryPrice"))
                if q > 0 and mark > 0:
                    total += q * mark
        except Exception as e:
            logger.warning(f"SYMBOL NOTIONAL SNAPSHOT FAIL | {symbol} | {e}")
        return total

    def base_margin_budget(self, strategy_state: Dict[str, Any]) -> Decimal:
        eq = dec(strategy_state.get("equity"), str(INITIAL_BANKROLL_USD))
        desired = eq
        desired = min(desired, eq * MAX_MARGIN_FRACTION_PER_STRATEGY)
        return max(D(0), desired)

    def sizing_for_profit_target(self, symbol: str, price: Decimal, strategy_state: Dict[str, Any],
                                 target_profit: Optional[Decimal], target_move_pct: Decimal,
                                 adverse_distance_pct: Decimal, recovery_level: int = 0,
                                 desired_notional_override: Optional[Decimal] = None,
                                 recovery_multiplier: Optional[Decimal] = None) -> Optional[Dict[str, Any]]:
        self.sync()
        active = bool(strategy_state.get("position") or strategy_state.get("basket"))
        configured_base = configured_strategy_bankroll(symbol, strategy_state)
        previous_base = dec(strategy_state.get("bankroll_config_base"), str(INITIAL_BANKROLL_USD))
        if not active and configured_base != previous_base:
            previous_equity = dec(strategy_state.get("equity"), str(previous_base))
            strategy_state["equity"] = str(previous_equity + configured_base - previous_base)
            strategy_state["bankroll_config_base"] = str(configured_base)
            strategy_state["last_update"] = now_iso()
            self.store.save()
            logger.info(
                f"BANKROLL MIGRATION | {strategy_state.get('strategy', symbol)} | base {previous_base}->{configured_base} | equity {previous_equity}->{strategy_state['equity']}"
            )
        logical_eq = dec(strategy_state.get("equity"), str(INITIAL_BANKROLL_USD))
        physical_free = self.free_margin(force=True)
        if logical_eq <= 0 or physical_free <= 0:
            return None

        base_budget = min(self.base_margin_budget(strategy_state), logical_eq, physical_free)
        if base_budget <= 0:
            return None

        recovery_level = max(0, min(int(recovery_level), MAX_RECOVERY_FAILURES))
        if recovery_multiplier is None:
            recovery_multiplier = RECOVERY_MULTIPLIER

        configured_notional = configured_strategy_initial_notional(symbol, strategy_state)
        base_notional = max(configured_notional, logical_eq) if AUTO_SCALE_NOTIONAL_WITH_EQUITY else configured_notional
        if recovery_level == 0:
            desired_notional = base_notional
            cap, meta = self.safe_leverage_cap(symbol, desired_notional, adverse_distance_pct)
            lev = cap
            margin = desired_notional / D(lev)
            if margin > base_budget:
                return None
        else:
            classic_notional = base_notional * (recovery_multiplier ** recovery_level)
            desired_notional = max(classic_notional, dec(desired_notional_override)) \
                if desired_notional_override is not None else classic_notional
            recovery_cap = configured_max_recovery_notional(symbol)
            if desired_notional > recovery_cap:
                logger.warning(f"RECOVERY CAP | {symbol} | requested={desired_notional} capped={recovery_cap} level={recovery_level}")
                desired_notional = recovery_cap
            cap, meta = self.safe_leverage_cap(symbol, desired_notional, adverse_distance_pct)
            lev = cap
            margin = desired_notional / D(lev)

        lev = max(MIN_LEVERAGE, min(int(lev), MAX_REQUESTED_LEVERAGE,
                                    BOT_HARD_MAX_LEVERAGE, API_HARD_MAX_LEVERAGE))
        fresh_operation = recovery_level == 0
        notional = desired_notional
        qty = self.rules.qty(symbol, notional / price, price)
        actual_notional = qty * price
        actual_margin = actual_notional / D(lev)
        current_symbol_notional = self.current_symbol_notional(symbol)
        symbol_cap = configured_max_total_symbol_notional(symbol)
        if current_symbol_notional + actual_notional > symbol_cap:
            logger.warning(f"SYMBOL EXPOSURE CAP | {symbol} | current={current_symbol_notional} new={actual_notional} cap={symbol_cap}")
            return None
        estimated_adverse_loss = actual_notional * adverse_distance_pct
        if fresh_operation:
            max_allowed = desired_notional * (D(1) + MAX_INITIAL_NOTIONAL_OVERSHOOT_PCT)
            if actual_notional > max_allowed:
                rule = self.rules.rules[symbol]
                logger.warning(
                    f"SIZING BLOCK | {symbol} | entrada_inicial={desired_notional} notional_minimo_real={actual_notional} "
                    f"limite_com_tolerancia={max_allowed} min_qty={rule.min_qty} step={rule.step_size} price={price}"
                )
                return None
        if estimated_adverse_loss > logical_eq * MAX_MARGIN_FRACTION_PER_STRATEGY:
            logger.warning(
                f"SIZING RISK BLOCK | {symbol} | notional={actual_notional} perda_estimada_stop={estimated_adverse_loss} caixa_logico={logical_eq} level={recovery_level}"
            )
            return None
        if actual_margin > physical_free:
            logger.warning(
                f"SIZING MARGIN BLOCK | {symbol} | margin_necessaria={actual_margin} margem_livre={physical_free} notional={actual_notional} lev={lev}x level={recovery_level}"
            )
            return None
        return {
            "leverage": lev,
            "qty": qty,
            "price": price,
            "notional": actual_notional,
            "margin": actual_margin,
            "estimated_adverse_loss": estimated_adverse_loss,
            "target_profit": target_profit or D(0),
            "recovery_level": recovery_level,
            "desired_notional_override": desired_notional_override,
            "recovery_multiplier": str(recovery_multiplier),
            "meta": meta,
        }

    def active_symbol_leverage(self, symbol: str) -> Tuple[Optional[int], int]:
        if not LIVE_TRADING:
            return None, 0
        rows = self.client.positions(symbol)
        if isinstance(rows, dict):
            rows = [rows]
        open_rows = [p for p in (rows or []) if abs(dec(p.get("positionAmt"))) > 0]
        if not open_rows:
            return None, 0
        vals: List[int] = []
        for p in open_rows:
            try:
                lv = int(dec(p.get("leverage")))
                if lv > 0:
                    vals.append(lv)
            except Exception:
                pass
        if not vals:
            logger.error("LEVERAGE SNAPSHOT INVALID | %s | posicao aberta sem leverage", symbol)
            return None, len(open_rows)
        current = max(vals)
        if any(v != current for v in vals):
            logger.warning("LEVERAGE SNAPSHOT DIVERGENTE | %s | values=%s usando=%sx", symbol, vals, current)
        return current, len(open_rows)

    def prepare_leverage_for_open(self, symbol: str, requested: int) -> Optional[int]:
        requested = max(
            MIN_LEVERAGE,
            min(int(requested), MAX_REQUESTED_LEVERAGE, BOT_HARD_MAX_LEVERAGE, API_HARD_MAX_LEVERAGE),
        )
        if not LIVE_TRADING:
            return requested
        try:
            current, open_count = self.active_symbol_leverage(symbol)
        except Exception as e:
            logger.warning("LEVERAGE PRECHECK FAIL | %s requested=%sx | %s", symbol, requested, e)
            return None

        if open_count == 0:
            try:
                self.client.set_leverage(symbol, requested)
                logger.info("LEVERAGE SET | %s | %sx | symbol_flat=True", symbol, requested)
                return requested
            except AsterAPIError as e:
                logger.warning("LEVERAGE SET BLOCK | %s | requested=%sx | %s", symbol, requested, e)
                return None

        if current is None:
            logger.warning("LEVERAGE ENTRY BLOCK | %s | current=UNKNOWN positions=%s", symbol, open_count)
            return None
        hard = min(MAX_REQUESTED_LEVERAGE, BOT_HARD_MAX_LEVERAGE, API_HARD_MAX_LEVERAGE)
        if current < MIN_LEVERAGE or current > hard:
            logger.warning(
                "LEVERAGE ENTRY BLOCK | %s | current=%sx requested=%sx positions=%s hard_cap=%sx",
                symbol, current, requested, open_count, hard,
            )
            return None
        if current != requested:
            logger.warning(
                "LEVERAGE ADOPT | %s | current=%sx requested=%sx positions=%s | simbolo aberto: sem alterar exchange",
                symbol, current, requested, open_count,
            )
        return current

    def set_leverage(self, symbol: str, leverage: int) -> None:
        effective = self.prepare_leverage_for_open(symbol, leverage)
        if effective is None:
            raise RuntimeError(f"Leverage nao pode ser preparado com seguranca: {symbol} requested={leverage}")

# -----------------------------------------------------------------------------
# EXECUTION + VIRTUAL LOT BOOK
# -----------------------------------------------------------------------------

class ExecutionEngine:
    PREFIX = "a3"

    def __init__(self, client: AsterClient, account: AccountManager, rules: RulesBook, store: StateStore,
                 ledger: FillLedger):
        self.client = client
        self.account = account
        self.rules = rules
        self.store = store
        self.ledger = ledger
        self.orders = OrderManager(client, ledger)
        self.seq = 0
        # 48 random bits per process boot materially reduce cross-restart collision risk.
        # The 32-bit monotonic sequence never wraps silently; exhaustion fails closed.
        self.boot_id = uuid.uuid4().hex[:12]
        self.lock = threading.RLock()

    def client_id(self, strategy_id: str, action: str) -> str:
        with self.lock:
            if self.seq >= 0xFFFFFFFF:
                raise RuntimeError("clientOrderId sequence exhausted for this process; restart required")
            self.seq += 1
            seq = self.seq
        digest = hashlib.sha1(strategy_id.encode()).hexdigest()[:6]
        cid = f"{self.PREFIX}-{self.boot_id}-{digest}-{action[:4]}{seq:08x}"
        if len(cid) > 36:
            raise RuntimeError(f"clientOrderId interno excedeu 36 caracteres: {cid}")
        return cid

    @staticmethod
    def order_side(position_side: str, opening: bool) -> str:
        if position_side == "LONG":
            return "BUY" if opening else "SELL"
        return "SELL" if opening else "BUY"

    def _fill_from_response(self, symbol: str, resp: Dict[str, Any], client_id: str,
                            fallback_price: Decimal, requested_qty: Decimal) -> Tuple[Decimal, Decimal]:
        status = str(resp.get("status", "")).upper()
        qty = dec(resp.get("executedQty"))
        avg = dec(resp.get("avgPrice"))
        end = time.time() + ORDER_FILL_WAIT_SECONDS
        terminal = {"FILLED", "CANCELED", "EXPIRED", "REJECTED"}
        last_query_error: Optional[str] = None
        while time.time() < end:
            if status == "FILLED" and qty > 0:
                break
            if status in terminal and status != "FILLED":
                break
            try:
                q = self.client.query_order(symbol, client_id)
                status = str(q.get("status", status)).upper()
                qty = dec(q.get("executedQty") or qty)
                avg = dec(q.get("avgPrice") or avg)
                resp = q
                last_query_error = None
            except Exception as e:
                last_query_error = f"{type(e).__name__}:{e}"
            if status == "FILLED" and qty > 0:
                break
            time.sleep(ORDER_POLL_SECONDS)
        if qty <= 0:
            raise RuntimeError(
                f"Ordem sem fill confirmado: {symbol} client_id={client_id} status={status} query_error={last_query_error}"
            )
        # Never let a known partial market fill masquerade as a completed logical open/close.
        # Keeping state/ledger exposure unchanged forces reconciliation instead of orphaning residual quantity.
        step = self.rules.rules[symbol].step_size if self.rules and symbol in self.rules.rules else D("0.00000001")
        if qty + step < requested_qty or status != "FILLED":
            raise RuntimeError(
                f"MARKET PARTIAL/UNRESOLVED | {symbol} cid={client_id} status={status} "
                f"filled={qty} requested={requested_qty} query_error={last_query_error}"
            )
        if avg <= 0:
            avg = fallback_price
            logger.warning(f"FILL AVG AUSENTE | {symbol} | cid={client_id} | usando ref_price={fallback_price}")
        return qty, avg

    def _actual_trade_costs(self, symbol: str, order_id: Any, around_ms: int) -> Tuple[Decimal, Decimal]:
        if not LIVE_TRADING or not order_id:
            return D(0), D(0)
        try:
            rows = self.client.user_trades(symbol, max(0, around_ms-120000), around_ms+120000, 1000)
            matched = [x for x in (rows if isinstance(rows, list) else []) if str(x.get("orderId")) == str(order_id)]
            commission = sum((abs(dec(x.get("commission"))) for x in matched), D(0))
            realized = sum((dec(x.get("realizedPnl")) for x in matched), D(0))
            return commission, realized
        except Exception as e:
            logger.warning(f"ACTUAL FEE/P&L LOOKUP FAIL | {symbol} order_id={order_id} | {e}")
            return D(0), D(0)

    def market(self, strategy_id: str, symbol: str, position_side: str, qty: Decimal,
               opening: bool, ref_price: Decimal) -> Dict[str, Any]:
        with self.lock:
            side = self.order_side(position_side, opening)
            cid = self.client_id(strategy_id, "open" if opening else "close")
            if not LIVE_TRADING:
                logger.info(f"SIM ORDER | {strategy_id} | {'OPEN' if opening else 'CLOSE'} {side} posSide={position_side} qty={qty} px~{ref_price} cid={cid}")
                return {"qty": qty, "price": ref_price, "client_id": cid,
                        "order_id": f"SIM-{cid}", "status": "FILLED", "time": now_ms(),
                        "price_source": "SIM_REF"}
            submitted_ms = now_ms()
            resp = self.orders.submit_market(strategy_id, symbol, position_side, side, qty, cid,
                                             "OPEN" if opening else "CLOSE")
            filled, avg = self._fill_from_response(symbol, resp, cid, ref_price, qty)
            order_id = resp.get("orderId")
            if not order_id:
                try:
                    order_id = self.client.query_order(symbol, cid).get("orderId")
                except Exception:
                    pass
            commission, realized = self._actual_trade_costs(symbol, order_id, now_ms())
            self.ledger.order_state(cid, strategy_id, symbol, position_side,
                                    "OPEN" if opening else "CLOSE", "MARKET", qty,
                                    "FILLED", order_id, filled, avg, commission, realized,
                                    "MARKET_EXECUTION")
            logger.info(f"ORDER FILLED | {strategy_id} | {'OPEN' if opening else 'CLOSE'} {side} posSide={position_side} requested_qty={qty} filled_qty={filled} avg={avg} commission={commission} realized={realized} cid={cid}")
            if opening:
                try:
                    self.account.sync(force=True)
                except Exception as e:
                    logger.warning("POST-FILL ACCOUNT REFRESH FAIL | %s | cid=%s | %s", strategy_id, cid, e)
            return {"qty": filled, "price": avg, "client_id": cid, "order_id": order_id,
                    "status": "FILLED", "time": submitted_ms, "price_source": "EXCHANGE_AVG",
                    "commission_actual": commission, "realized_pnl_exchange": realized}

    def open_leg(self, strategy_id: str, symbol: str, position_side: str, sizing: Dict[str, Any],
                 reason: str) -> Optional[Dict[str, Any]]:
        with self.client._rate_limit_lock:
            _cooldown = max(0.0, self.client._rate_limit_until - time.time())
        if _cooldown > 0:
            logger.warning("OPEN BLOCK RATE LIMIT | %s | %s %s | cooldown_remaining=%.1fs",
                           strategy_id, symbol, position_side, _cooldown)
            return None
        requested_leverage = int(sizing["leverage"])
        effective_leverage = self.account.prepare_leverage_for_open(symbol, requested_leverage)
        if effective_leverage is None:
            logger.warning(
                "OPEN BLOCK LEVERAGE | %s | %s %s | requested=%sx reason=%s",
                strategy_id, symbol, position_side, requested_leverage, reason,
            )
            return None

        actual_notional = dec(sizing.get("notional"))
        if actual_notional <= 0:
            actual_notional = dec(sizing["qty"]) * dec(sizing["price"])
        effective_margin = actual_notional / D(effective_leverage)
        free_margin = self.account.free_margin(force=True)
        if effective_margin > free_margin:
            logger.warning(
                "OPEN BLOCK MARGIN | %s | %s | notional=%s effective_lev=%sx margin=%s free=%s",
                strategy_id, symbol, actual_notional, effective_leverage, effective_margin, free_margin,
            )
            return None

        fill = self.market(strategy_id, symbol, position_side, sizing["qty"], True, sizing["price"])
        leg = {
            "id": fill["client_id"],
            "side": position_side,
            "qty": str(fill["qty"]),
            "entry_price": str(fill["price"]),
            "signal_price": str(sizing["price"]),
            "price_source": fill.get("price_source", "UNKNOWN"),
            "leverage": effective_leverage,
            "requested_leverage": requested_leverage,
            "notional": str(fill["qty"] * fill["price"]),
            "margin_est": str((fill["qty"] * fill["price"]) / D(effective_leverage)),
            "opened_at": now_iso(),
            "reason": reason,
        }
        self.ledger.record_open_lot(leg["id"], strategy_id, symbol, position_side, fill["qty"], fill["price"], fill["client_id"])
        jsonl_append(TRADES_FILE, {"event": "OPEN", "strategy": strategy_id, "symbol": symbol,
                                  "leg": leg, "at": now_iso()})
        return leg

    def _close_record(self, strategy_id: str, symbol: str, leg: Dict[str, Any],
                      closed_qty: Decimal, exitp: Decimal, reason: str,
                      close_client_id: str, exit_source: str) -> Dict[str, Any]:
        entry = dec(leg["entry_price"])
        gross = (exitp - entry) * closed_qty if leg["side"] == "LONG" else (entry - exitp) * closed_qty
        fee_rate = D(os.getenv("TAKER_FEE_RATE", "0.00035"))
        entry_fee_est = entry * closed_qty * fee_rate
        exit_fee_est = exitp * closed_qty * fee_rate
        fees_est = entry_fee_est + exit_fee_est
        entry_commission_actual = D(0); exit_commission_actual = D(0); exchange_realized = D(0)
        if LIVE_TRADING:
            try:
                open_row = self.ledger.db.execute("SELECT commission FROM orders WHERE client_id=?", (str(leg.get("id")),)).fetchone()
                if open_row:
                    full_open_fee = dec(open_row[0])
                    opened_qty = max(dec(leg.get("qty")), closed_qty)
                    if full_open_fee > 0 and opened_qty > 0:
                        entry_commission_actual = full_open_fee * (closed_qty / opened_qty)

                row = self.ledger.db.execute("SELECT order_id,commission,realized_pnl FROM orders WHERE client_id=?", (close_client_id,)).fetchone()
                order_id = row[0] if row and row[0] else None
                if row:
                    exit_commission_actual = dec(row[1]); exchange_realized = dec(row[2])
                if exit_commission_actual <= 0:
                    if not order_id:
                        try:
                            order_id = self.client.query_order(symbol, close_client_id).get("orderId")
                        except Exception:
                            order_id = None
                    if order_id:
                        exit_commission_actual, exchange_realized = self._actual_trade_costs(symbol, order_id, now_ms())
                        self.ledger.order_state(close_client_id, strategy_id, symbol, str(leg.get("side")), "CLOSE", "EXCHANGE_FILL", closed_qty,
                                                "FILLED", order_id, closed_qty, exitp, exit_commission_actual, exchange_realized, reason)
            except Exception as e:
                logger.warning(f"CLOSE ACTUAL COST RECONCILE FAIL | {close_client_id} | {e}")
        entry_fee_used = entry_commission_actual if entry_commission_actual > 0 else entry_fee_est
        exit_fee_used = exit_commission_actual if exit_commission_actual > 0 else exit_fee_est
        fees_actual = entry_commission_actual + exit_commission_actual
        fees_used = entry_fee_used + exit_fee_used
        pnl = gross - fees_used
        rec = {
            "leg_id": leg["id"], "side": leg["side"], "qty": str(closed_qty),
            "entry_price": str(entry), "exit_price": str(exitp), "gross": str(gross),
            "fees_est": str(fees_est), "entry_fee_actual": str(entry_commission_actual),
            "exit_fee_actual": str(exit_commission_actual), "fees_actual": str(fees_actual),
            "fees_used": str(fees_used), "exchange_realized_pnl": str(exchange_realized),
            "pnl_est": str(pnl), "reason": reason,
            "closed_at": now_iso(), "close_client_id": close_client_id,
            "exit_source": exit_source,
        }
        self.ledger.record_close_lot(str(leg.get("id")), closed_qty)
        jsonl_append(TRADES_FILE, {"event": "CLOSE", "strategy": strategy_id, "symbol": symbol,
                                  "close": rec, "at": now_iso()})
        return rec

    def physical_position_qty(self, symbol: str, position_side: str) -> Decimal:
        if not LIVE_TRADING:
            return D("1e50")
        rows = self.client.positions()
        for p in (rows if isinstance(rows, list) else []):
            if str(p.get("symbol", "")).upper() != str(symbol).upper():
                continue
            if str(p.get("positionSide", "")).upper() != str(position_side).upper():
                continue
            return abs(dec(p.get("positionAmt")))
        return D(0)

    def close_leg(self, strategy_id: str, symbol: str, leg: Dict[str, Any],
                  ref_price: Decimal, reason: str,
                  max_physical_qty: Optional[Decimal] = None) -> Optional[Dict[str, Any]]:
        wanted = dec(leg["qty"])
        qty = wanted
        if LIVE_TRADING:
            physical = self.physical_position_qty(symbol, str(leg["side"]))
            if max_physical_qty is not None:
                physical = min(physical, max(D(0), dec(max_physical_qty)))
            qty = min(wanted, physical)
            step = self.rules.rules[symbol].step_size
            qty = floor_step(qty, step)
            if qty <= 0:
                logger.warning(
                    f"CLOSE LEG SKIP | {strategy_id} | {symbol} {leg.get('side')} | wanted={wanted} physical_available={physical} | "
                    "motivo=POSICAO_FISICA_JA_ENCERRADA_OU_RESERVADA_PARA_OUTRA_ESTRATEGIA"
                )
                return None
        fill = self.market(strategy_id, symbol, leg["side"], qty, False, ref_price)
        closed_qty = min(qty, fill["qty"])
        return self._close_record(strategy_id, symbol, leg, closed_qty, fill["price"], reason,
                                  fill["client_id"], fill.get("price_source", "MARKET"))

    def close_legs(self, strategy_id: str, symbol: str, legs: List[Dict[str, Any]],
                   ref_price: Decimal, reason: str) -> Tuple[Decimal, List[Dict[str, Any]]]:
        closes = []
        total = D(0)
        for leg in list(legs):
            try:
                c = self.close_leg(strategy_id, symbol, leg, ref_price, reason)
                if c is None:
                    continue
                closes.append(c)
                total += dec(c["pnl_est"])
            except Exception as e:
                logger.exception(f"CLOSE LEG FAIL | {strategy_id} | leg={leg.get('id')} | {e}")
                raise
        return total, closes

    def install_bracket(self, strategy_id: str, symbol: str, leg: Dict[str, Any],
                        tp_price: Decimal, stop_price: Decimal) -> Optional[Dict[str, Any]]:
        if not NATIVE_PROTECTIVE_ORDERS:
            return None
        side = leg["side"]
        qty = dec(leg["qty"])
        if qty <= 0:
            return None
        if side == "LONG":
            tp = self.rules.trigger_price(symbol, tp_price, "UP")
            sl = self.rules.trigger_price(symbol, stop_price, "DOWN")
        else:
            tp = self.rules.trigger_price(symbol, tp_price, "DOWN")
            sl = self.rules.trigger_price(symbol, stop_price, "UP")
        close_side = self.order_side(side, False)
        tp_cid = self.client_id(strategy_id, "tp")
        sl_cid = self.client_id(strategy_id, "stop")
        if not LIVE_TRADING:
            logger.info(f"SIM BRACKET | {strategy_id} | {symbol} {side} qty={qty} TP={tp} SL={sl}")
            return {
                "tp": {"client_id": tp_cid, "stop_price": str(tp), "type": "TAKE_PROFIT_MARKET", "status": "NEW"},
                "sl": {"client_id": sl_cid, "stop_price": str(sl), "type": "STOP_MARKET", "status": "NEW"},
                "working_type": PROTECTIVE_WORKING_TYPE,
                "installed_at": now_iso(),
            }
        tp_resp = self.orders.submit_conditional(
            strategy_id, symbol, side, close_side, qty, tp, tp_cid, "TAKE_PROFIT_MARKET",
            PROTECTIVE_WORKING_TYPE, PROTECTIVE_PRICE_PROTECT, "TAKE_PROFIT",
        )
        try:
            sl_resp = self.orders.submit_conditional(
                strategy_id, symbol, side, close_side, qty, sl, sl_cid, "STOP_MARKET",
                PROTECTIVE_WORKING_TYPE, PROTECTIVE_PRICE_PROTECT, "STOP_LOSS",
            )
        except Exception:
            try:
                self.cancel_and_confirm_terminal(symbol, tp_cid)
            except Exception as rollback_error:
                self.store.set_protection_block(strategy_id, f"BRACKET_INSTALL_ROLLBACK_UNCONFIRMED:{rollback_error}")
                logger.critical("BRACKET INSTALL ROLLBACK INCOMPLETO | %s | %s", strategy_id, rollback_error)
            raise
        # POST success alone is not proof of durable protection. Confirm both orders live/accepted.
        # Any confirmation failure triggers a confirmed rollback of BOTH siblings before the
        # caller is allowed to market-close the newly opened exposure.
        confirmation_error: Optional[Exception] = None
        try:
            for _cid in (tp_cid, sl_cid):
                _q = self.client.query_order(symbol, _cid)
                if str(_q.get("status") or "").upper() not in ("NEW", "PARTIALLY_FILLED", "FILLED"):
                    raise RuntimeError(
                        f"PROTECAO NATIVA NAO CONFIRMADA | {symbol} | cid={_cid} | status={_q.get('status')}"
                    )
        except Exception as exc:
            confirmation_error = exc
        if confirmation_error is not None:
            rollback_failures = []
            for _cid in (tp_cid, sl_cid):
                try:
                    self.cancel_and_confirm_terminal(symbol, _cid)
                except Exception as rollback_error:
                    rollback_failures.append((_cid, str(rollback_error)))
            if rollback_failures:
                reason = f"BRACKET_CONFIRM_ROLLBACK_UNCERTAIN:{rollback_failures}"
                self.store.set_protection_block(strategy_id, reason)
                raise RuntimeError(
                    f"{confirmation_error}; rollback de bracket nao confirmado: {rollback_failures}"
                ) from confirmation_error
            raise RuntimeError(str(confirmation_error)) from confirmation_error
        bracket = {
            "tp": {"client_id": tp_cid, "order_id": tp_resp.get("orderId"), "stop_price": str(tp),
                   "type": "TAKE_PROFIT_MARKET", "status": tp_resp.get("status", "NEW")},
            "sl": {"client_id": sl_cid, "order_id": sl_resp.get("orderId"), "stop_price": str(sl),
                   "type": "STOP_MARKET", "status": sl_resp.get("status", "NEW")},
            "working_type": PROTECTIVE_WORKING_TYPE,
            "installed_at": now_iso(),
        }
        logger.info(f"NATIVE BRACKET | {strategy_id} | {symbol} {side} qty={qty} | TP={tp} cid={tp_cid} | SL={sl} cid={sl_cid}")
        return bracket

    def install_stop_only(self, strategy_id: str, symbol: str, leg: Dict[str, Any],
                          stop_price: Decimal, reason: str = "STOP_LOSS") -> Optional[Dict[str, Any]]:
        """Instala STOP_MARKET nativo sem TP para uma perna MACD."""
        if not NATIVE_PROTECTIVE_ORDERS:
            return None
        side = str(leg["side"])
        qty = dec(leg["qty"])
        if qty <= 0:
            return None
        direction = "DOWN" if side == "LONG" else "UP"
        sl = self.rules.trigger_price(symbol, stop_price, direction)
        close_side = self.order_side(side, False)
        cid = self.client_id(strategy_id, "mstop")
        if not LIVE_TRADING:
            logger.info("SIM MACD STOP NATIVO | %s | %s %s qty=%s stop=%s", strategy_id, symbol, side, qty, sl)
            return {"client_id": cid, "order_id": f"SIM-{cid}", "stop_price": str(sl),
                    "type": "STOP_MARKET", "status": "NEW", "working_type": PROTECTIVE_WORKING_TYPE,
                    "qty": str(qty), "installed_at": now_iso(), "reason": reason}
        resp = self.orders.submit_conditional(
            strategy_id, symbol, side, close_side, qty, sl, cid, "STOP_MARKET",
            PROTECTIVE_WORKING_TYPE, PROTECTIVE_PRICE_PROTECT, reason,)
        try:
            confirmed = self.client.query_order(symbol, cid)
            if str(confirmed.get("status") or "").upper() not in ("NEW", "PARTIALLY_FILLED", "FILLED"):
                raise RuntimeError(
                    f"MACD STOP NATIVO NAO CONFIRMADO | {symbol} | cid={cid} | status={confirmed.get('status')}"
                )
        except Exception as confirm_error:
            try:
                self.cancel_and_confirm_terminal(symbol, cid)
            except Exception as rollback_error:
                reason_block = f"STOP_CONFIRM_ROLLBACK_UNCERTAIN:{cid}:{rollback_error}"
                self.store.set_protection_block(strategy_id, reason_block)
                raise RuntimeError(
                    f"Stop nativo sem confirmacao e rollback incerto: {confirm_error}; {rollback_error}"
                ) from confirm_error
            raise
        out = {"client_id": cid, "order_id": resp.get("orderId"), "stop_price": str(sl),
               "type": "STOP_MARKET", "status": confirmed.get("status", resp.get("status", "NEW")),
               "working_type": PROTECTIVE_WORKING_TYPE, "qty": str(qty),
               "installed_at": now_iso(), "reason": reason}
        logger.info("MACD STOP NATIVO INSTALADO | %s | %s %s qty=%s stop=%s cid=%s",
                    strategy_id, symbol, side, qty, sl, cid)
        return out

    def cancel_and_confirm_terminal(self, symbol: str, client_id: str) -> Dict[str, Any]:
        """Cancel a conditional order and prove a terminal state before relying on the cancellation."""
        if not client_id or not LIVE_TRADING:
            return {"status": "CANCELED", "clientOrderId": client_id}
        try:
            self.client.cancel_order(symbol, client_id)
        except AsterAPIError as e:
            if e.code not in (-2011, -2013):
                raise
        terminal = {"CANCELED", "EXPIRED", "FILLED", "REJECTED", "MISSING", "UNKNOWN_OR_GONE"}
        last: Dict[str, Any] = {}
        for _ in range(max(1, CANCEL_CONFIRM_ATTEMPTS)):
            try:
                last = self.client.query_order(symbol, client_id) or {}
                if str(last.get("status") or "").upper() in terminal:
                    return last
            except AsterAPIError as e:
                if e.code in (-2011, -2013):
                    return {"status": "MISSING", "clientOrderId": client_id}
                last = {"status": "UNKNOWN", "error": str(e), "clientOrderId": client_id}
            time.sleep(max(0.05, CANCEL_CONFIRM_DELAY_SECONDS))
        raise RuntimeError(f"CANCEL NAO CONFIRMADO | {symbol} | cid={client_id} | last={last}")

    def cancel_stop_only(self, symbol: str, stop_order: Optional[Dict[str, Any]]) -> bool:
        if not stop_order or not LIVE_TRADING:
            return True
        cid = str(stop_order.get("client_id") or "")
        if not cid:
            return True
        try:
            self.cancel_and_confirm_terminal(symbol, cid)
            return True
        except Exception as e:
            logger.warning("CANCEL MACD STOP FAIL | %s | %s | %s", symbol, cid, e)
            return False

    def stop_status(self, symbol: str, stop_order: Optional[Dict[str, Any]]) -> Optional[Dict[str, Any]]:
        if not LIVE_TRADING or not stop_order:
            return None
        cid = str(stop_order.get("client_id") or "")
        if not cid:
            return None
        try:
            q = self.client.query_order(symbol, cid)
            stop_order["status"] = str(q.get("status") or stop_order.get("status") or "")
            return q
        except AsterAPIError as e:
            if e.code in (-2011, -2013):
                return {"status": "MISSING", "clientOrderId": cid}
            raise

    def replace_stop_only(self, strategy_id: str, symbol: str, leg: Dict[str, Any],
                          old_stop: Optional[Dict[str, Any]], new_stop_price: Decimal,
                          reason: str = "TRAILING_STOP") -> Optional[Dict[str, Any]]:
        """Move a proteção nativa. Instala o novo stop antes de cancelar o antigo para evitar janela sem proteção."""
        if not NATIVE_PROTECTIVE_ORDERS:
            return None
        side = str(leg["side"])
        direction = "DOWN" if side == "LONG" else "UP"
        rounded = self.rules.trigger_price(symbol, new_stop_price, direction)
        current = dec((old_stop or {}).get("stop_price"))
        tick = self.rules.rules[symbol].tick_size
        if current > 0:
            tighter = rounded > current if side == "LONG" else rounded < current
            if not tighter or abs(rounded - current) < tick:
                return old_stop
        new_meta = self.install_stop_only(strategy_id, symbol, leg, rounded, reason)
        if new_meta:
            if old_stop and not self.cancel_stop_only(symbol, old_stop):
                # Avoid leaving two active stop orders if the old one could not be removed.
                self.cancel_stop_only(symbol, new_meta)
                logger.warning("MACD STOP MOVE ROLLBACK | %s | mantendo stop antigo=%s", strategy_id, current)
                return old_stop
            logger.info("MACD STOP NATIVO MOVIDO | %s | %s %s | %s -> %s",
                        strategy_id, symbol, side, current, rounded)
            return new_meta
        return old_stop

    def consume_stop_fill(self, strategy_id: str, symbol: str, leg: Dict[str, Any],
                          stop_order: Optional[Dict[str, Any]], ref_price: Decimal) -> Optional[Dict[str, Any]]:
        """Consome fill do stop. Em partial fill, zera o remanescente antes de encerrar o lote lógico."""
        if not LIVE_TRADING or not stop_order:
            return None
        q = self.stop_status(symbol, stop_order)
        if not q:
            return None
        status = str(q.get("status") or "")
        executed = dec(q.get("executedQty"))
        if status not in ("FILLED", "PARTIALLY_FILLED") or executed <= 0:
            return None
        requested = dec(leg["qty"])
        first_qty = min(requested, executed)
        avg1 = dec(q.get("avgPrice")) or ref_price
        cid = str(stop_order.get("client_id") or q.get("clientOrderId") or "NATIVE_STOP")
        if first_qty < requested:
            try:
                frozen = self.cancel_and_confirm_terminal(symbol, cid)
                latest_executed = min(requested, dec(frozen.get("executedQty") or executed))
                if latest_executed > first_qty:
                    first_qty = latest_executed
                    avg1 = dec(frozen.get("avgPrice")) or avg1
            except Exception as e:
                self.store.set_protection_block(strategy_id, f"PARTIAL_STOP_CANCEL_UNCONFIRMED:{e}")
                raise RuntimeError(f"Partial stop nao congelado; market fallback bloqueado: {e}") from e
            remaining = requested - first_qty
            if remaining <= 0:
                return self._close_record(strategy_id, symbol, leg, requested, avg1,
                                          "NATIVE_STOP_LOSS", cid, "ASTER_CONDITIONAL_STOP")
            logger.warning("MACD NATIVE STOP PARTIAL | %s | frozen_filled=%s remaining=%s; zerando remanescente a mercado",
                           strategy_id, first_qty, remaining)
            fallback = self.market(strategy_id, symbol, str(leg["side"]), remaining, False, ref_price)
            second_qty = dec(fallback["qty"])
            total_qty = first_qty + second_qty
            if total_qty <= 0:
                return None
            combined = (avg1 * first_qty + dec(fallback["price"]) * second_qty) / total_qty
            # _close_record needs one close id for accounting; use market fill id, whose commission is available.
            return self._close_record(strategy_id, symbol, leg, min(requested, total_qty), combined,
                                      "NATIVE_STOP_PARTIAL_PLUS_MARKET", str(fallback["client_id"]),
                                      "ASTER_STOP_PLUS_MARKET")
        return self._close_record(strategy_id, symbol, leg, first_qty, avg1,
                                  "NATIVE_STOP_LOSS", cid, "ASTER_CONDITIONAL_STOP")

    def cancel_bracket(self, symbol: str, bracket: Optional[Dict[str, Any]]) -> None:
        if not bracket or not LIVE_TRADING:
            return
        failures = []
        for key in ("tp", "sl"):
            cid = str((bracket.get(key) or {}).get("client_id") or "")
            if not cid:
                continue
            try:
                self.cancel_and_confirm_terminal(symbol, cid)
            except Exception as e:
                failures.append((cid, str(e)))
                logger.warning(f"CANCEL PROTECTION FAIL | {symbol} | {cid} | {e}")
        if failures:
            raise RuntimeError(f"Protecao nao teve cancelamento confirmado: {failures}")

    def consume_bracket_fill(self, strategy_id: str, symbol: str, leg: Dict[str, Any],
                             bracket: Optional[Dict[str, Any]], ref_price: Decimal) -> Optional[Dict[str, Any]]:
        if not LIVE_TRADING or not bracket:
            return None
        snapshots: Dict[str, Dict[str, Any]] = {}
        first_triggered_key: Optional[str] = None
        for key in ("tp", "sl"):
            meta = bracket.get(key) or {}
            cid = str(meta.get("client_id") or "")
            if not cid:
                continue
            try:
                q = self.client.query_order(symbol, cid)
            except AsterAPIError as e:
                if e.code in (-2011, -2013):
                    q = {"status": "MISSING", "clientOrderId": cid, "executedQty": "0"}
                else:
                    raise
            snapshots[key] = q
            status = str(q.get("status") or "").upper()
            meta["status"] = status
            if first_triggered_key is None and status in ("FILLED", "PARTIALLY_FILLED") and dec(q.get("executedQty")) > 0:
                first_triggered_key = key
        if first_triggered_key is None:
            return None

        # Freeze BOTH conditional orders before any market fallback. This closes the race where a
        # partially filled conditional keeps executing while a market close is submitted.
        for key in ("tp", "sl"):
            meta = bracket.get(key) or {}
            cid = str(meta.get("client_id") or "")
            if not cid:
                continue
            q = snapshots.get(key, {})
            if str(q.get("status") or "").upper() != "FILLED":
                try:
                    q = self.cancel_and_confirm_terminal(symbol, cid)
                except Exception as e:
                    self.store.set_protection_block(strategy_id, f"BRACKET_CANCEL_UNCONFIRMED:{key}:{e}")
                    raise RuntimeError(f"Bracket nao congelado; market fallback bloqueado: {key} {e}") from e
                snapshots[key] = q
                meta["status"] = str(q.get("status") or "").upper()

        requested_qty = dec(leg["qty"])
        conditional_qty = D(0)
        weighted_value = D(0)
        active_fill_keys: List[str] = []
        for key in ("tp", "sl"):
            q = snapshots.get(key, {})
            qfilled = max(D(0), dec(q.get("executedQty")))
            if qfilled <= 0:
                continue
            qavg = dec(q.get("avgPrice")) or ref_price
            conditional_qty += qfilled
            weighted_value += qfilled * qavg
            active_fill_keys.append(key)
        if conditional_qty > requested_qty:
            self.store.set_protection_block(strategy_id, f"BRACKET_OVERFILL:{conditional_qty}>{requested_qty}")
            raise RuntimeError(f"Bracket overfill detectado {strategy_id}: filled={conditional_qty} requested={requested_qty}")

        total_qty = conditional_qty
        total_value = weighted_value
        close_cid = str((snapshots.get(first_triggered_key) or {}).get("clientOrderId") or
                        (bracket.get(first_triggered_key) or {}).get("client_id") or "")
        remaining = requested_qty - conditional_qty
        if remaining > 0:
            fallback = self.market(strategy_id, symbol, str(leg["side"]), remaining, False, ref_price)
            fq = dec(fallback["qty"])
            total_qty += fq
            total_value += fq * dec(fallback["price"])
            close_cid = str(fallback["client_id"])
        if total_qty <= 0:
            return None
        avg = total_value / total_qty
        if len(active_fill_keys) > 1:
            reason = "NATIVE_BRACKET_MULTI_FILL"
        else:
            reason = "NATIVE_TAKE_PROFIT" if first_triggered_key == "tp" else "NATIVE_STOP_LOSS"
        logger.warning("NATIVE EXIT FILLED | %s | %s | qty=%s avg=%s conditional=%s",
                       strategy_id, reason, total_qty, avg, active_fill_keys)
        return self._close_record(
            strategy_id, symbol, leg, min(requested_qty, total_qty), avg, reason,
            close_cid, "ASTER_CONDITIONAL_OR_FALLBACK",
        )

    def install_basket_exit(self, strategy_id: str, symbol: str, legs: List[Dict[str, Any]],
                            target_price: Decimal, ref_price: Decimal) -> Optional[Dict[str, Any]]:
        if not NATIVE_PROTECTIVE_ORDERS or not legs:
            return None
        target_direction = "UP" if target_price >= ref_price else "DOWN"
        trigger = self.rules.trigger_price(symbol, target_price, target_direction)
        grouped: Dict[str, Decimal] = {}
        for leg in legs:
            side = str(leg["side"])
            grouped[side] = grouped.get(side, D(0)) + dec(leg["qty"])
        orders: List[Dict[str, Any]] = []
        placed: List[str] = []
        try:
            for position_side, qty in grouped.items():
                close_side = self.order_side(position_side, False)
                if target_direction == "UP":
                    order_type = "TAKE_PROFIT_MARKET" if position_side == "LONG" else "STOP_MARKET"
                else:
                    order_type = "STOP_MARKET" if position_side == "LONG" else "TAKE_PROFIT_MARKET"
                cid = self.client_id(strategy_id, f"bx{position_side[0].lower()}")
                if not LIVE_TRADING:
                    resp = {"orderId": f"SIM-{cid}", "status": "NEW"}
                else:
                    resp = self.orders.submit_conditional(
                        strategy_id, symbol, position_side, close_side, qty, trigger, cid, order_type,
                        PROTECTIVE_WORKING_TYPE, PROTECTIVE_PRICE_PROTECT, "BASKET_EXIT",
                    )
                    placed.append(cid)
                    confirmed = self.client.query_order(symbol, cid)
                    if str(confirmed.get("status") or "").upper() not in ("NEW", "PARTIALLY_FILLED", "FILLED"):
                        raise RuntimeError(
                            f"BASKET EXIT NAO CONFIRMADO | {strategy_id} | {symbol} | cid={cid} | status={confirmed.get('status')}"
                        )
                    resp = {**resp, **confirmed}
                orders.append({
                    "position_side": position_side,
                    "qty": str(qty),
                    "client_id": cid,
                    "order_id": resp.get("orderId"),
                    "type": order_type,
                    "stop_price": str(trigger),
                    "status": resp.get("status", "NEW"),
                })
        except Exception:
            if LIVE_TRADING:
                rollback_failures = []
                for cid in placed:
                    try:
                        self.cancel_and_confirm_terminal(symbol, cid)
                    except Exception as e:
                        rollback_failures.append((cid, str(e)))
                if rollback_failures:
                    self.store.set_protection_block(strategy_id, f"BASKET_INSTALL_ROLLBACK_UNCONFIRMED:{rollback_failures}")
                    logger.critical("BASKET INSTALL ROLLBACK INCOMPLETO | %s | %s", strategy_id, rollback_failures)
            raise
        logger.info(f"NATIVE BASKET EXIT | {strategy_id} | {symbol} target={trigger} orders={[(x['position_side'], x['qty'], x['type'], x['client_id']) for x in orders]}")
        return {"target_price": str(trigger), "orders": orders, "installed_at": now_iso()}

    def cancel_basket_exit(self, symbol: str, native_exit: Optional[Dict[str, Any]]) -> None:
        if not native_exit or not LIVE_TRADING:
            return
        failures = []
        for meta in native_exit.get("orders", []):
            cid = str(meta.get("client_id") or "")
            if not cid:
                continue
            try:
                self.cancel_and_confirm_terminal(symbol, cid)
            except Exception as e:
                failures.append((cid, str(e)))
                logger.warning(f"CANCEL BASKET EXIT FAIL | {symbol} | {cid} | {e}")
        if failures:
            raise RuntimeError(f"Basket exit sem cancelamento confirmado: {failures}")

    def basket_exit_health(self, symbol: str, native_exit: Optional[Dict[str, Any]]) -> str:
        if not native_exit:
            return "MISSING"
        if not LIVE_TRADING:
            return "LIVE"
        expected = [str(x.get("client_id") or "") for x in native_exit.get("orders", []) if x.get("client_id")]
        if not expected:
            return "MISSING"
        try:
            rows = self.client.open_orders(symbol)
            if not isinstance(rows, list):
                return "UNKNOWN"
            live_cids = {
                str(r.get("clientOrderId") or r.get("origClientOrderId") or "")
                for r in rows
                if str(r.get("status", "NEW")) in ("NEW", "PARTIALLY_FILLED")
            }
            missing = [cid for cid in expected if cid not in live_cids]
            if missing:
                logger.warning("NATIVE BASKET EXIT AUSENTE | %s | missing=%s esperado=%s", symbol, missing, expected)
                return "MISSING"
            return "LIVE"
        except Exception as e:
            logger.warning("NATIVE BASKET EXIT VERIFY UNKNOWN | %s | %s", symbol, e)
            return "UNKNOWN"

    def basket_exit_is_live(self, symbol: str, native_exit: Optional[Dict[str, Any]]) -> bool:
        return self.basket_exit_health(symbol, native_exit) == "LIVE"

    def consume_basket_exit(self, strategy_id: str, symbol: str, legs: List[Dict[str, Any]],
                            native_exit: Optional[Dict[str, Any]], ref_price: Decimal,
                            close_reason: str = "NATIVE_RANGE_BASKET_TAKE_PROFIT"
                            ) -> Optional[Tuple[Decimal, List[Dict[str, Any]]]]:
        if not LIVE_TRADING or not native_exit:
            return None
        orders = native_exit.get("orders", [])
        snapshots: Dict[str, Dict[str, Any]] = {}
        any_fill = False
        for meta in orders:
            cid = str(meta.get("client_id") or "")
            if not cid:
                continue
            ps = str(meta["position_side"])
            try:
                q = self.client.query_order(symbol, cid)
            except AsterAPIError as e:
                if e.code in (-2011, -2013):
                    q = {"status": "MISSING", "clientOrderId": cid, "executedQty": "0"}
                else:
                    raise
            snapshots[ps] = q
            meta["status"] = str(q.get("status") or "").upper()
            if meta["status"] in ("FILLED", "PARTIALLY_FILLED") and dec(q.get("executedQty")) > 0:
                any_fill = True
        if not any_fill:
            return None

        # Once any basket conditional starts filling, freeze every still-live sibling BEFORE
        # calculating a market remainder. Then use the post-cancel executedQty as authoritative.
        for meta in orders:
            cid = str(meta.get("client_id") or "")
            if not cid:
                continue
            ps = str(meta["position_side"])
            q = snapshots.get(ps, {})
            if str(q.get("status") or "").upper() != "FILLED":
                try:
                    q = self.cancel_and_confirm_terminal(symbol, cid)
                except Exception as e:
                    self.store.set_protection_block(strategy_id, f"BASKET_PARTIAL_CANCEL_UNCONFIRMED:{ps}:{e}")
                    raise RuntimeError(f"Basket exit nao congelado; market fallback bloqueado: {ps} {e}") from e
                snapshots[ps] = q
                meta["status"] = str(q.get("status") or "").upper()

        side_avg: Dict[str, Decimal] = {}
        side_qty: Dict[str, Decimal] = {}
        for meta in orders:
            ps = str(meta["position_side"])
            wanted = dec(meta.get("qty"))
            q = snapshots.get(ps, {})
            filled = max(D(0), dec(q.get("executedQty")))
            if filled > wanted:
                self.store.set_protection_block(strategy_id, f"BASKET_OVERFILL:{ps}:{filled}>{wanted}")
                raise RuntimeError(f"Basket overfill {strategy_id} {ps}: filled={filled} wanted={wanted}")
            avg = dec(q.get("avgPrice"))
            if filled > 0 and avg <= 0:
                avg = ref_price
            remaining = wanted - filled
            if remaining > 0:
                fallback = self.market(strategy_id, symbol, ps, remaining, False, ref_price)
                totalq = filled + dec(fallback["qty"])
                avg = ((avg * filled) + (dec(fallback["price"]) * dec(fallback["qty"]))) / totalq if totalq > 0 else ref_price
                filled = totalq
            side_avg[ps] = avg if avg > 0 else ref_price
            side_qty[ps] = filled

        closes: List[Dict[str, Any]] = []
        total = D(0)
        remaining_by_side = dict(side_qty)
        for leg in legs:
            ps = str(leg["side"])
            leg_qty = dec(leg["qty"])
            alloc = min(leg_qty, remaining_by_side.get(ps, D(0)))
            if alloc <= 0:
                raise RuntimeError(f"Native basket exit sem quantidade suficiente para {strategy_id} {ps}")
            cid = str((snapshots.get(ps) or {}).get("clientOrderId") or "NATIVE_BASKET")
            rec = self._close_record(strategy_id, symbol, leg, alloc, side_avg[ps],
                                     close_reason, cid, "ASTER_CONDITIONAL_BASKET")
            closes.append(rec)
            total += dec(rec["pnl_est"])
            remaining_by_side[ps] = remaining_by_side.get(ps, D(0)) - alloc
        logger.warning(f"NATIVE BASKET EXIT FILLED | {strategy_id} | pnl={total} | target={native_exit.get('target_price')}")
        return total, closes

# -----------------------------------------------------------------------------
# OWNERSHIP / INTERFERENCE CONTROL
# -----------------------------------------------------------------------------

def acquire_owner(store: StateStore, symbol: str, strategy_id: str) -> bool:
    if ALLOW_MULTI_STRATEGY_SAME_SYMBOL:
        return True
    with store.lock:
        owner = store.state["symbol_owner"].get(symbol)
        if owner in (None, strategy_id):
            store.state["symbol_owner"][symbol] = strategy_id
            store.save()
            return True
        return False

def release_owner(store: StateStore, symbol: str, strategy_id: str) -> None:
    if ALLOW_MULTI_STRATEGY_SAME_SYMBOL:
        return
    with store.lock:
        if store.state["symbol_owner"].get(symbol) == strategy_id:
            store.state["symbol_owner"][symbol] = None
            store.save()

# -----------------------------------------------------------------------------
# UTILITY: apply realized PnL to strategy state
# -----------------------------------------------------------------------------

def _apply_realized_pnl_to_state(st: Dict[str, Any], pnl: Decimal, exit_price: Decimal,
                                 close_reason: str, is_macd: bool = False) -> None:
    before = dec(st.get("equity"))
    after = before + pnl
    st["equity"] = str(after)
    st["realized_pnl"] = str(dec(st.get("realized_pnl")) + pnl)
    rd_before = dec(st.get("recovery_deficit"))
    if pnl < 0:
        rd_after = rd_before + (-pnl)
        st["losses"] = int(st.get("losses", 0)) + 1
        st["last_result"] = "LOSS"
        if is_macd:
            st["loss_streak"] = int(st.get("loss_streak", 0)) + 1
            st["recovery_level"] = min(
                MAX_RECOVERY_FAILURES,
                max(1, int(st.get("recovery_level", 0)) + 1),
            )
    elif pnl > 0:
        rd_after = max(D(0), rd_before - pnl)
        st["wins"] = int(st.get("wins", 0)) + 1
        st["last_result"] = "WIN"
        if is_macd and rd_after == 0:
            st["loss_streak"] = 0
            st["recovery_level"] = 0
    else:
        rd_after = rd_before
        st["last_result"] = "FLAT"
    st["recovery_deficit"] = str(rd_after)
    if is_macd and int(st.get("loss_streak", 0)) >= MAX_RECOVERY_FAILURES:
        st["protect"] = True
        st["protect_anchor"] = str(exit_price)
    st["last_update"] = now_iso()

# -----------------------------------------------------------------------------
# RANGE ENGINE
# -----------------------------------------------------------------------------

class RangeEngine:
    def __init__(self, symbol: str, client: AsterClient, md: MarketData, news: NewsFilter,
                 account: AccountManager, exe: ExecutionEngine, store: StateStore,
                 state_bucket: str = "range", state_key: Optional[str] = None,
                 grid_id: str = "LEGACY", grid_phase: Decimal = D(0),
                 allow_new_entries: bool = True):
        self.symbol = symbol
        self.state_bucket = state_bucket
        self.state_key = state_key or symbol
        self.grid_id = grid_id
        self.grid_phase = grid_phase
        self.allow_new_entries = allow_new_entries
        self.id = f"RANGE:{symbol}" if grid_id == "LEGACY" else f"RANGE:{symbol}:{grid_id}"
        self.client = client
        self.md = md
        self.news = news
        self.account = account
        self.exe = exe
        self.store = store

    def st(self) -> Dict[str, Any]:
        return self.store.state[self.state_bucket][self.state_key]

    def _anchor_from_price(self, price: Decimal) -> Decimal:
        return price * (D(1) + self.grid_phase)

    def _grid_migration_ready(self) -> bool:
        if self.grid_id == "LEGACY":
            return True
        return bool(self.store.state.get("maintenance", {}).get("range_grid_v19_migrated", {}).get(self.symbol))

    def _other_strategy_reserved_qty(self, position_side: str) -> Decimal:
        side = str(position_side).upper()
        total = self.exe.ledger.open_by_symbol_side().get((self.symbol, side), D(0))
        own = self.exe.ledger.open_strategy_qty(self.id, self.symbol, side)
        return max(D(0), total - own)

    def _range_physical_capacity(self, position_side: str) -> Decimal:
        actual = self.exe.physical_position_qty(self.symbol, position_side)
        reserved = self._other_strategy_reserved_qty(position_side)
        return max(D(0), actual - reserved)

    def _reconcile_range_ghost_legs(self, b: Dict[str, Any], price: Decimal) -> bool:
        if not LIVE_TRADING:
            return False
        legs = list(b.get("legs") or [])
        if not legs:
            return False
        changed = False
        rebuilt: List[Dict[str, Any]] = []
        by_side_capacity = {
            "LONG": self._range_physical_capacity("LONG"),
            "SHORT": self._range_physical_capacity("SHORT"),
        }
        used = {"LONG": D(0), "SHORT": D(0)}
        for leg in legs:
            side = str(leg.get("side", "")).upper()
            qty = dec(leg.get("qty"))
            if side not in ("LONG", "SHORT") or qty <= 0:
                continue
            available = max(D(0), by_side_capacity[side] - used[side])
            keep = min(qty, available)
            step = self.exe.rules.rules[self.symbol].step_size
            keep = floor_step(keep, step)
            if keep <= 0:
                changed = True
                logger.warning(
                    f"RANGE GHOST LEG REMOVIDA | {self.symbol} | side={side} leg={leg.get('id')} virtual_qty={qty} "
                    f"physical_capacity={by_side_capacity[side]} reserved_other={self._other_strategy_reserved_qty(side)}"
                )
                continue
            if keep < qty:
                changed = True
                new_leg = dict(leg)
                new_leg["qty"] = str(keep)
                new_leg["notional"] = str(keep * dec(new_leg.get("entry_price")))
                leg = new_leg
                logger.warning(
                    f"RANGE GHOST LEG REDUZIDA | {self.symbol} | side={side} leg={leg.get('id')} old_qty={qty} new_qty={keep}"
                )
            rebuilt.append(leg)
            used[side] += keep
        if not changed:
            return False
        self.exe.cancel_basket_exit(self.symbol, b.get("native_basket_exit"))
        self.exe.cancel_basket_exit(self.symbol, b.get("native_basket_stop"))
        if b.get("native_bracket"):
            self.exe.cancel_bracket(self.symbol, b.get("native_bracket"))
        b["native_basket_exit"] = None
        b["native_basket_stop"] = None
        b["native_bracket"] = None
        b["legs"] = rebuilt
        st = self.st()
        if not rebuilt:
            st["basket"] = None
            st["status"] = "PROTECT" if dec(st.get("recovery_deficit")) > 0 else "IDLE"
            st["anchor"] = str(self._anchor_from_price(price))
            st["protect_anchor"] = str(price) if st["status"] == "PROTECT" else None
            st["last_result"] = "RECONCILED_ALREADY_CLOSED"
            st["last_update"] = now_iso()
            self.store.save()
            release_owner(self.store, self.symbol, self.id)
            logger.warning(
                f"RANGE BASKET RECONCILIADO | {self.symbol} | nenhuma quantidade RANGE restante na Aster | "
                f"status={st['status']} equity_preservada={st.get('equity')} RD_preservado={st.get('recovery_deficit')}"
            )
            return True
        b["active_side"] = str(rebuilt[-1].get("side"))
        st["last_update"] = now_iso()
        self.store.save()
        return False

    def _new_anchor(self, price: Decimal) -> None:
        st = self.st()
        st["anchor"] = str(self._anchor_from_price(price))
        st["status"] = "IDLE"
        st["basket"] = None
        st["failures"] = 0
        st["protect_anchor"] = None
        st["last_update"] = now_iso()
        self.store.save()
        release_owner(self.store, self.symbol, self.id)
        logger.info(f"RANGE ANCHOR | {self.symbol} | grid={self.grid_id} phase={self.grid_phase} anchor={st['anchor']}")

    def _target_recovery_profit(self, st: Dict[str, Any], basket: Optional[Dict[str, Any]] = None) -> Decimal:
        rd = dec(st.get("recovery_deficit"))
        if basket:
            pass
        return rd * RECOVERY_MULTIPLIER if rd > 0 else D(0)

    @staticmethod
    def unrealized(legs: List[Dict[str, Any]], price: Decimal) -> Decimal:
        total = D(0)
        for leg in legs:
            q = dec(leg["qty"]); ep = dec(leg["entry_price"])
            total += (price - ep) * q if leg["side"] == "LONG" else (ep - price) * q
        return total

    @staticmethod
    def estimated_net_pnl(legs: List[Dict[str, Any]], exit_price: Decimal) -> Decimal:
        fee_rate = D(os.getenv("TAKER_FEE_RATE", "0.00035"))
        total = D(0)
        for leg in legs:
            qty = dec(leg["qty"])
            entry = dec(leg["entry_price"])
            gross = (exit_price - entry) * qty if leg["side"] == "LONG" else (entry - exit_price) * qty
            fees = (entry * qty + exit_price * qty) * fee_rate
            total += gross - fees
        return total

    def dynamic_recovery_notional(self, st: Dict[str, Any], basket: Dict[str, Any],
                                  new_side: str, entry_price: Decimal,
                                  recovery_level: int) -> Tuple[Decimal, Decimal, Decimal]:
        tp_price = entry_price * (D(1) + RANGE_TAKE_PROFIT_PCT) \
            if new_side == "LONG" else entry_price * (D(1) - RANGE_TAKE_PROFIT_PCT)
        existing_at_tp = self.estimated_net_pnl(basket.get("legs", []), tp_price)
        base_notional = configured_strategy_initial_notional(self.symbol, st)
        if AUTO_SCALE_NOTIONAL_WITH_EQUITY:
            base_notional = max(base_notional, dec(st.get("equity")))
        desired_basket_profit = dec(st.get("recovery_deficit")) + base_notional * RANGE_TAKE_PROFIT_PCT
        fee_rate = D(os.getenv("TAKER_FEE_RATE", "0.00035"))
        move_yield = abs(tp_price - entry_price) / entry_price
        round_trip_fee_yield = fee_rate * (D(1) + tp_price / entry_price)
        net_yield = move_yield - round_trip_fee_yield
        if net_yield <= 0:
            raise RuntimeError("RANGE recovery sem rendimento liquido positivo no TP")
        dynamic_notional = max(D(0), (desired_basket_profit - existing_at_tp) / net_yield)
        classic_floor = base_notional * (RECOVERY_MULTIPLIER ** recovery_level)
        requested = max(dynamic_notional, classic_floor)
        capped = min(requested, configured_max_recovery_notional(self.symbol))
        if capped < requested:
            logger.warning(f"RANGE DYNAMIC RECOVERY CAPPED | {self.symbol} | requested={requested} cap={capped} level={recovery_level}")
        return capped, tp_price, existing_at_tp

    def _open(self, side: str, price: Decimal, target_profit: Optional[Decimal], reason: str,
              recovery_level: int = 0,
              desired_notional_override: Optional[Decimal] = None) -> Optional[Dict[str, Any]]:
        st = self.st()
        blocked, why = self.news.blocked()
        if blocked:
            logger.info(f"RANGE BLOQUEADO NEWS | {self.symbol} | {why}")
            return None
        if self.store.killed() != "OFF":
            return None
        gate_ok, gate_reason = self.store.entry_allowed()
        if not gate_ok:
            logger.warning(f"RANGE ENTRY GATE | {self.symbol} | {gate_reason}")
            return None
        if not self.md.is_fresh(self.symbol):
            logger.warning(f"RANGE ENTRY STALE PRICE | {self.symbol} | age_s={self.md.age(self.symbol):.3f}")
            return None
        if not acquire_owner(self.store, self.symbol, self.id):
            logger.info(f"RANGE BLOQUEADO OWNER | {self.symbol} | owner={self.store.state['symbol_owner'].get(self.symbol)}")
            return None
        sizing = self.account.sizing_for_profit_target(
            self.symbol, price, st, target_profit, RANGE_TAKE_PROFIT_PCT, RANGE_HARD_STOP_PCT,
            recovery_level=recovery_level,
            desired_notional_override=desired_notional_override,
            recovery_multiplier=RECOVERY_MULTIPLIER,
        )
        if not sizing:
            release_owner(self.store, self.symbol, self.id)
            logger.warning(f"RANGE SIZING NAO CABE | {self.symbol} | target={target_profit}")
            return None
        logger.info(f"RANGE SIZING | {self.symbol} | side={side} target={target_profit} lev={sizing['leverage']}x notional={sizing['notional']} margin={sizing['margin']} qty={sizing['qty']} meta={sizing['meta']}")
        leg = self.exe.open_leg(self.id, self.symbol, side, sizing, reason)
        if not leg:
            release_owner(self.store, self.symbol, self.id)
            return None
        return leg

    def _start_basket(self, side: str, price: Decimal) -> None:
        st = self.st()
        rd = dec(st.get("recovery_deficit"))
        target = rd * RECOVERY_MULTIPLIER if rd > 0 else None
        leg = self._open(side, price, target, "RANGE_INITIAL" if rd == 0 else "RANGE_REARM_RECOVERY",
                         recovery_level=1 if rd > 0 else 0)
        if not leg:
            return
        anchor = dec(st["anchor"])
        entry = dec(leg["entry_price"])
        tp_price = entry * (D(1) + RANGE_TAKE_PROFIT_PCT) if side == "LONG" else entry * (D(1) - RANGE_TAKE_PROFIT_PCT)
        hard_stop_price = entry * (D(1) - RANGE_HARD_STOP_PCT) if side == "LONG" else entry * (D(1) + RANGE_HARD_STOP_PCT)
        try:
            native_bracket = self.exe.install_bracket(self.id, self.symbol, leg, tp_price, hard_stop_price)
            if NATIVE_PROTECTIVE_ORDERS and not native_bracket:
                raise RuntimeError("native bracket nao confirmado")
        except Exception as exc:
            logger.exception(
                "RANGE PROTECTION INSTALL FAIL | %s grid=%s | fechando perna recem-aberta | %s",
                self.symbol, self.grid_id, exc,
            )
            try:
                self.exe.close_leg(
                    self.id, self.symbol, leg, price,
                    "RANGE_PROTECTION_INSTALL_FAILED",
                    max_physical_qty=dec(leg.get("qty")),
                )
            finally:
                self.store.set_protection_block(self.id, "RANGE_PROTECTION_INSTALL_FAILED")
                release_owner(self.store, self.symbol, self.id)
            return
        self.store.set_protection_block(self.id, None)
        st["status"] = "BASKET"
        st["basket"] = {
            "origin_anchor": str(anchor),
            "initial_side": side,
            "signal_entry": str(price),
            "initial_entry": str(entry),
            "legs": [leg],
            "active_side": side,
            "alternations": 0,
            "next_reverse_price": str(anchor),
            "tp_price": str(tp_price),
            "hard_stop_price": str(hard_stop_price),
            "native_bracket": native_bracket,
            "native_basket_exit": None,
            "native_basket_stop": None,
            "started_at": now_iso(),
        }
        st["last_update"] = now_iso()
        self.store.save()
        logger.info(f"RANGE BASKET START | {self.symbol} | {side} signal={price} fill={entry} | anchor={anchor} TP={tp_price} SL={hard_stop_price}")

    def _close_basket(self, price: Decimal, reason: str, protect_after: bool = False) -> None:
        st = self.st(); b = st.get("basket")
        if not b:
            return
        self.exe.cancel_bracket(self.symbol, b.get("native_bracket"))
        self.exe.cancel_basket_exit(self.symbol, b.get("native_basket_exit"))
        self.exe.cancel_basket_exit(self.symbol, b.get("native_basket_stop"))
        rd_before = dec(st.get("recovery_deficit"))
        recovery_attempt = int(b.get("alternations", 0)) > 0 or rd_before > 0
        recovery_tp_hit = reason == "RECOVERY_LEG_TP_1PCT_CLOSE_ALL"
        pnl = D(0)
        reserved_used = {"LONG": D(0), "SHORT": D(0)}
        for _leg in list(b.get("legs", [])):
            _side = str(_leg.get("side", "")).upper()
            _reserved_other = self._other_strategy_reserved_qty(_side)
            _actual = self.exe.physical_position_qty(self.symbol, _side)
            _available_range = max(D(0), _actual - _reserved_other - reserved_used.get(_side, D(0)))
            _c = self.exe.close_leg(
                self.id, self.symbol, _leg, price, reason,
                max_physical_qty=_available_range,
            )
            if _c is not None:
                pnl += dec(_c.get("pnl_est"))
                reserved_used[_side] = reserved_used.get(_side, D(0)) + dec(_c.get("qty"))

        _apply_realized_pnl_to_state(st, pnl, price, reason, is_macd=False)
        rd_after = dec(st.get("recovery_deficit"))
        recovery_success = recovery_attempt and recovery_tp_hit and rd_before > 0 and rd_after == 0 and pnl > 0
        recovery_partial = recovery_attempt and recovery_tp_hit and rd_after > 0

        st["basket"] = None
        st["failures"] = 0
        st["anchor"] = str(self._anchor_from_price(price))

        if recovery_success:
            st["recovery_deficit"] = "0"
            st["status"] = "IDLE"
            st["protect_anchor"] = None
            st["last_result"] = "RECOVERY_WIN_RESET"
            protect_after = False
            logger.warning(
                f"RANGE RECOVERY RESET | {self.symbol} grid={self.grid_id} | "
                f"pnl={pnl} RD_before={rd_before} RD_after=0"
            )
        elif recovery_partial:
            st["status"] = "PROTECT"
            st["protect_anchor"] = str(price)
            st["last_result"] = "RECOVERY_PARTIAL"
            protect_after = True
            logger.warning(
                f"RANGE RECOVERY PARTIAL | {self.symbol} grid={self.grid_id} | "
                f"pnl={pnl} RD_before={rd_before} RD_remaining={rd_after}"
            )
        elif protect_after:
            st["status"] = "PROTECT"
            st["protect_anchor"] = str(price)
        else:
            st["status"] = "IDLE"
            st["protect_anchor"] = None

        st["last_update"] = now_iso()
        self.store.save()
        release_owner(self.store, self.symbol, self.id)
        logger.info(
            f"RANGE CLOSE | {self.symbol} grid={self.grid_id} | reason={reason} pnl={pnl} "
            f"equity={st['equity']} RD={st['recovery_deficit']} protect={protect_after} "
            f"recovery_success={recovery_success}"
        )

    def _reverse(self, price: Decimal) -> None:
        st = self.st(); b = st.get("basket")
        if not b:
            return
        if int(b.get("alternations", 0)) >= MAX_RECOVERY_FAILURES:
            self._close_basket(price, "MAX_RECOVERY_FAILURES_AFTER_FULL_ATTEMPTS", protect_after=True)
            return
        current = b["active_side"]
        new_side = "SHORT" if current == "LONG" else "LONG"
        mtm = self.unrealized(b["legs"], price)
        accumulated_loss = dec(st.get("recovery_deficit")) + max(D(0), -mtm)
        target = accumulated_loss * RECOVERY_MULTIPLIER
        if target <= 0:
            target = None
        recovery_level = min(int(b.get("alternations", 0)) + 1, MAX_RECOVERY_FAILURES)
        self.exe.cancel_bracket(self.symbol, b.get("native_bracket"))
        self.exe.cancel_basket_exit(self.symbol, b.get("native_basket_exit"))
        self.exe.cancel_basket_exit(self.symbol, b.get("native_basket_stop"))
        b["native_bracket"] = None
        b["native_basket_exit"] = None
        b["native_basket_stop"] = None
        desired_notional, recovery_tp_signal, existing_at_tp = self.dynamic_recovery_notional(
            st, b, new_side, price, recovery_level
        )
        leg = self._open(new_side, price, target, "RANGE_ALTERNATING_RECOVERY",
                         recovery_level=recovery_level,
                         desired_notional_override=desired_notional)
        if not leg:
            if len(b.get("legs", [])) == 1:
                original_leg = b["legs"][0]
                b["native_bracket"] = self.exe.install_bracket(
                    self.id, self.symbol, original_leg,
                    dec(b.get("tp_price")), dec(b.get("hard_stop_price")),
                )
                self.store.save()
            return
        recovery_entry = dec(leg["entry_price"])
        recovery_tp = recovery_entry * (D(1) + RANGE_TAKE_PROFIT_PCT) \
            if new_side == "LONG" else recovery_entry * (D(1) - RANGE_TAKE_PROFIT_PCT)
        b["legs"].append(leg)
        b["active_side"] = new_side
        b["alternations"] = int(b.get("alternations", 0)) + 1
        st["failures"] = b["alternations"]
        if new_side == b["initial_side"]:
            b["next_reverse_price"] = b["origin_anchor"]
        else:
            b["next_reverse_price"] = b["initial_entry"]
        b["recovery_tp_price"] = str(recovery_tp)
        recovery_stop = recovery_entry * (D(1) - RANGE_HARD_STOP_PCT) if new_side == "LONG" else recovery_entry * (D(1) + RANGE_HARD_STOP_PCT)
        b["recovery_stop_price"] = str(recovery_stop)
        protection_errors = []
        try:
            b["native_basket_exit"] = self.exe.install_basket_exit(
                self.id + ":TP", self.symbol, b["legs"], recovery_tp, recovery_entry
            )
        except Exception as e:
            b["native_basket_exit"] = None
            protection_errors.append(f"TP:{e}")
            logger.exception(f"RANGE NATIVE BASKET TP FAIL | {self.symbol} | {e}")
        try:
            b["native_basket_stop"] = self.exe.install_basket_exit(
                self.id + ":SL", self.symbol, b["legs"], recovery_stop, recovery_entry
            )
        except Exception as e:
            b["native_basket_stop"] = None
            protection_errors.append(f"SL:{e}")
            logger.exception(f"RANGE NATIVE BASKET SL FAIL | {self.symbol} | {e}")
        if NATIVE_PROTECTIVE_ORDERS and (protection_errors or not b.get("native_basket_exit") or not b.get("native_basket_stop")):
            reason = "RANGE_RECOVERY_PROTECTION_INSTALL_FAILED:" + "|".join(protection_errors or ["MISSING_NATIVE_EXIT"])
            self.store.set_protection_block(self.id, reason)
            # Never market-close while a sibling conditional may still be live. First prove
            # cancellation of every successfully installed basket order.
            try:
                self.exe.cancel_basket_exit(self.symbol, b.get("native_basket_exit"))
                self.exe.cancel_basket_exit(self.symbol, b.get("native_basket_stop"))
            except Exception as cancel_error:
                self.store.set_protection_block(
                    self.id, f"RANGE_RECOVERY_PROTECTION_CANCEL_UNCERTAIN:{cancel_error}"
                )
                st["last_update"] = now_iso()
                self.store.save()
                logger.critical(
                    "RANGE RECOVERY PROTECTION UNCERTAIN | %s | market close bloqueado para evitar corrida | %s",
                    self.symbol, cancel_error,
                )
                return
            b["native_basket_exit"] = None
            b["native_basket_stop"] = None
            logger.critical(
                "RANGE RECOVERY PROTECTION FAIL-CLOSED | %s | fechando cesta apos rollback confirmado | %s",
                self.symbol, reason,
            )
            self._close_basket(price, "RANGE_RECOVERY_PROTECTION_INSTALL_FAILED", protect_after=True)
            return
        self.store.set_protection_block(self.id, None)
        logger.warning(f"RANGE RECOVERY PROTECTION | {self.symbol} | TP={recovery_tp} SL={recovery_stop} | native_tp={bool(b.get('native_basket_exit'))} native_sl={bool(b.get('native_basket_stop'))}")
        st["last_update"] = now_iso()
        self.store.save()
        logger.warning(f"RANGE REVERSE 4X DINAMICO | {self.symbol} | new={new_side} @{recovery_entry} | mtm={mtm} existing_at_tp={existing_at_tp} desired_notional={desired_notional} recovery_tp={recovery_tp} failures={st['failures']}")

    def tick(self, price: Decimal) -> None:
        with self.store.lock:
            if not self._grid_migration_ready():
                return
            st = self.st()
            if st.get("anchor") is None:
                self._new_anchor(price)
                return
            status = st.get("status", "IDLE")
            anchor = dec(st["anchor"])
            if status == "PROTECT":
                pa = dec(st.get("protect_anchor") or anchor)
                signed_move = pct_change(pa, price)
                move = abs(signed_move)
                if move >= RANGE_REARM_PCT:
                    # V48: os 3% do PROTECT sao o proprio gatilho de reentrada.
                    # Nao reancorar no preco atual e exigir RANGE_TRIGGER_PCT adicional,
                    # pois isso transformaria a regra efetiva em 3% + 1%.
                    # Se a abertura for bloqueada (news/risk/margem/gate), _start_basket
                    # retorna sem alterar PROTECT; assim o robô tenta novamente enquanto
                    # o preco permanecer alem do limiar de 3%.
                    if not self.allow_new_entries:
                        return
                    side = "LONG" if signed_move > 0 else "SHORT"
                    logger.info(
                        f"RANGE PROTECT 3PCT TRIGGER | {self.symbol} grid={self.grid_id} | "
                        f"side={side} protect_anchor={pa} price={price} move={signed_move} "
                        f"threshold={RANGE_REARM_PCT} RD={st['recovery_deficit']}"
                    )
                    self._start_basket(side, price)
                return
            if status == "IDLE":
                if not self.allow_new_entries:
                    return
                up = anchor * (D(1) + RANGE_TRIGGER_PCT)
                dn = anchor * (D(1) - RANGE_TRIGGER_PCT)
                if price >= up:
                    self._start_basket("LONG", price)
                elif price <= dn:
                    self._start_basket("SHORT", price)
                return
            b = st.get("basket")
            if not b:
                st["status"] = "IDLE"; self.store.save(); return
            active = b["active_side"]
            alternations = int(b.get("alternations", 0))
            if alternations == 0 and not b.get("native_bracket") and NATIVE_PROTECTIVE_ORDERS:
                try:
                    b["native_bracket"] = self.exe.install_bracket(
                        self.id, self.symbol, b["legs"][0],
                        dec(b.get("tp_price")), dec(b.get("hard_stop_price")),
                    )
                    self.store.save()
                except Exception as e:
                    logger.exception(f"RANGE BRACKET INSTALL FAIL | {self.symbol} | {e}")
            if alternations == 0 and b.get("native_bracket"):
                native_close = self.exe.consume_bracket_fill(
                    self.id, self.symbol, b["legs"][0], b.get("native_bracket"), price
                )
                if native_close:
                    pnl = dec(native_close["pnl_est"])
                    _apply_realized_pnl_to_state(st, pnl, dec(native_close["exit_price"]), native_close["reason"], is_macd=False)
                    protect_after = pnl < 0
                    st["basket"] = None
                    st["failures"] = 0
                    st["status"] = "PROTECT" if protect_after else "IDLE"
                    st["protect_anchor"] = str(dec(native_close["exit_price"])) if protect_after else None
                    st["anchor"] = str(self._anchor_from_price(dec(native_close["exit_price"])))
                    self.store.save()
                    release_owner(self.store, self.symbol, self.id)
                    logger.info(f"RANGE NATIVE CLOSE | {self.symbol} | pnl={pnl} equity={st['equity']} RD={st['recovery_deficit']} protect={protect_after}")
                    return
            if alternations == 0:
                tp = dec(b["tp_price"])
                hard = dec(b["hard_stop_price"])
                if (active == "LONG" and price >= tp) or (active == "SHORT" and price <= tp):
                    self._close_basket(price, "INITIAL_TP_1PCT", protect_after=False)
                    return
                if (b["initial_side"] == "LONG" and price <= hard) or (b["initial_side"] == "SHORT" and price >= hard):
                    self._close_basket(price, "INITIAL_HARD_STOP_2PCT", protect_after=True)
                    return
            else:
                active_recovery_side = str(b.get("active_side") or "")
                active_recovery_leg = None
                for _leg in reversed(b.get("legs", [])):
                    if str(_leg.get("side") or "") == active_recovery_side:
                        active_recovery_leg = _leg
                        break
                if active_recovery_leg:
                    _re = dec(active_recovery_leg.get("entry_price"))
                    if _re > 0:
                        expected_rtp = _re * (D(1) + RANGE_TAKE_PROFIT_PCT) if active_recovery_side == "LONG" else _re * (D(1) - RANGE_TAKE_PROFIT_PCT)
                        expected_rsl = _re * (D(1) - RANGE_HARD_STOP_PCT) if active_recovery_side == "LONG" else _re * (D(1) + RANGE_HARD_STOP_PCT)
                        stored_rtp = dec(b.get("recovery_tp_price"))
                        stored_rsl = dec(b.get("recovery_stop_price"))
                        tick = dec(self.exe.rules.rules[self.symbol].tick_size)
                        tol = max(tick * D(2), _re * D("0.000001"))
                        if abs(stored_rtp - expected_rtp) > tol or abs(stored_rsl - expected_rsl) > tol:
                            logger.warning(
                                f"RANGE RECOVERY PRICE MIGRATION | {self.symbol} | side={active_recovery_side} entry={_re} | old_tp={stored_rtp} old_sl={stored_rsl} -> new_tp={expected_rtp} new_sl={expected_rsl}"
                            )
                            self.exe.cancel_basket_exit(self.symbol, b.get("native_basket_exit"))
                            self.exe.cancel_basket_exit(self.symbol, b.get("native_basket_stop"))
                            b["native_basket_exit"] = None
                            b["native_basket_stop"] = None
                            b["recovery_tp_price"] = str(expected_rtp)
                            b["recovery_stop_price"] = str(expected_rsl)
                            self.store.save()
                rtp = dec(b.get("recovery_tp_price"))
                rsl = dec(b.get("recovery_stop_price"))
                native_result = None
                if b.get("native_basket_exit"):
                    native_result = self.exe.consume_basket_exit(
                        self.id, self.symbol, b.get("legs", []),
                        b.get("native_basket_exit"), price,
                        "NATIVE_RANGE_BASKET_TAKE_PROFIT",
                    )
                if native_result:
                    self.exe.cancel_basket_exit(self.symbol, b.get("native_basket_stop"))
                    pnl, closes = native_result
                    rd_before = dec(st.get("recovery_deficit"))
                    _apply_realized_pnl_to_state(st, pnl, price, "NATIVE_RANGE_BASKET_TAKE_PROFIT", is_macd=False)
                    rd_after = dec(st.get("recovery_deficit"))
                    st["basket"] = None
                    st["failures"] = 0
                    st["anchor"] = str(self._anchor_from_price(price))
                    if rd_before > 0 and rd_after == 0 and pnl > 0:
                        st["status"] = "IDLE"
                        st["protect_anchor"] = None
                        st["last_result"] = "RECOVERY_WIN_RESET"
                        logger.warning(
                            f"RANGE RECOVERY RESET NATIVE | {self.symbol} grid={self.grid_id} | "
                            f"pnl={pnl} RD_before={rd_before} RD_after=0"
                        )
                    elif rd_after > 0:
                        st["status"] = "PROTECT"
                        st["protect_anchor"] = str(price)
                        st["last_result"] = "RECOVERY_PARTIAL"
                        logger.warning(
                            f"RANGE RECOVERY PARTIAL NATIVE | {self.symbol} grid={self.grid_id} | "
                            f"pnl={pnl} RD_before={rd_before} RD_remaining={rd_after}"
                        )
                    else:
                        st["status"] = "IDLE"
                        st["protect_anchor"] = None
                    self.store.save()
                    release_owner(self.store, self.symbol, self.id)
                    logger.info(
                        f"RANGE NATIVE BASKET TP CLOSE | {self.symbol} grid={self.grid_id} | "
                        f"pnl={pnl} equity={st['equity']} RD={st['recovery_deficit']} status={st['status']}"
                    )
                    return
                native_stop = None
                if b.get("native_basket_stop"):
                    native_stop = self.exe.consume_basket_exit(
                        self.id, self.symbol, b.get("legs", []),
                        b.get("native_basket_stop"), price,
                        "NATIVE_RANGE_BASKET_STOP_LOSS",
                    )
                if native_stop:
                    self.exe.cancel_basket_exit(self.symbol, b.get("native_basket_exit"))
                    pnl, closes = native_stop
                    _apply_realized_pnl_to_state(st, pnl, price, "NATIVE_RANGE_BASKET_STOP_LOSS", is_macd=False)
                    st["basket"] = None
                    st["status"] = "PROTECT"
                    st["protect_anchor"] = str(price)
                    st["anchor"] = str(self._anchor_from_price(price))
                    self.store.save()
                    release_owner(self.store, self.symbol, self.id)
                    logger.warning(f"RANGE NATIVE BASKET SL CLOSE | {self.symbol} | pnl={pnl} equity={st['equity']} RD={st['recovery_deficit']}")
                    return
                if self._reconcile_range_ghost_legs(b, price):
                    return
                b = st.get("basket")
                if not b:
                    return
                active = b["active_side"]
                rtp = dec(b.get("recovery_tp_price"))
                rsl = dec(b.get("recovery_stop_price"))
                if NATIVE_PROTECTIVE_ORDERS and b.get("native_basket_exit") and not self.exe.basket_exit_is_live(self.symbol, b.get("native_basket_exit")):
                    self.exe.cancel_basket_exit(self.symbol, b.get("native_basket_exit"))
                    b["native_basket_exit"] = None
                    self.store.save()
                if NATIVE_PROTECTIVE_ORDERS and b.get("native_basket_stop") and not self.exe.basket_exit_is_live(self.symbol, b.get("native_basket_stop")):
                    self.exe.cancel_basket_exit(self.symbol, b.get("native_basket_stop"))
                    b["native_basket_stop"] = None
                    self.store.save()
                if rtp > 0 and not b.get("native_basket_exit") and NATIVE_PROTECTIVE_ORDERS:
                    try:
                        b["native_basket_exit"] = self.exe.install_basket_exit(
                            self.id + ":TP", self.symbol, b.get("legs", []), rtp, price
                        )
                        self.store.save()
                        logger.warning(f"RANGE BASKET TP REINSTALADO | {self.symbol} | trigger={rtp}")
                    except Exception as e:
                        logger.exception(f"RANGE BASKET TP REINSTALL FAIL | {self.symbol} | {e}")
                if rsl > 0 and not b.get("native_basket_stop") and NATIVE_PROTECTIVE_ORDERS:
                    try:
                        b["native_basket_stop"] = self.exe.install_basket_exit(
                            self.id + ":SL", self.symbol, b.get("legs", []), rsl, price
                        )
                        self.store.save()
                        logger.warning(f"RANGE BASKET SL REINSTALADO | {self.symbol} | trigger={rsl}")
                    except Exception as e:
                        logger.exception(f"RANGE BASKET SL REINSTALL FAIL | {self.symbol} | {e}")
                if rtp > 0 and ((active == "LONG" and price >= rtp) or (active == "SHORT" and price <= rtp)):
                    self._close_basket(price, "RECOVERY_LEG_TP_1PCT_CLOSE_ALL", protect_after=False); return
                if rsl > 0 and ((active == "LONG" and price <= rsl) or (active == "SHORT" and price >= rsl)):
                    self._close_basket(price, "RECOVERY_HARD_STOP_2PCT_CLOSE_ALL", protect_after=True); return
            rev = dec(b["next_reverse_price"])
            if (active == "LONG" and price <= rev) or (active == "SHORT" and price >= rev):
                self._reverse(price)

# -----------------------------------------------------------------------------
# MACD ENGINE com trailing stop e stop loss
# -----------------------------------------------------------------------------

class MacdEngine:
    def __init__(self, symbol: str, tf: str, client: AsterClient, md: MarketData, news: NewsFilter,
                 account: AccountManager, exe: ExecutionEngine, store: StateStore):
        self.symbol = symbol; self.tf = tf
        self.id = f"MACD:{symbol}:{tf}"
        self.client = client; self.md = md; self.news = news; self.account = account; self.exe = exe; self.store = store

    def st(self) -> Dict[str, Any]:
        return self.store.state["macd"][f"{self.symbol}:{self.tf}"]

    def closed_closes(self) -> Tuple[List[Decimal], int]:
        rows = self.client.klines(self.symbol, self.tf, max(100, MACD_SLOW + MACD_SIGNAL + 20))
        if not rows: return [], 0
        n = now_ms(); closed = [r for r in rows if int(r[6]) < n]
        if not closed: return [], 0
        return [dec(r[4]) for r in closed], int(closed[-1][6])

    def _finalize_close(self, st: Dict[str, Any], rec: Dict[str, Any], reason: str) -> None:
        pnl = dec(rec["pnl_est"]); exit_price = dec(rec.get("exit_price"))
        _apply_realized_pnl_to_state(st, pnl, exit_price, reason, is_macd=True)
        st["position"] = None
        if int(st.get("loss_streak", 0)) >= MAX_RECOVERY_FAILURES:
            st["protect"] = True; st["protect_anchor"] = str(exit_price)
        st["last_update"] = now_iso(); self.store.set_protection_block(self.id, None); self.store.save(); release_owner(self.store, self.symbol, self.id)
        logger.info("MACD CLOSE | %s | %s | pnl=%s eq=%s RD=%s streak=%s protect=%s",
                    self.id, reason, pnl, st["equity"], st["recovery_deficit"], st["loss_streak"], st["protect"])

    def _close(self, price: Decimal, reason: str) -> None:
        st = self.st(); pos = st.get("position")
        if not pos: return
        # Cancel all known old protection before deliberate market close.
        if pos.get("native_bracket"):
            self.exe.cancel_bracket(self.symbol, pos.get("native_bracket"))
        self.exe.cancel_stop_only(self.symbol, pos.get("native_stop"))
        c = self.exe.close_leg(self.id, self.symbol, pos["leg"], price, reason)
        if c is None:
            # Physical side may already have been closed by a native order. Do not invent PnL.
            logger.warning("MACD CLOSE SKIP | %s | %s | posição física indisponível; aguardando reconciliação", self.id, reason)
            return
        self._finalize_close(st, c, reason)

    def _open(self, side: str, price: Decimal) -> None:
        st = self.st(); blocked, why = self.news.blocked()
        if blocked: logger.info("MACD NEWS BLOCK | %s | %s", self.id, why); return
        if self.store.killed() != "OFF":
            logger.warning("MACD ENTRY BLOCKED BY KILL | %s | mode=%s | side=%s", self.id, self.store.killed(), side); return
        gate_ok, gate_reason = self.store.entry_allowed()
        if not gate_ok: logger.warning("MACD ENTRY GATE | %s | %s", self.id, gate_reason); return
        if not self.md.is_fresh(self.symbol):
            logger.warning("MACD ENTRY STALE PRICE | %s | age_s=%.3f", self.id, self.md.age(self.symbol)); return
        if not acquire_owner(self.store, self.symbol, self.id):
            logger.info("MACD OWNER BLOCK | %s | owner=%s", self.id, self.store.state["symbol_owner"].get(self.symbol)); return
        rd = dec(st.get("recovery_deficit"))
        recovery_level = min(MAX_RECOVERY_FAILURES, max(1, int(st.get("recovery_level",0)), int(st.get("loss_streak",0)))) if rd > 0 else 0
        st["recovery_level"] = recovery_level
        # No fixed TP: sizing uses the real adverse hard-stop distance and the configured MACD recovery multiplier.
        sizing = self.account.sizing_for_profit_target(
            self.symbol, price, st, target_profit=None, target_move_pct=MACD_HARD_STOP_PCT,
            adverse_distance_pct=MACD_HARD_STOP_PCT, recovery_level=recovery_level,
            recovery_multiplier=MACD_RECOVERY_MULTIPLIER)
        if not sizing:
            release_owner(self.store, self.symbol, self.id); logger.warning("MACD SIZING NAO CABE | %s", self.id); return
        leg = self.exe.open_leg(self.id, self.symbol, side, sizing, "MACD_CROSS")
        if not leg:
            release_owner(self.store, self.symbol, self.id)
            logger.warning("MACD OPEN BLOCKED | %s | leverage/margin precheck", self.id)
            return
        entry = dec(leg["entry_price"])
        hard_stop = entry * (D(1)-MACD_HARD_STOP_PCT) if side == "LONG" else entry * (D(1)+MACD_HARD_STOP_PCT)
        try:
            native_stop = self.exe.install_stop_only(self.id, self.symbol, leg, hard_stop, "MACD_HARD_STOP")
        except Exception:
            # A live MACD position without its emergency native stop is not acceptable.
            logger.exception("MACD STOP NATIVO INSTALL FAIL | %s | fechando posição recém-aberta", self.id)
            try:
                c = self.exe.close_leg(self.id, self.symbol, leg, price, "PROTECTION_INSTALL_FAILED")
                if c:
                    self._finalize_close(st, c, "PROTECTION_INSTALL_FAILED")
            finally:
                release_owner(self.store, self.symbol, self.id)
            return
        self.store.set_protection_block(self.id, None)
        st["position"] = {"side":side,"leg":leg,"opened_at":now_iso(),"signal_price":str(price),
                          "hard_stop_price":str(hard_stop),"native_stop":native_stop,"native_bracket":None,
                          "trailing_active":False,"trailing_stop":None,"highest_price":str(entry),"lowest_price":str(entry),
                          "last_stop_check_ms":0,"recovery_level":recovery_level}
        st["last_update"] = now_iso(); self.store.save()
        logger.info("MACD OPEN | %s | %s @%s | lev=%sx qty=%s notional=%s stop_nativo=%s recovery_level=%s multiplier=%sx",
                    self.id, side, entry, sizing["leverage"], sizing["qty"], sizing["notional"], hard_stop, recovery_level, MACD_RECOVERY_MULTIPLIER)

    def _migrate_old_bracket(self, st: Dict[str, Any], pos: Dict[str, Any], price: Decimal) -> bool:
        old = pos.get("native_bracket")
        if not old: return False
        # First consume a fill that may have happened while the bot was offline.
        native = self.exe.consume_bracket_fill(self.id, self.symbol, pos["leg"], old, price)
        if native:
            self._finalize_close(st, native, "MIGRATED_OLD_NATIVE_BRACKET_FILL")
            return True
        self.exe.cancel_bracket(self.symbol, old)
        pos["native_bracket"] = None
        logger.warning("MACD BRACKET ANTIGO REMOVIDO | %s | migrando para stop-only", self.id)
        return False

    def _desired_native_stop(self, pos: Dict[str, Any]) -> Decimal:
        hard = dec(pos.get("hard_stop_price")); trail = dec(pos.get("trailing_stop"))
        if not pos.get("trailing_active") or trail <= 0: return hard
        return max(hard, trail) if pos["side"] == "LONG" else min(hard, trail)

    def _watch_native_stop(self, st: Dict[str, Any], pos: Dict[str, Any], price: Decimal, force: bool=False) -> bool:
        if not NATIVE_PROTECTIVE_ORDERS: return False
        now = now_ms(); last = int(pos.get("last_stop_check_ms",0) or 0)
        if not force and now-last < int(PROTECTIVE_WATCHDOG_SECONDS*1000): return False
        pos["last_stop_check_ms"] = now
        # Legacy MACD state migration.
        if self._migrate_old_bracket(st, pos, price): return True
        stop = pos.get("native_stop")
        if stop:
            native = self.exe.consume_stop_fill(self.id, self.symbol, pos["leg"], stop, price)
            if native:
                self._finalize_close(st, native, native.get("reason","NATIVE_STOP_LOSS")); return True
            try:
                q = self.exe.stop_status(self.symbol, stop)
            except Exception as e:
                logger.warning("MACD STOP WATCHDOG QUERY UNKNOWN | %s | %s", self.id, e)
                self.store.set_protection_block(self.id, "NATIVE_STOP_VERIFY_UNKNOWN")
                self.store.save()
                return False
            status = str((q or {}).get("status") or "")
            if status in ("NEW","PARTIALLY_FILLED"):
                # After restart, persisted software trailing may be tighter than the exchange stop.
                if pos.get("trailing_active"):
                    self._sync_native_trailing(pos)
                self.store.set_protection_block(self.id, None)
                self.store.save(); return False
            if status not in ("CANCELED","EXPIRED","REJECTED","MISSING"):
                self.store.save(); return False
            logger.warning("MACD STOP WATCHDOG | %s | stop ausente/inativo status=%s; reinstalando", self.id, status)
        try:
            pos["native_stop"] = self.exe.install_stop_only(self.id, self.symbol, pos["leg"], self._desired_native_stop(pos), "MACD_STOP_WATCHDOG")
            self.store.set_protection_block(self.id, None)
            self.store.save()
        except Exception as e:
            logger.exception("MACD STOP WATCHDOG REINSTALL FAIL | %s | %s", self.id, e)
            # Independent durable fail-closed block; periodic position reconciliation cannot clear it.
            self.store.set_protection_block(self.id, "NATIVE_STOP_MISSING")
        return False

    def _sync_native_trailing(self, pos: Dict[str, Any]) -> None:
        if not (MACD_NATIVE_TRAILING_ENABLED and NATIVE_PROTECTIVE_ORDERS and pos.get("trailing_active")): return
        desired = self._desired_native_stop(pos); old = pos.get("native_stop")
        try:
            moved = self.exe.replace_stop_only(self.id, self.symbol, pos["leg"], old, desired, "MACD_NATIVE_TRAILING")
            if moved is not old: pos["native_stop"] = moved
        except Exception as e:
            logger.exception("MACD NATIVE TRAILING UPDATE FAIL | %s | desired=%s | %s", self.id, desired, e)

    def tick(self, price: Decimal) -> None:
        st = self.st(); pos = st.get("position")
        if pos:
            # Watchdog/consume first so a fill on Aster can never be followed by a second logical close.
            if self._watch_native_stop(st, pos, price): return
            side=pos["side"]; entry=dec(pos["leg"]["entry_price"])
            hard=dec(pos.get("hard_stop_price"))
            if hard <= 0:
                hard = entry*(D(1)-MACD_HARD_STOP_PCT) if side=="LONG" else entry*(D(1)+MACD_HARD_STOP_PCT)
                pos["hard_stop_price"] = str(hard)
            if side=="LONG":
                highest=max(dec(pos.get("highest_price") or entry), price); pos["highest_price"]=str(highest)
                if not pos.get("trailing_active") and pct_change(entry,price)>=MACD_TRAILING_ACTIVATION_PCT:
                    pos["trailing_active"]=True; pos["trailing_stop"]=str(entry); self._sync_native_trailing(pos); logger.info("MACD TRAILING ATIVADO | %s | LONG | stop=BE", self.id)
                if pos.get("trailing_active"):
                    nxt=highest*(D(1)-MACD_TRAILING_DISTANCE_PCT); cur=dec(pos.get("trailing_stop"))
                    if nxt>cur: pos["trailing_stop"]=str(nxt); self._sync_native_trailing(pos)
                if price<=hard: self._close(price,"MACD_HARD_STOP_SOFTWARE_BACKUP"); return
                if pos.get("trailing_active") and price<=dec(pos.get("trailing_stop")): self._close(price,"MACD_TRAILING_STOP"); return
            else:
                lowest=min(dec(pos.get("lowest_price") or entry), price); pos["lowest_price"]=str(lowest)
                if not pos.get("trailing_active") and pct_change(price,entry)>=MACD_TRAILING_ACTIVATION_PCT:
                    pos["trailing_active"]=True; pos["trailing_stop"]=str(entry); self._sync_native_trailing(pos); logger.info("MACD TRAILING ATIVADO | %s | SHORT | stop=BE", self.id)
                if pos.get("trailing_active"):
                    nxt=lowest*(D(1)+MACD_TRAILING_DISTANCE_PCT); cur=dec(pos.get("trailing_stop"))
                    if cur<=0 or nxt<cur: pos["trailing_stop"]=str(nxt); self._sync_native_trailing(pos)
                if price>=hard: self._close(price,"MACD_HARD_STOP_SOFTWARE_BACKUP"); return
                if pos.get("trailing_active") and price>=dec(pos.get("trailing_stop")): self._close(price,"MACD_TRAILING_STOP"); return
            self.store.save()

        try: closes, close_ms = self.closed_closes()
        except Exception as e: logger.warning("MACD KLINES FAIL | %s | %s",self.id,e); return
        if close_ms <= int(st.get("last_candle_close_ms",0)): return
        st["last_candle_close_ms"]=close_ms; cross=get_macd_cross(closes); self.store.save()
        if not cross: return
        logger.info("MACD CROSS | %s | cross=%s close_ms=%s price=%s",self.id,cross,close_ms,price)
        if st.get("protect"):
            pa=dec(st.get("protect_anchor"))
            if pa<=0: st["protect_anchor"]=str(price); self.store.save(); return
            if abs(pct_change(pa,price))<MACD_REARM_PCT:
                logger.info("MACD PROTECT | %s | falta deslocamento 3%% | move=%s",self.id,abs(pct_change(pa,price))); return
            st["protect"]=False
            if dec(st.get("recovery_deficit"))>0:
                st["recovery_level"]=min(MAX_RECOVERY_FAILURES,max(1,int(st.get("recovery_level",0)),int(st.get("loss_streak",0))))
                st["loss_streak"]=max(1,int(st.get("loss_streak",0)))
            else: st["recovery_level"]=0; st["loss_streak"]=0
            st["protect_anchor"]=None; self.store.save(); logger.info("MACD PROTECT LIBERADO | %s | cross=%s",self.id,cross)
        pos=st.get("position")
        if pos:
            if pos["side"]==cross: return
            self._close(price,"OPPOSITE_MACD_CROSS"); st=self.st()
            if st.get("protect") or st.get("position"): return
            self._open(cross,price)
        else: self._open(cross,price)

# -----------------------------------------------------------------------------
# STARTUP RECONCILIATION + KILL SWITCH
# -----------------------------------------------------------------------------

class Reconciler:
    def __init__(self, client: AsterClient, store: StateStore, ledger: FillLedger, rules: RulesBook, exe: ExecutionEngine):
        self.client = client; self.store = store; self.ledger = ledger; self.rules = rules; self.exe = exe
        self.last_snapshot: Optional[ExchangeSnapshot] = None
        self._state_ledger_mismatch_streak = 0

    def snapshot(self) -> ExchangeSnapshot:
        positions: Dict[Tuple[str, str], Decimal] = {}; entries: Dict[Tuple[str, str], Decimal] = {}
        for p in (self.client.positions() if LIVE_TRADING else []):
            sym = str(p.get("symbol", "")).upper(); side = str(p.get("positionSide", "")).upper()
            if sym not in SYMBOLS or side not in ("LONG", "SHORT"): continue
            q = abs(dec(p.get("positionAmt")))
            if q > 0:
                positions[(sym, side)] = q; entries[(sym, side)] = dec(p.get("entryPrice"))
        orders = self.client.open_orders() if LIVE_TRADING else []
        snap = ExchangeSnapshot(now_ms(), positions, entries, orders if isinstance(orders, list) else [])
        self.last_snapshot = snap
        return snap

    def expected_by_symbol_side(self) -> Dict[Tuple[str, str], Decimal]:
        return self.ledger.open_by_symbol_side()

    def expected_from_state_by_symbol_side(self) -> Dict[Tuple[str, str], Decimal]:
        out: Dict[Tuple[str, str], Decimal] = {}

        def add(symbol: str, side: str, qty: Any) -> None:
            sym = str(symbol).upper()
            ps = str(side).upper()
            q = dec(qty)
            if sym in SYMBOLS and ps in ("LONG", "SHORT") and q > 0:
                out[(sym, ps)] = out.get((sym, ps), D(0)) + q

        with self.store.lock:
            ranges: List[Dict[str, Any]] = []
            ranges.extend(x for x in self.store.state.get("range", {}).values() if isinstance(x, dict))
            ranges.extend(x for x in self.store.state.get("range_grids", {}).values() if isinstance(x, dict))
            for st in ranges:
                sym = str(st.get("symbol") or "").upper()
                for leg in (st.get("basket") or {}).get("legs", []) or []:
                    add(sym, leg.get("side"), leg.get("qty"))

            for st in self.store.state.get("macd", {}).values():
                if not isinstance(st, dict):
                    continue
                sym = str(st.get("symbol") or "").upper()
                pos = st.get("position") or {}
                leg = pos.get("leg") or {}
                add(sym, pos.get("side") or leg.get("side"), leg.get("qty"))

        return out

    def _confirm_side_orders_gone(self, symbol: str, side: str) -> None:
        """Cancel only bot-owned orders for one Hedge-Mode side and prove none remain.

        Opposite-side protection is deliberately untouched. Unknown/unattributed orders on
        the target side make the repair fail closed.
        """
        symbol = str(symbol).upper(); side = str(side).upper()
        attempts = max(1, CANCEL_CONFIRM_ATTEMPTS)
        last_remaining: List[Dict[str, Any]] = []
        for attempt in range(attempts):
            orders = self.client.open_orders(symbol)
            if not isinstance(orders, list):
                raise RuntimeError(f"openOrders indeterminado para {symbol}: {orders!r}")
            target: List[Dict[str, Any]] = []
            for order in orders:
                ps = str(order.get("positionSide") or "").upper()
                if ps and ps != side:
                    continue
                if not ps:
                    # In Hedge Mode an order without positionSide cannot be proven unrelated.
                    raise RuntimeError(f"ordem sem positionSide impede repair seguro: {order!r}")
                target.append(order)
            if not target:
                return
            last_remaining = target
            for order in target:
                cid = str(order.get("clientOrderId") or order.get("origClientOrderId") or "")
                if not cid:
                    raise RuntimeError(f"ordem {symbol} {side} sem clientOrderId: {order!r}")
                owner = self.ledger.order_owner(cid)
                if owner is None:
                    raise RuntimeError(f"ordem {symbol} {side} sem ownership no ledger: cid={cid}")
                try:
                    self.client.cancel_order(symbol, cid)
                except Exception as exc:
                    # DELETE can be execution-unknown; verification below is authoritative.
                    logger.warning(
                        "RECONCILE SIDE CANCEL UNKNOWN | %s %s | cid=%s owner=%s | %s",
                        symbol, side, cid, owner, exc,
                    )
            if attempt + 1 < attempts:
                time.sleep(max(0.05, CANCEL_CONFIRM_DELAY_SECONDS))
        verify = self.client.open_orders(symbol)
        if not isinstance(verify, list):
            raise RuntimeError(f"openOrders verify indeterminado para {symbol}: {verify!r}")
        remaining = [o for o in verify if str(o.get("positionSide") or "").upper() == side]
        if remaining:
            raise RuntimeError(
                f"ordens ainda abertas apos cancelamento seletivo {symbol} {side}: "
                f"{[(o.get('clientOrderId'), o.get('status')) for o in remaining]}"
            )

    def _confirm_physical_side_zero(self, symbol: str, side: str) -> None:
        step = self.rules.rules[symbol].step_size if symbol in self.rules.rules else D("0.00000001")
        for check_idx in range(2):
            rows = self.client.positions(symbol)
            if not isinstance(rows, list):
                raise RuntimeError(f"positionRisk indeterminado para {symbol}: {rows!r}")
            qty = D(0)
            for p in rows:
                if str(p.get("symbol") or "").upper() == symbol and str(p.get("positionSide") or "").upper() == side:
                    qty = abs(dec(p.get("positionAmt")))
                    break
            if qty >= step:
                raise RuntimeError(f"positionSide deixou de estar flat durante repair: {symbol} {side} qty={qty}")
            if check_idx == 0:
                time.sleep(0.10)

    def _clear_state_side_after_exchange_flat(self, symbol: str, side: str) -> int:
        changed = 0
        with self.store.lock:
            for bucket in ("range", "range_grids"):
                for st in self.store.state.get(bucket, {}).values():
                    if not isinstance(st, dict) or str(st.get("symbol") or "").upper() != symbol:
                        continue
                    basket = st.get("basket") or {}
                    legs = list(basket.get("legs", []) or [])
                    if not legs:
                        continue
                    target = [leg for leg in legs if str(leg.get("side") or "").upper() == side]
                    other = [leg for leg in legs if str(leg.get("side") or "").upper() != side]
                    if target and other:
                        raise RuntimeError(f"basket RANGE misto impede side-repair seguro: {st.get('strategy')} {symbol} {side}")
                    if target:
                        st["basket"] = None
                        st["status"] = "IDLE"
                        st["anchor"] = None
                        st["protect_anchor"] = None
                        st["last_result"] = "EXCHANGE_FLAT_RECONCILE_UNACCOUNTED"
                        st["last_update"] = now_iso()
                        changed += 1
            for st in self.store.state.get("macd", {}).values():
                if not isinstance(st, dict) or str(st.get("symbol") or "").upper() != symbol:
                    continue
                pos = st.get("position") or {}
                leg = pos.get("leg") or {}
                ps = str(pos.get("side") or leg.get("side") or "").upper()
                if pos and ps == side:
                    st["position"] = None
                    st["protect"] = False
                    st["protect_anchor"] = None
                    st["last_result"] = "EXCHANGE_FLAT_RECONCILE_UNACCOUNTED"
                    st["last_update"] = now_iso()
                    changed += 1
            if changed:
                self.store.save()
        return changed

    def _represented_state_leg_ids(self) -> set:
        ids = set()
        with self.store.lock:
            for bucket in ("range", "range_grids"):
                for st in self.store.state.get(bucket, {}).values():
                    if not isinstance(st, dict):
                        continue
                    for leg in ((st.get("basket") or {}).get("legs") or []):
                        lid = str(leg.get("id") or "")
                        if lid:
                            ids.add(lid)
            for st in self.store.state.get("macd", {}).values():
                if not isinstance(st, dict):
                    continue
                pos = st.get("position") or {}
                leg = pos.get("leg") or {}
                lid = str(leg.get("id") or "")
                if lid:
                    ids.add(lid)
        return ids

    @staticmethod
    def _is_current_range_grid_strategy(strategy_id: str, symbol: str) -> bool:
        sid = str(strategy_id)
        sym = str(symbol).upper()
        return any(sid == f"RANGE:{sym}:G{i}" for i, _ in enumerate(RANGE_GRID_PHASES))

    def _range_state_for_strategy(self, strategy_id: str) -> Optional[Dict[str, Any]]:
        sid = str(strategy_id)
        parts = sid.split(":")
        if len(parts) != 3 or parts[0] != "RANGE":
            return None
        symbol, grid_id = parts[1].upper(), parts[2]
        return self.store.state.get("range_grids", {}).get(f"{symbol}:{grid_id}")

    def _cancel_orphan_strategy_orders(self, symbol: str, side: str, strategy_ids: set) -> None:
        """Cancel only orders durably owned by the orphan RANGE strategies on one side.

        Orders owned by other current strategies are preserved. Any target-side order whose
        ownership cannot be proven makes the repair fail closed.
        """
        symbol = str(symbol).upper(); side = str(side).upper()
        orders = self.client.open_orders(symbol)
        if not isinstance(orders, list):
            raise RuntimeError(f"openOrders indeterminado para orphan repair {symbol}: {orders!r}")
        targets: List[Tuple[str, str]] = []
        for order in orders:
            ps = str(order.get("positionSide") or "").upper()
            if ps != side:
                continue
            cid = str(order.get("clientOrderId") or order.get("origClientOrderId") or "")
            if not cid:
                raise RuntimeError(f"ordem {symbol} {side} sem clientOrderId durante orphan repair: {order!r}")
            owner = self.ledger.order_owner(cid)
            if owner is None:
                raise RuntimeError(f"ordem {symbol} {side} sem ownership durante orphan repair: cid={cid}")
            if any(owner == sid or owner.startswith(sid + ":") for sid in strategy_ids):
                targets.append((cid, owner))
        for cid, owner in targets:
            try:
                self.exe.cancel_and_confirm_terminal(symbol, cid)
            except Exception as exc:
                raise RuntimeError(f"cancelamento orphan nao confirmado cid={cid} owner={owner}: {exc}") from exc
        verify = self.client.open_orders(symbol)
        if not isinstance(verify, list):
            raise RuntimeError(f"openOrders verify indeterminado para orphan repair {symbol}: {verify!r}")
        remaining = []
        for order in verify:
            if str(order.get("positionSide") or "").upper() != side:
                continue
            cid = str(order.get("clientOrderId") or order.get("origClientOrderId") or "")
            owner = self.ledger.order_owner(cid) if cid else None
            if owner is None:
                raise RuntimeError(f"ordem remanescente {symbol} {side} sem ownership: cid={cid}")
            if any(owner == sid or owner.startswith(sid + ":") for sid in strategy_ids):
                remaining.append((cid, owner))
        if remaining:
            raise RuntimeError(f"ordens orphan ainda abertas {symbol} {side}: {remaining}")

    def _repair_range_state_orphans(
        self,
        state_mismatches: List[Tuple[Tuple[str, str], Decimal, Decimal]],
        actual: Dict[Tuple[str, str], Decimal],
    ) -> List[Tuple[str, str, Decimal]]:
        """Safely liquidate durable RANGE lots that exist in ledger+exchange but disappeared from state.

        This is deliberately narrower than reconstructing a basket: the durable ledger does not
        contain enough information to recreate every recovery/native-protection field exactly.
        Therefore, when ownership is proven and ledger==physical, the safest deterministic repair
        is to close only the orphan lots, account their realized PnL back to the owning grid, and
        re-arm that grid from a clean state. Unknown/manual exposure is never touched.
        """
        repaired: List[Tuple[str, str, Decimal]] = []
        represented_ids = self._represented_state_leg_ids()
        for (symbol, side), ledger_qty, state_qty in list(state_mismatches):
            symbol = str(symbol).upper(); side = str(side).upper()
            step = self.rules.rules[symbol].step_size if symbol in self.rules.rules else D("0.00000001")
            missing = ledger_qty - state_qty
            physical_qty = actual.get((symbol, side), D(0))
            if missing < step:
                continue
            # We repair only the exact condition observed in production: state lost quantity while
            # durable ledger and exchange still agree. Any physical discrepancy is handled by the
            # existing position mismatch path instead.
            if abs(physical_qty - ledger_qty) >= step:
                continue
            lots = self.ledger.open_lots_for_symbol_side(symbol, side)
            orphan_lots = [lot for lot in lots if str(lot.get("id") or "") not in represented_ids]
            orphan_qty = sum((dec(lot.get("qty")) for lot in orphan_lots), D(0))
            if abs(orphan_qty - missing) >= step:
                continue
            if not orphan_lots:
                continue
            strategy_ids = {str(lot.get("strategy_id") or "") for lot in orphan_lots}
            if not strategy_ids or not all(self._is_current_range_grid_strategy(sid, symbol) for sid in strategy_ids):
                continue
            # Do not touch a strategy that still has any basket state. That would be a partial-state
            # corruption requiring manual review rather than deterministic orphan liquidation.
            states: Dict[str, Dict[str, Any]] = {}
            unsafe = False
            for sid in strategy_ids:
                st = self._range_state_for_strategy(sid)
                if not isinstance(st, dict) or st.get("basket"):
                    unsafe = True
                    break
                states[sid] = st
            if unsafe:
                continue

            logger.error(
                "RECONCILE | RANGE STATE ORPHAN CONFIRMED | %s %s | missing=%s strategies=%s | "
                "ledger=physical=%s; closing only proven orphan lots",
                symbol, side, missing, sorted(strategy_ids), ledger_qty,
            )
            self.store.set_operational_block(
                f"RANGE_STATE_ORPHAN_REPAIR:{symbol}:{side}",
                f"ledger=physical={ledger_qty}; state_missing={missing}; strategies={sorted(strategy_ids)}",
            )
            try:
                self._cancel_orphan_strategy_orders(symbol, side, strategy_ids)
                ref_price = self.client.mark(symbol)
                per_strategy_pnl: Dict[str, Decimal] = {sid: D(0) for sid in strategy_ids}
                closed_total = D(0)
                for lot in orphan_lots:
                    sid = str(lot["strategy_id"])
                    synthetic_leg = {
                        "id": str(lot["id"]),
                        "side": side,
                        "qty": str(dec(lot["qty"])),
                        "entry_price": str(dec(lot["entry_price"])),
                    }
                    closed = self.exe.close_leg(
                        sid, symbol, synthetic_leg, ref_price,
                        "STATE_LEDGER_ORPHAN_REPAIR_V53",
                        max_physical_qty=dec(lot["qty"]),
                    )
                    if closed is None or dec(closed.get("qty")) < step:
                        raise RuntimeError(f"orphan lot nao fechado: {sid} {lot['id']} qty={lot['qty']}")
                    cq = dec(closed.get("qty"))
                    if abs(cq - dec(lot["qty"])) >= step:
                        raise RuntimeError(f"orphan lot fechamento parcial: {sid} {lot['id']} {cq}/{lot['qty']}")
                    pnl = dec(closed.get("pnl_est"))
                    per_strategy_pnl[sid] = per_strategy_pnl.get(sid, D(0)) + pnl
                    closed_total += cq

                exit_price = self.client.mark(symbol)
                with self.store.lock:
                    for sid, pnl in per_strategy_pnl.items():
                        st = states[sid]
                        _apply_realized_pnl_to_state(st, pnl, exit_price, "STATE_LEDGER_ORPHAN_REPAIR_V53", is_macd=False)
                        st["basket"] = None
                        st["failures"] = 0
                        st["anchor"] = None
                        if dec(st.get("recovery_deficit")) > 0:
                            st["status"] = "PROTECT"
                            st["protect_anchor"] = str(exit_price)
                        else:
                            st["status"] = "IDLE"
                            st["protect_anchor"] = None
                        st["last_result"] = "STATE_LEDGER_ORPHAN_REPAIRED_V53"
                        st["last_update"] = now_iso()
                    self.store.save()

                # Authoritative post-close proof: physical must now equal the remaining ledger/state
                # quantity for this side, twice, before the operational block is removed.
                for check_idx in range(2):
                    rows = self.client.positions(symbol)
                    if not isinstance(rows, list):
                        raise RuntimeError(f"positionRisk indeterminado apos orphan repair {symbol}")
                    pq = D(0)
                    for row in rows:
                        if str(row.get("symbol") or "").upper() == symbol and str(row.get("positionSide") or "").upper() == side:
                            pq = abs(dec(row.get("positionAmt")))
                            break
                    lq_now = self.ledger.open_by_symbol_side().get((symbol, side), D(0))
                    sq_now = self.expected_from_state_by_symbol_side().get((symbol, side), D(0))
                    if abs(pq - lq_now) >= step or abs(pq - sq_now) >= step:
                        raise RuntimeError(f"post orphan repair mismatch {symbol} {side}: physical={pq} ledger={lq_now} state={sq_now}")
                    if check_idx == 0:
                        time.sleep(0.10)
                self.store.set_operational_block(f"RANGE_STATE_ORPHAN_REPAIR:{symbol}:{side}", None)
                repaired.append((symbol, side, closed_total))
                logger.warning(
                    "RECONCILE | RANGE STATE ORPHAN REPAIRED | %s %s | closed=%s strategies=%s | "
                    "state/ledger/physical novamente coerentes",
                    symbol, side, closed_total, sorted(strategy_ids),
                )
            except Exception as exc:
                reason = f"RANGE_STATE_ORPHAN_REPAIR_FAILED:{symbol}:{side}:{exc}"
                self.store.set_trade_gate(False, reason)
                self.store.set_operational_block(f"RANGE_STATE_ORPHAN_REPAIR:{symbol}:{side}", reason)
                logger.exception("RECONCILE | RANGE STATE ORPHAN REPAIR FAIL | %s", reason)
                return repaired
        return repaired

    def state_ledger_mismatches(self, ledger_expected: Dict[Tuple[str, str], Decimal]
                                ) -> List[Tuple[Tuple[str, str], Decimal, Decimal]]:
        state_expected = self.expected_from_state_by_symbol_side()
        out: List[Tuple[Tuple[str, str], Decimal, Decimal]] = []
        for key in set(ledger_expected) | set(state_expected):
            lq = ledger_expected.get(key, D(0))
            sq = state_expected.get(key, D(0))
            step = self.rules.rules[key[0]].step_size if key[0] in self.rules.rules else D("0.00000001")
            if abs(lq - sq) >= step:
                out.append((key, lq, sq))
        return out

    def reconcile(self) -> bool:
        if not LIVE_TRADING:
            self.store.set_trade_gate(True, None); return True
        expected = self.expected_by_symbol_side(); snap = self.snapshot(); actual = snap.positions
        mismatches = []
        for k in set(expected) | set(actual):
            e = expected.get(k, D(0)); a = actual.get(k, D(0))
            step = self.rules.rules[k[0]].step_size if k[0] in self.rules.rules else D("0.00000001")
            if abs(e - a) >= step:
                mismatches.append((k, e, a))
        if mismatches:
            # Side-scoped stale-ledger recovery. A flat LONG may be repaired while SHORT
            # remains live (and vice versa), without canceling protection for the live side.
            repaired_sides: List[Tuple[str, str, int]] = []
            if AUTO_REPAIR_ZERO_PHYSICAL_LEDGER:
                for (sym, side), exp_qty, act_qty in list(mismatches):
                    step = self.rules.rules[sym].step_size if sym in self.rules.rules else D("0.00000001")
                    if exp_qty < step or act_qty >= step:
                        continue
                    try:
                        self._confirm_side_orders_gone(sym, side)
                        self._confirm_physical_side_zero(sym, side)
                        cleared_state = self._clear_state_side_after_exchange_flat(sym, side)
                        n = self.ledger.zero_open_lots_for_symbol_side(
                            sym, side,
                            reason=f"exchange_flat_confirmed; state_records_cleared={cleared_state}",
                        )
                        if n:
                            repaired_sides.append((sym, side, n))
                            logger.warning(
                                "RECONCILE | AUTO-REPAIRED FLAT SIDE | %s %s | ghost_lots=%s state_records=%s | opposite_side_untouched",
                                sym, side, n, cleared_state,
                            )
                    except Exception as exc:
                        reason = f"FLAT_SIDE_REPAIR_UNCONFIRMED:{sym}:{side}:{exc}"
                        self.store.set_trade_gate(False, reason)
                        logger.error("RECONCILE | SIDE AUTO-REPAIR ABORTADO | %s", reason)
            if repaired_sides:
                expected = self.expected_by_symbol_side()
                snap = self.snapshot(); actual = snap.positions
                mismatches = []
                for k in set(expected) | set(actual):
                    e = expected.get(k, D(0)); a = actual.get(k, D(0))
                    step = self.rules.rules[k[0]].step_size if k[0] in self.rules.rules else D("0.00000001")
                    if abs(e - a) >= step:
                        mismatches.append((k, e, a))
                logger.warning("RECONCILE | SIDE AUTO-REPAIR RESULT | repaired=%s remaining=%s", repaired_sides, mismatches)
            if mismatches:
                reason = f"POSITION_MISMATCH_LEDGER expected_vs_actual={mismatches}"
                self.store.set_trade_gate(False, reason)
                current_ks = self.store.state.get("kill_switch", {}) or {}
                desired = "HARD" if HARD_KILL_ON_POSITION_MISMATCH else "SOFT"
                if str(current_ks.get("mode")) != desired or str(current_ks.get("reason")) != reason:
                    self.store.kill(desired, reason)
                logger.error(f"RECONCILE | BLOQUEADO | {reason}")
                return False
        state_mismatches = self.state_ledger_mismatches(expected)
        if state_mismatches:
            repaired_orphans = self._repair_range_state_orphans(state_mismatches, actual)
            if repaired_orphans:
                expected = self.expected_by_symbol_side()
                snap = self.snapshot(); actual = snap.positions
                state_mismatches = self.state_ledger_mismatches(expected)
                logger.warning(
                    "RECONCILE | RANGE STATE ORPHAN REPAIR RESULT | repaired=%s remaining_state_mismatches=%s",
                    repaired_orphans, state_mismatches,
                )
        if state_mismatches:
            self._state_ledger_mismatch_streak += 1
            logger.error(
                "RECONCILE | STATE_LEDGER_MISMATCH | streak=%s/%s | ledger_vs_state=%s | physical=%s",
                self._state_ledger_mismatch_streak,
                max(1, STATE_LEDGER_MISMATCH_CONFIRMATIONS),
                state_mismatches,
                actual,
            )
            if self._state_ledger_mismatch_streak >= max(1, STATE_LEDGER_MISMATCH_CONFIRMATIONS):
                self.store.set_trade_gate(False, f"STATE_LEDGER_MISMATCH:{state_mismatches}")
            return False

        self._state_ledger_mismatch_streak = 0
        self.store.set_trade_gate(True, None)
        cleared = self.store.clear_soft_position_mismatch()
        logger.info(
            "RECONCILE | OK | ledger=%s state=%s physical=%s | soft_mismatch_cleared=%s",
            expected, self.expected_from_state_by_symbol_side(), actual, cleared,
        )
        return True

# -----------------------------------------------------------------------------
# BUILT-IN REGRESSION CHECKS
# -----------------------------------------------------------------------------

def run_internal_regression_checks() -> None:
    assert STATE_LEDGER_MISMATCH_CONFIRMATIONS >= 1
    assert UNKNOWN_ORDER_QUERY_ATTEMPTS >= 1
    assert RANGE_SIGNAL_MODE == "VOLATILITY_ONLY"
    assert RANGE_TRIGGER_PCT > 0 and RANGE_TAKE_PROFIT_PCT > 0 and RANGE_HARD_STOP_PCT > 0
    assert MACD_FAST < MACD_SLOW and MACD_SIGNAL > 0
    assert RECOVERY_MULTIPLIER >= D(1) and MACD_RECOVERY_MULTIPLIER >= D(1) and MAX_RECOVERY_FAILURES >= 0
    assert configured_max_recovery_notional("BTCUSDT") >= configured_initial_notional("BTCUSDT")
    assert configured_max_recovery_notional("ETHUSDT") >= configured_initial_notional("ETHUSDT")
    fake = object.__new__(RulesBook)
    fake.rules = {"X": SymbolRules("X", D("0.1"), D("0.001"), D("0.001"), D("100"), D("5"))}
    assert fake.trigger_price("X", D("100.01"), "UP") == D("100.1")
    assert fake.trigger_price("X", D("100.09"), "DOWN") == D("100.0")
    assert MACD_RECOVERY_MULTIPLIER ** 1 == MACD_RECOVERY_MULTIPLIER
    assert RECOVERY_MULTIPLIER ** 2 == RECOVERY_MULTIPLIER * RECOVERY_MULTIPLIER
    assert MACD_HARD_STOP_PCT > 0 and MACD_TRAILING_ACTIVATION_PCT > 0 and MACD_TRAILING_DISTANCE_PCT > 0
    assert PROTECTIVE_WATCHDOG_SECONDS >= 1
    assert RANGE_GRID_PHASES == (D("0"), D("0.0025"), D("0.005"), D("0.0075"))
    assert RANGE_GRID_COUNT == 4
    assert RANGE_GRID_BANKROLL_USD > 0 and BTC_RANGE_GRID_BANKROLL_USD > 0
    p = D("100")
    anchors = [p * (D(1) + phase) for phase in RANGE_GRID_PHASES]
    assert anchors == [D("100"), D("100.2500"), D("100.500"), D("100.7500")]
    assert len(set(anchors)) == 4
    logger.info("SELF TEST | PASS | range-subgrids/ledger/recovery/risk/tick/native-stop/bankroll-separation/legacy-pyramid-retire invariants")

# -----------------------------------------------------------------------------
# BOT
# -----------------------------------------------------------------------------

class Bot:
    def __init__(self):
        # Fail fast before constructing components that may read/write persistent state.
        validate_runtime_config()
        self.instance_lock_fh = acquire_instance_lock()
        self.stop = threading.Event()
        self.client = AsterClient(USER_ADDRESS, SIGNER_ADDRESS, SIGNER_PRIVATE_KEY)
        self.store = StateStore()
        self.rules = RulesBook(self.client)
        self.md = MarketData(self.client)
        self.news = NewsFilter()
        self.account = AccountManager(self.client, self.rules, self.store)
        self.ledger = FillLedger(LEDGER_FILE)
        if self.store.loaded_fresh:
            _existing_ledger = self.ledger.open_by_symbol_side()
            if any(dec(q) > 0 for q in _existing_ledger.values()):
                raise RuntimeError(
                    f"STATE FRESH COM LEDGER NAO VAZIO | {_existing_ledger} | startup bloqueado para preservar ownership"
                )
        self.exe = ExecutionEngine(self.client, self.account, self.rules, self.store, self.ledger)
        self._last_periodic_reconcile_ms = 0
        self.reconciler = Reconciler(self.client, self.store, self.ledger, self.rules, self.exe)
        self.range_engines: List[RangeEngine] = []
        self.macd_engines: List[MacdEngine] = []
        self.last_hb = 0.0

    def _range_grid_migrated(self, symbol: str) -> bool:
        return bool(self.store.state.get("maintenance", {}).get("range_grid_v19_migrated", {}).get(symbol))

    def _range_grids_pristine(self, symbol: str) -> bool:
        for i, _phase in enumerate(RANGE_GRID_PHASES):
            st = self.store.state.get("range_grids", {}).get(f"{symbol}:G{i}", {})
            if st.get("basket") or dec(st.get("realized_pnl")) != 0 or int(st.get("wins", 0)) or int(st.get("losses", 0)):
                return False
        return True

    def _migrate_legacy_range_to_grids_if_flat(self, symbol: str) -> bool:
        with self.store.lock:
            if self._range_grid_migrated(symbol):
                return True
            legacy = self.store.state.get("range", {}).get(symbol) or {}
            if legacy.get("basket"):
                return False
            if not self._range_grids_pristine(symbol):
                legacy_neutral = (
                    dec(legacy.get("recovery_deficit")) == 0
                    and dec(legacy.get("realized_pnl")) == 0
                    and dec(legacy.get("equity"), str(configured_bankroll(symbol))) == configured_bankroll(symbol)
                )
                if not legacy_neutral:
                    self.store.kill("SOFT", f"RANGE_GRID_MIGRATION_CONFLICT:{symbol}")
                    return False

            old_base = dec(legacy.get("bankroll_config_base"), str(configured_bankroll(symbol)))
            old_eq = dec(legacy.get("equity"), str(old_base))
            old_rd = dec(legacy.get("recovery_deficit"))
            old_realized = dec(legacy.get("realized_pnl"))
            old_anchor = dec(legacy.get("anchor"))
            old_pa = dec(legacy.get("protect_anchor"))
            old_status = str(legacy.get("status", "IDLE")).upper()

            for i, phase in enumerate(RANGE_GRID_PHASES):
                gid = f"G{i}"
                g = self.store.state["range_grids"][f"{symbol}:{gid}"]
                inherited_base = old_base / D(RANGE_GRID_COUNT)
                inherited_eq = old_eq / D(RANGE_GRID_COUNT)
                target_base = configured_range_grid_bankroll(symbol)
                bankroll_uplift = target_base - inherited_base
                g["equity"] = str(inherited_eq + bankroll_uplift)
                g["bankroll_config_base"] = str(target_base)
                g["recovery_deficit"] = str(old_rd / D(RANGE_GRID_COUNT))
                g["realized_pnl"] = str(old_realized / D(RANGE_GRID_COUNT))
                g["grid_id"] = gid
                g["grid_phase"] = str(phase)
                g["strategy"] = f"RANGE:{symbol}:{gid}"
                g["basket"] = None
                g["failures"] = 0
                g["last_result"] = "MIGRATED_FROM_LEGACY_V19"
                g["anchor"] = str(old_anchor * (D(1) + phase)) if old_anchor > 0 else None
                if old_status == "PROTECT":
                    g["status"] = "PROTECT"
                    g["protect_anchor"] = str(old_pa if old_pa > 0 else old_anchor) if (old_pa > 0 or old_anchor > 0) else None
                else:
                    g["status"] = "IDLE"
                    g["protect_anchor"] = None
                g["last_update"] = now_iso()

            legacy["status"] = "RETIRED_TO_GRIDS"
            legacy["basket"] = None
            legacy["protect_anchor"] = None
            legacy["last_result"] = "MIGRATED_TO_RANGE_GRIDS_V19"
            legacy["last_update"] = now_iso()
            self.store.state["maintenance"].setdefault("range_grid_v19_migrated", {})[symbol] = {
                "at": now_iso(), "version": VERSION, "grid_count": RANGE_GRID_COUNT,
                "legacy_equity": str(old_eq), "legacy_base": str(old_base),
                "legacy_rd": str(old_rd), "target_grid_bankroll": str(configured_range_grid_bankroll(symbol)),
            }
            self.store.save()
            logger.warning(
                f"RANGE GRID MIGRATION | {symbol} | old_eq={old_eq} old_RD={old_rd} -> "
                f"{RANGE_GRID_COUNT} grids bankroll={configured_range_grid_bankroll(symbol)} cada"
            )
            return True

    def _refresh_range_grid_migrations(self) -> None:
        if not RANGE_ENGINE_ENABLED:
            return
        for symbol in SYMBOLS:
            self._migrate_legacy_range_to_grids_if_flat(symbol)

    def reset_inherited_range_protect_state(self) -> None:
        """One-shot cleanup of PROTECT/RD inherited from the pre-subgrid RANGE state.

        This is deliberately state-only: it never closes positions and never erases
        equity/realized PnL. Only flat, ledger-empty G0-G3 buckets that can still be
        proven to be untouched migration artifacts (last_result=MIGRATED_FROM_LEGACY_V19)
        are reset. New/current PROTECT states are never eligible.
        """
        if not RESET_INHERITED_RANGE_PROTECT_ON_STARTUP:
            logger.warning("INHERITED RANGE PROTECT RESET | DESABILITADO por configuracao")
            return

        maintenance = self.store.state.setdefault("maintenance", {})
        marker = maintenance.setdefault("range_inherited_protect_reset_v49", {})
        if marker.get("completed"):
            self.store.set_operational_block("INHERITED_RANGE_PROTECT_RESET", None)
            logger.info("INHERITED RANGE PROTECT RESET | one-shot ja concluido anteriormente")
            return

        candidates = []
        for symbol in SYMBOLS:
            if not self._range_grid_migrated(symbol):
                continue
            for i, _phase in enumerate(RANGE_GRID_PHASES):
                key = f"{symbol}:G{i}"
                st = self.store.state.get("range_grids", {}).get(key) or {}
                if str(st.get("last_result") or "") != "MIGRATED_FROM_LEGACY_V19":
                    continue
                if str(st.get("status", "IDLE")).upper() == "PROTECT" or dec(st.get("recovery_deficit")) > 0:
                    candidates.append((symbol, key))

        if not candidates:
            marker.update({
                "completed": True, "completed_at": now_iso(), "version": VERSION,
                "reason": "NO_INHERITED_PROTECT_CANDIDATES", "reset_grids": [],
            })
            self.store.save()
            self.store.set_operational_block("INHERITED_RANGE_PROTECT_RESET", None)
            logger.info("INHERITED RANGE PROTECT RESET | nenhum PROTECT/RD herdado elegivel")
            return

        self.store.set_operational_block(
            "INHERITED_RANGE_PROTECT_RESET", "ONE_SHOT_INHERITED_RANGE_PROTECT_RESET_IN_PROGRESS"
        )

        # Prove that no physical exposure exists on any symbol we are about to mutate.
        rows = self.client.positions()
        physical = {}
        for r in rows if isinstance(rows, list) else []:
            sym = str(r.get("symbol") or "").upper()
            if sym not in SYMBOLS:
                continue
            ps = str(r.get("positionSide") or "").upper()
            if ps not in ("LONG", "SHORT"):
                continue
            physical[(sym, ps)] = abs(dec(r.get("positionAmt")))

        target_symbols = sorted({sym for sym, _key in candidates})
        for symbol in target_symbols:
            step = self.rules.rules[symbol].step_size
            for side in ("LONG", "SHORT"):
                if physical.get((symbol, side), D(0)) > max(step, D("0.00000001")):
                    reason = f"PHYSICAL_NOT_FLAT:{symbol}:{side}:{physical.get((symbol, side), D(0))}"
                    self.store.set_operational_block("INHERITED_RANGE_PROTECT_RESET", reason)
                    raise RuntimeError(f"INHERITED RANGE PROTECT RESET | ABORT | {reason}")

        # Also prove every candidate strategy is ledger-flat.
        for symbol, key in candidates:
            gid = key.split(":", 1)[1]
            strategy_id = f"RANGE:{symbol}:{gid}"
            for side in ("LONG", "SHORT"):
                q = self.ledger.open_strategy_qty(strategy_id, symbol, side)
                if q > 0:
                    reason = f"LEDGER_NOT_FLAT:{strategy_id}:{side}:{q}"
                    self.store.set_operational_block("INHERITED_RANGE_PROTECT_RESET", reason)
                    raise RuntimeError(f"INHERITED RANGE PROTECT RESET | ABORT | {reason}")

        reset_grids = []
        with self.store.lock:
            for symbol, key in candidates:
                st = self.store.state.get("range_grids", {}).get(key) or {}
                # Re-check inside the state lock. A new/current state is never reset.
                if st.get("basket"):
                    reason = f"BASKET_PRESENT:{key}"
                    self.store.set_operational_block("INHERITED_RANGE_PROTECT_RESET", reason)
                    raise RuntimeError(f"INHERITED RANGE PROTECT RESET | ABORT | {reason}")
                if str(st.get("last_result") or "") != "MIGRATED_FROM_LEGACY_V19":
                    continue
                old_status = str(st.get("status", "IDLE"))
                old_rd = dec(st.get("recovery_deficit"))
                old_pa = st.get("protect_anchor")
                if old_status.upper() != "PROTECT" and old_rd <= 0:
                    continue
                # Preserve accounting. Reset only inherited operational recovery/protect state.
                st["recovery_deficit"] = "0"
                st["status"] = "IDLE"
                st["protect_anchor"] = None
                st["anchor"] = None
                st["failures"] = 0
                st["last_result"] = "INHERITED_PROTECT_RESET_V49"
                st["last_update"] = now_iso()
                reset_grids.append({
                    "grid": key, "old_status": old_status, "old_rd": str(old_rd),
                    "old_protect_anchor": old_pa, "equity_preserved": str(st.get("equity")),
                    "realized_pnl_preserved": str(st.get("realized_pnl")),
                })
            marker.update({
                "completed": True, "completed_at": now_iso(), "version": VERSION,
                "reason": "INHERITED_PROTECT_CLEARED", "reset_grids": reset_grids,
            })
            self.store.save()

        self.store.set_operational_block("INHERITED_RANGE_PROTECT_RESET", None)
        logger.warning(
            "INHERITED RANGE PROTECT RESET | CONCLUIDO | grids=%s | "
            "equity/realized_pnl preservados; RD/protect/anchors herdados zerados",
            [x["grid"] for x in reset_grids],
        )

    def reset_inherited_macd_protect_state(self) -> None:
        """One-shot cleanup of inherited MACD recovery/protect state.

        Accounting is preserved. The routine resets only operational recovery state and
        only after proving the six configured MACD strategies are logically and physically flat.
        This prevents historical PROTECT/RD/streak from blocking the current architecture while
        ensuring a legitimate live/current position can never be erased by startup maintenance.
        """
        if not RESET_INHERITED_MACD_PROTECT_ON_STARTUP:
            logger.info("INHERITED MACD PROTECT RESET | disabled")
            return

        maintenance = self.store.state.setdefault("maintenance", {})
        marker = maintenance.setdefault("macd_inherited_protect_reset_v51", {})
        if marker.get("completed"):
            self.store.set_operational_block("INHERITED_MACD_PROTECT_RESET", None)
            logger.info("INHERITED MACD PROTECT RESET | one-shot ja concluido anteriormente")
            return

        candidates = []
        with self.store.lock:
            for key, st in self.store.state.get("macd", {}).items():
                if not isinstance(st, dict):
                    continue
                symbol = str(st.get("symbol") or "").upper()
                tf = str(st.get("tf") or "")
                if symbol not in SYMBOLS or tf not in MACD_TIMEFRAMES:
                    continue
                if st.get("position"):
                    continue
                if (bool(st.get("protect")) or dec(st.get("recovery_deficit")) > 0
                        or int(st.get("loss_streak", 0) or 0) > 0
                        or int(st.get("recovery_level", 0) or 0) > 0):
                    candidates.append((symbol, tf, key))

        if not candidates:
            marker.update({
                "completed": True, "completed_at": now_iso(), "version": VERSION,
                "reason": "NO_INHERITED_MACD_PROTECT_CANDIDATES", "reset_macd": [],
            })
            self.store.save()
            self.store.set_operational_block("INHERITED_MACD_PROTECT_RESET", None)
            logger.info("INHERITED MACD PROTECT RESET | nenhum PROTECT/RD/streak herdado elegivel")
            return

        self.store.set_operational_block(
            "INHERITED_MACD_PROTECT_RESET", "ONE_SHOT_INHERITED_MACD_PROTECT_RESET_IN_PROGRESS"
        )

        rows = self.client.positions()
        physical = {}
        for r in rows if isinstance(rows, list) else []:
            sym = str(r.get("symbol") or "").upper()
            if sym not in SYMBOLS:
                continue
            ps = str(r.get("positionSide") or "").upper()
            if ps not in ("LONG", "SHORT"):
                continue
            physical[(sym, ps)] = abs(dec(r.get("positionAmt")))

        target_symbols = sorted({symbol for symbol, _tf, _key in candidates})
        for symbol in target_symbols:
            step = self.rules.rules[symbol].step_size
            for side in ("LONG", "SHORT"):
                qty = physical.get((symbol, side), D(0))
                if qty > max(step, D("0.00000001")):
                    reason = f"PHYSICAL_NOT_FLAT:{symbol}:{side}:{qty}"
                    self.store.set_operational_block("INHERITED_MACD_PROTECT_RESET", reason)
                    raise RuntimeError(f"INHERITED MACD PROTECT RESET | ABORT | {reason}")

        for symbol, tf, _key in candidates:
            strategy_id = f"MACD:{symbol}:{tf}"
            for side in ("LONG", "SHORT"):
                q = self.ledger.open_strategy_qty(strategy_id, symbol, side)
                if q > 0:
                    reason = f"LEDGER_NOT_FLAT:{strategy_id}:{side}:{q}"
                    self.store.set_operational_block("INHERITED_MACD_PROTECT_RESET", reason)
                    raise RuntimeError(f"INHERITED MACD PROTECT RESET | ABORT | {reason}")

        reset_macd = []
        with self.store.lock:
            for symbol, tf, key in candidates:
                st = self.store.state.get("macd", {}).get(key) or {}
                if st.get("position"):
                    reason = f"POSITION_PRESENT:{key}"
                    self.store.set_operational_block("INHERITED_MACD_PROTECT_RESET", reason)
                    raise RuntimeError(f"INHERITED MACD PROTECT RESET | ABORT | {reason}")
                old_protect = bool(st.get("protect"))
                old_rd = dec(st.get("recovery_deficit"))
                old_streak = int(st.get("loss_streak", 0) or 0)
                old_level = int(st.get("recovery_level", 0) or 0)
                old_pa = st.get("protect_anchor")
                if not (old_protect or old_rd > 0 or old_streak > 0 or old_level > 0):
                    continue
                st["recovery_deficit"] = "0"
                st["loss_streak"] = 0
                st["recovery_level"] = 0
                st["protect"] = False
                st["protect_anchor"] = None
                st["last_result"] = "INHERITED_MACD_PROTECT_RESET_V51"
                st["last_update"] = now_iso()
                reset_macd.append({
                    "macd": key, "old_protect": old_protect, "old_rd": str(old_rd),
                    "old_streak": old_streak, "old_recovery_level": old_level,
                    "old_protect_anchor": old_pa, "equity_preserved": str(st.get("equity")),
                    "realized_pnl_preserved": str(st.get("realized_pnl")),
                })
            marker.update({
                "completed": True, "completed_at": now_iso(), "version": VERSION,
                "reason": "INHERITED_MACD_PROTECT_CLEARED", "reset_macd": reset_macd,
            })
            self.store.save()

        self.store.set_operational_block("INHERITED_MACD_PROTECT_RESET", None)
        logger.warning(
            "INHERITED MACD PROTECT RESET | CONCLUIDO | macd=%s | "
            "equity/realized_pnl/last_candle preservados; RD/streak/recovery_level/protect herdados zerados",
            [x["macd"] for x in reset_macd],
        )

    def retire_legacy_range_positions(self) -> None:
        """One-shot retirement of pre-subgrid RANGE baskets.

        Only closes exposure proven to belong to the legacy RANGE:{symbol} strategy.
        Current RANGE:G0-G3 and MACD ownership is preserved. If state, ledger and
        physical quantities cannot be reconciled safely, the routine fails closed.
        """
        if not RETIRE_LEGACY_RANGE_ON_STARTUP:
            logger.warning("LEGACY RANGE RETIRE | DESABILITADO por configuracao")
            return

        maintenance = self.store.state.setdefault("maintenance", {})
        marker = maintenance.setdefault("legacy_range_retirement_v47", {})
        if marker.get("completed"):
            self.store.set_operational_block("LEGACY_RANGE_RETIRE", None)
            logger.info("LEGACY RANGE RETIRE | one-shot ja concluido anteriormente")
            return

        legacy_symbols = []
        for symbol in SYMBOLS:
            st = self.store.state.get("range", {}).get(symbol) or {}
            if st.get("basket"):
                legacy_symbols.append(symbol)

        if not legacy_symbols:
            marker.update({
                "completed": True,
                "completed_at": now_iso(),
                "reason": "NO_LEGACY_RANGE_BASKETS",
                "version": VERSION,
            })
            self.store.save()
            self.store.set_operational_block("LEGACY_RANGE_RETIRE", None)
            logger.info("LEGACY RANGE RETIRE | nenhum basket RANGE legado aberto")
            return

        self.store.set_operational_block(
            "LEGACY_RANGE_RETIRE",
            "ONE_SHOT_LEGACY_RANGE_RETIRE_IN_PROGRESS",
        )
        failures: List[str] = []
        closed_symbols: List[str] = []

        for symbol in legacy_symbols:
            strategy_id = f"RANGE:{symbol}"
            st = self.store.state.get("range", {}).get(symbol) or {}
            basket = st.get("basket") or {}
            legs = list(basket.get("legs") or [])
            if not legs:
                failures.append(f"STATE_BASKET_WITHOUT_LEGS:{symbol}")
                continue

            expected = {"LONG": D(0), "SHORT": D(0)}
            for leg in legs:
                side = str(leg.get("side", "")).upper()
                if side not in expected:
                    failures.append(f"INVALID_SIDE:{symbol}:{side}")
                    continue
                expected[side] += dec(leg.get("qty"))
            if failures and failures[-1].startswith("INVALID_SIDE:"):
                continue

            # State <-> ledger ownership proof for the legacy strategy itself.
            mismatch = False
            for side in ("LONG", "SHORT"):
                ledger_qty = self.ledger.open_strategy_qty(strategy_id, symbol, side)
                step = self.rules.rules[symbol].step_size
                if abs(ledger_qty - expected[side]) > step:
                    failures.append(
                        f"STATE_LEDGER_MISMATCH:{symbol}:{side}:state={expected[side]}:ledger={ledger_qty}"
                    )
                    mismatch = True
            if mismatch:
                continue

            # Physical must equal total ledger ownership (legacy + any current strategy),
            # otherwise there is unknown/manual exposure and retirement must not trade.
            try:
                positions = self.client.positions() if LIVE_TRADING else []
            except Exception as exc:
                failures.append(f"POSITION_SNAPSHOT_FAIL:{symbol}:{exc}")
                continue

            physical = {"LONG": D(0), "SHORT": D(0)}
            marks = []
            for p in (positions if isinstance(positions, list) else []):
                if str(p.get("symbol", "")).upper() != symbol:
                    continue
                side = str(p.get("positionSide", "")).upper()
                if side in physical:
                    physical[side] = abs(dec(p.get("positionAmt")))
                    mp = dec(p.get("markPrice") or p.get("entryPrice"))
                    if mp > 0:
                        marks.append(mp)

            for side in ("LONG", "SHORT"):
                owned = sum(self.ledger.open_strategy_breakdown(symbol, side).values(), D(0))
                step = self.rules.rules[symbol].step_size
                if abs(physical[side] - owned) > step:
                    failures.append(
                        f"PHYSICAL_LEDGER_MISMATCH:{symbol}:{side}:physical={physical[side]}:ledger={owned}"
                    )
                    mismatch = True
            if mismatch:
                continue

            price = marks[0] if marks else dec(basket.get("initial_entry") or basket.get("signal_entry") or st.get("anchor"))
            if price <= 0:
                failures.append(f"NO_REFERENCE_PRICE:{symbol}")
                continue

            logger.warning(
                "LEGACY RANGE RETIRE | CLOSING | symbol=%s strategy=%s | expected=%s physical=%s mark=%s",
                symbol, strategy_id, expected, physical, dstr(price, 8),
            )
            try:
                legacy_engine = RangeEngine(
                    symbol, self.client, self.md, self.news, self.account, self.exe, self.store,
                    state_bucket="range", state_key=symbol, grid_id="LEGACY",
                    grid_phase=D(0), allow_new_entries=False,
                )
                legacy_engine._close_basket(price, "RETIRE_LEGACY_RANGE_V47", protect_after=False)
            except Exception as exc:
                failures.append(f"CLOSE_FAIL:{symbol}:{exc}")
                logger.exception("LEGACY RANGE RETIRE | CLOSE FAIL | %s", symbol)
                continue

            # Post-close proof: legacy ledger must be zero and physical must be fully
            # explained by remaining non-legacy strategies.
            legacy_remaining = {
                side: self.ledger.open_strategy_qty(strategy_id, symbol, side)
                for side in ("LONG", "SHORT")
            }
            if any(q > 0 for q in legacy_remaining.values()):
                failures.append(f"LEGACY_LEDGER_REMAINS:{symbol}:{legacy_remaining}")
                continue
            if (self.store.state.get("range", {}).get(symbol) or {}).get("basket"):
                failures.append(f"LEGACY_STATE_BASKET_REMAINS:{symbol}")
                continue

            try:
                fresh = self.client.positions() if LIVE_TRADING else []
            except Exception as exc:
                failures.append(f"POST_CLOSE_POSITION_FAIL:{symbol}:{exc}")
                continue
            fresh_physical = {"LONG": D(0), "SHORT": D(0)}
            for p in (fresh if isinstance(fresh, list) else []):
                if str(p.get("symbol", "")).upper() == symbol:
                    side = str(p.get("positionSide", "")).upper()
                    if side in fresh_physical:
                        fresh_physical[side] = abs(dec(p.get("positionAmt")))
            post_bad = False
            for side in ("LONG", "SHORT"):
                remaining_owned = sum(self.ledger.open_strategy_breakdown(symbol, side).values(), D(0))
                step = self.rules.rules[symbol].step_size
                if abs(fresh_physical[side] - remaining_owned) > step:
                    failures.append(
                        f"POST_CLOSE_PHYSICAL_LEDGER_MISMATCH:{symbol}:{side}:physical={fresh_physical[side]}:ledger={remaining_owned}"
                    )
                    post_bad = True
            if post_bad:
                continue

            closed_symbols.append(symbol)
            logger.warning(
                "LEGACY RANGE RETIRE | CLOSED | symbol=%s | legacy_zero=True | remaining_physical=%s",
                symbol, fresh_physical,
            )

        remaining_baskets = [
            s for s in SYMBOLS
            if (self.store.state.get("range", {}).get(s) or {}).get("basket")
        ]
        marker.update({
            "completed": not remaining_baskets and not failures,
            "last_run_at": now_iso(),
            "version": VERSION,
            "closed_symbols": closed_symbols,
            "remaining_baskets": remaining_baskets,
            "failures": failures[-20:],
        })
        if marker["completed"]:
            marker["completed_at"] = now_iso()
        self.store.save()

        if marker["completed"]:
            self.store.set_operational_block("LEGACY_RANGE_RETIRE", None)
            logger.warning(
                "LEGACY RANGE RETIRE | CONCLUIDO | baskets legados encerrados=%s | somente G0-G3 + MACD permanecem",
                closed_symbols,
            )
        else:
            reason = f"LEGACY_RANGE_RETIRE_INCOMPLETE remaining={remaining_baskets} failures={failures[-5:]}"
            self.store.set_operational_block("LEGACY_RANGE_RETIRE", reason)
            logger.error("LEGACY RANGE RETIRE | INCOMPLETO | novas entradas bloqueadas | %s", reason)

    def retire_legacy_pyramid_positions(self) -> None:
        """Fecha somente lots persistentes PYRAMID:* que sobraram do robô antigo.

        O Perpetual Principal não possui PyramidEngine. O ledger é usado como prova de
        ownership para que nenhuma quantidade RANGE/MACD seja fechada por engano.
        """
        if not RETIRE_LEGACY_PYRAMID_ON_STARTUP:
            logger.warning("LEGACY PYRAMID RETIRE | DESABILITADO por configuracao")
            return

        maintenance = self.store.state.setdefault("maintenance", {})
        marker = maintenance.setdefault("legacy_pyramid_retirement", {})
        lots = self.ledger.open_lots_by_strategy_prefix("PYRAMID:")

        if not lots:
            if not marker.get("completed"):
                marker.update({
                    "completed": True,
                    "completed_at": now_iso(),
                    "reason": "NO_OPEN_PYRAMID_LEDGER_LOTS",
                })
                self.store.save()
            self.store.set_operational_block("LEGACY_PYRAMID_RETIRE", None)
            logger.info("LEGACY PYRAMID RETIRE | nenhum lot PYRAMID aberto no ledger")
            return

        logger.warning(
            "LEGACY PYRAMID RETIRE | encontrados=%s lots | action=CLOSE_LEDGER_OWNED_ONLY",
            len(lots),
        )

        failures: List[str] = []
        for lot in lots:
            strategy_id = str(lot["strategy_id"])
            symbol = str(lot["symbol"]).upper()
            side = str(lot["side"]).upper()
            qty = dec(lot["qty"])

            if symbol not in SYMBOLS or side not in ("LONG", "SHORT") or qty <= 0:
                failures.append(f"INVALID_LOT:{strategy_id}:{symbol}:{side}:{qty}")
                continue

            # Re-read physical position immediately before every close.
            positions = self.client.positions() if LIVE_TRADING else []
            physical_qty = D(0)
            mark = dec(lot.get("entry_price"))
            for p in (positions if isinstance(positions, list) else []):
                if str(p.get("symbol", "")).upper() == symbol and str(p.get("positionSide", "")).upper() == side:
                    physical_qty = abs(dec(p.get("positionAmt")))
                    mark = dec(p.get("markPrice") or p.get("entryPrice") or mark)
                    break

            if LIVE_TRADING and physical_qty <= 0:
                # Physical already gone: reconcile this specific ledger lot without
                # sending a duplicate order.
                self.ledger.record_close_lot(str(lot["id"]), qty)
                logger.warning(
                    "LEGACY PYRAMID RETIRE | physical already flat | strategy=%s symbol=%s side=%s qty=%s "
                    "| ledger lot marcado fechado sem nova ordem",
                    strategy_id, symbol, side, dstr(qty, 8),
                )
                continue

            close_qty = qty if not LIVE_TRADING else min(qty, physical_qty)
            step = self.rules.rules[symbol].step_size
            close_qty = floor_step(close_qty, step)
            if close_qty <= 0:
                failures.append(
                    f"NO_CLOSABLE_QTY:{strategy_id}:{symbol}:{side}:ledger={qty}:physical={physical_qty}"
                )
                continue

            # Construct only the fields required by close_leg/_close_record.
            leg = {
                "id": str(lot["id"]),
                "side": side,
                "qty": str(close_qty),
                "entry_price": str(dec(lot["entry_price"])),
            }

            logger.warning(
                "LEGACY PYRAMID RETIRE | CLOSING | strategy=%s symbol=%s side=%s "
                "| ledger_qty=%s physical_qty=%s close_qty=%s mark=%s",
                strategy_id, symbol, side, dstr(qty, 8), dstr(physical_qty, 8),
                dstr(close_qty, 8), dstr(mark, 8),
            )

            try:
                rec = self.exe.close_leg(
                    strategy_id,
                    symbol,
                    leg,
                    mark,
                    "RETIRE_LEGACY_PYRAMID_V21",
                    max_physical_qty=close_qty,
                )
                if rec is None:
                    failures.append(f"CLOSE_SKIPPED:{strategy_id}:{symbol}:{side}:{close_qty}")
                    continue
                logger.warning(
                    "LEGACY PYRAMID RETIRE | CLOSED | strategy=%s symbol=%s side=%s qty=%s "
                    "| entry=%s exit=%s pnl_est=%s exchange_realized=%s",
                    strategy_id, symbol, side, rec.get("qty"), rec.get("entry_price"),
                    rec.get("exit_price"), rec.get("pnl_est"), rec.get("exchange_realized_pnl"),
                )
            except Exception as exc:
                failures.append(f"CLOSE_FAIL:{strategy_id}:{symbol}:{side}:{exc}")
                logger.exception(
                    "LEGACY PYRAMID RETIRE | CLOSE FAIL | strategy=%s symbol=%s side=%s qty=%s",
                    strategy_id, symbol, side, dstr(close_qty, 8),
                )

        remaining = self.ledger.open_lots_by_strategy_prefix("PYRAMID:")
        marker.update({
            "completed": not bool(remaining) and not bool(failures),
            "last_run_at": now_iso(),
            "remaining_open_lots": [
                {
                    "strategy_id": x["strategy_id"],
                    "symbol": x["symbol"],
                    "side": x["side"],
                    "qty": x["qty"],
                }
                for x in remaining
            ],
            "failures": failures[-20:],
        })
        if marker["completed"]:
            marker["completed_at"] = now_iso()
            # Old strategy state is no longer executable in Principal; keep only
            # retirement metadata. Ledger/trades retain the durable audit trail.
            if "pyramid" in self.store.state:
                self.store.state["pyramid"] = {}
            if "pyramid_grids" in self.store.state:
                self.store.state["pyramid_grids"] = {}
        self.store.save()

        if remaining or failures:
            reason = f"LEGACY_PYRAMID_RETIRE_INCOMPLETE remaining={remaining} failures={failures[-5:]}"
            self.store.set_operational_block("LEGACY_PYRAMID_RETIRE", reason)
            logger.error(
                "LEGACY PYRAMID RETIRE | INCOMPLETO | novas entradas bloqueadas | %s",
                reason,
            )
        else:
            self.store.set_operational_block("LEGACY_PYRAMID_RETIRE", None)
            logger.warning(
                "LEGACY PYRAMID RETIRE | CONCLUIDO | todos os lots PYRAMID legados encerrados; "
                "Principal segue somente RANGE+MACD"
            )

    def startup(self) -> None:
        logger.info("=" * 90)
        logger.info(f"{BOT_NAME} | version={VERSION} | LIVE_TRADING={LIVE_TRADING}")
        validate_runtime_config()
        logger.info("CONFIG GUARD | PASS | configuracao coerente antes de rede/ordens")
        logger.info(f"SYMBOLS={SYMBOLS} | RANGE={RANGE_ENGINE_ENABLED} mode={RANGE_SIGNAL_MODE} SUBGRIDS={RANGE_GRID_PHASES} | MACD_SEPARADO={MACD_ENGINE_ENABLED} TF={MACD_TIMEFRAMES}")
        logger.info(f"MARGIN=ISOLATED | MODE=HEDGE | MAX_REQUESTED_LEV={MAX_REQUESTED_LEVERAGE} | BOT_HARD_CAP={BOT_HARD_MAX_LEVERAGE} | API_HARD_CAP={API_HARD_MAX_LEVERAGE}")
        logger.info(f"MACD BASE ETH/HYPE bankroll={INITIAL_BANKROLL_USD} notional={INITIAL_OPERATION_NOTIONAL_USD} | MACD BTC bankroll={BTC_INITIAL_BANKROLL_USD} notional={BTC_INITIAL_OPERATION_NOTIONAL_USD} | RANGE GRID ETH/HYPE bankroll={RANGE_GRID_BANKROLL_USD} notional={RANGE_GRID_INITIAL_NOTIONAL_USD} | RANGE GRID BTC bankroll={BTC_RANGE_GRID_BANKROLL_USD} notional={BTC_RANGE_GRID_INITIAL_NOTIONAL_USD} | autoscale_notional={AUTO_SCALE_NOTIONAL_WITH_EQUITY}")
        logger.info(f"EXITS | RANGE_TP={RANGE_TAKE_PROFIT_PCT} RANGE_STOP={RANGE_HARD_STOP_PCT} | MACD: trailing_activation={MACD_TRAILING_ACTIVATION_PCT} trailing_distance={MACD_TRAILING_DISTANCE_PCT} stop_loss={MACD_HARD_STOP_PCT}")
        logger.info(f"NEWS 3-STAR={NEWS_FILTER_ENABLED} | janela=-{NEWS_WINDOW_BEFORE_MIN}m/+{NEWS_WINDOW_AFTER_MIN}m | fail_closed={NEWS_FAIL_CLOSED}")
        logger.info(f"SAME_SYMBOL_MULTI_STRATEGY={ALLOW_MULTI_STRATEGY_SAME_SYMBOL} | NATIVE_PROTECTIVE_ORDERS={NATIVE_PROTECTIVE_ORDERS} workingType={PROTECTIVE_WORKING_TYPE}")
        logger.info(f"HARDENING | state_backup={STATE_BACKUP_FILE} | ledger={LEDGER_FILE} | news_stale_max={NEWS_MAX_STALE_SECONDS}s | entry_price_max_age={MAX_PRICE_AGE_FOR_ENTRY_SECONDS}s | reconcile={RECONCILE_INTERVAL_SECONDS}s")
        logger.info(f"RISK CAPS | ETH/HYPE recovery={MAX_RECOVERY_NOTIONAL_USD} total_symbol={MAX_TOTAL_SYMBOL_NOTIONAL_USD} | BTC recovery={BTC_MAX_RECOVERY_NOTIONAL_USD} total_symbol={BTC_MAX_TOTAL_SYMBOL_NOTIONAL_USD}")
        logger.info(f"LEGACY PYRAMID RETIRE | enabled={RETIRE_LEGACY_PYRAMID_ON_STARTUP} | mode=LEDGER_OWNED_ONLY")
        logger.info(f"LEGACY RANGE RETIRE | enabled={RETIRE_LEGACY_RANGE_ON_STARTUP} | mode=ONE_SHOT_LEDGER_OWNED_ONLY")
        logger.info(f"INHERITED RANGE PROTECT RESET | enabled={RESET_INHERITED_RANGE_PROTECT_ON_STARTUP} | mode=ONE_SHOT_STATE_ONLY_ACCOUNTING_PRESERVED")
        logger.info(f"INHERITED MACD PROTECT RESET | enabled={RESET_INHERITED_MACD_PROTECT_ON_STARTUP} | mode=ONE_SHOT_STATE_ONLY_ACCOUNTING_PRESERVED")
        logger.info(f"FULL FACTORY RESET | enabled={FULL_FACTORY_RESET_ON_STARTUP} | id={FULL_FACTORY_RESET_ID} | mode=ONE_SHOT_ACCOUNT_WIDE_CLOSE_AND_HISTORY_RESET")
        logger.info("=" * 90)
        if (LIVE_TRADING or VALIDATE_API_ONLY) and (not USER_ADDRESS or not SIGNER_ADDRESS or not SIGNER_PRIVATE_KEY):
            raise RuntimeError("LIVE_TRADING=1 ou VALIDATE_API_ONLY=1 requer as tres credenciais da API Wallet V3")
        if SELF_TEST_ON_STARTUP:
            run_internal_regression_checks()
        self.client.sync_time()
        self.rules.refresh()
        if VALIDATE_API_ONLY:
            mode = self.client.position_mode()
            multi_assets = self.client.multi_assets_mode()
            balances = self.client.balance()
            account = self.client.account()
            positions = self.client.positions()
            logger.info(f"API V3 VALIDADA | signer={SIGNER_ADDRESS} | hedge={mode} | multi_assets={multi_assets} | balances={len(balances) if isinstance(balances, list) else 0} | positions={len(positions) if isinstance(positions, list) else 0} | canTrade={account.get('canTrade') if isinstance(account, dict) else None}")
            return
        if LIVE_TRADING:
            self.account.ensure_modes()
            self.account.sync(force=True)
            if LEDGER_RECONCILE_ON_STARTUP:
                self.ledger.bootstrap_from_state(self.store)
            if FULL_FACTORY_RESET_ON_STARTUP:
                self.full_factory_reset_all_and_start_fresh()
            elif EMERGENCY_CLOSE_ALL_AND_RESET:
                self.emergency_close_all_and_reset()
            if RETIRE_LEGACY_PYRAMID_ON_STARTUP:
                self.retire_legacy_pyramid_positions()
            if RETIRE_LEGACY_RANGE_ON_STARTUP:
                self.retire_legacy_range_positions()
            self.reconciler.reconcile()
        else:
            logger.warning("MODO SIMULACAO: nenhuma ordem real sera enviada")

        if RANGE_ENGINE_ENABLED:
            self.range_engines = []
            if LIVE_TRADING:
                self._refresh_range_grid_migrations()
                self.reset_inherited_range_protect_state()
                self.reset_inherited_macd_protect_state()
            else:
                logger.info("RANGE GRID MIGRATION | SKIP | LIVE_TRADING=0; startup de simulacao nao migra estado persistido")
            for symbol in SYMBOLS:
                legacy = self.store.state.get("range", {}).get(symbol, {})
                if legacy.get("basket"):
                    self.range_engines.append(
                        RangeEngine(symbol, self.client, self.md, self.news, self.account, self.exe, self.store,
                                    state_bucket="range", state_key=symbol, grid_id="LEGACY",
                                    grid_phase=D(0), allow_new_entries=False)
                    )
                for i, phase in enumerate(RANGE_GRID_PHASES):
                    gid = f"G{i}"
                    self.range_engines.append(
                        RangeEngine(symbol, self.client, self.md, self.news, self.account, self.exe, self.store,
                                    state_bucket="range_grids", state_key=f"{symbol}:{gid}",
                                    grid_id=gid, grid_phase=phase, allow_new_entries=True)
                    )
        if MACD_ENGINE_ENABLED:
            self.macd_engines = [MacdEngine(s, tf, self.client, self.md, self.news, self.account, self.exe, self.store)
                                 for s in SYMBOLS for tf in MACD_TIMEFRAMES]
        self.md.start(); self.news.start()

    def full_factory_reset_all_and_start_fresh(self) -> None:
        """One-shot account-wide reset requested for V52.

        Intentionally closes *all* account positions and cancels *all* account orders,
        including exposure not owned by the bot. It proceeds only after the exchange
        proves zero remaining positions and zero remaining open orders. Then it resets
        all RANGE/MACD accounting/history artifacts and writes the same fresh state to
        both primary and backup so historical strategy state cannot be restored later.
        """
        maintenance = self.store.state.setdefault("maintenance", {"completed_emergency_actions": []})
        completed = maintenance.setdefault("completed_factory_resets", [])
        completed_ids = {
            str(x.get("id")) if isinstance(x, dict) else str(x)
            for x in completed
        }
        if FULL_FACTORY_RESET_ID in completed_ids:
            logger.warning(
                "FULL FACTORY RESET | id=%s ja concluido; nenhuma ordem/posicao sera repetida",
                FULL_FACTORY_RESET_ID,
            )
            return

        self.store.set_operational_block(
            "FULL_FACTORY_RESET",
            f"ONE_SHOT_ACCOUNT_WIDE_RESET:{FULL_FACTORY_RESET_ID}",
        )
        logger.critical(
            "FULL FACTORY RESET | INICIO | id=%s | cancelando TODAS as ordens e fechando TODAS as posicoes da conta",
            FULL_FACTORY_RESET_ID,
        )

        open_orders = self.client.open_orders()
        positions = self.client.positions()
        symbols = {
            str(x.get("symbol", "")).upper()
            for x in (open_orders if isinstance(open_orders, list) else [])
            if x.get("symbol")
        }
        symbols.update(
            str(x.get("symbol", "")).upper()
            for x in (positions if isinstance(positions, list) else [])
            if x.get("symbol") and abs(dec(x.get("positionAmt"))) > 0
        )

        for symbol in sorted(symbols):
            if not self.client.cancel_all_confirmed(symbol):
                raise RuntimeError(f"FULL FACTORY RESET | cancelamento NAO confirmado | {symbol}")
            logger.warning("FULL FACTORY RESET | ordens canceladas e confirmadas | %s", symbol)

        for p in (positions if isinstance(positions, list) else []):
            qty = abs(dec(p.get("positionAmt")))
            if qty <= 0:
                continue
            symbol = str(p.get("symbol", "")).upper()
            position_side = str(p.get("positionSide", "")).upper()
            if position_side not in ("LONG", "SHORT"):
                raise RuntimeError(f"FULL FACTORY RESET encontrou positionSide invalido: {p}")
            mark = dec(p.get("markPrice") or p.get("entryPrice") or 0)
            if mark <= 0:
                raise RuntimeError(f"FULL FACTORY RESET sem preco valido para fechar {symbol} {position_side}")
            logger.critical(
                "FULL FACTORY CLOSE | symbol=%s side=%s qty=%s entry=%s mark=%s notional=%s unreal=%s",
                symbol, position_side, qty, p.get("entryPrice"), p.get("markPrice"),
                abs(dec(p.get("notional") or qty * mark)),
                p.get("unRealizedProfit") or p.get("unrealizedProfit"),
            )
            self.exe.market("FULL_FACTORY_RESET", symbol, position_side, qty, False, mark)

        remaining_positions = []
        remaining_orders = []
        for _ in range(8):
            time.sleep(1)
            remaining_positions = [
                p for p in self.client.positions()
                if abs(dec(p.get("positionAmt"))) > 0
            ]
            remaining_orders = self.client.open_orders()
            if not isinstance(remaining_orders, list):
                remaining_orders = [remaining_orders] if remaining_orders else []
            if not remaining_positions and not remaining_orders:
                break
            # Orders can appear transiently while closes settle; cancel them again and prove zero.
            residual_symbols = {
                str(x.get("symbol", "")).upper()
                for x in remaining_orders
                if isinstance(x, dict) and x.get("symbol")
            }
            for symbol in sorted(residual_symbols):
                self.client.cancel_all_confirmed(symbol)

        if remaining_positions or remaining_orders:
            raise RuntimeError(
                "FULL FACTORY RESET NAO CONFIRMADO | posicoes_restantes="
                + str([(p.get("symbol"), p.get("positionSide"), p.get("positionAmt")) for p in remaining_positions])
                + " | ordens_restantes="
                + str([(o.get("symbol"), o.get("orderId"), o.get("clientOrderId")) for o in remaining_orders if isinstance(o, dict)])
            )

        reset = fresh_state()
        reset["maintenance"]["completed_factory_resets"] = [{
            "id": FULL_FACTORY_RESET_ID,
            "completed_at": now_iso(),
            "action": "ACCOUNT_WIDE_CLOSE_CANCEL_AND_FULL_HISTORY_RESET",
            "version": VERSION,
        }]
        reset["maintenance"]["completed_emergency_actions"] = []

        # Replace primary state and force backup to the same fresh image. StateStore.save()
        # normally preserves the prior generation in backup; that behavior is intentionally
        # overridden here because this operation explicitly erases pre-V52 strategy history.
        with self.store.lock:
            self.store.state = reset
            self.store.save()
            atomic_json_write(STATE_BACKUP_FILE, reset)

        # Clear durable execution/accounting history only after exchange-flat proof.
        self.ledger.reset()
        try:
            with self.ledger.lock:
                self.ledger.db.execute("VACUUM")
                self.ledger.db.commit()
        except Exception as e:
            logger.warning("FULL FACTORY RESET | SQLite VACUUM nao concluido | %s", e)

        for history_file in (TRADES_FILE, ORDER_JOURNAL_FILE):
            try:
                history_file.write_text("", encoding="utf-8")
            except Exception as e:
                raise RuntimeError(f"FULL FACTORY RESET falhou ao limpar {history_file}: {e}") from e

        self.account.sync(force=True)
        # Final authenticated proof after all local resets.
        final_positions = [
            p for p in self.client.positions()
            if abs(dec(p.get("positionAmt"))) > 0
        ]
        final_orders = self.client.open_orders()
        if not isinstance(final_orders, list):
            final_orders = [final_orders] if final_orders else []
        if final_positions or final_orders:
            raise RuntimeError(
                "FULL FACTORY RESET | PROVA FINAL FALHOU | positions="
                + str([(p.get("symbol"), p.get("positionSide"), p.get("positionAmt")) for p in final_positions])
                + " orders=" + str([(o.get("symbol"), o.get("orderId")) for o in final_orders if isinstance(o, dict)])
            )

        logger.critical(
            "FULL FACTORY RESET | CONCLUIDO | id=%s | positions=0 orders=0 | state+backup novos | ledger/trades/order_journal zerados | RANGE+MACD reiniciados nos bankrolls-base",
            FULL_FACTORY_RESET_ID,
        )

    def emergency_close_all_and_reset(self) -> None:
        maintenance = self.store.state.setdefault("maintenance", {"completed_emergency_actions": []})
        completed = maintenance.setdefault("completed_emergency_actions", [])
        completed_ids = {
            str(x.get("id")) if isinstance(x, dict) else str(x)
            for x in completed
        }
        if EMERGENCY_RESET_ID in completed_ids:
            logger.warning(f"EMERGENCY RESET | id={EMERGENCY_RESET_ID} ja concluido; nenhuma ordem repetida")
            return

        logger.critical(
            f"EMERGENCY RESET INICIO | id={EMERGENCY_RESET_ID} | cancelando TODAS as ordens e fechando TODAS as posicoes da conta"
        )
        open_orders = self.client.open_orders()
        positions = self.client.positions()
        symbols = {
            str(x.get("symbol", "")).upper()
            for x in (open_orders if isinstance(open_orders, list) else [])
            if x.get("symbol")
        }
        symbols.update(
            str(x.get("symbol", "")).upper()
            for x in (positions if isinstance(positions, list) else [])
            if x.get("symbol") and abs(dec(x.get("positionAmt"))) > 0
        )
        for symbol in sorted(symbols):
            self.client.cancel_all_confirmed(symbol)
            logger.warning(f"EMERGENCY RESET | ordens canceladas e CONFIRMADAS | {symbol}")

        for p in (positions if isinstance(positions, list) else []):
            qty = abs(dec(p.get("positionAmt")))
            if qty <= 0:
                continue
            symbol = str(p.get("symbol", "")).upper()
            position_side = str(p.get("positionSide", "")).upper()
            if position_side not in ("LONG", "SHORT"):
                raise RuntimeError(f"EMERGENCY RESET encontrou positionSide invalido: {p}")
            mark = dec(p.get("markPrice") or p.get("entryPrice") or 0)
            logger.critical(
                f"EMERGENCY CLOSE | symbol={symbol} strategy_owner={self.store.state.get('symbol_owner', {}).get(symbol)} side={position_side} qty={qty} entry={p.get('entryPrice')} mark={p.get('markPrice')} notional={abs(dec(p.get('notional') or qty * mark))} unreal={p.get('unRealizedProfit') or p.get('unrealizedProfit')}"
            )
            self.exe.market("EMERGENCY_RESET", symbol, position_side, qty, False, mark)

        remaining = []
        for _ in range(5):
            time.sleep(1)
            remaining = [
                p for p in self.client.positions()
                if abs(dec(p.get("positionAmt"))) > 0
            ]
            if not remaining:
                break
        if remaining:
            raise RuntimeError(
                "EMERGENCY RESET NAO CONFIRMADO; posicoes restantes="
                + str([(p.get("symbol"), p.get("positionSide"), p.get("positionAmt")) for p in remaining])
            )

        reset = fresh_state()
        reset["maintenance"]["completed_emergency_actions"] = [{
            "id": EMERGENCY_RESET_ID,
            "completed_at": now_iso(),
            "action": "CLOSE_ALL_POSITIONS_CANCEL_ALL_ORDERS_AND_RESET_STATE",
        }]
        with self.store.lock:
            self.store.state = reset
            self.store.save()
        self.ledger.reset()
        self.account.sync(force=True)
        logger.critical(
            f"EMERGENCY RESET CONCLUIDO | id={EMERGENCY_RESET_ID} | posicoes=0 | ordens=0 | estado zerado | novas entradas usam notional base configurado"
        )

    def hard_kill(self) -> bool:
        """Fail-closed HARD kill. Returns True only after exchange proves zero exposure."""
        if not LIVE_TRADING:
            return True
        logger.error("HARD KILL EXECUTION | cancelando ordens e fechando posicoes conhecidas")
        cancel_guard_ok = True
        for s in SYMBOLS:
            try:
                self.client.cancel_all_confirmed(s)
            except Exception as e:
                cancel_guard_ok = False
                logger.critical(f"HARD KILL cancel NAO CONFIRMADO {s} | {e}")
        if not cancel_guard_ok:
            logger.critical("HARD KILL | fechamento a mercado adiado: cancelamento de ordens nao foi confirmado em todos os simbolos")
            return False

        # Snapshot autenticado para nao depender do market-data WS durante uma emergencia.
        try:
            rows = self.client.positions()
            if not isinstance(rows, list):
                rows = [rows] if rows else []
        except Exception as e:
            logger.critical(f"HARD KILL | positionRisk indisponivel antes do fechamento | {e}")
            return False
        fallback_price: Dict[str, Decimal] = {}
        for row in rows:
            sym = str(row.get("symbol") or "").upper()
            px = dec(row.get("markPrice") or row.get("entryPrice") or 0)
            if sym in SYMBOLS and px > 0:
                fallback_price[sym] = px

        close_errors = False
        for e in self.range_engines:
            try:
                st = e.st(); b = st.get("basket")
                p = self.md.get(e.symbol) or fallback_price.get(e.symbol)
                if b:
                    if not p or p <= 0:
                        raise RuntimeError("preco de referencia indisponivel para fechar RANGE em HARD_KILL")
                    e._close_basket(p, "HARD_KILL", protect_after=False)
            except Exception as ex:
                close_errors = True
                logger.exception(f"HARD KILL range {e.symbol} | {ex}")
        for e in self.macd_engines:
            try:
                st = e.st(); p = self.md.get(e.symbol) or fallback_price.get(e.symbol)
                if st.get("position"):
                    if not p or p <= 0:
                        raise RuntimeError("preco de referencia indisponivel para fechar MACD em HARD_KILL")
                    e._close(p, "HARD_KILL")
            except Exception as ex:
                close_errors = True
                logger.exception(f"HARD KILL macd {e.id} | {ex}")

        # Nunca declara sucesso apenas porque as rotinas locais retornaram. A exchange e a autoridade final.
        remaining: List[Dict[str, Any]] = []
        for _ in range(5):
            try:
                snap = self.client.positions()
                if not isinstance(snap, list):
                    snap = [snap] if snap else []
                remaining = [
                    p for p in snap
                    if str(p.get("symbol") or "").upper() in SYMBOLS and abs(dec(p.get("positionAmt"))) > 0
                ]
            except Exception as e:
                logger.critical(f"HARD KILL | verificacao final positionRisk falhou | {e}")
                return False
            if not remaining:
                if close_errors:
                    logger.warning("HARD KILL | houve erro local de fechamento, mas exchange confirma exposicao zero")
                logger.critical("HARD KILL CONFIRMADO | exchange confirma zero exposicao nos simbolos configurados")
                return True
            time.sleep(1)
        logger.critical(
            "HARD KILL NAO CONFIRMADO | posicoes restantes=%s",
            [(p.get("symbol"), p.get("positionSide"), p.get("positionAmt")) for p in remaining],
        )
        return False

    def heartbeat(self) -> None:
        if time.time() - self.last_hb < HEARTBEAT_SECONDS:
            return
        self.last_hb = time.time()
        api_ok = True
        try:
            if LIVE_TRADING: self.account.sync(force=True)
        except Exception as e:
            api_ok = False
            logger.warning(f"HEARTBEAT account sync | {e}")
        parts = []
        with self.store.lock:
            for e in self.range_engines:
                r = e.st()
                parts.append(f"R:{e.symbol}:{e.grid_id}:eq={r['equity']},RD={r['recovery_deficit']},status={r['status']},fail={r['failures']},phase={r.get('grid_phase','0')}")
            for key, m in self.store.state["macd"].items():
                if m["symbol"] in SYMBOLS and m["tf"] in MACD_TIMEFRAMES:
                    parts.append(f"M:{m['symbol']}:{m['tf']}:eq={m['equity']},RD={m['recovery_deficit']},streak={m['loss_streak']},pos={'1' if m.get('position') else '0'},prot={int(bool(m.get('protect')))}")
            ks = self.store.state["kill_switch"]
            gate = self.store.state.get("trade_gate", {})
        logger.info(f"HEARTBEAT | wallet={self.account.wallet_balance} avail={self.account.available_balance} unreal={self.account.unrealized} | kill={ks.get('mode')}:{ks.get('reason')} | entry_gate={gate.get('open_allowed')}:{gate.get('reason')} | ledger={self.ledger.open_by_symbol_side()} | {' | '.join(parts)}")
        # RANGE PRICE MONITOR: exibe o ponto zero fixado e os gatilhos exatos de entrada +/-1%.
        # O anchor permanece fixo enquanto o RANGE estiver IDLE; portanto estes sao os precos
        # que o mercado precisa atingir para disparar LONG ou SHORT.
        for e in self.range_engines:
            try:
                rst = e.st()
                mark = self.md.get(e.symbol)
                anchor = dec(rst.get("anchor"))
                status = str(rst.get("status", "IDLE"))
                if anchor > 0:
                    long_trigger = e.exe.rules.trigger_price(
                        e.symbol, anchor * (D(1) + RANGE_TRIGGER_PCT), "UP"
                    )
                    short_trigger = e.exe.rules.trigger_price(
                        e.symbol, anchor * (D(1) - RANGE_TRIGGER_PCT), "DOWN"
                    )
                    if mark is not None and mark > 0:
                        to_long = max(D(0), (long_trigger / mark - D(1)) * D(100))
                        to_short = max(D(0), (D(1) - short_trigger / mark) * D(100))
                        logger.info(
                            f"RANGE PRICE MONITOR | {e.symbol} | status={status} mark={mark} "
                            f"anchor_fixado={anchor} LONG_entrada={long_trigger} SHORT_entrada={short_trigger} "
                            f"faltam_LONG={to_long:.6f}% faltam_SHORT={to_short:.6f}%"
                        )
                    else:
                        logger.info(
                            f"RANGE PRICE MONITOR | {e.symbol} | status={status} mark=INDISPONIVEL "
                            f"anchor_fixado={anchor} LONG_entrada={long_trigger} SHORT_entrada={short_trigger}"
                        )
                else:
                    logger.info(f"RANGE PRICE MONITOR | {e.symbol} | status={status} anchor_fixado=AGUARDANDO_PRIMEIRO_PRECO")
            except Exception as ex:
                logger.warning(f"RANGE PRICE MONITOR FAIL | {e.symbol} | {ex}")
        # MACD MONITOR: visibility only; no extra REST/klines calls are made here.
        # It shows whether each engine is free, protected or in-position, plus the remaining
        # protect-rearm distance when applicable. Cross/open/close events continue to be logged
        # by MacdEngine itself on closed candles.
        for e in self.macd_engines:
            try:
                mst = e.st()
                mark = self.md.get(e.symbol)
                pos = mst.get("position")
                protected = bool(mst.get("protect"))
                status = "POSITION" if pos else ("PROTECT" if protected else "IDLE")
                pa = dec(mst.get("protect_anchor"))
                move_pct = None
                falta_pct = None
                if protected and pa > 0 and mark is not None and mark > 0:
                    move_pct = abs(pct_change(pa, mark)) * D(100)
                    falta_pct = max(D(0), (MACD_REARM_PCT - abs(pct_change(pa, mark))) * D(100))
                logger.info(
                    "MACD MONITOR | %s | status=%s mark=%s RD=%s streak=%s recovery_level=%s "
                    "protect_anchor=%s move_protect=%s faltam_rearm=%s last_candle_close_ms=%s",
                    e.id, status, mark if mark is not None else "INDISPONIVEL",
                    mst.get("recovery_deficit"), mst.get("loss_streak"), mst.get("recovery_level"),
                    mst.get("protect_anchor"),
                    (f"{move_pct:.6f}%" if move_pct is not None else "-"),
                    (f"{falta_pct:.6f}%" if falta_pct is not None else "-"),
                    mst.get("last_candle_close_ms", 0),
                )
            except Exception as ex:
                logger.warning("MACD MONITOR FAIL | %s | %s", e.id, ex)
        with self.news._lock:
            news_events = len(self.news.events)
            news_source = self.news.last_source
            news_age = int(max(0, time.time() - self.news.last_success)) if self.news.last_success else -1
        news_health = (
            "DISABLED" if not NEWS_FILTER_ENABLED else
            "OK" if self.news.last_success and news_age <= NEWS_MAX_STALE_SECONDS else
            "STALE"
        )
        logger.info(
            f"HEALTH SNAPSHOT | version={VERSION} live={LIVE_TRADING} api_v3={'OK' if api_ok else 'DEGRADED'} signer={SIGNER_ADDRESS} | "
            f"mode=HEDGE margin=ISOLATED multi_strategy_same_symbol={ALLOW_MULTI_STRATEGY_SAME_SYMBOL} native_protection={NATIVE_PROTECTIVE_ORDERS} | "
            f"news={news_health} source={news_source} events={news_events} age_s={news_age} fail_closed={NEWS_FAIL_CLOSED} window=-{NEWS_WINDOW_BEFORE_MIN}m/+{NEWS_WINDOW_AFTER_MIN}m | "
            f"range=VOLATILITY_ONLY trigger={RANGE_TRIGGER_PCT} tp={RANGE_TAKE_PROFIT_PCT} stop={RANGE_HARD_STOP_PCT} | "
            f"macd={MACD_ENGINE_ENABLED} tf={MACD_TIMEFRAMES} trailing_activation={MACD_TRAILING_ACTIVATION_PCT} trailing_distance={MACD_TRAILING_DISTANCE_PCT} hard_stop={MACD_HARD_STOP_PCT} native_trailing={MACD_NATIVE_TRAILING_ENABLED} watchdog={PROTECTIVE_WATCHDOG_SECONDS}s recovery_multiplier={MACD_RECOVERY_MULTIPLIER}x | recovery={RECOVERY_MULTIPLIER}x range, {MACD_RECOVERY_MULTIPLIER}x macd, max_fail={MAX_RECOVERY_FAILURES}"
        )
        if LIVE_TRADING:
            try:
                self.log_open_positions_detailed()
            except Exception as e:
                logger.warning(f"OPEN POSITION DETAIL FAIL | {e}")

    def log_open_positions_detailed(self) -> None:
        positions = self.client.positions()
        found = 0
        with self.store.lock:
            state_range = dict(self.store.state.get("range", {}))
            state_range.update(self.store.state.get("range_grids", {}))
            state_macd = self.store.state.get("macd", {})
            legacy_owners = dict(self.store.state.get("symbol_owner", {}))

        logical: Dict[Tuple[str, str], List[Dict[str, Any]]] = {}

        def add_logical(symbol: str, side: str, strategy: str, vqty: Decimal,
                        target: Any = "-", stop: Any = "-", recovery: Any = "-",
                        virtual_entry: Any = "-") -> None:
            symbol = str(symbol).upper()
            side = str(side).upper()
            if symbol not in SYMBOLS or side not in ("LONG", "SHORT") or vqty <= 0:
                return
            logical.setdefault((symbol, side), []).append({
                "strategy": strategy, "qty": vqty, "target": target,
                "stop": stop, "recovery": recovery, "entry": virtual_entry,
            })

        for _state_key, rst in state_range.items():
            rst = rst or {}
            symbol = str(rst.get("symbol") or "").upper()
            strategy_id = str(rst.get("strategy") or f"RANGE:{symbol}")
            basket = rst.get("basket") or {}
            legs = basket.get("legs") or []
            grouped: Dict[str, Decimal] = {}
            weighted_entry: Dict[str, Decimal] = {}
            for leg in legs:
                side = str(leg.get("side", "")).upper()
                q = dec(leg.get("qty"))
                ep = dec(leg.get("entry_price"))
                if side in ("LONG", "SHORT") and q > 0:
                    grouped[side] = grouped.get(side, D(0)) + q
                    weighted_entry[side] = weighted_entry.get(side, D(0)) + q * ep
            for side, q in grouped.items():
                ventry = weighted_entry.get(side, D(0)) / q if q > 0 else D(0)
                add_logical(
                    symbol, side, strategy_id, q,
                    basket.get("recovery_tp_price") or basket.get("tp_price") or "-",
                    basket.get("hard_stop_price") or "-",
                    basket.get("alternations", 0),
                    ventry,
                )

        for key, mst in state_macd.items():
            mst = mst or {}
            pos = mst.get("position") or {}
            leg = pos.get("leg") or {}
            symbol = str(mst.get("symbol") or pos.get("symbol") or "").upper()
            side = str(pos.get("side") or leg.get("side") or "").upper()
            q = dec(leg.get("qty"))
            if q > 0:
                strategy = str(mst.get("strategy") or f"MACD:{key.replace(':', ':')}")
                add_logical(
                    symbol, side, strategy, q,
                    pos.get("trailing_stop") or "-",
                    pos.get("hard_stop_price") or "-",
                    pos.get("recovery_level", mst.get("recovery_level", mst.get("loss_streak", 0))),
                    leg.get("entry_price") or "-",
                )

        for p in (positions if isinstance(positions, list) else []):
            qty = abs(dec(p.get("positionAmt")))
            if qty <= 0:
                continue
            found += 1
            symbol = str(p.get("symbol", "")).upper()
            side = str(p.get("positionSide", "")).upper()
            candidates = logical.get((symbol, side), [])
            virtual_qty = sum((dec(x.get("qty")) for x in candidates), D(0))

            try:
                rule = self.rules.rules.get(symbol)
                step = dec(rule.step_size) if rule is not None else D(0)
            except Exception:
                step = D(0)
            tol = max(D("0.00000001"), step)
            residual = qty - virtual_qty

            ledger_owners = self.ledger.open_strategy_breakdown(symbol, side)
            ledger_qty = sum(ledger_owners.values(), D(0))

            if candidates:
                names = [str(x["strategy"]) for x in candidates]
                unique_names = list(dict.fromkeys(names))
                if len(unique_names) == 1:
                    owner = unique_names[0]
                else:
                    owner = "AGREGADA[" + ",".join(unique_names) + "]"
                if abs(residual) > tol:
                    owner += f"+RESIDUO_EXTERNO({dstr(residual, 8)})"
            else:
                legacy = legacy_owners.get(symbol) if not ALLOW_MULTI_STRATEGY_SAME_SYMBOL else None
                if ledger_owners:
                    ledger_names = list(ledger_owners.keys())
                    if len(ledger_names) == 1:
                        strategy_id = ledger_names[0]
                        if strategy_id.startswith("PYRAMID:"):
                            owner = strategy_id + "+LEGADO_FORA_DO_MOTOR_PRINCIPAL"
                        else:
                            owner = strategy_id + "+OWNER_LEDGER"
                    else:
                        owner = "AGREGADA_LEDGER[" + ",".join(ledger_names) + "]"
                    ledger_residual = qty - ledger_qty
                    if abs(ledger_residual) > tol:
                        owner += f"+RESIDUO_EXTERNO({dstr(ledger_residual, 8)})"
                else:
                    owner = legacy or "DESCONHECIDO/EXTERNO"

            entry = dec(p.get("entryPrice"))
            mark = dec(p.get("markPrice"))
            notional = abs(dec(p.get("notional") or qty * mark))
            unreal = dec(p.get("unRealizedProfit") or p.get("unrealizedProfit"))
            margin = dec(p.get("isolatedWallet") or p.get("isolatedMargin"))
            leverage = p.get("leverage") or "?"
            liq = p.get("liquidationPrice") or "?"
            move = pct_change(entry, mark) if entry > 0 and mark > 0 else D(0)
            favorable = move if side == "LONG" else -move
            target = stop = recovery_level = "-"

            unique_strategies = list(dict.fromkeys(str(x["strategy"]) for x in candidates))
            if len(unique_strategies) == 1 and candidates:
                target = candidates[0].get("target") or "-"
                stop = candidates[0].get("stop") or "-"
                recovery_level = candidates[0].get("recovery", "-")

            virtual_lot_parts = []
            for x in candidates:
                x_qty = dec(x.get("qty"))
                x_recovery_raw = x.get("recovery", 0)
                try:
                    x_recovery = max(0, int(x_recovery_raw))
                except Exception:
                    x_recovery = 0
                x_multiplier = RECOVERY_MULTIPLIER ** x_recovery
                x_base_notional = configured_initial_notional(symbol)
                x_notional = x_qty * mark if mark > 0 else D(0)
                x_mode = "NORMAL" if x_recovery == 0 else "RECOVERY"
                virtual_lot_parts.append(
                    f"{x['strategy']}:{side}"
                    f"|qty={dstr(x_qty, 8)}"
                    f"|entry={x.get('entry','-')}"
                    f"|notional_usd={dstr(x_notional, 8)}"
                    f"|mode={x_mode}"
                    f"|recovery_level={x_recovery}"
                    f"|multiplier={dstr(x_multiplier, 4)}x"
                    f"|base_notional_usd={dstr(x_base_notional, 8)}"
                    f"|tp={x.get('target','-')}"
                    f"|sl={x.get('stop','-')}"
                )
            virtual_lots = ";".join(virtual_lot_parts) or "-"

            if not candidates and ledger_owners:
                for ledger_strategy, ledger_strategy_qty in ledger_owners.items():
                    if str(ledger_strategy).startswith("PYRAMID:"):
                        logger.warning(
                            "LEGACY PYRAMID ATTRIBUTION | strategy=%s | symbol=%s side=%s "
                            "| qty=%s | status=OWNERSHIP_RECOGNIZED_NO_NEW_PYRAMID_ENTRIES",
                            ledger_strategy,
                            symbol,
                            side,
                            dstr(ledger_strategy_qty, 8),
                        )

            def remaining_pct(raw: Any) -> str:
                try:
                    level = dec(raw)
                    if level <= 0 or mark <= 0:
                        return "-"
                    return dstr(abs(level - mark) / mark * D(100), 6)
                except Exception:
                    return "-"

            tp_distance = remaining_pct(target)
            stop_distance = remaining_pct(stop)
            liq_distance = remaining_pct(liq)
            stop_liq_buffer = "-"
            try:
                stop_px, liq_px = dec(stop), dec(liq)
                if stop_px > 0 and liq_px > 0 and entry > 0:
                    stop_liq_buffer = dstr(abs(liq_px - stop_px) / entry * D(100), 6)
            except Exception:
                pass

            logger.warning(
                f"POSITION SNAPSHOT | strategy={owner} | symbol={symbol} side={side} qty={qty} virtual_qty={virtual_qty} residual={dstr(residual, 8)} "
                f"| ledger_qty={dstr(ledger_qty, 8)} ledger_owners={ledger_owners or '-'} | "
                f"entry={entry} mark={mark} move_favoravel={dstr(favorable * D(100), 6)}% | notional_usd={notional} margin_isolada={margin} leverage={leverage}x unreal_pnl={unreal} | "
                f"tp={target} distancia_tp={tp_distance}% | stop={stop} distancia_stop={stop_distance}% | "
                f"liq={liq} distancia_liq={liq_distance}% buffer_stop_liq={stop_liq_buffer}% | recovery_level={recovery_level} | virtual_lots={virtual_lots}"
            )

            for x in candidates:
                x_qty = dec(x.get("qty"))
                try:
                    x_recovery = max(0, int(x.get("recovery", 0)))
                except Exception:
                    x_recovery = 0
                x_multiplier = RECOVERY_MULTIPLIER ** x_recovery
                x_base_notional = configured_initial_notional(symbol)
                x_notional = x_qty * mark if mark > 0 else D(0)
                x_mode = "NORMAL" if x_recovery == 0 else "RECOVERY"
                logger.warning(
                    f"VIRTUAL STRATEGY | strategy={x.get('strategy')} | symbol={symbol} side={side} | qty={dstr(x_qty, 8)} | notional_usd={dstr(x_notional, 8)} | "
                    f"mode={x_mode} | recovery_level={x_recovery} | multiplier={dstr(x_multiplier, 4)}x | base_notional_usd={dstr(x_base_notional, 8)} | tp={x.get('target', '-')} | sl={x.get('stop', '-')}"
                )
        if found == 0:
            logger.info("POSITION SNAPSHOT | nenhuma posicao real aberta")

    def run(self) -> None:
        self.startup()
        if VALIDATE_API_ONLY:
            logger.info("VALIDATE_API_ONLY concluido; encerrando sem alterar configuracoes e sem enviar ordens")
            self.shutdown()
            return
        while not self.stop.is_set():
            try:
                if self.client.api_error_streak >= KILL_SWITCH_ON_API_ERRORS and self.store.killed() == "OFF":
                    self.store.kill("SOFT", f"API_ERROR_STREAK={self.client.api_error_streak}")
                if self.store.killed() == "HARD":
                    if self.hard_kill():
                        self.store.kill("SOFT", "HARD_KILL_CONFIRMED_ZERO_EXPOSURE; manual review required")
                    else:
                        logger.critical("HARD KILL permanece HARD | zero exposicao nao confirmado")
                prices = {s: self.md.get(s) for s in SYMBOLS}

                _now_reconcile = now_ms()
                if _now_reconcile - self._last_periodic_reconcile_ms >= int(RECONCILE_INTERVAL_SECONDS * 1000):
                    self._last_periodic_reconcile_ms = _now_reconcile
                    try:
                        self.reconciler.reconcile()
                    except Exception as _re:
                        reason = f"RECONCILE_UNAVAILABLE:{type(_re).__name__}:{_re}"
                        with self.store.lock:
                            self.store.state["trade_gate"] = {"open_allowed": False, "reason": reason, "at": now_iso()}
                        try:
                            self.store.save()
                        except Exception as _save_error:
                            logger.critical("RECONCILE FAIL-CLOSED | gate bloqueado em memoria; persistencia falhou | %s", _save_error)
                        logger.error("PERIODIC RECONCILE FAIL-CLOSED | novas entradas bloqueadas | %s", _re)

                self._refresh_range_grid_migrations()
                for e in self.range_engines:
                    p = prices.get(e.symbol)
                    if p and p > 0:
                        try: e.tick(p)
                        except Exception as ex: logger.exception(f"RANGE TICK FAIL | {e.symbol} | {ex}")
                for e in self.macd_engines:
                    p = prices.get(e.symbol)
                    if p and p > 0:
                        try: e.tick(p)
                        except Exception as ex: logger.exception(f"MACD TICK FAIL | {e.id} | {ex}")
                self.heartbeat()
            except KeyboardInterrupt:
                break
            except Exception as e:
                logger.exception(f"MAIN LOOP | {e}")
            self.stop.wait(MAIN_LOOP_SECONDS)
        self.shutdown()

    def shutdown(self) -> None:
        logger.info("SHUTDOWN | salvando estado")
        self.store.save()
        try:
            self.ledger.close()
        except Exception as exc:
            logger.warning("SHUTDOWN | falha ao fechar ledger SQLite | %s", exc)
        self.md.stop.set(); self.news.stop.set(); self.stop.set()


def main() -> None:
    bot = Bot()
    def _sig(signum, frame):
        logger.warning(f"SIGNAL {signum} recebido")
        bot.stop.set()
    signal.signal(signal.SIGINT, _sig)
    signal.signal(signal.SIGTERM, _sig)
    bot.run()


if __name__ == "__main__":
    main()
