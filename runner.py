#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Production entrypoint for Perpetual Principal.

Safety fixes layered over main.py without changing strategy parameters:
1) One narrowly-scoped, fail-closed cleanup for the already-proven stale
   RANGE:HYPEUSDT:G0 SHORT ledger owner. Historical rows are preserved.
2) RANGE reverse gate precheck: when a new recovery leg cannot legally be opened
   because the operational entry gate is blocked, do NOT cancel/recreate the
   native protection already covering the live basket.
3) Clear the persisted RANGE:HYPEUSDT:G0 protection block only when G0 is proven
   flat in state and ledger and owns no active native exchange order.
4) MACD STOP_MARKET installation is idempotent: an already-live exchange stop
   owned by the same MACD strategy, on the same side, quantity and requested
   trigger is reused instead of creating a duplicate. Exact duplicate stops are
   safely reduced to one only after a keeper is proven live. A one-shot startup
   cleanup applies the same rule to duplicates left by the prior watchdog bug.

No bankroll, trigger, TP, SL, MACD, leverage, position, BOT_DIR or Volume
parameter is changed by this wrapper.
"""

import signal
import main as bot

TARGET_SYMBOL = "HYPEUSDT"
TARGET_SIDE = "SHORT"
TARGET_OWNER = "RANGE:HYPEUSDT:G0"
TARGET_STATE_KEY = "HYPEUSDT:G0"


def _d(v):
    return bot.dec(v)


def _owner_open_qty(app, owner):
    with app.ledger.lock:
        rows = app.ledger.db.execute(
            "SELECT open_qty FROM lots WHERE strategy_id=? AND symbol=? AND position_side=? AND CAST(open_qty AS REAL)>0",
            (owner, TARGET_SYMBOL, TARGET_SIDE),
        ).fetchall()
    return sum((_d(r[0]) for r in rows), bot.D(0))


def _ledger_side_qty(app):
    return app.ledger.open_by_symbol_side().get((TARGET_SYMBOL, TARGET_SIDE), bot.D(0))


def _state_side_qty(app):
    return app.reconciler.expected_from_state_by_symbol_side().get((TARGET_SYMBOL, TARGET_SIDE), bot.D(0))


def _target_state_is_flat(app):
    st = (app.store.state.get("range_grids", {}) or {}).get(TARGET_STATE_KEY) or {}
    basket = st.get("basket") or {}
    qty = sum((max(bot.D(0), _d(x.get("qty"))) for x in (basket.get("legs") or [])), bot.D(0))
    return qty == 0


def _target_has_open_native_orders(app, snap):
    for order in snap.open_orders or []:
        if str(order.get("symbol", "")).upper() != TARGET_SYMBOL:
            continue
        if str(order.get("positionSide", "")).upper() != TARGET_SIDE:
            continue
        status = str(order.get("status", "")).upper()
        if status not in ("NEW", "PARTIALLY_FILLED"):
            continue
        cid = str(order.get("clientOrderId") or order.get("origClientOrderId") or "")
        owner = app.ledger.order_owner(cid) if cid else None
        if owner == TARGET_OWNER:
            return True
    return False


def repair_proven_stale_owner(app):
    if not _target_state_is_flat(app):
        bot.logger.info("STALE OWNER REPAIR | skip | target state still has live legs")
        return False

    snap1 = app.reconciler.snapshot()
    physical1 = snap1.positions.get((TARGET_SYMBOL, TARGET_SIDE), bot.D(0))
    state_qty = _state_side_qty(app)
    ledger_qty = _ledger_side_qty(app)
    ghost_qty = _owner_open_qty(app, TARGET_OWNER)

    if ghost_qty <= 0:
        bot.logger.info("STALE OWNER REPAIR | already clean | owner=%s", TARGET_OWNER)
        return False
    if physical1 != state_qty:
        bot.logger.error("STALE OWNER REPAIR ABORT | physical/state differ | physical=%s state=%s", physical1, state_qty)
        return False
    if ledger_qty - ghost_qty != physical1:
        bot.logger.error("STALE OWNER REPAIR ABORT | excess not isolated to target owner | ledger=%s ghost=%s physical=%s", ledger_qty, ghost_qty, physical1)
        return False
    if _target_has_open_native_orders(app, snap1):
        bot.logger.error("STALE OWNER REPAIR ABORT | target owner still has live native orders")
        return False

    snap2 = app.reconciler.snapshot()
    physical2 = snap2.positions.get((TARGET_SYMBOL, TARGET_SIDE), bot.D(0))
    if physical2 != physical1 or physical2 != _state_side_qty(app):
        bot.logger.error("STALE OWNER REPAIR ABORT | physical changed during verification | before=%s after=%s state=%s", physical1, physical2, _state_side_qty(app))
        return False
    if _target_has_open_native_orders(app, snap2):
        bot.logger.error("STALE OWNER REPAIR ABORT | target owner live order appeared during verification")
        return False

    closed_ms = bot.now_ms()
    with app.ledger.lock:
        app.ledger.db.execute("BEGIN IMMEDIATE")
        rows = app.ledger.db.execute(
            "SELECT leg_id, open_qty FROM lots WHERE strategy_id=? AND symbol=? AND position_side=? AND CAST(open_qty AS REAL)>0",
            (TARGET_OWNER, TARGET_SYMBOL, TARGET_SIDE),
        ).fetchall()
        current = sum((_d(r[1]) for r in rows), bot.D(0))
        if current != ghost_qty:
            app.ledger.db.rollback()
            raise RuntimeError(f"ghost quantity changed before commit: expected={ghost_qty} current={current}")
        app.ledger.db.execute(
            "UPDATE lots SET open_qty='0', closed_ms=COALESCE(closed_ms, ?) WHERE strategy_id=? AND symbol=? AND position_side=? AND CAST(open_qty AS REAL)>0",
            (closed_ms, TARGET_OWNER, TARGET_SYMBOL, TARGET_SIDE),
        )
        app.ledger.db.commit()

    bot.logger.warning("STALE OWNER REPAIR APPLIED | owner=%s | preserved_history_rows=%s | closed_open_qty=%s | physical=%s state=%s", TARGET_OWNER, len(rows), ghost_qty, physical2, state_qty)
    if not app.reconciler.reconcile():
        raise RuntimeError("post-repair reconcile did not converge")
    bot.logger.warning("STALE OWNER REPAIR VERIFIED | ledger=%s state=%s physical=%s | gate reopened if no other fault", app.ledger.open_by_symbol_side(), app.reconciler.expected_from_state_by_symbol_side(), app.reconciler.last_snapshot.positions if app.reconciler.last_snapshot else {})
    return True


def clear_proven_stale_flat_protection_block(app):
    if not _target_state_is_flat(app):
        bot.logger.info("STALE PROTECTION BLOCK | skip | target state has live legs")
        return False
    if _owner_open_qty(app, TARGET_OWNER) > 0:
        bot.logger.info("STALE PROTECTION BLOCK | skip | target ledger owner is not flat")
        return False

    snap1 = app.reconciler.snapshot()
    if _target_has_open_native_orders(app, snap1):
        bot.logger.info("STALE PROTECTION BLOCK | skip | target owns active native orders")
        return False
    if not _target_state_is_flat(app) or _owner_open_qty(app, TARGET_OWNER) > 0:
        bot.logger.warning("STALE PROTECTION BLOCK | abort | target changed during verification")
        return False
    snap2 = app.reconciler.snapshot()
    if _target_has_open_native_orders(app, snap2):
        bot.logger.warning("STALE PROTECTION BLOCK | abort | target order appeared during verification")
        return False

    app.store.set_protection_block(TARGET_OWNER, None)
    app.store.save()
    bot.logger.warning(
        "STALE PROTECTION BLOCK CLEARED | owner=%s | state_flat=True ledger_flat=True native_orders=False",
        TARGET_OWNER,
    )
    return True


# Preserve the original recovery algorithm, but never let it cancel a live
# bracket when the same operational gate would immediately reject _open().
_original_range_reverse = bot.RangeEngine._reverse


def _range_reverse_gate_safe(self, price):
    gate_ok, gate_reason = self.store.entry_allowed()
    if not gate_ok:
        st = self.st()
        basket = st.get("basket") or {}
        sig = str(gate_reason or "ENTRY_GATE_BLOCKED")
        if str(basket.get("last_reverse_gate_block") or "") != sig:
            basket["last_reverse_gate_block"] = sig
            st["last_update"] = bot.now_iso()
            self.store.save()
            bot.logger.warning(
                "RANGE REVERSE GATE-SAFE HOLD | %s grid=%s | gate=%s | existing_native_protection_preserved=True",
                self.symbol, self.grid_id, sig,
            )
        return
    st = self.st()
    basket = st.get("basket") or {}
    if basket.get("last_reverse_gate_block") is not None:
        basket["last_reverse_gate_block"] = None
        st["last_update"] = bot.now_iso()
        self.store.save()
    return _original_range_reverse(self, price)


bot.RangeEngine._reverse = _range_reverse_gate_safe


# -----------------------------------------------------------------------------
# MACD native stop idempotency / duplicate repair
# -----------------------------------------------------------------------------

_original_install_stop_only = bot.ExecutionEngine.install_stop_only


def _active_owner_stops(exe, strategy_id, symbol, position_side):
    rows = exe.client.open_orders(symbol)
    if not isinstance(rows, list):
        return []
    out = []
    for row in rows:
        if str(row.get("symbol") or symbol).upper() != symbol.upper():
            continue
        if str(row.get("positionSide") or "").upper() != position_side.upper():
            continue
        if str(row.get("type") or "").upper() != "STOP_MARKET":
            continue
        if str(row.get("status") or "NEW").upper() not in ("NEW", "PARTIALLY_FILLED"):
            continue
        cid = str(row.get("clientOrderId") or row.get("origClientOrderId") or "")
        if not cid or exe.ledger.order_owner(cid) != strategy_id:
            continue
        remaining = max(bot.D(0), bot.dec(row.get("origQty")) - bot.dec(row.get("executedQty")))
        item = dict(row)
        item["_cid"] = cid
        item["_remaining"] = remaining
        item["_stop"] = bot.dec(row.get("stopPrice"))
        out.append(item)
    return out


def _stop_meta_from_exchange(row, requested_qty, reason):
    return {
        "client_id": row["_cid"],
        "order_id": row.get("orderId"),
        "stop_price": str(row["_stop"]),
        "type": "STOP_MARKET",
        "status": str(row.get("status") or "NEW").upper(),
        "working_type": str(row.get("workingType") or bot.PROTECTIVE_WORKING_TYPE),
        "qty": str(requested_qty),
        "installed_at": bot.now_iso(),
        "reason": reason,
    }


def _cancel_exact_duplicate_stops(exe, strategy_id, symbol, side, keeper, duplicates):
    for row in duplicates:
        if row["_cid"] == keeper["_cid"]:
            continue
        try:
            exe.cancel_and_confirm_terminal(symbol, row["_cid"])
            bot.logger.warning(
                "MACD DUPLICATE STOP CANCELED | %s | %s %s | keep=%s canceled=%s stop=%s qty=%s",
                strategy_id, symbol, side, keeper["_cid"], row["_cid"], row["_stop"], row["_remaining"],
            )
        except Exception as exc:
            # Keeper was already proven live. Do not cancel it and do not alter exposure.
            bot.logger.error(
                "MACD DUPLICATE STOP CLEANUP FAIL | %s | keep=%s duplicate=%s | %s",
                strategy_id, keeper["_cid"], row["_cid"], exc,
            )


def _install_stop_only_idempotent(self, strategy_id, symbol, leg, stop_price, reason="STOP_LOSS"):
    if not bot.NATIVE_PROTECTIVE_ORDERS or not bot.LIVE_TRADING:
        return _original_install_stop_only(self, strategy_id, symbol, leg, stop_price, reason)

    side = str(leg["side"]).upper()
    qty = bot.dec(leg["qty"])
    if qty <= 0:
        return None
    direction = "DOWN" if side == "LONG" else "UP"
    requested_stop = self.rules.trigger_price(symbol, stop_price, direction)
    tick = self.rules.rules[symbol].tick_size

    try:
        candidates = _active_owner_stops(self, strategy_id, symbol, side)
    except Exception as exc:
        bot.logger.warning("MACD STOP IDEMPOTENCY LOOKUP UNKNOWN | %s | %s", strategy_id, exc)
        return _original_install_stop_only(self, strategy_id, symbol, leg, stop_price, reason)

    exact = [
        r for r in candidates
        if r["_remaining"] >= qty and abs(r["_stop"] - requested_stop) < tick
    ]
    if exact:
        # Prefer the oldest/smallest order id deterministically. All exact matches
        # have the same protection price and sufficient remaining quantity.
        exact.sort(key=lambda r: (str(r.get("time") or ""), str(r.get("orderId") or ""), r["_cid"]))
        keeper = exact[0]
        if len(exact) > 1:
            _cancel_exact_duplicate_stops(self, strategy_id, symbol, side, keeper, exact[1:])
        bot.logger.info(
            "MACD STOP IDEMPOTENT REUSE | %s | %s %s qty=%s stop=%s cid=%s duplicates=%s",
            strategy_id, symbol, side, qty, requested_stop, keeper["_cid"], max(0, len(exact) - 1),
        )
        return _stop_meta_from_exchange(keeper, qty, reason)

    return _original_install_stop_only(self, strategy_id, symbol, leg, stop_price, reason)


bot.ExecutionEngine.install_stop_only = _install_stop_only_idempotent


def cleanup_existing_macd_stop_duplicates(app):
    """One-shot startup cleanup for exact duplicate live MACD stops.

    Only orders whose durable ledger owner starts with MACD: are considered. For
    each owner/side/stop-price group, one live stop is kept and all others are
    canceled only after the keeper is observed in the same exchange snapshot.
    Different stop prices are left untouched because they may represent a valid
    in-flight trailing replacement.
    """
    snap = app.reconciler.snapshot()
    grouped = {}
    for row in snap.open_orders or []:
        if str(row.get("type") or "").upper() != "STOP_MARKET":
            continue
        if str(row.get("status") or "NEW").upper() not in ("NEW", "PARTIALLY_FILLED"):
            continue
        cid = str(row.get("clientOrderId") or row.get("origClientOrderId") or "")
        if not cid:
            continue
        owner = app.ledger.order_owner(cid)
        if not owner or not str(owner).startswith("MACD:"):
            continue
        symbol = str(row.get("symbol") or "").upper()
        side = str(row.get("positionSide") or "").upper()
        stop = bot.dec(row.get("stopPrice"))
        remaining = max(bot.D(0), bot.dec(row.get("origQty")) - bot.dec(row.get("executedQty")))
        if not symbol or side not in ("LONG", "SHORT") or stop <= 0 or remaining <= 0:
            continue
        key = (str(owner), symbol, side, str(stop))
        item = dict(row)
        item["_cid"] = cid
        item["_remaining"] = remaining
        item["_stop"] = stop
        grouped.setdefault(key, []).append(item)

    cleaned = 0
    for (owner, symbol, side, stop), rows in grouped.items():
        if len(rows) <= 1:
            continue
        rows.sort(key=lambda r: (str(r.get("time") or ""), str(r.get("orderId") or ""), r["_cid"]))
        keeper = rows[0]
        # Fail closed: prove the keeper still exists immediately before touching siblings.
        try:
            live = app.client.query_order(symbol, keeper["_cid"])
            if str(live.get("status") or "").upper() not in ("NEW", "PARTIALLY_FILLED"):
                bot.logger.error("MACD STARTUP DUPLICATE CLEANUP ABORT | %s | keeper not live=%s", owner, live)
                continue
        except Exception as exc:
            bot.logger.error("MACD STARTUP DUPLICATE CLEANUP ABORT | %s | keeper verify failed | %s", owner, exc)
            continue
        for dup in rows[1:]:
            try:
                app.exe.cancel_and_confirm_terminal(symbol, dup["_cid"])
                cleaned += 1
                bot.logger.warning(
                    "MACD STARTUP DUPLICATE STOP CANCELED | %s | %s %s | keep=%s canceled=%s stop=%s",
                    owner, symbol, side, keeper["_cid"], dup["_cid"], stop,
                )
            except Exception as exc:
                bot.logger.error(
                    "MACD STARTUP DUPLICATE STOP CLEANUP FAIL | %s | keep=%s duplicate=%s | %s",
                    owner, keeper["_cid"], dup["_cid"], exc,
                )

    if cleaned:
        verify = app.reconciler.snapshot()
        bot.logger.warning(
            "MACD STARTUP DUPLICATE STOP CLEANUP VERIFIED | canceled=%s | physical=%s",
            cleaned, verify.positions,
        )
    else:
        bot.logger.info("MACD STARTUP DUPLICATE STOP CLEANUP | no exact duplicates found")
    return cleaned


bot.VERSION = f"{bot.VERSION}-range-gate-safe-flat-block-clear-macd-stop-idempotent"


def main():
    app = bot.Bot()
    repair_proven_stale_owner(app)
    clear_proven_stale_flat_protection_block(app)
    cleanup_existing_macd_stop_duplicates(app)
    bot.logger.warning("RANGE GATE-SAFE PROTECTION HOLD ACTIVE | cancel/reinstall churn prevention enabled")
    bot.logger.warning("MACD STOP IDEMPOTENCY ACTIVE | duplicate STOP_MARKET prevention/cleanup enabled")

    def _sig(signum, frame):
        bot.logger.warning("SIGNAL %s recebido", signum)
        app.stop.set()

    signal.signal(signal.SIGINT, _sig)
    signal.signal(signal.SIGTERM, _sig)
    app.run()


if __name__ == "__main__":
    main()
