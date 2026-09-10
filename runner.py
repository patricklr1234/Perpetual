#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Production entrypoint for Perpetual Principal.

Safety fixes layered over main.py without changing strategy parameters:
1) One narrowly-scoped, fail-closed cleanup for the already-proven stale
   RANGE:HYPEUSDT:G0 SHORT ledger owner. Historical rows are preserved.
2) RANGE reverse gate precheck: when a new recovery leg cannot legally be opened
   because the operational entry gate is blocked, do NOT cancel/recreate the
   native protection already covering the live basket. This eliminates exchange
   TP/SL order churn while preserving the physical position and its protection.
3) Clear the persisted RANGE:HYPEUSDT:G0 protection block only when G0 is proven
   flat in state and ledger and owns no active native exchange order. A flat
   strategy has no exposure requiring a protection block; leaving that stale
   marker set can incorrectly block unrelated strategies.

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
    """Clear only the target strategy's stale protection block when it is provably flat."""
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

    # Re-check immediately before mutation so the cleanup is fail-closed if
    # exposure/order state changes during verification.
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
bot.VERSION = f"{bot.VERSION}-range-gate-safe-flat-block-clear"


def main():
    app = bot.Bot()
    repair_proven_stale_owner(app)
    clear_proven_stale_flat_protection_block(app)
    bot.logger.warning("RANGE GATE-SAFE PROTECTION HOLD ACTIVE | cancel/reinstall churn prevention enabled")

    def _sig(signum, frame):
        bot.logger.warning("SIGNAL %s recebido", signum)
        app.stop.set()

    signal.signal(signal.SIGINT, _sig)
    signal.signal(signal.SIGTERM, _sig)
    app.run()


if __name__ == "__main__":
    main()
