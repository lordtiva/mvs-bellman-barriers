"""Zero-dependency formal auditor for Article A CEGIS-PWL certificates (Cases 1-6)."""
from __future__ import annotations
import argparse, bisect, ctypes, json, lzma, math, os, time
from concurrent.futures import ProcessPoolExecutor
from decimal import Decimal, localcontext, ROUND_CEILING, ROUND_FLOOR

A0, A1, B0, B1, Q0, Q1, E0, E1 = 0.749, 0.751, 0.9699, 0.9701, 0.9199, 0.9201, 0.6999, 0.7001
AB0, AB1, BM, HM, PREC_P = 0.349, 0.351, 0.10, 0.28, 1.0 / 3.0
LN2_LO = Decimal("0.693147180559945309417232121458176568075500134360255254120680")
LN2_HI = Decimal("0.693147180559945309417232121458176568075500134360255254120681")
TWO32 = Decimal("2.8284271247461900976033774484193961571393437507538961463533595")
PREC, IPREC, _LNC, _LIB_C = 50, 66, {}, {}

def _d(x: Decimal, rnd) -> Decimal:
    with localcontext() as c: c.prec, c.rounding = PREC, rnd; return +x
def _op(fn, a: Decimal, b: Decimal, rnd) -> Decimal:
    with localcontext() as c: c.prec, c.rounding = PREC, rnd; return fn(a, b)
def _ln_dec(x: Decimal) -> tuple[Decimal, Decimal]:
    res = _LNC.get(x)
    if res is not None: return res
    if x <= 0: return Decimal("-1e999"), Decimal("-1e999")
    if x == 1: return Decimal(0), Decimal(0)
    with localcontext() as c:
        c.prec = IPREC; k, two, half, m = 0, Decimal(2), Decimal("0.5"), x
        while m >= two: m, k = m * half, k + 1
        while m < 1: m, k = m * two, k - 1
        mlo = mhi = m
        for _ in range(4): c.rounding = ROUND_FLOOR; mlo = mlo.sqrt(); c.rounding = ROUND_CEILING; mhi = mhi.sqrt()
        c.rounding = ROUND_FLOOR; vlo = (mlo - 1) / (mlo + 1); v2lo = vlo * vlo; slo = tlo = vlo
        c.rounding = ROUND_CEILING; vhi = (mhi - 1) / (mhi + 1); v2hi = vhi * vhi; shi = thi = vhi
        for j in range(1, 18):
            d = Decimal(2 * j + 1)
            c.rounding = ROUND_FLOOR; tlo = tlo * v2lo; slo = slo + tlo / d
            c.rounding = ROUND_CEILING; thi = thi * v2hi; shi = shi + thi / d
        c.rounding = ROUND_CEILING; rem = (two * thi * v2hi) / (Decimal(37) * (1 - v2hi)); kd, m32 = Decimal(k), Decimal(32)
        c.rounding = ROUND_FLOOR; lo = m32 * slo + (kd * LN2_LO if k >= 0 else kd * LN2_HI)
        c.rounding = ROUND_CEILING; hi = m32 * shi + Decimal(16) * rem + (kd * LN2_HI if k >= 0 else kd * LN2_LO)
    out = (_d(lo, ROUND_FLOOR), _d(hi, ROUND_CEILING))
    if len(_LNC) < 25000: _LNC[x] = out
    return out
class Iv:
    __slots__ = ("lo", "hi")
    def __init__(self, x):
        if isinstance(x, Iv): self.lo, self.hi = x.lo, x.hi; return
        d = Decimal.from_float(x) if isinstance(x, float) else (x if isinstance(x, Decimal) else Decimal(x))
        self.lo, self.hi = _d(d, ROUND_FLOOR), _d(d, ROUND_CEILING)
    @classmethod
    def raw(cls, lo: Decimal, hi: Decimal) -> "Iv":
        o = cls.__new__(cls); o.lo, o.hi = _d(lo, ROUND_FLOOR), _d(hi, ROUND_CEILING); return o
    def __add__(self, o): o = Iv(o); return Iv.raw(_op(Decimal.__add__, self.lo, o.lo, ROUND_FLOOR), _op(Decimal.__add__, self.hi, o.hi, ROUND_CEILING))
    def __sub__(self, o): o = Iv(o); return Iv.raw(_op(Decimal.__sub__, self.lo, o.hi, ROUND_FLOOR), _op(Decimal.__sub__, self.hi, o.lo, ROUND_CEILING))
    def __mul__(self, o):
        o = Iv(o); return Iv.raw(min(_op(Decimal.__mul__, a, b, ROUND_FLOOR) for a in (self.lo, self.hi) for b in (o.lo, o.hi)), max(_op(Decimal.__mul__, a, b, ROUND_CEILING) for a in (self.lo, self.hi) for b in (o.lo, o.hi)))
    def __truediv__(self, o):
        o = Iv(o); assert o.lo > 0 or o.hi < 0
        return Iv.raw(min(_op(Decimal.__truediv__, a, b, ROUND_FLOOR) for a in (self.lo, self.hi) for b in (o.lo, o.hi)), max(_op(Decimal.__truediv__, a, b, ROUND_CEILING) for a in (self.lo, self.hi) for b in (o.lo, o.hi)))
    def ln(self) -> "Iv": return Iv.raw(_ln_dec(self.lo)[0], _ln_dec(self.hi)[1])
    def sqrt(self) -> "Iv":
        with localcontext() as c: c.prec, c.rounding = PREC, ROUND_FLOOR; lo = Decimal(0) if self.lo <= 0 else self.lo.sqrt(); c.rounding = ROUND_CEILING; hi = Decimal(0) if self.hi <= 0 else self.hi.sqrt()
        return Iv.raw(lo, hi)
    def pow_int(self, n: int) -> "Iv":
        r, b, e = Iv(1), self, n
        while e > 0:
            if e & 1: r = r * b
            b, e = b * b, e >> 1
        return r
    def pow_half(self, num: int) -> "Iv":
        if num == 0: return Iv(1)
        pos = (self.sqrt() if num & 1 else Iv(1)) * (self.pow_int(abs(num) // 2) if abs(num) // 2 else Iv(1))
        return pos if num > 0 else Iv(1) / pos
TWO32_IV = Iv.raw(TWO32 - Decimal("1e-45"), TWO32 + Decimal("1e-45"))
iv_fa = lambda a, k, l: Iv(0) if l.hi <= 0 else a * ((Iv(2) * k * l) / (k + l)).pow_half(3)
def pwl_eval(pwl: dict, k: Iv) -> Iv:
    kd, ivv, lks = pwl["kd"], pwl["iv_v"], pwl["iv_lk"]; lo, hi = Decimal("1e99"), Decimal("-1e99")
    if k.lo <= kd[0]: v = ivv[0] + Iv(pwl["s_lo"]) * (Iv.raw(k.lo, min(k.hi, kd[0])) / Iv.raw(kd[0], kd[0])).ln(); lo, hi = min(lo, v.lo), max(hi, v.hi)
    if k.hi >= kd[-1]: v = ivv[-1] + Iv(pwl["s_hi"]) * (Iv.raw(max(k.lo, kd[-1]), k.hi) / Iv.raw(kd[-1], kd[-1])).ln(); lo, hi = min(lo, v.lo), max(hi, v.hi)
    i0, i1 = max(0, bisect.bisect_right(kd, k.lo) - 1), min(len(kd) - 2, bisect.bisect_left(kd, k.hi))
    for i in range(i0, i1 + 1):
        xL, xR = max(k.lo, kd[i]), min(k.hi, kd[i + 1])
        if xL <= xR:
            lk0, dv, den = lks[i], ivv[i + 1] - ivv[i], lks[i + 1] - lks[i]
            for xp in (xL, xR): v = ivv[i] + dv * ((Iv.raw(xp, xp).ln() - lk0) / den); lo, hi = min(lo, v.lo), max(hi, v.hi)
    return Iv.raw(lo, hi)
def pwl_deriv(pwl: dict, k: Iv) -> Iv:
    kd, ivv, lks = pwl["kd"], pwl["iv_v"], pwl["iv_lk"]; lo, hi = Decimal("1e99"), Decimal("-1e99")
    if k.lo < kd[0]: d = Iv(pwl["s_lo"]) / Iv.raw(k.lo, min(k.hi, kd[0])); lo, hi = min(lo, d.lo), max(hi, d.hi)
    if k.hi > kd[-1]: d = Iv(pwl["s_hi"]) / Iv.raw(max(k.lo, kd[-1]), k.hi); lo, hi = min(lo, d.lo), max(hi, d.hi)
    i0, i1 = max(0, bisect.bisect_right(kd, k.lo) - 1), min(len(kd) - 2, bisect.bisect_left(kd, k.hi))
    for i in range(i0, i1 + 1):
        xL, xR = max(k.lo, kd[i]), min(k.hi, kd[i + 1])
        if xL <= xR: d = ((ivv[i + 1] - ivv[i]) / (lks[i + 1] - lks[i])) / Iv.raw(xL, xR); lo, hi = min(lo, d.lo), max(hi, d.hi)
    return Iv.raw(lo, hi)
def check_deriv_below(ev: dict, kb: float, blo: float, alo: float, qlo: float, ax: float, l0: float, eL: float, eU: float):
    ivA, ivq, ivK, iva, ivl = Iv(str(alo)), Iv(str(qlo)), Iv(str(kb)), Iv(str(ax)), Iv(str(l0))
    t = Iv("1.5") * ivA * TWO32_IV * ivK.pow_half(5) * ivl.sqrt() / (ivK + ivl).pow_half(5); cs = ivq * ivK + iv_fa(ivA, ivK, ivl) + (Iv(1) - ivl) * t - iva
    clo = min((cs - t * Iv.raw(*([min(Decimal(1), ((Iv(1) - Iv(str(e))) * cs / t).hi)] * 2))).lo for e in (eL, eU))
    kd, ivv, lks, md = ev["kd"], ev["iv_v"], ev["iv_lk"], (Iv(ev["s_lo"]) / Iv.raw(ev["kd"][0], ev["kd"][0])).lo
    for i in range(len(kd) - 1):
        if ev["ks"][i] >= kb: break
        sl = (ivv[i + 1] - ivv[i]) / (lks[i + 1] - lks[i]); assert sl.lo > 0; md = min(md, (sl / Iv(min(ev["ks"][i + 1], kb))).lo)
    assert (Iv(str(blo)) * Iv.raw(md, md) - Iv(str(eU)) / Iv.raw(clo, clo)).lo > 0
def super_tail_max(vs: dict, ev: dict, av: float, qhi: float, bL: float, bR: float, eL: float, eU: float, ak: bool, p: float, vr: float, hs: float) -> float:
    ks_e, ixlo, ixc = ev["ks"], Iv.raw(vs["kd"][0], vs["kd"][0]), Iv.raw(vs["kd"][-1], vs["kd"][-1])
    ivA, ivq, ieL, ieU = Iv(str(av)), Iv(str(qhi)), Iv(str(eL)), Iv(str(eU))
    slo, Dhi, sloe, Dhie = Iv(vs["s_lo"]), Iv(vs["s_hi"]), Iv(ev["s_lo"]), Iv(ev["s_hi"])
    vs0, ve0, vse, vee = vs["iv_v"][0], ev["iv_v"][0], vs["iv_v"][-1], ev["iv_v"][-1]
    rt = ivq + iv_fa(ivA, ixlo, Iv(1)) / ixlo; assert rt.hi < 1; out = Decimal("-1e99")
    for bv in (bL, bR):
        ivb = Iv(str(bv)); be = ivb * (Iv(1) - Iv(str(p))) if (p > 0 and vs["ks"][0] <= hs) else ivb
        cslo, cdhi = ieL + be * sloe, ieU + ivb * Dhie; assert (cslo - slo).lo >= 0 and (cdhi - Dhi).hi <= 0
        sopt, shopt = (be * sloe) / cslo, (ivb * Dhie) / cdhi; sh = (ivb * Iv(str(p)) * Iv(str(vr))) if (p > 0 and vs["ks"][0] <= hs) else Iv(0)
        tlo = ieL * ((Iv(1) - sopt) * ixlo).ln() + be * sloe * sopt.ln() + cslo * rt.ln() + be * ve0 + sh - vs0
        if not ak:
            Finf = ivA * Iv(2).pow_half(3); Ye = ivq * ixc + Finf; assert Ye.hi < ixc.lo
            th1 = ieU * Ye.ln() + ivb * pwl_eval(ev, Iv(1)) - vse; i1 = max(0, sum(1 for k in ks_e if k < 1.0) - 1)
            slm = min((((ev["iv_v"][j + 1] - ev["iv_v"][j]) / (ev["iv_lk"][j + 1] - ev["iv_lk"][j])) / Iv.raw(ev["kd"][j + 1], ev["kd"][j + 1])).lo for j in range(i1, len(ks_e) - 1))
            assert slm > 0; ivsl = Iv.raw(slm, slm); cs = ieU / (ivb * ivsl); xc, xp = (ixc + cs - Finf) / ivq, (Dhi * (ixc - Finf)) / ((Dhi - ieU) * ivq)
            g1 = lambda x: ieU * cs.ln() + ivb * (vee + ivsl * (ivq * x + Finf - cs - ixc)) - (vse + Dhi * (x / ixc).ln())
            g2p = ieU * (ivq * xp + Finf - ixc).ln() + ivb * vee - (vse + Dhi * (xp / ixc).ln())
            thl = ieU * (Iv(1) - shopt).ln() + ivb * Dhie * shopt.ln() + cdhi * (Ye / ixc).ln() + ieU * ixc.ln() + ivb * vee - vse
            thi = max(th1.hi, g1(ixc).hi, g1(xc).hi, g2p.hi, thl.hi)
        else:
            ih, ak_hi, stk = Iv(str(HM)), Decimal("-1e99"), [(Decimal(0), Decimal(1) - Decimal("1e-12"), 0)]
            while stk:
                l0d, l1d, dp = stk.pop(); l_iv = Iv.raw(l0d, l1d); v_iv = cdhi * (ivq + iv_fa(ivA, ih, l_iv) / ih).ln() + (Iv(1) - ieU) * (Iv(1) - l_iv).ln()
                if v_iv.hi <= ak_hi: continue
                if dp >= 18: ak_hi = max(ak_hi, v_iv.hi)
                else: lm = (l0d + l1d) * Decimal("0.5"); stk.extend([(l0d, lm, dp + 1), (lm, l1d, dp + 1)])
            thl = ieU * (Iv(1) - shopt).ln() + ivb * Dhie * shopt.ln() + Iv.raw(ak_hi, ak_hi) + (ieU + ivb * Dhie - Dhi) * ixc.ln() + ivb * (vee - Dhie * ixc.ln()) - (vse - Dhi * ixc.ln())
            thi = max(thl.hi, (ieU * ((ivq + iv_fa(ivA, ih, Iv(1)) / ih) * ixc).ln() + ivb * Iv.raw(max(Decimal(0), vee.lo), max(Decimal(0), vee.hi)) - vse).hi)
        out = max(out, tlo.hi, thi)
    return math.nextafter(float(out), math.inf)
def _c_pwl(p: dict):
    n = len(p["ks"]); A, As = ctypes.c_double * n, ctypes.c_double * (n - 1)
    return A(*p["ks"]), A(*p["lks"]), A(*p["vals"]), As(*p["slopes"]), n, float(p["s_lo"]), float(p["s_hi"])
class BbOut(ctypes.Structure):
    _fields_ = [("certified", ctypes.c_int), ("iv_certified", ctypes.c_int), ("d_ub", ctypes.c_double), ("d_ub_iv", ctypes.c_double), ("d_lb", ctypes.c_double), ("leaf_count", ctypes.c_size_t), ("n_ce", ctypes.c_size_t)]
def load_dll(pure: bool = False):
    if pure: return None
    if 0 not in _LIB_C:
        lib = ctypes.CDLL(os.path.join(os.path.dirname(os.path.abspath(__file__)), "rust_verifier", "mvs_verifier.dll"))
        P, D, Z, I = ctypes.POINTER(ctypes.c_double), ctypes.c_double, ctypes.c_size_t, ctypes.c_int
        for fn, args in [("rs_verify_staying_barrier_bb_ext", [P, P, P, P, Z, D, D, P, P, P, P, Z, D, D, D, D, D, D, D, D, D, D, D, D, D, Z, P, Z]),
                         ("rs_verify_super_barrier_bb_ext", [P, P, P, P, Z, D, D, P, P, P, P, Z, D, D, D, D, D, D, D, D, D, D, D, D, D, I, Z, Z, P, Z]),
                         ("rs_verify_adverse_exit_bb", [P, P, P, P, Z, D, D, D, D, D, D, D, D, D, D, D, D, D, I, D, Z, I, P, Z])]:
            getattr(lib, fn).argtypes, getattr(lib, fn).restype = args, BbOut
        _LIB_C[0] = lib
    return _LIB_C[0]
def check_witness_1d(W: dict, EV: dict, kp: dict, L: dict, alo: float, qlo: float, bL: float, bR: float, eL: float, eU: float, ka: float, kb: float, ak: bool, p: float, vr: float, hs: float):
    ks = sorted({x for d in (W, kp, L) for x in d["ks"] if ka < x < kb} | {ka, kb})
    ivA, ivq, ibL, ibR, ieL, ieU = Iv(str(alo)), Iv(str(qlo)), Iv(str(bL)), Iv(str(bR)), Iv(str(eL)), Iv(str(eU))
    omp, pv, ih = Iv(1) - Iv(str(p)), Iv(str(p)) * Iv(str(vr)), Iv(str(hs))
    stk = [(Decimal.from_float(a), Decimal.from_float(b), 0) for a, b in zip(ks[:-1], ks[1:])]
    while stk:
        x0, x1, dp = stk.pop()
        if p > 0 and x0 < ih.lo < x1: xm = ih.lo; stk.extend([(x0, xm, dp + 1), (xm, x1, dp + 1)]); continue
        xk = Iv.raw(x0, x1); hr = p > 0 and x1 <= ih.lo; yk, lk = pwl_eval(kp, xk), pwl_eval(L, xk); assert 0 <= lk.lo and lk.hi < 1
        c = ivq * xk + ((iv_fa(ivA, ih, lk) * (xk / ih)) if (ak and x0 >= ih.lo) else iv_fa(ivA, xk, lk)) - yk
        if c.lo <= 0: assert dp < 12; xm = (x0 + x1) * Decimal("0.5"); stk.extend([(x0, xm, dp + 1), (xm, x1, dp + 1)]); continue
        def _ev(x_iv):
            yi, li = pwl_eval(kp, x_iv), pwl_eval(L, x_iv); ci = ivq * x_iv + ((iv_fa(ivA, ih, li) * (x_iv / ih)) if (ak and x_iv.lo >= ih.lo) else iv_fa(ivA, x_iv, li)) - yi
            lc, ll = ci.ln(), (Iv(1) - li).ln(); u0, u1 = ieL * lc + (Iv(1) - ieL) * ll, ieU * lc + (Iv(1) - ieU) * ll
            ew = pwl_eval(EV, yi); cb = (omp * ew + pv) if hr else ew
            bv = Iv.raw(min((ibL * cb).lo, (ibR * cb).lo), min((ibL * cb).hi, (ibR * cb).hi))
            return pwl_eval(W, x_iv) - (Iv.raw(min(u0.lo, u1.lo), min(u0.hi, u1.hi)) + bv), ew
        res, ew = _ev(xk)
        if res.hi <= 0: continue
        xm = (x0 + x1) * Decimal("0.5"); rm, _ = _ev(Iv.raw(xm, xm)); ak_h = ak and x0 >= ih.lo
        dW, dL, dkp, dEW = pwl_deriv(W, xk), pwl_deriv(L, xk), pwl_deriv(kp, xk), ((omp * pwl_deriv(EV, yk)) if hr else pwl_deriv(EV, yk))
        kbv = ih if ak_h else xk; den = kbv + lk; kp_f = (Iv(2) * kbv * lk) / den
        dYk = (iv_fa(ivA, ih, lk) / ih) if ak_h else (Iv("1.5") * ivA * kp_f.sqrt() * Iv(2) * (lk * lk) / (den * den))
        dYL = Iv("1.5") * ivA * kp_f.sqrt() * Iv(2) * (kbv * kbv) / (den * den) * ((xk / ih) if ak_h else Iv(1))
        dc = ivq + dYk + dYL * dL - dkp; ec = ieU if c.lo >= 1 else (ieL if c.hi < 1 else Iv.raw(ieL.lo, ieU.hi))
        df = dW - ((ec / c) * dc - ((Iv(1) - ec) / (Iv(1) - lk)) * dL) - (ibL if ew.lo >= 0 else (ibR if ew.hi < 0 else Iv.raw(ibL.lo, ibR.hi))) * dEW * dkp
        ma = max(abs(df.lo), abs(df.hi))
        if rm.hi + (Iv.raw(ma, ma) * Iv.raw((x1 - x0) * Decimal("0.5"), (x1 - x0) * Decimal("0.5"))).hi <= 0: continue
        assert dp < 24 and float(x1 - x0) > 1e-13, f"Witness 1D fail [{x0},{x1}]: {res.hi}"
        stk.extend([(x0, xm, dp + 1), (xm, x1, dp + 1)])
def verify_stay(lib, Bl, Be, bm, hm, Ahi, qhi, bL, bR, eL, eU, p=0.0, vr=0.0) -> float:
    if lib is not None:
        r = lib.rs_verify_staying_barrier_bb_ext(*_c_pwl(Bl), *_c_pwl(Be), bm, hm, Ahi, qhi, bL, bR, eL, eU, p, vr, 2e-4, 45, None, 0)
        assert r.iv_certified == 1 and r.d_ub_iv <= 0.0, f"Stay fail: {r.d_ub_iv}"; return r.d_ub_iv
    ivA, ivq, ibL, ibR, ieL, ieU = Iv(str(Ahi)), Iv(str(qhi)), Iv(str(bL)), Iv(str(bR)), Iv(str(eL)), Iv(str(eU))
    omp, pv = Iv(1) - Iv(str(p)), Iv(str(p)) * Iv(str(vr))
    stk, worst = [(Decimal.from_float(bm), Decimal.from_float(hm), Decimal.from_float(bm), Decimal.from_float(hm), Decimal(0), Decimal("0.9999"), 0)], Decimal("-1e99")
    while stk:
        x0, x1, y0, y1, l0, l1, dp = stk.pop(); xk, yk, lk = Iv.raw(x0, x1), Iv.raw(y0, y1), Iv.raw(l0, l1); c = ivq * xk + iv_fa(ivA, xk, lk) - yk
        if c.hi <= 0: continue
        ec = ieL if c.hi < 1 else (ieU if c.lo >= 1 else Iv.raw(ieL.lo, ieU.hi)); by = (omp * pwl_eval(Be, yk) + pv) if p > 0 else pwl_eval(Be, yk)
        ub = (ec * c.ln() + (Iv(1) - ieU) * (Iv(1) - lk).ln() + Iv.raw(min((ibL * by).lo, (ibR * by).lo), max((ibL * by).hi, (ibR * by).hi)) - pwl_eval(Bl, xk)).hi
        if ub <= 0: worst = max(worst, ub); continue
        assert dp < 18, f"Pure-Py stay fail: {ub}"; xm, ym, lm = (x0 + x1) * Decimal("0.5"), (y0 + y1) * Decimal("0.5"), (l0 + l1) * Decimal("0.5")
        sx, sy, sl = (x1 - x0) / x0, (y1 - y0) / y0, Decimal("0.25") * (l1 - l0) / max(Decimal("1e-3"), 1 - l1)
        if sx >= sy and sx >= sl: stk.extend([(x0, xm, y0, y1, l0, l1, dp + 1), (xm, x1, y0, y1, l0, l1, dp + 1)])
        elif sy >= sl: stk.extend([(x0, x1, y0, ym, l0, l1, dp + 1), (x0, x1, ym, y1, l0, l1, dp + 1)])
        else: stk.extend([(x0, x1, y0, y1, l0, lm, dp + 1), (x0, x1, y0, y1, lm, l1, dp + 1)])
    return float(worst)
def verify_super(lib, Vs, EV, Av, bL, bR, qhi, eL, eU, ak=False, p=0.0, vr=0.0, hs=HM, tol=2e-4):
    tmax = super_tail_max(Vs, EV, Av, qhi, bL, bR, eL, eU, ak, p, vr, hs); assert tmax <= 0.0
    if lib is not None:
        r = lib.rs_verify_super_barrier_bb_ext(*_c_pwl(Vs), *_c_pwl(EV), Av, qhi, bL, bR, eL, eU, p, vr, hs, tmax, tol, int(ak), 55, 350000, None, 0)
        assert r.iv_certified == 1 and r.d_ub_iv <= 0.0, f"Super fail: {r.d_ub_iv}"
def verify_exit(lib, W, evc, Ahi, qhi, bL, bR, eL, eU, ae, l0, ka, kb, ak=False):
    if lib is not None:
        r = lib.rs_verify_adverse_exit_bb(*_c_pwl(W), evc, Ahi, qhi, bL, bR, eL, eU, ae, l0, ka, kb, int(ak), 2e-4, 35, 1, None, 0)
        assert r.iv_certified == 1 and r.d_ub_iv > 0.0, f"Exit fail: {r.d_ub_iv}"; return
    ivA, ivq, iva, ivl, ieL, ieU = Iv(str(Ahi)), Iv(str(qhi)), Iv(str(ae)), Iv(str(l0)), Iv(str(eL)), Iv(str(eU))
    cont, stk = (Iv(str(bL)) if evc < 0 else Iv(str(bR))) * Iv(str(evc)), [(Decimal.from_float(ka), Decimal.from_float(kb), 0)]
    while stk:
        x0, x1, dp = stk.pop(); xk, ih = Iv.raw(x0, x1), Iv(str(HM))
        t = ((xk / ih) * (Iv("1.5") * ivA * TWO32_IV * ih.pow_half(5) * ivl.sqrt() / (ih + ivl).pow_half(5))) if (ak and float(x0) >= HM) else (Iv("1.5") * ivA * TWO32_IV * xk.pow_half(5) * ivl.sqrt() / (xk + ivl).pow_half(5))
        cs = (ivq * xk + (xk / ih) * iv_fa(ivA, ih, ivl) if (ak and float(x0) >= HM) else ivq * xk + iv_fa(ivA, xk, ivl)) + (Iv(1) - ivl) * t - iva
        e_hi = max((ev_i * (cs - t * Iv.raw(*([min(Decimal(1), ((Iv(1) - ev_i) * cs / t).lo)] * 2))).ln() + (Iv(1) - ev_i) * Iv.raw(*([min(Decimal(1), ((Iv(1) - ev_i) * cs / t).hi)] * 2)).ln()).hi for ev_i in (ieL, ieU))
        lb = pwl_eval(W, xk).lo - (Iv.raw(e_hi, e_hi) + cont).hi
        if lb > 0: continue
        assert dp < 18, f"Pure-Py exit fail: {lb}"; xm = (x0 + x1) * Decimal("0.5"); stk.extend([(x0, xm, dp + 1), (xm, x1, dp + 1)])
def _kgrid(pwls, bm: float, hm: float) -> list[Decimal]:
    return sorted({d for pwl in pwls for d in pwl["kd"] if bm < float(d) < hm} | {Decimal.from_float(bm * ((hm / bm) ** (j / 60.0))) for j in range(1, 60)} | {Decimal.from_float(bm), Decimal.from_float(hm)})
def check_deadline(B, Psi, W, b_max, bm, hm, p=0.0) -> int:
    ks = _kgrid((B, Psi, W), bm, hm); inf_w = min((pwl_eval(W, Iv.raw(a, b)) - pwl_eval(B, Iv.raw(a, b))).lo for a, b in zip(ks[:-1], ks[1:]))
    sup_p = max((pwl_eval(Psi, Iv.raw(a, b)) - pwl_eval(B, Iv.raw(a, b))).hi for a, b in zip(ks[:-1], ks[1:])); beff = Iv(str(b_max)) * (Iv(1) - Iv(str(p)))
    for T in range(1, 500):
        if (beff.pow_int(T) * Iv.raw(sup_p, sup_p)).hi < inf_w: return T
    raise AssertionError("Deadline > 500")
def check_doob_coupled(BG, BB, WG, WB, pG, pB, b_max, A_hi, q_hi, bm, hm) -> tuple[float, float]:
    ks = _kgrid((BG, BB, WG, WB, pG, pB), bm, hm)
    m_inf = min(min((pwl_eval(WG, Iv.raw(a, b)) - pwl_eval(BG, Iv.raw(a, b))).lo, (pwl_eval(WB, Iv.raw(a, b)) - pwl_eval(BB, Iv.raw(a, b))).lo) for a, b in zip(ks[:-1], ks[1:]))
    d_stay = max(max((pwl_eval(pG, Iv.raw(a, b)) - pwl_eval(BG, Iv.raw(a, b))).hi, (pwl_eval(pB, Iv.raw(a, b)) - pwl_eval(BB, Iv.raw(a, b))).hi) for a, b in zip(ks[:-1], ks[1:]))
    ih = Iv(str(hm)); ym = Iv(str(q_hi)) * ih + iv_fa(Iv(str(A_hi)), ih, Iv(1)); de = max((pwl_eval(pG, ym) - pwl_eval(BG, ih)).hi, (pwl_eval(pB, ym) - pwl_eval(BB, ih)).hi)
    ivm, ivds, ivex, ivb, best_e, best_eps = Iv.raw(m_inf, m_inf), Iv.raw(d_stay, d_stay), Iv(str(b_max)) * Iv.raw(de, de), Iv(str(b_max)), Decimal("1e30"), Decimal(0)
    for T in range(1, 401):
        tl, den = ivb.pow_int(T) * ivds, ivex - ivb.pow_int(T) * ivds
        if tl.hi < m_inf and den.lo > 0:
            eps = (ivm - tl) / den
            if eps.lo > 0 and (Iv(T) / eps).hi < best_e: best_e, best_eps = (Iv(T) / eps).hi, eps.lo
    assert best_eps > 0; return float(best_eps), float(best_e)
def bpwl(n: dict) -> dict:
    if n.get("type") == "log_relu":
        z0, z1 = float(_ln_dec(Decimal.from_float(n["k_lo"]))[0]), float(_ln_dec(Decimal.from_float(n["k_hi"]))[0]); zr = 0.5 * (z0 + z1)
        zk = sorted({z0, z1} | {zr - b / w for w, b in zip(n["W1"], n["b1"]) if abs(w) > 1e-15 and z0 < zr - b / w < z1}); ks = [math.exp(z) for z in zk]
        vals = [n["c0"] + n["alpha_lin"] * (z - zr) + sum(vi * max(0.0, wi * (z - zr) + bi) for wi, bi, vi in zip(n["W1"], n["b1"], n["v"])) for z in zk]
    else: ks, vals = [float(x) for x in n["ks"]], [float(x) for x in n["vals"]]
    kd = [Decimal.from_float(x) for x in ks]; lk_hl = [_ln_dec(d) for d in kd]; lks = [float(a) for a, _ in lk_hl]
    return {"type": "log_pwl", "ks": ks, "kd": kd, "lks": lks, "iv_lk": [Iv.raw(a, b) for a, b in lk_hl], "vals": vals, "iv_v": [Iv(v) for v in vals], "slopes": [(vals[i + 1] - vals[i]) / (lks[i + 1] - lks[i]) for i in range(len(vals) - 1)], "s_lo": float(n.get("s_lo") or 0.0), "s_hi": float(n.get("s_hi") or 0.0)}
def comb_pwl(p1: dict, c1: float, p2: dict, c2: float) -> dict:
    assert p1["ks"] == p2["ks"]; vals = [c1 * a + c2 * b for a, b in zip(p1["vals"], p2["vals"])]
    return {"type": "log_pwl", "ks": p1["ks"], "kd": p1["kd"], "lks": p1["lks"], "iv_lk": p1["iv_lk"], "vals": vals, "iv_v": [Iv(v) for v in vals], "slopes": [(vals[i + 1] - vals[i]) / (p1["lks"][i + 1] - p1["lks"][i]) for i in range(len(vals) - 1)], "s_lo": p1["s_lo"] if p1["s_lo"] == p2["s_lo"] else c1 * p1["s_lo"] + c2 * p2["s_lo"], "s_hi": p1["s_hi"] if p1["s_hi"] == p2["s_hi"] else c1 * p1["s_hi"] + c2 * p2["s_hi"]}
def _wk_c1b(arg):
    sb, bx, pure = arg; lib, Ps, Ws = load_dll(pure), bpwl(sb["Psi_net"]), bpwl(sb["W_net"])
    verify_super(lib, Ps, Ps, sb["aU"], sb["bL"], sb["bR"], Q1, E0, E1); check_witness_1d(Ws, Ws, bpwl(sb["kp_net"]), bpwl(sb["L_net"]), sb["aL"], Q0, sb["bL"], sb["bR"], E0, E1, bx, 5.5, False, 0.0, 0.0, HM)
    check_deriv_below(Ps, bx, sb["bL"], sb["aL"], Q0, bx, sb["l0_ext"], E0, E1); verify_exit(lib, Ws, float(pwl_eval(Ps, Iv(str(bx))).hi), sb["aU"], Q1, sb["bL"], sb["bR"], E0, E1, bx, sb["l0_ext"], bx, HM)
    assert sum(check_deadline(bpwl(st["B_net"]), Ps, Ws, sb["bR"], st["b_m"], st["h_m"]) for st in sb["stages"] if verify_stay(lib, bpwl(st["B_net"]), bpwl(st["B_net"]), st["b_m"], st["h_m"], sb["aU"], Q1, sb["bL"], sb["bR"], E0, E1) <= 0.0) <= sb["T_total"]
def _wk_c2(arg):
    b, pure = arg; lib, Psi, W, Bc = load_dll(pure), bpwl(b["Psi_net"]), bpwl(b["W_net"]), bpwl(b["B_cegis_net"])
    verify_super(lib, Psi, Psi, A1, b["b_min"], b["b_max"], Q1, E0, E1); verify_stay(lib, Bc, Bc, BM, HM, A1, Q1, b["b_min"], b["b_max"], E0, E1)
    check_deriv_below(Psi, BM, b["b_min"], A0, Q0, BM, 0.44, E0, E1); check_deriv_below(Psi, HM, b["b_min"], A0, Q0, HM, 0.57, E0, E1)
    verify_exit(lib, W, float(pwl_eval(Psi, Iv(str(BM))).hi), A1, Q1, b["b_min"], b["b_max"], E0, E1, BM, 0.44, BM, HM); verify_exit(lib, W, float(pwl_eval(Psi, Iv(str(HM))).hi), A1, Q1, b["b_min"], b["b_max"], E0, E1, HM, 0.57, HM, 0.80)
    assert check_deadline(Bc, Psi, W, b["b_max"], BM, HM) <= b["metrics"]["T_star_cegis"]
def _wk_c3_out(arg):
    p, b, pure = arg; lib = load_dll(pure); pG, pB, WG, WB, BG, BB = bpwl(b["PsiG_net"]), bpwl(b["PsiB_net"]), bpwl(b["WG_net"]), bpwl(b["WB_net"]), bpwl(b["BG_comp_net"]), bpwl(b["BB_comp_net"])
    verify_super(lib, pG, comb_pwl(pG, 1 - p, pB, p), A1, b["bL"], b["bR"], Q1, E0, E1); verify_super(lib, pB, comb_pwl(pG, PREC_P, pB, 1 - PREC_P), AB1, b["bL"], b["bR"], Q1, E0, E1)
    verify_stay(lib, BG, comb_pwl(BG, 1 - p, BB, p), BM, HM, A1, Q1, b["bL"], b["bR"], E0, E1); verify_stay(lib, BB, comb_pwl(BG, PREC_P, BB, 1 - PREC_P), BM, HM, AB1, Q1, b["bL"], b["bR"], E0, E1)
    eps, etau = check_doob_coupled(BG, BB, WG, WB, pG, pB, b["bR"], A1, Q1, BM, HM); assert eps > 0.0 and etau <= b["metrics"]["E_tau_comp"] + 0.05
def _wk_c3_sub(arg):
    lf, pure = arg; lib = load_dll(pure); pG, pB, WG, WB = bpwl(lf["PsiG_net"]), bpwl(lf["PsiB_net"]), bpwl(lf["WG_net"]), bpwl(lf["WB_net"]); evB = comb_pwl(pG, PREC_P, pB, 1 - PREC_P)
    verify_super(lib, pB, evB, lf["abU"], lf["bL"], lf["bR"], lf["qU"], lf["eL"], lf["eU"]); check_deriv_below(evB, HM, lf["bL"], lf["abL"], lf["qL"], HM, 0.603, lf["eL"], lf["eU"])
    check_witness_1d(WB, comb_pwl(WG, PREC_P, WB, 1 - PREC_P), bpwl(lf["kpB_net"]), bpwl(lf["LB_net"]), lf["abL"], lf["qL"], lf["bL"], lf["bR"], lf["eL"], lf["eU"], BM, 5.5, False, 0.0, 0.0, HM)
    verify_exit(lib, WB, float(pwl_eval(evB, Iv(str(HM))).hi), lf["abU"], lf["qU"], lf["bL"], lf["bR"], lf["eL"], lf["eU"], HM, 0.603, HM, 0.80)
def _wk_c6(arg):
    lf, pure = arg; lib = load_dll(pure); Psi, W, B = bpwl(lf["Psi_net"]), bpwl(lf["W_net"]), bpwl(lf["B_net"])
    verify_super(lib, Psi, Psi, lf["aU"], lf["bL"], lf["bU"], lf["qU"], lf["eL"], lf["eU"]); verify_stay(lib, B, B, BM, HM, lf["aU"], lf["qU"], lf["bL"], lf["bU"], lf["eL"], lf["eU"])
    check_witness_1d(W, W, bpwl(lf["kp_net"]), bpwl(lf["L_net"]), lf["aL"], lf["qL"], lf["bL"], lf["bU"], lf["eL"], lf["eU"], BM, 5.5, False, 0.0, 0.0, HM)
    check_deriv_below(Psi, BM, lf["bL"], lf["aL"], lf["qL"], BM, 0.44, lf["eL"], lf["eU"]); check_deriv_below(Psi, HM, lf["bL"], lf["aL"], lf["qL"], HM, 0.57, lf["eL"], lf["eU"])
    verify_exit(lib, W, float(pwl_eval(Psi, Iv(str(BM))).hi), lf["aU"], lf["qU"], lf["bL"], lf["bU"], lf["eL"], lf["eU"], BM, 0.44, BM, HM); verify_exit(lib, W, float(pwl_eval(Psi, Iv(str(HM))).hi), lf["aU"], lf["qU"], lf["bL"], lf["bU"], lf["eL"], lf["eU"], HM, 0.57, HM, 0.80)
    assert check_deadline(B, Psi, W, lf["bU"], BM, HM) <= lf["metrics"]["T_full"]
def _run_batch(pool, fn, items, serial: bool):
    if serial or len(items) <= 2: [fn(x) for x in items]
    else: list(pool.map(fn, items))
def audit_case(cid: int, data: dict, pure: bool, serial: bool, quick: bool, pool) -> str:
    lib = load_dll(pure)
    if cid == 1:
        c = data["case1_affine_gap"]; B, Psi, W = bpwl(c.get("B_pwl", c["B_net"])), bpwl(c["Psi_net"]), bpwl(c["W_net"])
        verify_stay(lib, B, B, BM, HM, A1, Q1, B0, B1, E0, E1); verify_super(lib, Psi, Psi, A1, B0, B1, Q1, E0, E1)
        check_witness_1d(W, W, bpwl(c["kp_net"]), bpwl(c["L_net"]), A0, Q0, B0, B1, E0, E1, BM, 5.5, False, 0.0, 0.0, HM)
        assert check_deadline(B, Psi, W, B1, BM, HM) == c["metrics"]["T_theta_full"]
        if not quick: _run_batch(pool, _wk_c1b, [(sb, c["near_skiba_cascade"]["b_ext"], pure) for sb in c["near_skiba_cascade"]["subbands"]], serial)
        for ch, Ahi, qhi, b_l, b_h, e_l, e_h, Pc, Wc in [(c["nonstationary_chain"]["box_P"], A1, Q1, B0, B1, E0, E1, Psi, W), (c["nonstationary_chain"]["center_theta0"], 0.75, 0.92, 0.97, 0.97, 0.70, 0.70, None, None)]:
            Js = [bpwl(j) for j in ch["J_nets"]]
            for k in range(1, len(Js)): verify_stay(lib, Js[k], Js[k - 1], BM, HM, Ahi, qhi, b_l, b_h, e_l, e_h)
            if Pc is not None: assert all(pwl_eval(Js[0], Iv(x)).lo >= pwl_eval(Pc, Iv(x)).lo for x in Js[0]["ks"]) and all(pwl_eval(Wc, Iv(x)).lo > pwl_eval(Js[-1], Iv(x)).hi for x in Wc["ks"] if BM <= x <= HM)
        return f"Case 1 OK (T_full={c['metrics']['T_theta_full']}, cascade={c['metrics']['cascade_T_total']}, nonstat={c['metrics']['T_nonstat_box']}/{c['metrics']['T_nonstat_center']})"
    elif cid == 2:
        bands = list(data["case2_ruin_hazard"].values()); _run_batch(pool, _wk_c2, [(b, pure) for b in bands], serial)
        return f"Case 2 OK ({len(bands)} beta bands, T_cegis={max(x['metrics']['T_star_cegis'] for x in bands)})"
    elif cid == 3:
        outs = [(r["p"], b, pure) for r in data["case3_markov_h1"].values() for b in r["beta_bands"]]; subs = [(lf, pure) for r in data["case3_markov_h1"].values() for lf in r["subbox_leaves"]]
        _run_batch(pool, _wk_c3_out, outs, serial); _run_batch(pool, _wk_c3_sub, subs, serial)
        return f"Case 3 OK ({len(outs)} outer bands + coupled Doob, {len(subs)} H1_B leaves)"
    elif cid == 4:
        c = data["case4_ak_regime"]; Psi, W, B = bpwl(c["Psi_net"]), bpwl(c["W_net"]), bpwl(c["B_net"])
        verify_super(lib, Psi, Psi, A1, B0, B1, Q1, E0, E1, ak=True, tol=1e-3); check_witness_1d(W, W, bpwl(c["kp_net"]), bpwl(c["L_net"]), A0, Q0, B0, B1, E0, E1, BM, 3.5, True, 0.0, 0.0, HM)
        verify_exit(lib, W, float(pwl_eval(Psi, Iv(str(HM))).hi), A1, Q1, B0, B1, E0, E1, HM, 0.57, HM, 3.5, ak=True); assert check_deadline(B, Psi, W, B1, BM, HM) == c["metrics"]["T_ak"]
        return f"Case 4 AK OK (T_ak={c['metrics']['T_ak']})"
    elif cid == 5:
        for r in data["case5_endogenous_ruin"].values():
            p, vr, hs = r["p"], r["v_ruin"], r["h_safe"]; Psi, WM, WH, B = bpwl(r["Psi_net"]), bpwl(r["W_M_net"]), bpwl(r["W_H_net"]), bpwl(r["B_net"])
            verify_super(lib, Psi, Psi, A1, B0, B1, Q1, E0, E1, False, p, vr, hs); check_witness_1d(WM, WM, bpwl(r["kp_M_net"]), bpwl(r["L_M_net"]), A0, Q0, B0, B1, E0, E1, BM, 5.5, False, p, vr, hs)
            check_witness_1d(WH, WH, bpwl(r["kp_H_net"]), bpwl(r["L_H_net"]), A0, Q0, B0, B1, E0, E1, HM, 5.5, False, 0.0, 0.0, hs); verify_stay(lib, B, B, BM, HM, A1, Q1, B0, B1, E0, E1, p, vr)
            check_deriv_below(Psi, BM, B0 * (1 - p), A0, Q0, BM, 0.44, E0, E1); check_deriv_below(Psi, HM, B0, A0, Q0, HM, 0.57, E0, E1)
            verify_exit(lib, WM, float(((Iv(1) - Iv(str(p))) * pwl_eval(Psi, Iv(str(BM))) + Iv(str(p)) * Iv(str(vr))).hi), A1, Q1, B0, B1, E0, E1, BM, 0.44, BM, HM)
            verify_exit(lib, WH, float(pwl_eval(Psi, Iv(str(HM))).hi), A1, Q1, B0, B1, E0, E1, HM, 0.57, HM, 0.80); assert check_deadline(B, Psi, WM, B1, BM, HM, p) == r["metrics"]["T_star"]
        return f"Case 5 OK ({len(data['case5_endogenous_ruin'])} regimes, T*=5)"
    elif cid == 6:
        parts = []
        for nm in ("mr_box_7_1", "macro_10x_box"):
            ts, sbs = time.time(), data["case6_wide_boxes"][nm]["subboxes"]; _run_batch(pool, _wk_c6, [(lf, pure) for lf in sbs], serial)
            parts.append(f"{nm}:{len(sbs)}bx/{time.time() - ts:.2f}s")
        return f"Case 6 OK ({', '.join(parts)})"
    raise ValueError(cid)
def main():
    ap = argparse.ArgumentParser(description="Zero-dependency formal auditor (Cases 1-6).")
    ap.add_argument("archive"); ap.add_argument("--pure-python", action="store_true"); ap.add_argument("--serial", action="store_true"); ap.add_argument("--quick", action="store_true"); ap.add_argument("--case", type=int, default=0); args = ap.parse_args()
    with (lzma.open(args.archive, "rt", encoding="utf-8") if args.archive.endswith(".xz") else open(args.archive, "r", encoding="utf-8")) as f: data = json.load(f)
    print(f"Standalone Auditor | mode={'PURE-PYTHON 50-digit Decimal' if args.pure_python else 'Rust mvs_verifier.dll + 50-digit Decimal'} | stdlib MR Lemma 11 ln()")
    t0_all, cases = time.time(), ([args.case] if args.case else [1, 2, 3, 4, 5, 6])
    with ProcessPoolExecutor(max_workers=1 if args.serial else min(12, os.cpu_count() or 4)) as pool:
        for cid in cases: t0 = time.time(); print(f"  [Case {cid}] {audit_case(cid, data, args.pure_python, args.serial, args.quick, pool)} | re-verify={time.time() - t0:.2f}s")
    print(f"ALL {len(cases)} CASE(S) PASSED IN {time.time() - t0_all:.2f}s.")
if __name__ == "__main__": main()
