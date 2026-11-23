"""
Two-Layer Outward-Rounded Interval Arithmetic & Audit Kernels:
  1. 50-digit Decimal `Interval` (ROUND_FLOOR / ROUND_CEILING + math.nextafter)
     for all analytical Section 3 proofs, 1D B&B audits, derivatives, and tails.
  2. Numba-compiled IEEE-754 outward-rounded interval arithmetic (`np.nextafter`)
     for rigorous 100% leaf-box auditing of 3D B&B partitions (Cases 1-4).
"""

from __future__ import annotations

from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
import math
from typing import Dict, Tuple
import numpy as np
from numba import njit


# ---------------------------------------------------------------------------
# Box (7.3) and Markov Benchmark Primitives
# ---------------------------------------------------------------------------
A_MIN, A_MAX = 0.749, 0.751
BETA_MIN, BETA_MAX = 0.9699, 0.9701
Q_MIN, Q_MAX = 0.9199, 0.9201
ETA_MIN, ETA_MAX = 0.6999, 0.7001
B_M, H_M = 0.10, 0.28
AB_MIN, AB_MAX = 0.349, 0.351
P_REC = 1.0 / 3.0


# ---------------------------------------------------------------------------
# Standard float64 Model Primitives (used only in float64 B&B pruning / VFI)
# ---------------------------------------------------------------------------
def F_A(A, K, L):
    return A * (2.0 * K * L / (K + L)) ** 1.5


def dF_dK(A, K, L):
    return 1.5 * A * (2.0 ** 1.5) * (K ** 0.5) * (L ** 2.5) * ((K + L) ** (-2.5))


def d2F_dK2(A, K, L):
    return 0.75 * A * (2.0 ** 1.5) * (L ** 2.5) * (L - 4.0 * K) * (K ** (-0.5)) * ((K + L) ** (-3.5))


def dF_dL(A, K, L):
    return 1.5 * A * (2.0 ** 1.5) * (K ** 2.5) * (L ** 0.5) * ((K + L) ** (-2.5))


def d2F_dKdL(A, K, L):
    return 2.25 * A * (2.0 ** 1.5) * (K ** 0.5) * (L ** 0.5) * ((K + L) ** (-3.5)) * (K + L / 3.0)


def exact_kappa(A_val, delta_val=0.08):
    coeffs = [-delta_val**2, -3 * delta_val**2, 8 * (A_val**2) - 3 * delta_val**2, -delta_val**2]
    roots = np.roots(coeffs)
    real_pos = sorted([float(np.real(rt)) for rt in roots if abs(np.imag(rt)) < 1e-12 and np.real(rt) > 0])
    return real_pos[0]


def box_worst_u(c, L):
    u1 = ETA_MIN * np.log(c) + (1.0 - ETA_MIN) * np.log(1.0 - L)
    u2 = ETA_MAX * np.log(c) + (1.0 - ETA_MAX) * np.log(1.0 - L)
    return np.minimum(u1, u2)


def E_plus_exact(A_hi, q_hi, K, a, l0, ak_mode: bool = False):
    """Exact tangent adverse-exit envelope max_{eta in box} E^+(K, a; l0)."""
    if not ak_mode:
        t = dF_dL(A_hi, K, l0)
        S = q_hi * K + F_A(A_hi, K, l0) + (1.0 - l0) * t
    else:
        if K <= H_M:
            t = dF_dL(A_hi, K, l0)
            S = q_hi * K + F_A(A_hi, K, l0) + (1.0 - l0) * t
        else:
            t = (K / H_M) * dF_dL(A_hi, H_M, l0)
            S = q_hi * K + (K / H_M) * F_A(A_hi, H_M, l0) + (1.0 - l0) * t
    c_sup = S - a
    vals = []
    for eta in (ETA_MIN, ETA_MAX):
        om_L = min(1.0, (1.0 - eta) * c_sup / t)
        c_opt = c_sup - t * om_L
        vals.append(eta * np.log(c_opt) + (1.0 - eta) * np.log(om_L))
    return max(vals)


# ---------------------------------------------------------------------------
# Layer 1: 50-digit Outward-Rounded Decimal Interval Arithmetic
# ---------------------------------------------------------------------------
class Interval:
    """Outward-rounded closed interval [lo, hi] using 50-digit Decimal arithmetic."""

    PREC = 50

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        self.lo = self._to_dec(lo, ROUND_FLOOR)
        self.hi = self._to_dec(hi, ROUND_CEILING)
        assert self.lo <= self.hi, f"Invalid interval [{self.lo}, {self.hi}]"

    @classmethod
    def _to_dec(cls, x, rounding):
        with localcontext() as ctx:
            ctx.prec = cls.PREC
            ctx.rounding = rounding
            if isinstance(x, Decimal):
                return +x
            if isinstance(x, int):
                return Decimal(x)
            if isinstance(x, str):
                return +Decimal(x)
            return +Decimal.from_float(float(x))

    @classmethod
    def _raw(cls, lo, hi):
        obj = cls.__new__(cls)
        obj.lo = lo
        obj.hi = hi
        return obj

    def __add__(self, other):
        o = other if isinstance(other, Interval) else Interval(other)
        with localcontext() as ctx:
            ctx.prec = self.PREC
            ctx.rounding = ROUND_FLOOR
            lo = self.lo + o.lo
            ctx.rounding = ROUND_CEILING
            hi = self.hi + o.hi
        return Interval._raw(lo, hi)

    def __radd__(self, other):
        return self.__add__(other)

    def __neg__(self):
        return Interval._raw(-self.hi, -self.lo)

    def __sub__(self, other):
        o = other if isinstance(other, Interval) else Interval(other)
        with localcontext() as ctx:
            ctx.prec = self.PREC
            ctx.rounding = ROUND_FLOOR
            lo = self.lo - o.hi
            ctx.rounding = ROUND_CEILING
            hi = self.hi - o.lo
        return Interval._raw(lo, hi)

    def __rsub__(self, other):
        o = other if isinstance(other, Interval) else Interval(other)
        return o.__sub__(self)

    def __mul__(self, other):
        o = other if isinstance(other, Interval) else Interval(other)
        pairs = [(self.lo, o.lo), (self.lo, o.hi), (self.hi, o.lo), (self.hi, o.hi)]
        with localcontext() as ctx:
            ctx.prec = self.PREC
            ctx.rounding = ROUND_FLOOR
            lo = min(a * b for a, b in pairs)
            ctx.rounding = ROUND_CEILING
            hi = max(a * b for a, b in pairs)
        return Interval._raw(lo, hi)

    def __rmul__(self, other):
        return self.__mul__(other)

    def __truediv__(self, other):
        o = other if isinstance(other, Interval) else Interval(other)
        if o.lo <= 0 <= o.hi:
            raise ZeroDivisionError("Interval divisor spans zero")
        pairs = [(self.lo, o.lo), (self.lo, o.hi), (self.hi, o.lo), (self.hi, o.hi)]
        with localcontext() as ctx:
            ctx.prec = self.PREC
            ctx.rounding = ROUND_FLOOR
            lo = min(a / b for a, b in pairs)
            ctx.rounding = ROUND_CEILING
            hi = max(a / b for a, b in pairs)
        return Interval._raw(lo, hi)

    def __rtruediv__(self, other):
        o = other if isinstance(other, Interval) else Interval(other)
        return o.__truediv__(self)

    def sqrt(self):
        assert self.lo >= 0
        with localcontext() as ctx:
            ctx.prec = self.PREC
            ctx.rounding = ROUND_FLOOR
            lo = self.lo.sqrt()
            ctx.rounding = ROUND_CEILING
            hi = self.hi.sqrt()
        return Interval._raw(lo, hi)

    def ln(self):
        assert self.lo > 0
        lo = self._ln_pt(self.lo, is_hi=False)
        hi = self._ln_pt(self.hi, is_hi=True)
        return Interval._raw(lo, hi)

    @classmethod
    def _ln_lemma11_series(cls, m_lo: Decimal, m_hi: Decimal, n_terms: int = 55) -> Tuple[Decimal, Decimal]:
        """MR Lemma 11 (Eq. F.5) rational enclosure of log(m) for 1 <= m_lo <= m_hi <= 2."""
        with localcontext() as ctx:
            ctx.prec = cls.PREC + 12
            one = Decimal(1)
            two = Decimal(2)
            ctx.rounding = ROUND_FLOOR
            v_lo = (m_lo - one) / (m_lo + one)
            v2_lo = v_lo * v_lo
            term_lo = v_lo
            s_lo = v_lo
            for j in range(1, n_terms):
                term_lo = term_lo * v2_lo
                s_lo = s_lo + term_lo / Decimal(2 * j + 1)
            if v_lo >= Decimal(0):
                out_lo = two * s_lo
            else:
                ctx.rounding = ROUND_CEILING
                av_lo = -v_lo
                av2_lo = av_lo * av_lo
                av_tail = (av_lo ** (2 * n_terms + 1))
                ctx.rounding = ROUND_FLOOR
                den_lo = Decimal(2 * n_terms + 1) * (one - av2_lo)
                ctx.rounding = ROUND_CEILING
                rem_lo = (two * av_tail) / den_lo
                ctx.rounding = ROUND_FLOOR
                out_lo = two * s_lo - rem_lo

            ctx.rounding = ROUND_CEILING
            v_hi = (m_hi - one) / (m_hi + one)
            v2_hi = v_hi * v_hi
            term_hi = v_hi
            s_hi = v_hi
            for j in range(1, n_terms):
                term_hi = term_hi * v2_hi
                s_hi = s_hi + term_hi / Decimal(2 * j + 1)
            v_tail = term_hi * v2_hi
            ctx.rounding = ROUND_FLOOR
            one_m_v2 = one - v2_hi
            ctx.rounding = ROUND_CEILING
            rem = (two * v_tail) / (Decimal(2 * n_terms + 1) * one_m_v2)
            out_hi = two * s_hi + rem
        return out_lo, out_hi

    @classmethod
    def _get_ln2_bounds(cls) -> Tuple[Decimal, Decimal]:
        bounds = getattr(cls, "_LN2_BOUNDS", None)
        if bounds is None:
            bounds = cls._ln_lemma11_series(Decimal(2), Decimal(2), n_terms=60)
            cls._LN2_BOUNDS = bounds
        return bounds

    @classmethod
    def _ln_pt(cls, x: Decimal, is_hi: bool) -> Decimal:
        if x == Decimal(1):
            return Decimal(0)
        with localcontext() as ctx:
            ctx.prec = cls.PREC + 12
            two = Decimal(2)
            if x >= Decimal(1):
                k = max(0, int(x).bit_length() - 1)
                pow2 = two ** k
                ctx.rounding = ROUND_FLOOR
                m_lo = x / pow2
                ctx.rounding = ROUND_CEILING
                m_hi = x / pow2
                while m_lo >= two:
                    k += 1
                    pow2 *= two
                    ctx.rounding = ROUND_FLOOR
                    m_lo = x / pow2
                    ctx.rounding = ROUND_CEILING
                    m_hi = x / pow2
                while m_hi < Decimal(1):
                    k -= 1
                    pow2 //= two
                    ctx.rounding = ROUND_FLOOR
                    m_lo = x / pow2
                    ctx.rounding = ROUND_CEILING
                    m_hi = x / pow2
            else:
                ctx.rounding = ROUND_CEILING
                inv_x = Decimal(1) / x
                k = -int(inv_x).bit_length()
                pow2 = two ** (-k)
                ctx.rounding = ROUND_FLOOR
                m_lo = x * pow2
                ctx.rounding = ROUND_CEILING
                m_hi = x * pow2
                while m_hi < Decimal(1):
                    k -= 1
                    pow2 *= two
                    ctx.rounding = ROUND_FLOOR
                    m_lo = x * pow2
                    ctx.rounding = ROUND_CEILING
                    m_hi = x * pow2
                while m_lo >= two:
                    k += 1
                    pow2 //= two
                    ctx.rounding = ROUND_FLOOR
                    m_lo = x * pow2
                    ctx.rounding = ROUND_CEILING
                    m_hi = x * pow2

            ln_m_lo, ln_m_hi = cls._ln_lemma11_series(m_lo, m_hi, n_terms=55)
            ln2_lo, ln2_hi = cls._get_ln2_bounds()
            kd = Decimal(k)
            if is_hi:
                ctx.rounding = ROUND_CEILING
                k_term = kd * (ln2_hi if k >= 0 else ln2_lo)
                val = k_term + ln_m_hi
            else:
                ctx.rounding = ROUND_FLOOR
                k_term = kd * (ln2_lo if k >= 0 else ln2_hi)
                val = k_term + ln_m_lo
        with localcontext() as ctx:
            ctx.prec = cls.PREC
            ctx.rounding = ROUND_CEILING if is_hi else ROUND_FLOOR
            return +val

    def pow_int(self, n):
        assert isinstance(n, int) and n >= 0
        if n == 0:
            return Interval("1")
        if n == 1:
            return self
        if n % 2 == 0 and self.lo <= 0 <= self.hi:
            with localcontext() as ctx:
                ctx.prec = self.PREC
                ctx.rounding = ROUND_CEILING
                return Interval._raw(Decimal(0), max(abs(self.lo), abs(self.hi)) ** n)
        if n % 2 == 0 and self.hi < 0:
            with localcontext() as ctx:
                ctx.prec = self.PREC
                ctx.rounding = ROUND_FLOOR
                lo = self.hi ** n
                ctx.rounding = ROUND_CEILING
                hi = self.lo ** n
            return Interval._raw(lo, hi)
        with localcontext() as ctx:
            ctx.prec = self.PREC
            ctx.rounding = ROUND_FLOOR
            lo = self.lo ** n
            ctx.rounding = ROUND_CEILING
            hi = self.hi ** n
        return Interval._raw(min(lo, hi), max(lo, hi))

    def pow_half_int(self, num_halves):
        if num_halves == 0:
            return Interval("1")
        k = abs(num_halves)
        p = self.pow_int(k // 2) if k % 2 == 0 else self.pow_int(k).sqrt()
        return p if num_halves > 0 else Interval("1") / p

    def abs(self):
        if self.lo >= 0:
            return self
        if self.hi <= 0:
            return -self
        return Interval._raw(Decimal(0), max(-self.lo, self.hi))

    def max_abs(self):
        return max(abs(self.lo), abs(self.hi))

    def hull(self, other):
        o = other if isinstance(other, Interval) else Interval(other)
        return Interval._raw(min(self.lo, o.lo), max(self.hi, o.hi))

    def to_float_bounds(self):
        lo_f = float(self.lo)
        if Decimal.from_float(lo_f) > self.lo:
            lo_f = math.nextafter(lo_f, -math.inf)
        hi_f = float(self.hi)
        if Decimal.from_float(hi_f) < self.hi:
            hi_f = math.nextafter(hi_f, math.inf)
        return lo_f, hi_f


def iv_F_A(A: Interval, K: Interval, L: Interval) -> Interval:
    """Outward-rounded monotonic evaluation of CES F_A(K, L)."""
    if L.hi <= 0:
        return Interval("0")
    A_lo = Interval._raw(A.lo, A.lo)
    A_hi = Interval._raw(A.hi, A.hi)
    K_lo = Interval._raw(K.lo, K.lo)
    K_hi = Interval._raw(K.hi, K.hi)
    L_lo = Interval._raw(L.lo, L.lo)
    L_hi = Interval._raw(L.hi, L.hi)

    def _pt(ap, kp, lp):
        if lp.hi <= 0:
            return Interval("0")
        return ap * (Interval("2") * kp * lp / (kp + lp)).pow_half_int(3)

    return Interval._raw(_pt(A_lo, K_lo, L_lo).lo, _pt(A_hi, K_hi, L_hi).hi)


def iv_prod_Y(A_iv: Interval, K_iv: Interval, L_iv: Interval, ak_mode: bool = False) -> Interval:
    """Outward-rounded monotonic enclosure of Y(A, K, L) (CES or piecewise AK)."""
    if not ak_mode:
        return iv_F_A(A_iv, K_iv, L_iv)
    h_iv = Interval(str(H_M))
    A_lo = Interval._raw(A_iv.lo, A_iv.lo)
    A_hi = Interval._raw(A_iv.hi, A_iv.hi)
    K_lo = Interval._raw(K_iv.lo, K_iv.lo)
    K_hi = Interval._raw(K_iv.hi, K_iv.hi)
    L_lo = Interval._raw(L_iv.lo, L_iv.lo)
    L_hi = Interval._raw(L_iv.hi, L_iv.hi)

    def _pt(ap, kp, lp):
        if kp.hi <= h_iv.lo:
            return iv_F_A(ap, kp, lp)
        return (kp / h_iv) * iv_F_A(ap, h_iv, lp)

    return Interval._raw(_pt(A_lo, K_lo, L_lo).lo, _pt(A_hi, K_hi, L_hi).hi)


def iv_dF_dK(A_iv: Interval, K_iv: Interval, L_iv: Interval) -> Interval:
    """Outward-rounded enclosure of dF_A/dK on K_iv x L_iv (exact unimodality at K = L/4)."""
    two_3_2 = Interval("2").pow_half_int(3)
    c15 = Interval("1.5") * A_iv * two_3_2
    # Evaluate dF/dK at point K with interval L (monotone increasing in L)
    def _at_k(k_pt: Interval, l_pt: Interval) -> Interval:
        if l_pt.hi <= 0:
            return Interval("0")
        return c15 * k_pt.pow_half_int(1) * l_pt.pow_half_int(5) * (k_pt + l_pt).pow_half_int(-5)

    L_lo = Interval._raw(L_iv.lo, L_iv.lo)
    L_hi = Interval._raw(L_iv.hi, L_iv.hi)
    K_lo = Interval._raw(K_iv.lo, K_iv.lo)
    K_hi = Interval._raw(K_iv.hi, K_iv.hi)

    lo = min(_at_k(K_lo, L_lo).lo, _at_k(K_hi, L_lo).lo)
    hi = max(_at_k(K_lo, L_hi).hi, _at_k(K_hi, L_hi).hi)
    # Peak in K occurs at K = L / 4 (enclosed in 50-digit Interval arithmetic)
    kp_iv = L_hi / Interval("4")
    if kp_iv.hi >= K_iv.lo and kp_iv.lo <= K_iv.hi:
        kp_clipped = Interval._raw(max(kp_iv.lo, K_iv.lo), min(kp_iv.hi, K_iv.hi))
        hi = max(hi, _at_k(kp_clipped, L_hi).hi)
    return Interval._raw(lo, hi)


def iv_dF_dL(A_iv: Interval, K_iv: Interval, L_iv: Interval) -> Interval:
    """Outward-rounded enclosure of dF_A/dL on K_iv x L_iv (exact unimodality at L = K/4)."""
    two_3_2 = Interval("2").pow_half_int(3)
    c15 = Interval("1.5") * A_iv * two_3_2

    def _at_kl(k_pt: Interval, l_pt: Interval) -> Interval:
        if l_pt.hi <= 0:
            return Interval("0")
        return c15 * k_pt.pow_half_int(5) * l_pt.pow_half_int(1) * (k_pt + l_pt).pow_half_int(-5)

    L_lo = Interval._raw(L_iv.lo, L_iv.lo)
    L_hi = Interval._raw(L_iv.hi, L_iv.hi)
    K_lo = Interval._raw(K_iv.lo, K_iv.lo)
    K_hi = Interval._raw(K_iv.hi, K_iv.hi)

    lo = min(_at_kl(K_lo, L_lo).lo, _at_kl(K_lo, L_hi).lo)
    hi = max(_at_kl(K_hi, L_lo).hi, _at_kl(K_hi, L_hi).hi)
    lp_iv = K_hi / Interval("4")
    if lp_iv.hi >= L_iv.lo and lp_iv.lo <= L_iv.hi:
        lp_clipped = Interval._raw(max(lp_iv.lo, L_iv.lo), min(lp_iv.hi, L_iv.hi))
        hi = max(hi, _at_kl(K_hi, lp_clipped).hi)
    return Interval._raw(lo, hi)


def iv_d2F_dKdL(A_iv: Interval, K_iv: Interval, L_iv: Interval) -> Interval:
    """Outward-rounded enclosure of mixed partial d^2 F_A / (dK dL) >= 0."""
    two_3_2 = Interval("2").pow_half_int(3)
    c225 = Interval("2.25") * A_iv * two_3_2
    num = K_iv.pow_half_int(1) * L_iv.pow_half_int(1) * (K_iv + L_iv / Interval("3"))
    den = (K_iv + L_iv).pow_half_int(7)
    return c225 * num / den


def iv_prod_dY_dK(A_iv: Interval, K_iv: Interval, L_iv: Interval, ak_mode: bool = False) -> Interval:
    if not ak_mode:
        return iv_dF_dK(A_iv, K_iv, L_iv)
    h_iv = Interval(str(H_M))
    if K_iv.hi <= h_iv.lo:
        return iv_dF_dK(A_iv, K_iv, L_iv)
    ak_iv = iv_F_A(A_iv, h_iv, L_iv) / h_iv
    if K_iv.lo >= h_iv.hi:
        return ak_iv
    return iv_dF_dK(A_iv, K_iv, L_iv).hull(ak_iv)


def iv_prod_dY_dL(A_iv: Interval, K_iv: Interval, L_iv: Interval, ak_mode: bool = False) -> Interval:
    if not ak_mode:
        return iv_dF_dL(A_iv, K_iv, L_iv)
    h_iv = Interval(str(H_M))
    if K_iv.hi <= h_iv.lo:
        return iv_dF_dL(A_iv, K_iv, L_iv)
    ak_iv = (K_iv / h_iv) * iv_dF_dL(A_iv, h_iv, L_iv)
    if K_iv.lo >= h_iv.hi:
        return ak_iv
    return iv_dF_dL(A_iv, K_iv, L_iv).hull(ak_iv)


def iv_box_worst_u(c: Interval, L: Interval, eL: Interval = None, eU: Interval = None) -> Interval:
    e_lo = Interval(str(ETA_MIN)) if eL is None else eL
    e_hi = Interval(str(ETA_MAX)) if eU is None else eU
    one = Interval("1")
    lc = c.ln()
    ll = (one - L).ln()
    u1 = e_lo * lc + (one - e_lo) * ll
    u2 = e_hi * lc + (one - e_hi) * ll
    return Interval._raw(min(u1.lo, u2.lo), min(u1.hi, u2.hi))


def iv_E_plus_exact(
    A_hi: Interval,
    q_hi: Interval,
    K: Interval,
    a: Interval,
    l0: Interval,
    eL: Interval = None,
    eU: Interval = None,
    ak_mode: bool = False,
) -> Interval:
    """Outward-rounded tangent adverse-exit envelope max_{eta in [eL, eU]} E^+(K, a; l0)."""
    e_lo = Interval(str(ETA_MIN)) if eL is None else eL
    e_hi = Interval(str(ETA_MAX)) if eU is None else eU
    one = Interval("1")
    h_iv = Interval(str(H_M))
    if not ak_mode or K.hi <= h_iv.lo:
        two_3_2 = Interval("2").pow_half_int(3)
        t = Interval("1.5") * A_hi * two_3_2 * K.pow_half_int(5) * l0.pow_half_int(1) * (K + l0).pow_half_int(-5)
        S = q_hi * K + iv_F_A(A_hi, K, l0) + (one - l0) * t
    elif K.lo >= h_iv.hi:
        two_3_2 = Interval("2").pow_half_int(3)
        t_h = Interval("1.5") * A_hi * two_3_2 * h_iv.pow_half_int(5) * l0.pow_half_int(1) * (h_iv + l0).pow_half_int(-5)
        F_h = iv_F_A(A_hi, h_iv, l0)
        t = (K / h_iv) * t_h
        S = q_hi * K + (K / h_iv) * F_h + (one - l0) * t
    else:
        raise ValueError("K interval crosses H_M in AK mode")
    c_sup = S - a
    vals = []
    for eta in (e_lo, e_hi):
        om_raw = (one - eta) * c_sup / t
        om_L = Interval._raw(min(om_raw.lo, Decimal(1)), min(om_raw.hi, Decimal(1)))
        c_opt = c_sup - t * om_L
        vals.append(eta * c_opt.ln() + (one - eta) * om_L.ln())
    return Interval._raw(max(v.lo for v in vals), max(v.hi for v in vals))


def iv_dE_plus_dK(
    A_hi: Interval,
    q_hi: Interval,
    K: Interval,
    a: Interval,
    l0: Interval,
    eL: Interval = None,
    eU: Interval = None,
    ak_mode: bool = False,
) -> Interval:
    """
    Rigorous outward-rounded enclosure of dE^+/dK on K = [kL, kR].

    When interior leisure omega^* = (1 - eta)*(S(K) - a)/t(K) < 1 is certified
    for all eta in [eL, eU] across the interval K, uses the exact Proposition 1**
    identity:
      CES: dE^+/dK = S'(K)/(S(K)-a) - (1 - eta) * (5*l0) / (2*K*(K + l0))
      AK (K >= h): dE^+/dK = R_tan / (K*R_tan - a) - (1 - eta) / K
    Otherwise (boundary omega^* = 1 or mixed), computes the full general envelope
    including the negative -(eta / c_opt) * t'(K) * omega^* term.
    """
    e_lo = Interval(str(ETA_MIN)) if eL is None else eL
    e_hi = Interval(str(ETA_MAX)) if eU is None else eU
    one = Interval("1")
    h_iv = Interval(str(H_M))
    two_3_2 = Interval("2").pow_half_int(3)

    if not ak_mode or K.hi <= h_iv.lo:
        # Monotone bounds for t, S, t', S'
        t_lo = Interval("1.5") * A_hi * two_3_2 * K.lo * Interval._raw(K.lo, K.lo).pow_half_int(3) * l0.pow_half_int(1) * (Interval._raw(K.lo, K.lo) + l0).pow_half_int(-5)
        # Wait: t(K) is strictly increasing in K (since t'/t = 5 l0 / (2 K (K+l0)) > 0)
        K_lo = Interval._raw(K.lo, K.lo)
        K_hi = Interval._raw(K.hi, K.hi)
        t_at_lo = Interval("1.5") * A_hi * two_3_2 * K_lo.pow_half_int(5) * l0.pow_half_int(1) * (K_lo + l0).pow_half_int(-5)
        t_at_hi = Interval("1.5") * A_hi * two_3_2 * K_hi.pow_half_int(5) * l0.pow_half_int(1) * (K_hi + l0).pow_half_int(-5)
        t_iv = Interval._raw(t_at_lo.lo, t_at_hi.hi)

        S_at_lo = q_hi * K_lo + iv_F_A(A_hi, K_lo, l0) + (one - l0) * t_at_lo
        S_at_hi = q_hi * K_hi + iv_F_A(A_hi, K_hi, l0) + (one - l0) * t_at_hi
        c_sup_iv = Interval._raw((S_at_lo - a).lo, (S_at_hi - a).hi)

        # S'(K) = q_hi + dF_dK(K, l0) + (1 - l0) * d2F_dKdL(K, l0)
        # d2F_dKdL(K, l0) = (5/2) * t(K) * l0 / (K * (K + l0)) * ... wait:
        # t(K) = dF/dL, so t'(K) = d2F/(dK dL) = t(K) * 5 * l0 / (2 * K * (K + l0))!
        # Peak of t'(K) is at K = (3/4)*l0; peak of dF_dK(K, l0) is at K = l0/4.
        def _t_prime(k_pt: Interval) -> Interval:
            t_k = Interval("1.5") * A_hi * two_3_2 * k_pt.pow_half_int(5) * l0.pow_half_int(1) * (k_pt + l0).pow_half_int(-5)
            return t_k * (Interval("2.5") * l0) / (k_pt * (k_pt + l0))

        tp_lo = min(_t_prime(K_lo).lo, _t_prime(K_hi).lo)
        tp_hi = max(_t_prime(K_lo).hi, _t_prime(K_hi).hi)
        kp_tp = (Decimal("0.75") * l0.lo)
        if K.lo <= kp_tp <= K.hi:
            tp_hi = max(tp_hi, _t_prime(Interval._raw(kp_tp, kp_tp)).hi)
        tp_iv = Interval._raw(tp_lo, tp_hi)

        dFK_iv = iv_dF_dK(A_hi, K, l0)
        Sp_iv = q_hi + dFK_iv + (one - l0) * tp_iv

        # Check interior omega^* < 1 across whole interval for both eta in [e_lo, e_hi]
        om_max_iv = (one - e_lo) * c_sup_iv / t_iv
        if om_max_iv.hi < Decimal("1"):
            # Exact Prop 1** identity!
            t_log_d = (Interval("2.5") * l0) / (K * (K + l0))
            d_vals = []
            for eta_pt in (e_lo, e_hi):
                d_vals.append(Sp_iv / c_sup_iv - (one - eta_pt) * t_log_d)
            return d_vals[0].hull(d_vals[1])

        # General envelope (allows omega^* = 1 or mixed):
        # dE/dK = eta * (S'(K) - t'(K) * om) / c_opt, where c_opt = S - a - t*om
        d_vals = []
        for eta_pt in (e_lo, e_hi):
            om_raw = (one - eta_pt) * c_sup_iv / t_iv
            om_clamped = Interval._raw(min(max(om_raw.lo, Decimal(0)), Decimal(1)),
                                       min(max(om_raw.hi, Decimal(0)), Decimal(1)))
            c_opt = c_sup_iv - t_iv * om_clamped
            # Note: if c_sup <= t/(1-eta) we have interior c_opt = eta*(S-a)
            # Compute safe lower/upper on c_opt
            c_opt_direct = eta_pt * c_sup_iv
            c_opt_bnd = c_sup_iv - t_iv
            if om_raw.hi <= Decimal(1):
                c_opt_use = c_opt_direct
            elif om_raw.lo >= Decimal(1):
                c_opt_use = c_opt_bnd
            else:
                c_opt_use = c_opt_direct.hull(c_opt_bnd)
            d_vals.append(eta_pt * (Sp_iv - tp_iv * om_clamped) / c_opt_use)
        return d_vals[0].hull(d_vals[1])

    elif K.lo >= h_iv.hi:
        # AK mode for K >= H_M: Y = (K/h)*F(h, L), t = (K/h)*t_h, S = K * R_tan
        t_h = Interval("1.5") * A_hi * two_3_2 * h_iv.pow_half_int(5) * l0.pow_half_int(1) * (h_iv + l0).pow_half_int(-5)
        F_h = iv_F_A(A_hi, h_iv, l0)
        R_tan = q_hi + F_h / h_iv + (one - l0) * (t_h / h_iv)
        t_over_K = t_h / h_iv
        t_iv = K * t_over_K
        c_sup_iv = K * R_tan - a
        om_max_iv = (one - e_lo) * c_sup_iv / t_iv
        if om_max_iv.hi < Decimal("1"):
            d_vals = []
            for eta_pt in (e_lo, e_hi):
                d_vals.append(R_tan / c_sup_iv - (one - eta_pt) / K)
            return d_vals[0].hull(d_vals[1])
        d_vals = []
        for eta_pt in (e_lo, e_hi):
            om_raw = (one - eta_pt) * c_sup_iv / t_iv
            om_clamped = Interval._raw(min(max(om_raw.lo, Decimal(0)), Decimal(1)),
                                       min(max(om_raw.hi, Decimal(0)), Decimal(1)))
            c_opt = c_sup_iv - t_iv * om_clamped
            d_vals.append(eta_pt * (R_tan - t_over_K * om_clamped) / c_opt)
        return d_vals[0].hull(d_vals[1])
    else:
        raise ValueError("K interval crosses H_M in AK mode")


def _get_pwl_iv_cache(pwl: Dict[str, object]) -> Dict[str, object]:
    """Lazily cache 50-digit Decimal knot logs and exact segment slopes on the PWL dict."""
    cache = pwl.get("_iv_cache")
    if cache is not None:
        return cache
    ks_dec = [Decimal.from_float(float(x)) for x in pwl["ks"]]
    vals_iv = [Interval(float(v)) for v in pwl["vals"]]
    lks_iv = [Interval._raw(kd, kd).ln() for kd in ks_dec]
    slopes_iv = [
        (vals_iv[i + 1] - vals_iv[i]) / (lks_iv[i + 1] - lks_iv[i])
        for i in range(len(ks_dec) - 1)
    ]
    cache = {
        "ks_dec": ks_dec,
        "vals_iv": vals_iv,
        "lks_iv": lks_iv,
        "slopes_iv": slopes_iv,
        "s_lo_iv": Interval(float(pwl["s_lo"])),
        "s_hi_iv": Interval(float(pwl["s_hi"])),
    }
    pwl["_iv_cache"] = cache
    return cache


def iv_eval_logpwl(pwl: Dict[str, object], k_iv: Interval) -> Interval:
    """Outward-rounded 50-digit Interval enclosure of exact log-PWL on interval k_iv."""
    c = _get_pwl_iv_cache(pwl)
    ks_dec = c["ks_dec"]
    vals_iv = c["vals_iv"]
    lks_iv = c["lks_iv"]
    slopes_iv = c["slopes_iv"]
    s_lo_iv = c["s_lo_iv"]
    s_hi_iv = c["s_hi_iv"]

    def _eval_pt(k_val: Decimal) -> Interval:
        kv = Interval._raw(k_val, k_val)
        if k_val <= ks_dec[0]:
            return vals_iv[0] + s_lo_iv * (kv.ln() - lks_iv[0])
        if k_val >= ks_dec[-1]:
            return vals_iv[-1] + s_hi_iv * (kv.ln() - lks_iv[-1])
        lo_i, hi_i = 0, len(ks_dec) - 2
        idx = 0
        while lo_i <= hi_i:
            mid = (lo_i + hi_i) // 2
            if ks_dec[mid] <= k_val <= ks_dec[mid + 1]:
                idx = mid
                break
            elif k_val < ks_dec[mid]:
                hi_i = mid - 1
            else:
                lo_i = mid + 1
        else:
            idx = max(0, min(len(ks_dec) - 2, lo_i))
        return vals_iv[idx] + slopes_iv[idx] * (kv.ln() - lks_iv[idx])

    out = _eval_pt(k_iv.lo).hull(_eval_pt(k_iv.hi))
    for i, kd in enumerate(ks_dec):
        if k_iv.lo < kd < k_iv.hi:
            out = out.hull(vals_iv[i])
    return out


def iv_deriv_bounds_logpwl(pwl: Dict[str, object], k_iv: Interval) -> Interval:
    """Outward-rounded 50-digit Interval enclosure of dN/dK on k_iv."""
    c = _get_pwl_iv_cache(pwl)
    ks_dec = c["ks_dec"]
    slopes_iv = c["slopes_iv"]
    s_lo_iv = c["s_lo_iv"]
    s_hi_iv = c["s_hi_iv"]

    s_min_dec = None
    s_max_dec = None

    def _upd_iv(iv_s: Interval):
        nonlocal s_min_dec, s_max_dec
        if s_min_dec is None:
            s_min_dec, s_max_dec = iv_s.lo, iv_s.hi
        else:
            s_min_dec = min(s_min_dec, iv_s.lo)
            s_max_dec = max(s_max_dec, iv_s.hi)

    if k_iv.lo < ks_dec[0]:
        _upd_iv(s_lo_iv)
    for i, sl_iv in enumerate(slopes_iv):
        if k_iv.hi > ks_dec[i] and k_iv.lo < ks_dec[i + 1]:
            _upd_iv(sl_iv)
    if k_iv.hi > ks_dec[-1]:
        _upd_iv(s_hi_iv)
    if s_min_dec is None:
        if k_iv.lo <= ks_dec[0]:
            _upd_iv(s_lo_iv)
        if k_iv.hi >= ks_dec[-1]:
            _upd_iv(s_hi_iv)
        for i, sl_iv in enumerate(slopes_iv):
            if ks_dec[i] <= k_iv.lo <= ks_dec[i + 1]:
                _upd_iv(sl_iv)

    return Interval._raw(s_min_dec, s_max_dec) / k_iv


# ---------------------------------------------------------------------------
# Layer 2: Numba IEEE-754 Outward-Rounded Interval Kernels (3D Leaf Audits)
# ---------------------------------------------------------------------------
@njit(cache=True)
def _dn(x: float, n_ulp: int = 1) -> float:
    for _ in range(n_ulp):
        x = np.nextafter(x, -np.inf)
    return x


@njit(cache=True)
def _up(x: float, n_ulp: int = 1) -> float:
    for _ in range(n_ulp):
        x = np.nextafter(x, np.inf)
    return x


@njit(cache=True)
def ivf_add(a0: float, a1: float, b0: float, b1: float) -> Tuple[float, float]:
    return _dn(a0 + b0, 1), _up(a1 + b1, 1)


@njit(cache=True)
def ivf_sub(a0: float, a1: float, b0: float, b1: float) -> Tuple[float, float]:
    return _dn(a0 - b1, 1), _up(a1 - b0, 1)


@njit(cache=True)
def ivf_mul(a0: float, a1: float, b0: float, b1: float) -> Tuple[float, float]:
    p1 = a0 * b0
    p2 = a0 * b1
    p3 = a1 * b0
    p4 = a1 * b1
    lo = min(min(p1, p2), min(p3, p4))
    hi = max(max(p1, p2), max(p3, p4))
    return _dn(lo, 1), _up(hi, 1)


@njit(cache=True)
def ivf_div(a0: float, a1: float, b0: float, b1: float) -> Tuple[float, float]:
    p1 = a0 / b0
    p2 = a0 / b1
    p3 = a1 / b0
    p4 = a1 / b1
    lo = min(min(p1, p2), min(p3, p4))
    hi = max(max(p1, p2), max(p3, p4))
    return _dn(lo, 1), _up(hi, 1)


@njit(cache=True)
def ivf_sqrt(a0: float, a1: float) -> Tuple[float, float]:
    return _dn(math.sqrt(max(0.0, a0)), 2), _up(math.sqrt(max(0.0, a1)), 2)


@njit(cache=True)
def ivf_log(a0: float, a1: float) -> Tuple[float, float]:
    return _dn(math.log(a0), 4), _up(math.log(a1), 4)


@njit(cache=True)
def ivf_pow32(a0: float, a1: float) -> Tuple[float, float]:
    s0, s1 = ivf_sqrt(a0, a1)
    return ivf_mul(a0, a1, s0, s1)


@njit(cache=True)
def ivf_pow52(a0: float, a1: float) -> Tuple[float, float]:
    s0, s1 = ivf_sqrt(a0, a1)
    q0, q1 = ivf_mul(a0, a1, a0, a1)
    return ivf_mul(q0, q1, s0, s1)


@njit(cache=True)
def ivf_F_A_pt(A_v: float, K_v: float, L_v: float) -> Tuple[float, float]:
    if L_v <= 0.0:
        return 0.0, 0.0
    n0, n1 = ivf_mul(2.0 * K_v, 2.0 * K_v, L_v, L_v)
    d0, d1 = ivf_add(K_v, K_v, L_v, L_v)
    q0, q1 = ivf_div(n0, n1, d0, d1)
    p0, p1 = ivf_pow32(q0, q1)
    return ivf_mul(A_v, A_v, p0, p1)


@njit(cache=True)
def ivf_prod_Y_box(A_v: float, xL: float, xR: float, LL: float, LR: float, ak_mode: bool, H_v: float) -> Tuple[float, float]:
    if not ak_mode:
        lo, _ = ivf_F_A_pt(A_v, xL, LL)
        _, hi = ivf_F_A_pt(A_v, xR, LR)
        return lo, hi
    # Piecewise AK
    if xR <= H_v:
        lo, _ = ivf_F_A_pt(A_v, xL, LL)
        _, hi = ivf_F_A_pt(A_v, xR, LR)
        return lo, hi
    if xL >= H_v:
        fh0, _ = ivf_F_A_pt(A_v, H_v, LL)
        _, fh1 = ivf_F_A_pt(A_v, H_v, LR)
        r0, _ = ivf_div(xL, xL, H_v, H_v)
        _, r1 = ivf_div(xR, xR, H_v, H_v)
        lo, _ = ivf_mul(r0, r0, fh0, fh0)
        _, hi = ivf_mul(r1, r1, fh1, fh1)
        return lo, hi
    lo, _ = ivf_F_A_pt(A_v, xL, LL)
    _, fh1 = ivf_F_A_pt(A_v, H_v, LR)
    _, r1 = ivf_div(xR, xR, H_v, H_v)
    _, hi = ivf_mul(r1, r1, fh1, fh1)
    return lo, hi


@njit(cache=True)
def ivf_dF_dK_box(A_v: float, xL: float, xR: float, LL: float, LR: float) -> Tuple[float, float]:
    t0, t1 = ivf_sqrt(2.0, 2.0)
    t0, t1 = ivf_mul(2.0, 2.0, t0, t1)
    a0, a1 = ivf_mul(1.5, 1.5, A_v, A_v)
    c0, c1 = ivf_mul(a0, a1, t0, t1)

    def _pt(kv: float, lv: float) -> Tuple[float, float]:
        if lv <= 0.0:
            return 0.0, 0.0
        k0, k1 = ivf_sqrt(kv, kv)
        l0, l1 = ivf_pow52(lv, lv)
        num0, num1 = ivf_mul(c0, c1, k0, k1)
        num0, num1 = ivf_mul(num0, num1, l0, l1)
        s0, s1 = ivf_add(kv, kv, lv, lv)
        den0, den1 = ivf_pow52(s0, s1)
        return ivf_div(num0, num1, den0, den1)

    a0, _ = _pt(xL, LL)
    b0, _ = _pt(xR, LL)
    lo = min(a0, b0)
    _, a1 = _pt(xL, LR)
    _, b1 = _pt(xR, LR)
    hi = max(a1, b1)
    pk = 0.25 * LR
    if xL <= pk <= xR:
        _, p1 = _pt(pk, LR)
        hi = max(hi, p1)
    return lo, hi


@njit(cache=True)
def ivf_dF_dL_box(A_v: float, xL: float, xR: float, LL: float, LR: float) -> Tuple[float, float]:
    t0, t1 = ivf_sqrt(2.0, 2.0)
    t0, t1 = ivf_mul(2.0, 2.0, t0, t1)
    a0, a1 = ivf_mul(1.5, 1.5, A_v, A_v)
    c0, c1 = ivf_mul(a0, a1, t0, t1)

    def _pt(kv: float, lv: float) -> Tuple[float, float]:
        if lv <= 0.0:
            return 0.0, 0.0
        k0, k1 = ivf_pow52(kv, kv)
        l0, l1 = ivf_sqrt(lv, lv)
        num0, num1 = ivf_mul(c0, c1, k0, k1)
        num0, num1 = ivf_mul(num0, num1, l0, l1)
        s0, s1 = ivf_add(kv, kv, lv, lv)
        den0, den1 = ivf_pow52(s0, s1)
        return ivf_div(num0, num1, den0, den1)

    a0, _ = _pt(xL, LL)
    b0, _ = _pt(xL, LR)
    lo = min(a0, b0)
    _, a1 = _pt(xR, LL)
    _, b1 = _pt(xR, LR)
    hi = max(a1, b1)
    pl = 0.25 * xR
    if LL <= pl <= LR:
        _, p1 = _pt(xR, pl)
        hi = max(hi, p1)
    return lo, hi


@njit(cache=True)
def ivf_precompute_pwl(ks, vals):
    """Outward-rounded IEEE-754 knot logs and segment slopes from (ks, vals)."""
    nk = len(ks)
    ns = max(0, nk - 1)
    lks_lo = np.empty(nk, dtype=np.float64)
    lks_hi = np.empty(nk, dtype=np.float64)
    for i in range(nk):
        lks_lo[i], lks_hi[i] = ivf_log(ks[i], ks[i])
    slopes_lo = np.empty(ns, dtype=np.float64)
    slopes_hi = np.empty(ns, dtype=np.float64)
    for i in range(ns):
        dv0, dv1 = ivf_sub(vals[i + 1], vals[i + 1], vals[i], vals[i])
        dl0, dl1 = ivf_sub(lks_lo[i + 1], lks_hi[i + 1], lks_lo[i], lks_hi[i])
        slopes_lo[i], slopes_hi[i] = ivf_div(dv0, dv1, dl0, dl1)
    return lks_lo, lks_hi, slopes_lo, slopes_hi


@njit(cache=True)
def ivf_eval_logpwl_pt(ks, lks_lo, lks_hi, vals, slopes_lo, slopes_hi, s_lo: float, s_hi: float, kv: float) -> Tuple[float, float]:
    nk = len(ks)
    lk0, lk1 = ivf_log(kv, kv)
    if kv <= ks[0]:
        dl0, dl1 = ivf_sub(lk0, lk1, lks_lo[0], lks_hi[0])
        p0, p1 = ivf_mul(s_lo, s_lo, dl0, dl1)
        return ivf_add(vals[0], vals[0], p0, p1)
    if kv >= ks[nk - 1]:
        dl0, dl1 = ivf_sub(lk0, lk1, lks_lo[nk - 1], lks_hi[nk - 1])
        p0, p1 = ivf_mul(s_hi, s_hi, dl0, dl1)
        return ivf_add(vals[nk - 1], vals[nk - 1], p0, p1)
    # Binary search
    lo_i = 0
    hi_i = nk - 2
    idx = 0
    while lo_i <= hi_i:
        mid = (lo_i + hi_i) // 2
        if ks[mid] <= kv <= ks[mid + 1]:
            idx = mid
            break
        elif kv < ks[mid]:
            hi_i = mid - 1
        else:
            lo_i = mid + 1
    dl0, dl1 = ivf_sub(lk0, lk1, lks_lo[idx], lks_hi[idx])
    p0, p1 = ivf_mul(slopes_lo[idx], slopes_hi[idx], dl0, dl1)
    return ivf_add(vals[idx], vals[idx], p0, p1)


@njit(cache=True)
def ivf_range_logpwl(ks, lks_lo, lks_hi, vals, slopes_lo, slopes_hi, s_lo: float, s_hi: float, kL: float, kR: float) -> Tuple[float, float]:
    v0, v1 = ivf_eval_logpwl_pt(ks, lks_lo, lks_hi, vals, slopes_lo, slopes_hi, s_lo, s_hi, kL)
    w0, w1 = ivf_eval_logpwl_pt(ks, lks_lo, lks_hi, vals, slopes_lo, slopes_hi, s_lo, s_hi, kR)
    vmin = min(v0, w0)
    vmax = max(v1, w1)
    nk = len(ks)
    for i in range(nk):
        if kL < ks[i] < kR:
            if vals[i] < vmin:
                vmin = vals[i]
            if vals[i] > vmax:
                vmax = vals[i]
    return vmin, vmax


@njit(cache=True)
def ivf_deriv_bounds_logpwl(ks, slopes_lo, slopes_hi, s_lo: float, s_hi: float, kL: float, kR: float) -> Tuple[float, float]:
    smin = 1e300
    smax = -1e300
    if kL < ks[0]:
        smin = min(smin, s_lo)
        smax = max(smax, s_lo)
    ns = len(slopes_lo)
    for i in range(ns):
        if kR > ks[i] and kL < ks[i + 1]:
            smin = min(smin, slopes_lo[i])
            smax = max(smax, slopes_hi[i])
    if kR > ks[ns]:
        smin = min(smin, s_hi)
        smax = max(smax, s_hi)
    if smin > smax:
        # Degenerate point box on knot
        if kL <= ks[0]:
            smin = min(smin, s_lo); smax = max(smax, s_lo)
        if kR >= ks[ns]:
            smin = min(smin, s_hi); smax = max(smax, s_hi)
        for i in range(ns):
            if ks[i] <= kL <= ks[i + 1]:
                smin = min(smin, slopes_lo[i]); smax = max(smax, slopes_hi[i])
    return ivf_div(smin, smax, kL, kR)


@njit(cache=True)
def audit_staying_boxes_ivf(
    ks_l, lks_l, vals_l, slopes_l, s_lo_l: float, s_hi_l: float,
    ks_e, lks_e, vals_e, slopes_e, s_lo_e: float, s_hi_e: float,
    bxL, bxR, byL, byR, bLL, bLR,
    A_hi: float, q_hi: float, b_lo: float, b_hi: float, e_lo: float, e_hi: float,
    p_ruin: float = 0.0, v_ruin: float = 0.0,
) -> float:
    """100% outward-rounded IEEE-754 audit over all 3D leaf boxes for Staying Barrier."""
    lks_l_lo, lks_l_hi, slopes_l_lo, slopes_l_hi = ivf_precompute_pwl(ks_l, vals_l)
    lks_e_lo, lks_e_hi, slopes_e_lo, slopes_e_hi = ivf_precompute_pwl(ks_e, vals_e)
    omp0, omp1 = ivf_sub(1.0, 1.0, p_ruin, p_ruin)
    pv0, pv1 = ivf_mul(p_ruin, p_ruin, v_ruin, v_ruin)
    n = len(bxL)
    global_ub = -1e300
    for i in range(n):
        xL = bxL[i]; xR = bxR[i]
        yL = byL[i]; yR = byR[i]
        LL = bLL[i]; LR = bLR[i]
        Y0, Y1 = ivf_prod_Y_box(A_hi, xL, xR, LL, LR, False, 0.28)
        qx0, _ = ivf_mul(q_hi, q_hi, xL, xL)
        _, qx1 = ivf_mul(q_hi, q_hi, xR, xR)
        Ym0, _ = ivf_add(qx0, qx0, Y0, Y0)
        _, Ym1 = ivf_add(qx1, qx1, Y1, Y1)
        c0, c1 = ivf_sub(Ym0, Ym1, yL, yR)
        if c1 <= 0.0:
            continue

        # Monotone bound
        Bx0, _ = ivf_range_logpwl(ks_l, lks_l_lo, lks_l_hi, vals_l, slopes_l_lo, slopes_l_hi, s_lo_l, s_hi_l, xL, xR)
        By0, By1 = ivf_range_logpwl(ks_e, lks_e_lo, lks_e_hi, vals_e, slopes_e_lo, slopes_e_hi, s_lo_e, s_hi_e, yL, yR)
        if p_ruin > 0.0:
            t0, t1 = ivf_mul(omp0, omp1, By0, By1)
            By0, By1 = ivf_add(t0, t1, pv0, pv1)
        ba0 = b_lo if By0 < 0.0 else b_hi
        ba1 = b_lo if By1 < 0.0 else b_hi
        bBy1 = max(ivf_mul(ba0, ba0, By0, By0)[1], ivf_mul(ba1, ba1, By1, By1)[1])
        _, lc1 = ivf_log(c1, c1)
        ec_hi = e_lo if c1 < 1.0 else e_hi
        _, ulc1 = ivf_mul(ec_hi, ec_hi, lc1, lc1)
        omL0, omL1 = ivf_sub(1.0, 1.0, LL, LL)
        if omL1 <= 0.0:
            continue
        ome0, ome1 = ivf_sub(1.0, 1.0, e_hi, e_hi)
        _, lL1 = ivf_log(omL1, omL1)
        _, uom1 = ivf_mul(ome0, ome1, lL1, lL1)
        t1_0, t1_1 = ivf_add(ulc1, ulc1, uom1, uom1)
        t2_0, t2_1 = ivf_add(t1_1, t1_1, bBy1, bBy1)
        _, ub_mono = ivf_sub(t2_1, t2_1, Bx0, Bx0)
        box_ub = ub_mono

        # Centered-form bound if LR < 1 and c0 > 0
        if LR < 1.0 and c0 > 0.0:
            xm = 0.5 * (xL + xR)
            ym = 0.5 * (yL + yR)
            Lm = 0.5 * (LL + LR)
            _, hx = ivf_sub(xR, xR, xm, xm)
            _, hx2 = ivf_sub(xm, xm, xL, xL)
            hx = max(hx, hx2)
            _, hy = ivf_sub(yR, yR, ym, ym)
            _, hy2 = ivf_sub(ym, ym, yL, yL)
            hy = max(hy, hy2)
            _, hL = ivf_sub(LR, LR, Lm, Lm)
            _, hL2 = ivf_sub(Lm, Lm, LL, LL)
            hL = max(hL, hL2)

            Ymid0, Ymid1 = ivf_prod_Y_box(A_hi, xm, xm, Lm, Lm, False, 0.28)
            qxm0, qxm1 = ivf_mul(q_hi, q_hi, xm, xm)
            Ym_m0, Ym_m1 = ivf_add(qxm0, qxm1, Ymid0, Ymid1)
            cm0, cm1 = ivf_sub(Ym_m0, Ym_m1, ym, ym)
            if cm0 > 0.0:
                lcm0, lcm1 = ivf_log(cm0, cm1)
                omLm0, omLm1 = ivf_sub(1.0, 1.0, Lm, Lm)
                lLm0, lLm1 = ivf_log(omLm0, omLm1)
                Bxm0, Bxm1 = ivf_eval_logpwl_pt(ks_l, lks_l_lo, lks_l_hi, vals_l, slopes_l_lo, slopes_l_hi, s_lo_l, s_hi_l, xm)
                Bym0, Bym1 = ivf_eval_logpwl_pt(ks_e, lks_e_lo, lks_e_hi, vals_e, slopes_e_lo, slopes_e_hi, s_lo_e, s_hi_e, ym)
                if p_ruin > 0.0:
                    tm0, tm1 = ivf_mul(omp0, omp1, Bym0, Bym1)
                    Bym0, Bym1 = ivf_add(tm0, tm1, pv0, pv1)
                ome0, ome1 = ivf_sub(1.0, 1.0, e_hi, e_hi)
                _, uLm1 = ivf_mul(ome0, ome1, lLm0, lLm1)
                bm0 = b_lo if Bym1 < 0.0 else (b_hi if Bym0 >= 0.0 else b_lo)
                bm1 = b_lo if Bym1 < 0.0 else b_hi
                _, bBym1 = ivf_mul(bm0, bm1, Bym0, Bym1)

                Yx0, Yx1 = ivf_dF_dK_box(A_hi, xL, xR, LL, LR)
                Yx0, Yx1 = ivf_add(q_hi, q_hi, Yx0, Yx1)
                YL0, YL1 = ivf_dF_dL_box(A_hi, xL, xR, LL, LR)
                dBx0, dBx1 = ivf_deriv_bounds_logpwl(ks_l, slopes_l_lo, slopes_l_hi, s_lo_l, s_hi_l, xL, xR)
                dBy0, dBy1 = ivf_deriv_bounds_logpwl(ks_e, slopes_e_lo, slopes_e_hi, s_lo_e, s_hi_e, yL, yR)
                if p_ruin > 0.0:
                    dBy0, dBy1 = ivf_mul(omp0, omp1, dBy0, dBy1)
                bef0 = b_lo if By1 < 0.0 else (b_hi if By0 >= 0.0 else b_lo)
                bef1 = b_lo if By1 < 0.0 else b_hi
                bdBy0, bdBy1 = ivf_mul(bef0, bef1, dBy0, dBy1)

                invc0, invc1 = ivf_div(1.0, 1.0, c0, c1)
                omLR0, omLR1 = ivf_sub(1.0, 1.0, LR, LR)
                omLL0, omLL1 = ivf_sub(1.0, 1.0, LL, LL)
                inv_1mL_0 = ivf_div(ome0, ome1, omLL0, omLL1)[0]
                inv_1mL_1 = ivf_div(ome0, ome1, omLR0, omLR1)[1]

                cross_c1 = (c0 < 1.0) and (c1 >= 1.0)
                best_cent = -1e300
                for pass_idx in range(2):
                    if pass_idx == 0 and not (c0 < 1.0):
                        continue
                    if pass_idx == 1 and not (c1 >= 1.0):
                        continue
                    ec = e_lo if pass_idx == 0 else e_hi
                    ec0 = e_lo if cross_c1 else ec
                    ec1 = e_hi if cross_c1 else ec

                    _, ucm1 = ivf_mul(ec, ec, lcm0, lcm1)
                    hm1 = ivf_add(ucm1, ucm1, uLm1, uLm1)[1]
                    hm1 = ivf_add(hm1, hm1, bBym1, bBym1)[1]
                    hm1 = ivf_sub(hm1, hm1, Bxm0, Bxm0)[1]

                    eic0, eic1 = ivf_mul(ec0, ec1, invc0, invc1)
                    tYx0, tYx1 = ivf_mul(eic0, eic1, Yx0, Yx1)
                    dx0, dx1 = ivf_sub(tYx0, tYx1, dBx0, dBx1)
                    dy0, dy1 = ivf_sub(bdBy0, bdBy1, eic0, eic1)
                    tYL0, tYL1 = ivf_mul(eic0, eic1, YL0, YL1)
                    dL0, dL1 = ivf_sub(tYL0, tYL1, inv_1mL_0, inv_1mL_1)

                    sx = ivf_mul(max(abs(dx0), abs(dx1)), max(abs(dx0), abs(dx1)), hx, hx)[1]
                    sL = ivf_mul(max(abs(dL0), abs(dL1)), max(abs(dL0), abs(dL1)), hL, hL)[1]
                    sy = ivf_mul(max(abs(dy0), abs(dy1)), max(abs(dy0), abs(dy1)), hy, hy)[1]
                    ub_ec = ivf_add(hm1, hm1, sx, sx)[1]
                    ub_ec = ivf_add(ub_ec, ub_ec, sy, sy)[1]
                    ub_ec = ivf_add(ub_ec, ub_ec, sL, sL)[1]
                    if ub_ec > best_cent:
                        best_cent = ub_ec
                if best_cent < box_ub:
                    box_ub = best_cent

        if math.isnan(box_ub):
            return 1e300
        if box_ub > global_ub:
            global_ub = box_ub
    return global_ub


@njit(cache=True)
def audit_super_boxes_ivf(
    ks_s, lks_s, vals_s, slopes_s, s_lo_s: float, s_hi_s: float,
    ks_e, lks_e, vals_e, slopes_e, s_lo_e: float, s_hi_e: float,
    bxL, bxR, bLL, bLR, bsL, bsR,
    Av: float, q_hi: float, bL: float, bR: float, eL: float, eU: float,
    ak_mode: bool, H_v: float,
    p_ruin: float = 0.0, v_ruin: float = 0.0, h_safe: float = 0.28,
) -> float:
    """100% outward-rounded IEEE-754 audit over all 3D leaf boxes for Super-Barrier."""
    lks_s_lo, lks_s_hi, slopes_s_lo, slopes_s_hi = ivf_precompute_pwl(ks_s, vals_s)
    lks_e_lo, lks_e_hi, slopes_e_lo, slopes_e_hi = ivf_precompute_pwl(ks_e, vals_e)
    omp0, omp1 = ivf_sub(1.0, 1.0, p_ruin, p_ruin)
    pv0, pv1 = ivf_mul(p_ruin, p_ruin, v_ruin, v_ruin)
    n = len(bxL)
    global_ub = -1e300
    for i in range(n):
        xL = bxL[i]; xR = bxR[i]
        LL = bLL[i]; LR = bLR[i]
        sL = bsL[i]; sR = bsR[i]
        if sL >= 1.0 or sR <= 0.0 or LL >= 1.0:
            continue
        has_ruin = (p_ruin > 0.0) and (xR <= h_safe)

        Y0, Y1 = ivf_prod_Y_box(Av, xL, xR, LL, LR, ak_mode, H_v)
        qx0, _ = ivf_mul(q_hi, q_hi, xL, xL)
        _, qx1 = ivf_mul(q_hi, q_hi, xR, xR)
        Y0 = ivf_add(qx0, qx0, Y0, Y0)[0]
        Y1 = ivf_add(qx1, qx1, Y1, Y1)[1]

        om_sL0, om_sL1 = ivf_sub(1.0, 1.0, sL, sL)
        om_sR0, om_sR1 = ivf_sub(1.0, 1.0, sR, sR)
        c_max = ivf_mul(om_sL0, om_sL1, Y1, Y1)[1]
        c_min = ivf_mul(om_sR0, om_sR1, Y0, Y0)[0]
        if c_max <= 0.0:
            continue

        Vs0, _ = ivf_range_logpwl(ks_s, lks_s_lo, lks_s_hi, vals_s, slopes_s_lo, slopes_s_hi, s_lo_s, s_hi_s, xL, xR)
        y1 = ivf_mul(sR, sR, Y1, Y1)[1]
        if y1 <= 0.0:
            continue
        if sL > 0.0:
            y0 = ivf_mul(sL, sL, Y0, Y0)[0]
        else:
            y0 = 0.0
        ev0 = 0.0; ev1 = 0.0
        if y0 > 0.0:
            ev0, ev1 = ivf_range_logpwl(ks_e, lks_e_lo, lks_e_hi, vals_e, slopes_e_lo, slopes_e_hi, s_lo_e, s_hi_e, y0, y1)
            if has_ruin:
                t0, t1 = ivf_mul(omp0, omp1, ev0, ev1)
                ev0, ev1 = ivf_add(t0, t1, pv0, pv1)
            ba0 = bL if ev0 < 0.0 else bR
            ba1 = bL if ev1 < 0.0 else bR
            b_ev1 = max(ivf_mul(ba0, ba0, ev0, ev0)[1], ivf_mul(ba1, ba1, ev1, ev1)[1])
        else:
            _, ev1 = ivf_eval_logpwl_pt(ks_e, lks_e_lo, lks_e_hi, vals_e, slopes_e_lo, slopes_e_hi, s_lo_e, s_hi_e, y1)
            if has_ruin:
                t0, t1 = ivf_mul(omp0, omp1, ev1, ev1)
                ev0_r, ev1_r = ivf_add(t0, t1, pv0, pv1)
                b_ev1 = ivf_mul(bL if ev1_r < 0.0 else bR, bL if ev1_r < 0.0 else bR, ev0_r, ev1_r)[1]
            else:
                b_ev1 = ivf_mul(bL if ev1 < 0.0 else bR, bL if ev1 < 0.0 else bR, ev1, ev1)[1]

        ec_hi = eL if c_max < 1.0 else eU
        _, lc1 = ivf_log(c_max, c_max)
        _, ulc1 = ivf_mul(ec_hi, ec_hi, lc1, lc1)
        omLL = ivf_sub(1.0, 1.0, LL, LL)[1]
        omeU0, omeU1 = ivf_sub(1.0, 1.0, eU, eU)
        _, lL1 = ivf_log(omLL, omLL)
        _, uom1 = ivf_mul(omeU0, omeU1, lL1, lL1)
        t1 = ivf_add(ulc1, ulc1, uom1, uom1)[1]
        t2 = ivf_add(t1, t1, b_ev1, b_ev1)[1]
        ub_mono = ivf_sub(t2, t2, Vs0, Vs0)[1]
        box_ub = ub_mono

        ruin_ok = (p_ruin == 0.0) or (xR <= h_safe) or (xL >= h_safe)
        can_cent = ruin_ok and (LR < 1.0) and (sL > 0.0) and (y0 > 0.0) and (sR < 1.0) and (c_min > 1e-30) and ((not ak_mode) or (xR <= H_v) or (xL >= H_v))
        if can_cent:
            xm = 0.5 * (xL + xR)
            Lm = 0.5 * (LL + LR)
            sm = 0.5 * (sL + sR)
            hx = max(ivf_sub(xR, xR, xm, xm)[1], ivf_sub(xm, xm, xL, xL)[1])
            hL = max(ivf_sub(LR, LR, Lm, Lm)[1], ivf_sub(Lm, Lm, LL, LL)[1])
            hs = max(ivf_sub(sR, sR, sm, sm)[1], ivf_sub(sm, sm, sL, sL)[1])

            Ym0, Ym1 = ivf_prod_Y_box(Av, xm, xm, Lm, Lm, ak_mode, H_v)
            qxm0, qxm1 = ivf_mul(q_hi, q_hi, xm, xm)
            Ym0, Ym1 = ivf_add(qxm0, qxm1, Ym0, Ym1)
            om_sm0, om_sm1 = ivf_sub(1.0, 1.0, sm, sm)
            cm0, cm1 = ivf_mul(om_sm0, om_sm1, Ym0, Ym1)
            ym0, ym1 = ivf_mul(sm, sm, Ym0, Ym1)
            if cm0 > 0.0 and ym0 > 0.0:
                lcm0, lcm1 = ivf_log(cm0, cm1)
                omLm0, omLm1 = ivf_sub(1.0, 1.0, Lm, Lm)
                lLm0, lLm1 = ivf_log(omLm0, omLm1)
                omeU0, omeU1 = ivf_sub(1.0, 1.0, eU, eU)
                _, uLm1 = ivf_mul(omeU0, omeU1, lLm0, lLm1)
                evm0, evm1 = ivf_range_logpwl(ks_e, lks_e_lo, lks_e_hi, vals_e, slopes_e_lo, slopes_e_hi, s_lo_e, s_hi_e, ym0, ym1)
                if has_ruin:
                    tm0, tm1 = ivf_mul(omp0, omp1, evm0, evm1)
                    evm0, evm1 = ivf_add(tm0, tm1, pv0, pv1)
                Vsm0, Vsm1 = ivf_eval_logpwl_pt(ks_s, lks_s_lo, lks_s_hi, vals_s, slopes_s_lo, slopes_s_hi, s_lo_s, s_hi_s, xm)
                bm0 = bL if evm1 < 0.0 else (bR if evm0 >= 0.0 else bL)
                bm1 = bL if evm1 < 0.0 else bR
                _, bevm1 = ivf_mul(bm0, bm1, evm0, evm1)

                if not ak_mode or xR <= H_v:
                    Yx0, Yx1 = ivf_dF_dK_box(Av, xL, xR, LL, LR)
                    YL0, YL1 = ivf_dF_dL_box(Av, xL, xR, LL, LR)
                else:
                    Fh0, _ = ivf_F_A_pt(Av, H_v, LL)
                    _, Fh1 = ivf_F_A_pt(Av, H_v, LR)
                    Yx0, Yx1 = ivf_div(Fh0, Fh1, H_v, H_v)
                    dFh0, dFh1 = ivf_dF_dL_box(Av, H_v, H_v, LL, LR)
                    rx0, rx1 = ivf_div(xL, xR, H_v, H_v)
                    YL0, YL1 = ivf_mul(rx0, rx1, dFh0, dFh1)
                Yx0, Yx1 = ivf_add(q_hi, q_hi, Yx0, Yx1)

                dEV0, dEV1 = ivf_deriv_bounds_logpwl(ks_e, slopes_e_lo, slopes_e_hi, s_lo_e, s_hi_e, y0, y1)
                if has_ruin:
                    dEV0, dEV1 = ivf_mul(omp0, omp1, dEV0, dEV1)
                dVs0, dVs1 = ivf_deriv_bounds_logpwl(ks_s, slopes_s_lo, slopes_s_hi, s_lo_s, s_hi_s, xL, xR)
                bef0 = bL if ev1 < 0.0 else (bR if ev0 >= 0.0 else bL)
                bef1 = bL if ev1 < 0.0 else bR
                bdEV0, bdEV1 = ivf_mul(bef0, bef1, dEV0, dEV1)
                sbd0, sbd1 = ivf_mul(sL, sR, bdEV0, bdEV1)
                Ybd0, Ybd1 = ivf_mul(Y0, Y1, bdEV0, bdEV1)

                omLR0, omLR1 = ivf_sub(1.0, 1.0, LR, LR)
                omLL0, omLL1 = ivf_sub(1.0, 1.0, LL, LL)
                om_sR_v0, om_sR_v1 = ivf_sub(1.0, 1.0, sR, sR)
                om_sL_v0, om_sL_v1 = ivf_sub(1.0, 1.0, sL, sL)
                dL_pen_0 = ivf_div(omeU0, omeU1, omLL0, omLL1)[0]
                dL_pen_1 = ivf_div(omeU0, omeU1, omLR0, omLR1)[1]

                cross_c1 = (c_min < 1.0) and (c_max >= 1.0)
                best_cent = -1e300
                for pass_idx in range(2):
                    if pass_idx == 0 and not (c_min < 1.0):
                        continue
                    if pass_idx == 1 and not (c_max >= 1.0):
                        continue
                    ec = eL if pass_idx == 0 else eU
                    ec0 = eL if cross_c1 else ec
                    ec1 = eU if cross_c1 else ec

                    _, ucm1 = ivf_mul(ec, ec, lcm0, lcm1)
                    hm1 = ivf_add(ucm1, ucm1, uLm1, uLm1)[1]
                    hm1 = ivf_add(hm1, hm1, bevm1, bevm1)[1]
                    hm1 = ivf_sub(hm1, hm1, Vsm0, Vsm0)[1]

                    eY0, eY1 = ivf_div(ec0, ec1, Y0, Y1)
                    A0, A1 = ivf_add(eY0, eY1, sbd0, sbd1)
                    AYx0, AYx1 = ivf_mul(A0, A1, Yx0, Yx1)
                    hx_d0, hx_d1 = ivf_sub(AYx0, AYx1, dVs0, dVs1)
                    AYL0, AYL1 = ivf_mul(A0, A1, YL0, YL1)
                    hL_d0, hL_d1 = ivf_sub(AYL0, AYL1, dL_pen_0, dL_pen_1)
                    ec_s0 = ivf_div(ec0, ec1, om_sL_v0, om_sL_v1)[0]
                    ec_s1 = ivf_div(ec0, ec1, om_sR_v0, om_sR_v1)[1]
                    hs_d0, hs_d1 = ivf_sub(Ybd0, Ybd1, ec_s0, ec_s1)

                    sx = ivf_mul(max(abs(hx_d0), abs(hx_d1)), max(abs(hx_d0), abs(hx_d1)), hx, hx)[1]
                    sL_e = ivf_mul(max(abs(hL_d0), abs(hL_d1)), max(abs(hL_d0), abs(hL_d1)), hL, hL)[1]
                    ss_e = ivf_mul(max(abs(hs_d0), abs(hs_d1)), max(abs(hs_d0), abs(hs_d1)), hs, hs)[1]
                    ub_ec = ivf_add(hm1, hm1, sx, sx)[1]
                    ub_ec = ivf_add(ub_ec, ub_ec, sL_e, sL_e)[1]
                    ub_ec = ivf_add(ub_ec, ub_ec, ss_e, ss_e)[1]
                    if ub_ec > best_cent:
                        best_cent = ub_ec
                if best_cent < box_ub:
                    box_ub = best_cent

        if math.isnan(box_ub):
            return 1e300
        if box_ub > global_ub:
            global_ub = box_ub
    return global_ub
