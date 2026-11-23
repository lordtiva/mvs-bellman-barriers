"""
Exact Log-PWL Representation & LogReLUNetwork (1D bijection) for CEGIS-PWL Synthesis.

Provides:
  - Exact log-PWL table utilities (`make_pwl_from_knots`, `build_slope_tables`,
    `eval_logpwl`, `deriv_bounds_logpwl`, `range_bounds_logpwl`).
  - `LogReLUNetwork`: exact 1-hidden-layer ReLU(log K) representation used in
    Case 1 for moving-knot compression on M = [0.10, 0.28), and exact bijection
    `set_from_knots_values` / `extract_exact_log_pwl` for JSON serialization.
"""

from __future__ import annotations

import math
from typing import Dict, List, Optional, Sequence, Tuple
import numpy as np
from scipy.optimize import minimize as scipy_minimize


def _relu(x: np.ndarray) -> np.ndarray:
    return np.maximum(x, 0.0)


def make_pwl_from_knots(
    ks: np.ndarray,
    vals: np.ndarray,
    s_lo: float,
    s_hi: float,
) -> Dict[str, object]:
    """Build exact log-PWL dictionary from sorted knots ks and values vals."""
    ks_arr = np.asarray(ks, dtype=np.float64)
    vals_arr = np.asarray(vals, dtype=np.float64)
    assert ks_arr.ndim == 1 and len(ks_arr) >= 2
    assert len(ks_arr) == len(vals_arr)
    assert np.all(np.diff(ks_arr) > 0.0)
    lks = np.log(ks_arr)
    slopes = np.diff(vals_arr) / np.diff(lks)
    return {
        "ks": ks_arr,
        "lks": lks,
        "vals": vals_arr,
        "slopes": slopes,
        "s_lo": float(s_lo),
        "s_hi": float(s_hi),
    }


def pwl_to_dict(pwl: Dict[str, object]) -> Dict[str, object]:
    """Serialize log-PWL table directly into JSON-safe dict."""
    return {
        "type": "log_pwl",
        "ks": np.asarray(pwl["ks"], dtype=np.float64).tolist(),
        "vals": np.asarray(pwl["vals"], dtype=np.float64).tolist(),
        "s_lo": float(pwl["s_lo"]),
        "s_hi": float(pwl["s_hi"]),
    }


def pwl_from_dict(data: Dict[str, object]) -> Dict[str, object]:
    """Deserialize either a direct `log_pwl` dict or a `LogReLUNetwork` dict."""
    if data.get("type") == "log_pwl":
        return make_pwl_from_knots(
            np.asarray(data["ks"], dtype=np.float64),
            np.asarray(data["vals"], dtype=np.float64),
            float(data["s_lo"]),
            float(data["s_hi"]),
        )
    return LogReLUNetwork.from_dict(data).extract_exact_log_pwl()


def build_slope_tables(slopes_arr: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    """Precompute O(1) min/max slope lookup tables over contiguous knot ranges."""
    m = len(slopes_arr)
    smin = np.full((m, m), np.inf, dtype=np.float64)
    smax = np.full((m, m), -np.inf, dtype=np.float64)
    for i in range(m):
        smin[i, i:] = np.minimum.accumulate(slopes_arr[i:])
        smax[i, i:] = np.maximum.accumulate(slopes_arr[i:])
    return smin, smax


def eval_logpwl(pwl: Dict[str, object], k_arr: np.ndarray) -> np.ndarray:
    """Evaluate exact continuous log-PWL function in float64."""
    ks = pwl["ks"]
    lks = pwl["lks"]
    vals = pwl["vals"]
    s_lo = float(pwl["s_lo"])
    s_hi = float(pwl["s_hi"])
    k = np.asarray(k_arr, dtype=np.float64)
    lk = np.log(np.maximum(k, 1e-300))
    r = np.interp(np.clip(lk, lks[0], lks[-1]), lks, vals)
    below = k < ks[0]
    if np.any(below):
        r = np.where(below, vals[0] + s_lo * (lk - lks[0]), r)
    above = k > ks[-1]
    if np.any(above):
        r = np.where(above, vals[-1] + s_hi * (lk - lks[-1]), r)
    return r


def deriv_bounds_logpwl(
    pwl: Dict[str, object],
    smin_tbl: np.ndarray,
    smax_tbl: np.ndarray,
    kL: np.ndarray,
    kR: np.ndarray,
) -> Tuple[np.ndarray, np.ndarray]:
    """Fast float64 derivative bounds [dN/dK_lo, dN/dK_hi] on [kL, kR] for B&B pruning."""
    ks = pwl["ks"]
    nk = len(ks)
    s_lo = float(pwl["s_lo"])
    s_hi = float(pwl["s_hi"])
    iL = np.clip(np.searchsorted(ks, kL, side="right") - 1, 0, nk - 2)
    iR = np.maximum(iL, np.clip(np.searchsorted(ks, kR, side="left") - 1, 0, nk - 2))
    lo_s = smin_tbl[iL, iR].copy()
    hi_s = smax_tbl[iL, iR].copy()
    below = kL < ks[0]
    if np.any(below):
        lo_s = np.where(below, np.minimum(lo_s, s_lo), lo_s)
        hi_s = np.where(below, np.maximum(hi_s, s_lo), hi_s)
    above = kR > ks[-1]
    if np.any(above):
        lo_s = np.where(above, np.minimum(lo_s, s_hi), lo_s)
        hi_s = np.where(above, np.maximum(hi_s, s_hi), hi_s)
    d_lo = np.where(lo_s >= 0.0, lo_s / kR, lo_s / kL)
    d_hi = np.where(hi_s >= 0.0, hi_s / kL, hi_s / kR)
    return d_lo, d_hi


def range_bounds_logpwl(
    pwl: Dict[str, object],
    kL: np.ndarray,
    kR: np.ndarray,
) -> Tuple[np.ndarray, np.ndarray]:
    """Fast vectorized range enclosure [min_{K in [kL,kR]} N(K), max_{K in [kL,kR]} N(K)]."""
    ks = pwl["ks"]
    vals = pwl["vals"]
    nk = len(ks)
    vL = eval_logpwl(pwl, kL)
    vR = eval_logpwl(pwl, kR)
    vmin = np.minimum(vL, vR)
    vmax = np.maximum(vL, vR)
    if nk > 2:
        i_first = np.searchsorted(ks, kL, side="right")
        i_last = np.searchsorted(ks, kR, side="left") - 1
        has_int = i_first <= i_last
        if np.any(has_int):
            idxs = np.where(has_int)[0]
            for idx in idxs:
                sl = vals[i_first[idx]:i_last[idx] + 1]
                vmin[idx] = min(vmin[idx], float(np.min(sl)))
                vmax[idx] = max(vmax[idx], float(np.max(sl)))
    return vmin, vmax


class LogReLUNetwork:
    """
    Exact continuous piecewise-linear spline in z = log(K) represented in the
    1-hidden-layer ReLU basis (used for Case 1 adaptive moving-knot compression
    and compatible serialization).
    """

    def __init__(
        self,
        k_lo: float,
        k_hi: float,
        hidden_sizes: Sequence[int] = (32,),
        s_lo: Optional[float] = None,
        s_hi: Optional[float] = None,
        seed: int = 42,
        init_alpha: float = 0.0,
        init_c0: float = 0.0,
        init_knots_k: Optional[Sequence[float]] = None,
    ):
        assert k_lo > 0.0 and k_hi > k_lo
        assert len(hidden_sizes) in (1, 2)
        self.k_lo = float(k_lo)
        self.k_hi = float(k_hi)
        self.z_lo = math.log(self.k_lo)
        self.z_hi = math.log(self.k_hi)
        self.z_ref = 0.5 * (self.z_lo + self.z_hi)
        self.z_scale = max(0.5 * (self.z_hi - self.z_lo), 1e-6)
        self.hidden_sizes = tuple(int(h) for h in hidden_sizes)
        self.s_lo = None if s_lo is None else float(s_lo)
        self.s_hi = None if s_hi is None else float(s_hi)

        rng = np.random.default_rng(seed)
        self.c0 = float(init_c0)
        self.alpha_lin = float(init_alpha)

        h1 = self.hidden_sizes[0]
        if init_knots_k is not None:
            zk = np.log(np.clip(np.asarray(init_knots_k, dtype=np.float64), self.k_lo * 1.0001, self.k_hi * 0.9999))
            if len(zk) != h1:
                zk = np.interp(np.linspace(0.0, 1.0, h1), np.linspace(0.0, 1.0, len(zk)), np.sort(zk))
            knots_init = zk - self.z_ref
        else:
            knots_init = np.linspace(self.z_lo, self.z_hi, h1 + 2)[1:-1] - self.z_ref
        signs = np.where(np.arange(h1) % 2 == 0, 1.0, -1.0)
        self.W1 = signs * (1.0 / self.z_scale)
        self.b1 = -self.W1 * knots_init

        if len(self.hidden_sizes) == 1:
            self.W2 = None
            self.b2 = None
            self.v = rng.normal(0.0, 1e-3, size=h1)
        else:
            h2 = self.hidden_sizes[1]
            self.W2 = rng.normal(0.0, 0.25 / math.sqrt(h1), size=(h2, h1))
            self.b2 = rng.normal(0.0, 0.05, size=h2)
            self.v = rng.normal(0.0, 1e-3, size=h2)

    def fit_linear_head_lstsq(self, ks: np.ndarray, targets: np.ndarray, ridge: float = 1e-8) -> None:
        z_c = np.clip(np.log(np.asarray(ks, dtype=np.float64)), self.z_lo, self.z_hi)
        dz = z_c - self.z_ref
        h1 = _relu(dz[:, None] * self.W1[None, :] + self.b1[None, :])
        feat = h1 if self.W2 is None else _relu(h1 @ self.W2.T + self.b2[None, :])
        Phi = np.column_stack([np.ones_like(dz), dz, feat])
        A = Phi.T @ Phi + ridge * np.eye(Phi.shape[1])
        b = Phi.T @ np.asarray(targets, dtype=np.float64)
        sol = np.linalg.solve(A, b)
        self.c0 = float(sol[0])
        self.alpha_lin = float(sol[1])
        self.v = sol[2:].copy()

    def set_from_knots_values(self, ks: np.ndarray, vals: np.ndarray) -> None:
        """Exact bijection mapping sorted knot values (ks, vals) on [k_lo, k_hi] into 1-layer ReLU weights."""
        assert self.W2 is None and len(ks) >= 3
        lks = np.log(np.asarray(ks, dtype=np.float64))
        vals = np.asarray(vals, dtype=np.float64)
        assert abs(lks[0] - self.z_lo) < 1e-9 and abs(lks[-1] - self.z_hi) < 1e-9
        h1 = len(lks) - 2
        self.hidden_sizes = (h1,)
        slopes = np.diff(vals) / np.diff(lks)
        self.alpha_lin = float(slopes[0])
        self.c0 = float(vals[0] - slopes[0] * (lks[0] - self.z_ref))
        self.W1 = np.ones(h1, dtype=np.float64)
        self.b1 = -(lks[1:-1] - self.z_ref)
        self.v = np.diff(slopes).astype(np.float64)

    def get_params_vector(self) -> np.ndarray:
        parts = [np.array([self.c0, self.alpha_lin], dtype=np.float64), self.W1, self.b1]
        if self.W2 is not None:
            parts.extend([self.W2.ravel(), self.b2])
        parts.append(self.v)
        return np.concatenate(parts)

    def set_params_vector(self, vec: np.ndarray) -> None:
        vec = np.asarray(vec, dtype=np.float64)
        idx = 0
        self.c0 = float(vec[idx]); idx += 1
        self.alpha_lin = float(vec[idx]); idx += 1
        h1 = self.hidden_sizes[0]
        self.W1 = vec[idx:idx + h1].copy(); idx += h1
        self.b1 = vec[idx:idx + h1].copy(); idx += h1
        if self.W2 is not None:
            h2 = self.hidden_sizes[1]
            self.W2 = vec[idx:idx + h2 * h1].reshape(h2, h1).copy(); idx += h2 * h1
            self.b2 = vec[idx:idx + h2].copy(); idx += h2
        else:
            h2 = h1
        self.v = vec[idx:idx + h2].copy(); idx += h2
        assert idx == len(vec)

    def _eval_clamped(self, z_c: np.ndarray) -> np.ndarray:
        dz = z_c - self.z_ref
        h1 = _relu(dz[:, None] * self.W1[None, :] + self.b1[None, :])
        if self.W2 is None:
            return self.c0 + self.alpha_lin * dz + h1 @ self.v
        h2 = _relu(h1 @ self.W2.T + self.b2[None, :])
        return self.c0 + self.alpha_lin * dz + h2 @ self.v

    def forward_log(self, z: np.ndarray) -> np.ndarray:
        z_arr = np.asarray(z, dtype=np.float64)
        flat = z_arr.ravel()
        if self.s_lo is None and self.s_hi is None:
            return self._eval_clamped(flat).reshape(z_arr.shape)
        z_c = np.clip(flat, self.z_lo, self.z_hi)
        out = self._eval_clamped(z_c)
        below = flat < self.z_lo
        if np.any(below):
            out = np.where(below, out + self.s_lo * (flat - self.z_lo) if self.s_lo is not None else self._eval_clamped(flat), out)
        above = flat > self.z_hi
        if np.any(above):
            out = np.where(above, out + self.s_hi * (flat - self.z_hi) if self.s_hi is not None else self._eval_clamped(flat), out)
        return out.reshape(z_arr.shape)

    def __call__(self, K: np.ndarray) -> np.ndarray:
        return self.forward_log(np.log(np.maximum(np.asarray(K, dtype=np.float64), 1e-300)))

    def forward_and_grad_params(self, z: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
        z_flat = np.asarray(z, dtype=np.float64).ravel()
        z_c = np.clip(z_flat, self.z_lo, self.z_hi) if (self.s_lo is not None or self.s_hi is not None) else z_flat
        dz = z_c - self.z_ref
        pre1 = dz[:, None] * self.W1[None, :] + self.b1[None, :]
        mask1 = (pre1 > 0.0).astype(np.float64)
        h1 = pre1 * mask1
        N = len(z_flat)
        g_c0 = np.ones((N, 1), dtype=np.float64)
        g_alpha = dz[:, None]
        if self.W2 is None:
            out = self.c0 + self.alpha_lin * dz + h1 @ self.v
            dh1 = mask1 * self.v[None, :]
            g_W1 = dh1 * dz[:, None]
            g_b1 = dh1
            g_v = h1
            if self.s_lo is not None:
                below = z_flat < self.z_lo
                if np.any(below):
                    out = np.where(below, out + self.s_lo * (z_flat - self.z_lo), out)
            if self.s_hi is not None:
                above = z_flat > self.z_hi
                if np.any(above):
                    out = np.where(above, out + self.s_hi * (z_flat - self.z_hi), out)
            return out, np.hstack([g_c0, g_alpha, g_W1, g_b1, g_v])
        raise NotImplementedError("Only 1-hidden-layer forward_and_grad_params is used.")

    def extract_exact_log_pwl(
        self,
        extra_lks: Optional[np.ndarray] = None,
        min_knots: int = 2,
    ) -> Dict[str, object]:
        knots: List[float] = [self.z_lo, self.z_hi]
        if extra_lks is not None:
            for z in np.asarray(extra_lks, dtype=np.float64).ravel():
                if self.z_lo < z < self.z_hi:
                    knots.append(float(z))
        for w, b in zip(self.W1, self.b1):
            if abs(w) > 1e-15:
                zk = self.z_ref - b / w
                if self.z_lo < zk < self.z_hi:
                    knots.append(float(zk))
        knots_arr = np.unique(np.round(np.array(knots, dtype=np.float64), 14))
        knots_arr[0] = self.z_lo
        knots_arr[-1] = self.z_hi
        clean = [knots_arr[0]]
        for z in knots_arr[1:]:
            if z - clean[-1] > 1e-11:
                clean.append(float(z))
        if clean[-1] < self.z_hi - 1e-12:
            clean.append(self.z_hi)
        else:
            clean[-1] = self.z_hi
        if len(clean) < min_knots:
            clean = list(np.linspace(self.z_lo, self.z_hi, min_knots))

        lks = np.array(clean, dtype=np.float64)
        ks = np.exp(lks)
        vals = self._eval_clamped(lks)
        slopes = np.diff(vals) / np.diff(lks)
        if self.s_lo is not None:
            s_lo_eff = self.s_lo
        else:
            dz_eps = 1e-7
            s_lo_eff = float((self._eval_clamped(np.array([self.z_lo]))[0] - self._eval_clamped(np.array([self.z_lo - dz_eps]))[0]) / dz_eps)
        if self.s_hi is not None:
            s_hi_eff = self.s_hi
        else:
            dz_eps = 1e-7
            s_hi_eff = float((self._eval_clamped(np.array([self.z_hi + dz_eps]))[0] - self._eval_clamped(np.array([self.z_hi]))[0]) / dz_eps)
        return {
            "ks": ks,
            "lks": lks,
            "vals": vals,
            "slopes": slopes,
            "s_lo": float(s_lo_eff),
            "s_hi": float(s_hi_eff),
        }

    def to_dict(self) -> Dict[str, object]:
        return {
            "type": "log_relu",
            "k_lo": self.k_lo,
            "k_hi": self.k_hi,
            "hidden_sizes": list(self.hidden_sizes),
            "s_lo": self.s_lo,
            "s_hi": self.s_hi,
            "c0": self.c0,
            "alpha_lin": self.alpha_lin,
            "W1": self.W1.tolist(),
            "b1": self.b1.tolist(),
            "W2": None if self.W2 is None else self.W2.tolist(),
            "b2": None if self.b2 is None else self.b2.tolist(),
            "v": self.v.tolist(),
        }

    @classmethod
    def from_dict(cls, data: Dict[str, object]) -> "LogReLUNetwork":
        obj = cls(
            k_lo=float(data["k_lo"]),
            k_hi=float(data["k_hi"]),
            hidden_sizes=tuple(int(x) for x in data["hidden_sizes"]),
            s_lo=None if data["s_lo"] is None else float(data["s_lo"]),
            s_hi=None if data["s_hi"] is None else float(data["s_hi"]),
        )
        obj.c0 = float(data["c0"])
        obj.alpha_lin = float(data["alpha_lin"])
        obj.W1 = np.array(data["W1"], dtype=np.float64)
        obj.b1 = np.array(data["b1"], dtype=np.float64)
        obj.W2 = None if data["W2"] is None else np.array(data["W2"], dtype=np.float64)
        obj.b2 = None if data["b2"] is None else np.array(data["b2"], dtype=np.float64)
        obj.v = np.array(data["v"], dtype=np.float64)
        return obj
