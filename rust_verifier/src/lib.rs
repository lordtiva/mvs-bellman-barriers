#![allow(non_snake_case)]
use std::slice;

const B_M: f64 = 0.10;
const H_M: f64 = 0.28;

#[inline(always)]
fn dn(mut x: f64, n: u32) -> f64 {
    for _ in 0..n {
        x = x.next_down();
    }
    x
}

#[inline(always)]
fn up(mut x: f64, n: u32) -> f64 {
    for _ in 0..n {
        x = x.next_up();
    }
    x
}

#[derive(Clone, Copy)]
struct Iv {
    lo: f64,
    hi: f64,
}

impl Iv {
    #[inline(always)]
    fn pt(x: f64) -> Self {
        Self { lo: x, hi: x }
    }
    #[inline(always)]
    fn raw(lo: f64, hi: f64) -> Self {
        Self { lo, hi }
    }
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        Self {
            lo: (self.lo + o.lo).next_down(),
            hi: (self.hi + o.hi).next_up(),
        }
    }
    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        Self {
            lo: (self.lo - o.hi).next_down(),
            hi: (self.hi - o.lo).next_up(),
        }
    }
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        let p1 = self.lo * o.lo;
        let p2 = self.lo * o.hi;
        let p3 = self.hi * o.lo;
        let p4 = self.hi * o.hi;
        Self {
            lo: p1.min(p2).min(p3.min(p4)).next_down(),
            hi: p1.max(p2).max(p3.max(p4)).next_up(),
        }
    }
    #[inline(always)]
    fn div(self, o: Self) -> Self {
        let p1 = self.lo / o.lo;
        let p2 = self.lo / o.hi;
        let p3 = self.hi / o.lo;
        let p4 = self.hi / o.hi;
        Self {
            lo: p1.min(p2).min(p3.min(p4)).next_down(),
            hi: p1.max(p2).max(p3.max(p4)).next_up(),
        }
    }
    #[inline(always)]
    fn sqrt(self) -> Self {
        let mut lo = self.lo.max(0.0).sqrt();
        if lo > 0.0 {
            lo = dn(lo, 1);
            while lo > 0.0 && lo * lo > self.lo {
                lo = lo.next_down();
            }
        }
        let mut hi = self.hi.max(0.0).sqrt();
        hi = up(hi, 1);
        while hi * hi < self.hi {
            hi = hi.next_up();
        }
        Self { lo, hi }
    }
    #[inline(always)]
    fn ln(self) -> Self {
        if self.lo <= 0.0 {
            return Self::raw(f64::NEG_INFINITY, iv_ln_pt(self.hi).hi);
        }
        Self::raw(iv_ln_pt(self.lo).lo, iv_ln_pt(self.hi).hi)
    }
    #[inline(always)]
    fn pow32(self) -> Self {
        self.mul(self.sqrt())
    }
    #[inline(always)]
    fn pow52(self) -> Self {
        let s = self.sqrt();
        self.mul(self).mul(s)
    }
    #[inline(always)]
    fn hull(self, o: Self) -> Self {
        Self {
            lo: self.lo.min(o.lo),
            hi: self.hi.max(o.hi),
        }
    }
    #[inline(always)]
    fn max_abs(self) -> f64 {
        self.lo.abs().max(self.hi.abs())
    }
}

/// Self-contained libm-free natural logarithm enclosure via MR Lemma 11 (Eq. F.5):
/// x = 2^k * m with m in [1, 2), v = (m-1)/(m+1) in [0, 1/3),
/// log(m) in [2*sum_{j=0}^{N-1} v^{2j+1}/(2j+1), + 2*v^{2N+1}/((2N+1)*(1-v^2))].
#[inline]
fn iv_ln_pt(x: f64) -> Iv {
    if x.is_nan() || x <= 0.0 {
        return Iv::raw(f64::NEG_INFINITY, f64::NEG_INFINITY);
    }
    if x == 1.0 {
        return Iv::pt(0.0);
    }
    const POW2_54: f64 = 18014398509481984.0;
    let mut xv = x;
    let mut k: i32 = 0;
    if xv < 2.2250738585072014e-308 {
        xv *= POW2_54;
        k -= 54;
    }
    let bits = xv.to_bits();
    let exp = ((bits >> 52) & 0x7ff) as i32 - 1023;
    k += exp;
    let mant = f64::from_bits((bits & 0x000f_ffff_ffff_ffff) | 0x3ff0_0000_0000_0000);

    let m_iv = Iv::pt(mant);
    let one = Iv::pt(1.0);
    let v = m_iv.sub(one).div(m_iv.add(one));
    let v2 = v.mul(v);
    let mut term = v;
    let mut sum = v;
    for j in 1..16usize {
        term = term.mul(v2);
        let denom = Iv::pt((2 * j + 1) as f64);
        sum = sum.add(term.div(denom));
    }
    let v33 = term.mul(v2);
    let rem_den = Iv::pt(33.0).mul(one.sub(v2));
    let rem_hi = Iv::pt(2.0).mul(Iv::pt(v33.hi)).div(Iv::pt(rem_den.lo)).hi;
    let ln_m = Iv::pt(2.0).mul(sum).add(Iv::raw(0.0, rem_hi));

    // Exact IEEE-754 outward enclosure of ln(2) = 0.693147180559945309417232121458...
    const LN2_LO: f64 = 0.6931471805599452;
    const LN2_HI: f64 = 0.6931471805599454;
    let ln2_iv = Iv::raw(LN2_LO, LN2_HI);
    Iv::pt(k as f64).mul(ln2_iv).add(ln_m)
}

#[no_mangle]
pub extern "C" fn rs_test_iv_ln(x: f64, out_lo: *mut f64, out_hi: *mut f64) {
    let iv = iv_ln_pt(x);
    unsafe {
        if !out_lo.is_null() { *out_lo = iv.lo; }
        if !out_hi.is_null() { *out_hi = iv.hi; }
    }
}

struct Pwl<'a> {
    ks: &'a [f64],
    lks: &'a [f64],
    vals: &'a [f64],
    slopes: &'a [f64],
    s_lo: f64,
    s_hi: f64,
    ns: usize,
    smin_tbl: Vec<f64>,
    smax_tbl: Vec<f64>,
    lks_lo: Vec<f64>,
    lks_hi: Vec<f64>,
    slopes_lo: Vec<f64>,
    slopes_hi: Vec<f64>,
    smin_lo_tbl: Vec<f64>,
    smax_hi_tbl: Vec<f64>,
}

impl<'a> Pwl<'a> {
    fn new(ks: &'a [f64], lks: &'a [f64], vals: &'a [f64], slopes: &'a [f64], s_lo: f64, s_hi: f64) -> Self {
        let nk = ks.len();
        let ns = slopes.len();
        let mut lks_lo = Vec::with_capacity(nk);
        let mut lks_hi = Vec::with_capacity(nk);
        for &kv in ks {
            let lk_iv = Iv::pt(kv).ln();
            lks_lo.push(lk_iv.lo);
            lks_hi.push(lk_iv.hi);
        }
        let mut slopes_lo = Vec::with_capacity(ns);
        let mut slopes_hi = Vec::with_capacity(ns);
        for i in 0..ns {
            let dv = Iv::pt(vals[i + 1]).sub(Iv::pt(vals[i]));
            let dl = Iv::raw(lks_lo[i + 1], lks_hi[i + 1]).sub(Iv::raw(lks_lo[i], lks_hi[i]));
            let sl = dv.div(dl);
            slopes_lo.push(sl.lo);
            slopes_hi.push(sl.hi);
        }
        let mut smin_tbl = vec![f64::INFINITY; ns * ns];
        let mut smax_tbl = vec![f64::NEG_INFINITY; ns * ns];
        let mut smin_lo_tbl = vec![f64::INFINITY; ns * ns];
        let mut smax_hi_tbl = vec![f64::NEG_INFINITY; ns * ns];
        for i in 0..ns {
            let mut mn = f64::INFINITY;
            let mut mx = f64::NEG_INFINITY;
            let mut mn_lo = f64::INFINITY;
            let mut mx_hi = f64::NEG_INFINITY;
            for j in i..ns {
                let sv = slopes[j];
                if sv < mn { mn = sv; }
                if sv > mx { mx = sv; }
                smin_tbl[i * ns + j] = mn;
                smax_tbl[i * ns + j] = mx;
                if slopes_lo[j] < mn_lo { mn_lo = slopes_lo[j]; }
                if slopes_hi[j] > mx_hi { mx_hi = slopes_hi[j]; }
                smin_lo_tbl[i * ns + j] = mn_lo;
                smax_hi_tbl[i * ns + j] = mx_hi;
            }
        }
        Self {
            ks, lks, vals, slopes, s_lo, s_hi, ns,
            smin_tbl, smax_tbl, lks_lo, lks_hi, slopes_lo, slopes_hi, smin_lo_tbl, smax_hi_tbl,
        }
    }

    #[inline(always)]
    fn eval_f64(&self, k: f64) -> f64 {
        let nk = self.ks.len();
        let lk = k.max(1e-300).ln();
        if k <= self.ks[0] {
            return self.vals[0] + self.s_lo * (lk - self.lks[0]);
        }
        if k >= self.ks[nk - 1] {
            return self.vals[nk - 1] + self.s_hi * (lk - self.lks[nk - 1]);
        }
        let idx = (self.ks.partition_point(|&v| v <= k).saturating_sub(1)).min(nk - 2);
        self.vals[idx] + self.slopes[idx] * (lk - self.lks[idx])
    }

    #[inline(always)]
    fn range_f64(&self, kL: f64, kR: f64) -> (f64, f64) {
        let vL = self.eval_f64(kL);
        let vR = self.eval_f64(kR);
        let mut vmin = vL.min(vR);
        let mut vmax = vL.max(vR);
        let nk = self.ks.len();
        if nk > 2 {
            let i_first = self.ks.partition_point(|&v| v <= kL);
            let i_last_plus_1 = self.ks.partition_point(|&v| v < kR);
            for i in i_first..i_last_plus_1 {
                let v = self.vals[i];
                if v < vmin { vmin = v; }
                if v > vmax { vmax = v; }
            }
        }
        (vmin, vmax)
    }

    #[inline(always)]
    fn deriv_bounds_f64(&self, kL: f64, kR: f64) -> (f64, f64) {
        let nk = self.ks.len();
        let iL = (self.ks.partition_point(|&v| v <= kL).saturating_sub(1)).min(nk - 2);
        let iR_raw = (self.ks.partition_point(|&v| v < kR).saturating_sub(1)).min(nk - 2);
        let iR = iR_raw.max(iL);
        let mut lo_s = self.smin_tbl[iL * self.ns + iR];
        let mut hi_s = self.smax_tbl[iL * self.ns + iR];
        if kL < self.ks[0] {
            if self.s_lo < lo_s { lo_s = self.s_lo; }
            if self.s_lo > hi_s { hi_s = self.s_lo; }
        }
        if kR > self.ks[nk - 1] {
            if self.s_hi < lo_s { lo_s = self.s_hi; }
            if self.s_hi > hi_s { hi_s = self.s_hi; }
        }
        let d_lo = if lo_s >= 0.0 { lo_s / kR } else { lo_s / kL };
        let d_hi = if hi_s >= 0.0 { hi_s / kL } else { hi_s / kR };
        (d_lo, d_hi)
    }

    #[inline(always)]
    fn iv_eval_pt(&self, kv: f64) -> Iv {
        let nk = self.ks.len();
        let lk = Iv::pt(kv).ln();
        if kv <= self.ks[0] {
            let dl = lk.sub(Iv::raw(self.lks_lo[0], self.lks_hi[0]));
            return Iv::pt(self.vals[0]).add(Iv::pt(self.s_lo).mul(dl));
        }
        if kv >= self.ks[nk - 1] {
            let dl = lk.sub(Iv::raw(self.lks_lo[nk - 1], self.lks_hi[nk - 1]));
            return Iv::pt(self.vals[nk - 1]).add(Iv::pt(self.s_hi).mul(dl));
        }
        let idx = (self.ks.partition_point(|&v| v <= kv).saturating_sub(1)).min(nk - 2);
        let dl = lk.sub(Iv::raw(self.lks_lo[idx], self.lks_hi[idx]));
        Iv::pt(self.vals[idx]).add(Iv::raw(self.slopes_lo[idx], self.slopes_hi[idx]).mul(dl))
    }

    #[inline(always)]
    fn iv_range(&self, kL: f64, kR: f64) -> Iv {
        let v0 = self.iv_eval_pt(kL);
        let v1 = self.iv_eval_pt(kR);
        let mut vmin = v0.lo.min(v1.lo);
        let mut vmax = v0.hi.max(v1.hi);
        let i_first = self.ks.partition_point(|&v| v <= kL);
        let i_last_plus_1 = self.ks.partition_point(|&v| v < kR);
        for i in i_first..i_last_plus_1 {
            let v = self.vals[i];
            if v < vmin { vmin = v; }
            if v > vmax { vmax = v; }
        }
        Iv::raw(vmin, vmax)
    }

    #[inline(always)]
    fn iv_deriv_bounds(&self, kL: f64, kR: f64) -> Iv {
        let mut smin = f64::INFINITY;
        let mut smax = f64::NEG_INFINITY;
        if kL < self.ks[0] {
            smin = smin.min(self.s_lo);
            smax = smax.max(self.s_lo);
        }
        let i_start = self.ks.partition_point(|&v| v <= kL).saturating_sub(1);
        let cnt_lt = self.ks.partition_point(|&v| v < kR);
        if cnt_lt > 0 {
            let i_end = (cnt_lt - 1).min(self.ns - 1);
            if i_start <= i_end {
                let mn = self.smin_lo_tbl[i_start * self.ns + i_end];
                let mx = self.smax_hi_tbl[i_start * self.ns + i_end];
                if mn < smin { smin = mn; }
                if mx > smax { smax = mx; }
            }
        }
        if kR > self.ks[self.ns] {
            smin = smin.min(self.s_hi);
            smax = smax.max(self.s_hi);
        }
        if smin > smax {
            if kL <= self.ks[0] {
                smin = smin.min(self.s_lo);
                smax = smax.max(self.s_lo);
            }
            if kR >= self.ks[self.ns] {
                smin = smin.min(self.s_hi);
                smax = smax.max(self.s_hi);
            }
            let idx = (self.ks.partition_point(|&v| v <= kL).saturating_sub(1)).min(self.ns - 1);
            smin = smin.min(self.slopes_lo[idx]);
            smax = smax.max(self.slopes_hi[idx]);
            if idx > 0 && self.ks[idx] == kL {
                smin = smin.min(self.slopes_lo[idx - 1]);
                smax = smax.max(self.slopes_hi[idx - 1]);
            }
            if idx + 1 < self.ns && self.ks[idx + 1] == kL {
                smin = smin.min(self.slopes_lo[idx + 1]);
                smax = smax.max(self.slopes_hi[idx + 1]);
            }
        }
        Iv::raw(smin, smax).div(Iv::raw(kL, kR))
    }
}

#[inline(always)]
fn f_a(a: f64, k: f64, l: f64) -> f64 {
    if l <= 0.0 {
        return 0.0;
    }
    let ratio = (2.0 * k * l) / (k + l);
    a * ratio * ratio.sqrt()
}

#[inline(always)]
fn df_dk(a: f64, k: f64, l: f64) -> f64 {
    if l <= 0.0 {
        return 0.0;
    }
    1.5 * a * 2.8284271247461903 * k.sqrt() * l.powf(2.5) * (k + l).powf(-2.5)
}

#[inline(always)]
fn df_dl(a: f64, k: f64, l: f64) -> f64 {
    if l <= 0.0 {
        return 0.0;
    }
    1.5 * a * 2.8284271247461903 * k.powf(2.5) * l.sqrt() * (k + l).powf(-2.5)
}

#[inline(always)]
fn prod_y_f64(a: f64, k: f64, l: f64, ak_mode: bool) -> f64 {
    if !ak_mode || k < H_M {
        f_a(a, k, l)
    } else {
        (k / H_M) * f_a(a, H_M, l)
    }
}

#[inline(always)]
fn prod_dy_dk_bounds_f64(a: f64, xL: f64, xR: f64, lL: f64, lR: f64, ak_mode: bool) -> (f64, f64) {
    let px_hi = (lR * 0.25).clamp(xL, xR);
    let lo_ces = df_dk(a, xL, lL).min(df_dk(a, xR, lL));
    let hi_ces = df_dk(a, xL, lR).max(df_dk(a, xR, lR)).max(df_dk(a, px_hi, lR));
    if !ak_mode {
        return (lo_ces, hi_ces);
    }
    let ak_lo = f_a(a, H_M, lL) / H_M;
    let ak_hi = f_a(a, H_M, lR) / H_M;
    if xL >= H_M {
        (ak_lo, ak_hi)
    } else if xR <= H_M {
        (lo_ces, hi_ces)
    } else {
        (lo_ces.min(ak_lo), hi_ces.max(ak_hi))
    }
}

#[inline(always)]
fn prod_dy_dl_bounds_f64(a: f64, xL: f64, xR: f64, lL: f64, lR: f64, ak_mode: bool) -> (f64, f64) {
    let pL_hi = (xR * 0.25).clamp(lL, lR);
    let lo_ces = df_dl(a, xL, lL).min(df_dl(a, xL, lR));
    let hi_ces = df_dl(a, xR, lL).max(df_dl(a, xR, lR)).max(df_dl(a, xR, pL_hi));
    if !ak_mode {
        return (lo_ces, hi_ces);
    }
    let pL_h = (H_M * 0.25).clamp(lL, lR);
    let dfh_lo = df_dl(a, H_M, lL).min(df_dl(a, H_M, lR));
    let dfh_hi = df_dl(a, H_M, lL).max(df_dl(a, H_M, lR)).max(df_dl(a, H_M, pL_h));
    let ak_lo = (xL / H_M) * dfh_lo;
    let ak_hi = (xR / H_M) * dfh_hi;
    if xL >= H_M {
        (ak_lo, ak_hi)
    } else if xR <= H_M {
        (lo_ces, hi_ces)
    } else {
        (lo_ces.min(ak_lo), hi_ces.max(ak_hi))
    }
}

#[inline(always)]
fn iv_f_a_pt(a: f64, k: f64, l: f64) -> Iv {
    if l <= 0.0 {
        return Iv::pt(0.0);
    }
    let num = Iv::pt(2.0 * k).mul(Iv::pt(l));
    let den = Iv::pt(k).add(Iv::pt(l));
    let q = num.div(den);
    Iv::pt(a).mul(q.pow32())
}

#[inline(always)]
fn iv_prod_y_box(a: f64, xL: f64, xR: f64, lL: f64, lR: f64, ak_mode: bool, h_v: f64) -> Iv {
    if !ak_mode || xR <= h_v {
        return Iv::raw(iv_f_a_pt(a, xL, lL).lo, iv_f_a_pt(a, xR, lR).hi);
    }
    if xL >= h_v {
        let fh_lo = iv_f_a_pt(a, h_v, lL).lo;
        let fh_hi = iv_f_a_pt(a, h_v, lR).hi;
        let r0 = Iv::pt(xL).div(Iv::pt(h_v)).lo;
        let r1 = Iv::pt(xR).div(Iv::pt(h_v)).hi;
        return Iv::raw(Iv::pt(r0).mul(Iv::pt(fh_lo)).lo, Iv::pt(r1).mul(Iv::pt(fh_hi)).hi);
    }
    let lo = iv_f_a_pt(a, xL, lL).lo;
    let fh_hi = iv_f_a_pt(a, h_v, lR).hi;
    let r1 = Iv::pt(xR).div(Iv::pt(h_v)).hi;
    Iv::raw(lo, Iv::pt(r1).mul(Iv::pt(fh_hi)).hi)
}

#[inline(always)]
fn iv_df_dk_box(a: f64, xL: f64, xR: f64, lL: f64, lR: f64) -> Iv {
    let t = Iv::pt(2.0).sqrt().mul(Iv::pt(2.0));
    let c = Iv::pt(1.5).mul(Iv::pt(a)).mul(t);
    let pt = |kv: f64, lv: f64| -> Iv {
        if lv <= 0.0 {
            return Iv::pt(0.0);
        }
        let k_s = Iv::pt(kv).sqrt();
        let l_52 = Iv::pt(lv).pow52();
        let num = c.mul(k_s).mul(l_52);
        let den = Iv::pt(kv).add(Iv::pt(lv)).pow52();
        num.div(den)
    };
    let lo = pt(xL, lL).lo.min(pt(xR, lL).lo);
    let mut hi = pt(xL, lR).hi.max(pt(xR, lR).hi);
    let pk = 0.25 * lR;
    if xL <= pk && pk <= xR {
        hi = hi.max(pt(pk, lR).hi);
    }
    Iv::raw(lo, hi)
}

#[inline(always)]
fn iv_df_dl_box(a: f64, xL: f64, xR: f64, lL: f64, lR: f64) -> Iv {
    let t = Iv::pt(2.0).sqrt().mul(Iv::pt(2.0));
    let c = Iv::pt(1.5).mul(Iv::pt(a)).mul(t);
    let pt = |kv: f64, lv: f64| -> Iv {
        if lv <= 0.0 {
            return Iv::pt(0.0);
        }
        let k_52 = Iv::pt(kv).pow52();
        let l_s = Iv::pt(lv).sqrt();
        let num = c.mul(k_52).mul(l_s);
        let den = Iv::pt(kv).add(Iv::pt(lv)).pow52();
        num.div(den)
    };
    let lo = pt(xL, lL).lo.min(pt(xL, lR).lo);
    let mut hi = pt(xR, lL).hi.max(pt(xR, lR).hi);
    let pl = 0.25 * xR;
    if lL <= pl && pl <= lR {
        hi = hi.max(pt(xR, pl).hi);
    }
    Iv::raw(lo, hi)
}

#[inline(always)]
fn sorted_dedup(mut v: Vec<f64>) -> Vec<f64> {
    v.sort_by(|a, b| a.total_cmp(b));
    let mut out = Vec::with_capacity(v.len());
    for x in v {
        if out.last().copied() != Some(x) {
            out.push(x);
        }
    }
    out
}

#[inline(always)]
fn push_geomspace(out: &mut Vec<f64>, a: f64, b: f64, n: usize) {
    if n == 0 {
        return;
    }
    if n == 1 {
        out.push(a);
        return;
    }
    let la = a.ln();
    let lb = b.ln();
    for i in 0..n {
        let t = (i as f64) / ((n - 1) as f64);
        out.push((la + t * (lb - la)).exp());
    }
}

#[inline(always)]
fn push_linspace(out: &mut Vec<f64>, a: f64, b: f64, n: usize, endpoint: bool) {
    if n == 0 {
        return;
    }
    let denom = if endpoint { (n - 1).max(1) as f64 } else { n as f64 };
    for i in 0..n {
        out.push(a + ((i as f64) / denom) * (b - a));
    }
}

#[repr(C)]
pub struct BbOut {
    pub certified: i32,
    pub iv_certified: i32,
    pub d_ub: f64,
    pub d_ub_iv: f64,
    pub d_lb: f64,
    pub leaf_count: usize,
    pub n_ce: usize,
}

fn audit_staying_boxes_rs(
    b_lhs: &Pwl,
    b_ev: &Pwl,
    bxL: &[f64], bxR: &[f64], byL: &[f64], byR: &[f64], bLL: &[f64], bLR: &[f64],
    a_hi: f64, q_hi: f64, b_lo: f64, b_hi: f64, e_lo: f64, e_hi: f64,
    p_ruin: f64, v_ruin: f64,
) -> f64 {
    let mut global_ub = f64::NEG_INFINITY;
    let b_iv_box = Iv::raw(b_lo, b_hi);
    let omp = Iv::pt(1.0).sub(Iv::pt(p_ruin));
    let pv_iv = Iv::pt(p_ruin).mul(Iv::pt(v_ruin));
    for i in 0..bxL.len() {
        let xL = bxL[i]; let xR = bxR[i];
        let yL = byL[i]; let yR = byR[i];
        let lL = bLL[i]; let lR = bLR[i];
        let y_iv = iv_prod_y_box(a_hi, xL, xR, lL, lR, false, H_M);
        let qx = Iv::pt(q_hi).mul(Iv::raw(xL, xR));
        let ym_iv = qx.add(y_iv);
        let c_iv = ym_iv.sub(Iv::raw(yL, yR));
        if c_iv.hi <= 0.0 {
            continue;
        }
        let bx_iv = b_lhs.iv_range(xL, xR);
        let by_raw = b_ev.iv_range(yL, yR);
        let cb_iv = if p_ruin > 0.0 { omp.mul(by_raw).add(pv_iv) } else { by_raw };
        let bby_a = Iv::pt(if cb_iv.lo < 0.0 { b_lo } else { b_hi }).mul(Iv::pt(cb_iv.lo));
        let bby_b = Iv::pt(if cb_iv.hi < 0.0 { b_lo } else { b_hi }).mul(Iv::pt(cb_iv.hi));
        let bby1 = bby_a.hi.max(bby_b.hi);
        let lc1 = Iv::pt(c_iv.hi).ln().hi;
        let ec_hi = if c_iv.hi < 1.0 { e_lo } else { e_hi };
        let ulc1 = Iv::pt(ec_hi).mul(Iv::pt(lc1)).hi;
        let om_l = Iv::pt(1.0).sub(Iv::pt(lL));
        if om_l.hi <= 0.0 {
            continue;
        }
        let ome_hi = Iv::pt(1.0).sub(Iv::pt(e_hi));
        let ll1 = Iv::pt(om_l.hi).ln().hi;
        let uom1 = ome_hi.mul(Iv::pt(ll1)).hi;
        let ub_mono = Iv::pt(ulc1).add(Iv::pt(uom1)).add(Iv::pt(bby1)).sub(Iv::pt(bx_iv.lo)).hi;
        let mut box_ub = ub_mono;

        if lR < 1.0 && c_iv.lo > 0.0 {
            let xm = 0.5 * (xL + xR);
            let ym = 0.5 * (yL + yR);
            let lm = 0.5 * (lL + lR);
            let hx = Iv::pt(xR).sub(Iv::pt(xm)).hi.max(Iv::pt(xm).sub(Iv::pt(xL)).hi);
            let hy = Iv::pt(yR).sub(Iv::pt(ym)).hi.max(Iv::pt(ym).sub(Iv::pt(yL)).hi);
            let hl = Iv::pt(lR).sub(Iv::pt(lm)).hi.max(Iv::pt(lm).sub(Iv::pt(lL)).hi);

            let ymid = iv_prod_y_box(a_hi, xm, xm, lm, lm, false, H_M);
            let qxm = Iv::pt(q_hi).mul(Iv::pt(xm));
            let cm_iv = qxm.add(ymid).sub(Iv::pt(ym));
            if cm_iv.lo > 0.0 {
                let lcm = cm_iv.ln();
                let llm = Iv::pt(1.0).sub(Iv::pt(lm)).ln();
                let ulm1 = ome_hi.mul(llm).hi;
                let bxm_lo = b_lhs.iv_eval_pt(xm).lo;
                let bym_raw = b_ev.iv_eval_pt(ym);
                let cbm_iv = if p_ruin > 0.0 { omp.mul(bym_raw).add(pv_iv) } else { bym_raw };
                let b_m = if cbm_iv.hi < 0.0 {
                    Iv::pt(b_lo)
                } else if cbm_iv.lo >= 0.0 {
                    Iv::pt(b_hi)
                } else {
                    b_iv_box
                };
                let bbym1 = b_m.mul(cbm_iv).hi;

                let yx = Iv::pt(q_hi).add(iv_df_dk_box(a_hi, xL, xR, lL, lR));
                let yl = iv_df_dl_box(a_hi, xL, xR, lL, lR);
                let dbx = b_lhs.iv_deriv_bounds(xL, xR);
                let dby_raw = b_ev.iv_deriv_bounds(yL, yR);
                let dby = if p_ruin > 0.0 { omp.mul(dby_raw) } else { dby_raw };
                let b_eff = if cb_iv.hi < 0.0 {
                    Iv::pt(b_lo)
                } else if cb_iv.lo >= 0.0 {
                    Iv::pt(b_hi)
                } else {
                    b_iv_box
                };
                let bdby = b_eff.mul(dby);
                let invc = Iv::pt(1.0).div(c_iv);
                let om_ll = Iv::pt(1.0).sub(Iv::pt(lL));
                let om_lr = Iv::pt(1.0).sub(Iv::pt(lR));
                let inv_1ml = Iv::raw(
                    ome_hi.div(om_ll).lo,
                    ome_hi.div(om_lr).hi,
                );

                let cross_c1 = c_iv.lo < 1.0 && c_iv.hi >= 1.0;
                let mut best_cent = f64::NEG_INFINITY;
                for pass_idx in 0..2 {
                    if pass_idx == 0 && !(c_iv.lo < 1.0) { continue; }
                    if pass_idx == 1 && !(c_iv.hi >= 1.0) { continue; }
                    let ec = if pass_idx == 0 { e_lo } else { e_hi };
                    let ec_iv = if cross_c1 { Iv::raw(e_lo, e_hi) } else { Iv::pt(ec) };
                    let ucm1 = Iv::pt(ec).mul(lcm).hi;
                    let hm1 = Iv::pt(ucm1).add(Iv::pt(ulm1)).add(Iv::pt(bbym1)).sub(Iv::pt(bxm_lo)).hi;
                    let eic = ec_iv.mul(invc);
                    let dx = eic.mul(yx).sub(dbx);
                    let dy = bdby.sub(eic);
                    let dl = eic.mul(yl).sub(inv_1ml);
                    let sx = Iv::pt(dx.max_abs()).mul(Iv::pt(hx)).hi;
                    let sy = Iv::pt(dy.max_abs()).mul(Iv::pt(hy)).hi;
                    let sl = Iv::pt(dl.max_abs()).mul(Iv::pt(hl)).hi;
                    let ub_ec = Iv::pt(hm1).add(Iv::pt(sx)).add(Iv::pt(sy)).add(Iv::pt(sl)).hi;
                    if ub_ec > best_cent { best_cent = ub_ec; }
                }
                if best_cent < box_ub { box_ub = best_cent; }
            }
        }
        if box_ub.is_nan() { return f64::INFINITY; }
        if box_ub > global_ub { global_ub = box_ub; }
    }
    global_ub
}

fn audit_super_boxes_rs(
    vs_pwl: &Pwl,
    ev_pwl: &Pwl,
    bxL: &[f64], bxR: &[f64], bLL: &[f64], bLR: &[f64], bsL: &[f64], bsR: &[f64],
    av: f64, q_hi: f64, b_lo: f64, b_hi: f64, e_lo: f64, e_hi: f64, ak_mode: bool,
    p_ruin: f64, v_ruin: f64, h_safe: f64,
) -> f64 {
    let mut global_ub = f64::NEG_INFINITY;
    let b_iv_box = Iv::raw(b_lo, b_hi);
    let omp = Iv::pt(1.0).sub(Iv::pt(p_ruin));
    let pv_iv = Iv::pt(p_ruin).mul(Iv::pt(v_ruin));
    for i in 0..bxL.len() {
        let xL = bxL[i]; let xR = bxR[i];
        let lL = bLL[i]; let lR = bLR[i];
        let sL = bsL[i]; let sR = bsR[i];
        if sL >= 1.0 || sR <= 0.0 || lL >= 1.0 {
            continue;
        }
        let has_ruin = p_ruin > 0.0 && xR <= h_safe;
        let y_f = iv_prod_y_box(av, xL, xR, lL, lR, ak_mode, H_M);
        let qx0 = Iv::pt(q_hi).mul(Iv::pt(xL)).lo;
        let qx1 = Iv::pt(q_hi).mul(Iv::pt(xR)).hi;
        let y_tot = Iv::raw(
            Iv::pt(qx0).add(Iv::pt(y_f.lo)).lo,
            Iv::pt(qx1).add(Iv::pt(y_f.hi)).hi,
        );
        let om_sL = Iv::pt(1.0).sub(Iv::pt(sL));
        let om_sR = Iv::pt(1.0).sub(Iv::pt(sR));
        let c_max = om_sL.mul(Iv::pt(y_tot.hi)).hi;
        let c_min = om_sR.mul(Iv::pt(y_tot.lo)).lo;
        if c_max <= 0.0 {
            continue;
        }
        let vs_iv = vs_pwl.iv_range(xL, xR);
        let y1 = Iv::pt(sR).mul(Iv::pt(y_tot.hi)).hi;
        if y1 <= 0.0 {
            continue;
        }
        let y0 = if sL > 0.0 { Iv::pt(sL).mul(Iv::pt(y_tot.lo)).lo } else { 0.0 };
        let mut cb_box = Iv::raw(0.0, 0.0);
        let b_ev1 = if y0 > 0.0 {
            let ev_raw = ev_pwl.iv_range(y0, y1);
            cb_box = if has_ruin { omp.mul(ev_raw).add(pv_iv) } else { ev_raw };
            let bev_a = Iv::pt(if cb_box.lo < 0.0 { b_lo } else { b_hi }).mul(Iv::pt(cb_box.lo)).hi;
            let bev_b = Iv::pt(if cb_box.hi < 0.0 { b_lo } else { b_hi }).mul(Iv::pt(cb_box.hi)).hi;
            bev_a.max(bev_b)
        } else {
            let ev_hi = ev_pwl.iv_eval_pt(y1).hi;
            let cb_hi = if has_ruin { omp.mul(Iv::pt(ev_hi)).add(pv_iv).hi } else { ev_hi };
            Iv::pt(if cb_hi < 0.0 { b_lo } else { b_hi }).mul(Iv::pt(cb_hi)).hi
        };

        let ec_hi = if c_max < 1.0 { e_lo } else { e_hi };
        let lc1 = Iv::pt(c_max).ln().hi;
        let ulc1 = Iv::pt(ec_hi).mul(Iv::pt(lc1)).hi;
        let ome_hi = Iv::pt(1.0).sub(Iv::pt(e_hi));
        let om_lL = Iv::pt(1.0).sub(Iv::pt(lL)).hi;
        let ll1 = Iv::pt(om_lL).ln().hi;
        let uom1 = ome_hi.mul(Iv::pt(ll1)).hi;
        let ub_mono = Iv::pt(ulc1).add(Iv::pt(uom1)).add(Iv::pt(b_ev1)).sub(Iv::pt(vs_iv.lo)).hi;
        let mut box_ub = ub_mono;

        let ruin_split_ok = p_ruin == 0.0 || xR <= h_safe || xL >= h_safe;
        let can_cent = ruin_split_ok && (lR < 1.0) && (sL > 0.0) && (y0 > 0.0) && (sR < 1.0) && (c_min > 1e-30) && (!ak_mode || xR <= H_M || xL >= H_M);
        if can_cent {
            let xm = 0.5 * (xL + xR);
            let lm = 0.5 * (lL + lR);
            let sm = 0.5 * (sL + sR);
            let hx = Iv::pt(xR).sub(Iv::pt(xm)).hi.max(Iv::pt(xm).sub(Iv::pt(xL)).hi);
            let hl = Iv::pt(lR).sub(Iv::pt(lm)).hi.max(Iv::pt(lm).sub(Iv::pt(lL)).hi);
            let hs = Iv::pt(sR).sub(Iv::pt(sm)).hi.max(Iv::pt(sm).sub(Iv::pt(sL)).hi);

            let ym_f = iv_prod_y_box(av, xm, xm, lm, lm, ak_mode, H_M);
            let ym_tot = Iv::pt(q_hi).mul(Iv::pt(xm)).add(ym_f);
            let om_sm = Iv::pt(1.0).sub(Iv::pt(sm));
            let cm_iv = om_sm.mul(ym_tot);
            let ym_iv = Iv::pt(sm).mul(ym_tot);
            if cm_iv.lo > 0.0 && ym_iv.lo > 0.0 {
                let lcm = cm_iv.ln();
                let llm = Iv::pt(1.0).sub(Iv::pt(lm)).ln();
                let ulm1 = ome_hi.mul(llm).hi;
                let evm_raw = ev_pwl.iv_range(ym_iv.lo, ym_iv.hi);
                let cbm_iv = if has_ruin { omp.mul(evm_raw).add(pv_iv) } else { evm_raw };
                let vsm_lo = vs_pwl.iv_eval_pt(xm).lo;
                let bm = if cbm_iv.hi < 0.0 {
                    Iv::pt(b_lo)
                } else if cbm_iv.lo >= 0.0 {
                    Iv::pt(b_hi)
                } else {
                    b_iv_box
                };
                let bevm1 = bm.mul(cbm_iv).hi;

                let (yx0, yl0) = if !ak_mode || xR <= H_M {
                    (iv_df_dk_box(av, xL, xR, lL, lR), iv_df_dl_box(av, xL, xR, lL, lR))
                } else {
                    let fh0 = iv_f_a_pt(av, H_M, lL).lo;
                    let fh1 = iv_f_a_pt(av, H_M, lR).hi;
                    let yx_ak = Iv::raw(fh0, fh1).div(Iv::pt(H_M));
                    let dfh = iv_df_dl_box(av, H_M, H_M, lL, lR);
                    let rx = Iv::raw(xL, xR).div(Iv::pt(H_M));
                    (yx_ak, rx.mul(dfh))
                };
                let yx = Iv::pt(q_hi).add(yx0);

                let d_ev_raw = ev_pwl.iv_deriv_bounds(y0, y1);
                let d_ev = if has_ruin { omp.mul(d_ev_raw) } else { d_ev_raw };
                let d_vs = vs_pwl.iv_deriv_bounds(xL, xR);
                let beff = if cb_box.hi < 0.0 {
                    Iv::pt(b_lo)
                } else if cb_box.lo >= 0.0 {
                    Iv::pt(b_hi)
                } else {
                    b_iv_box
                };
                let bd_ev = beff.mul(d_ev);
                let sbd = Iv::raw(sL, sR).mul(bd_ev);
                let ybd = y_tot.mul(bd_ev);

                let om_lr = Iv::pt(1.0).sub(Iv::pt(lR));
                let om_ll = Iv::pt(1.0).sub(Iv::pt(lL));
                let dl_pen = Iv::raw(
                    ome_hi.div(om_ll).lo,
                    ome_hi.div(om_lr).hi,
                );
                let ec_s_range = |ec_iv: Iv| -> Iv {
                    Iv::raw(ec_iv.div(om_sL).lo, ec_iv.div(om_sR).hi)
                };

                let cross_c1 = c_min < 1.0 && c_max >= 1.0;
                let mut best_cent = f64::NEG_INFINITY;
                for pass_idx in 0..2 {
                    if pass_idx == 0 && !(c_min < 1.0) { continue; }
                    if pass_idx == 1 && !(c_max >= 1.0) { continue; }
                    let ec = if pass_idx == 0 { e_lo } else { e_hi };
                    let ec_iv = if cross_c1 { Iv::raw(e_lo, e_hi) } else { Iv::pt(ec) };
                    let ucm1 = Iv::pt(ec).mul(lcm).hi;
                    let hm1 = Iv::pt(ucm1).add(Iv::pt(ulm1)).add(Iv::pt(bevm1)).sub(Iv::pt(vsm_lo)).hi;

                    let a_iv = ec_iv.div(y_tot).add(sbd);
                    let hx_d = a_iv.mul(yx).sub(d_vs);
                    let hl_d = a_iv.mul(yl0).sub(dl_pen);
                    let hs_d = ybd.sub(ec_s_range(ec_iv));

                    let sx = Iv::pt(hx_d.max_abs()).mul(Iv::pt(hx)).hi;
                    let sl_e = Iv::pt(hl_d.max_abs()).mul(Iv::pt(hl)).hi;
                    let ss_e = Iv::pt(hs_d.max_abs()).mul(Iv::pt(hs)).hi;
                    let ub_ec = Iv::pt(hm1).add(Iv::pt(sx)).add(Iv::pt(sl_e)).add(Iv::pt(ss_e)).hi;
                    if ub_ec > best_cent { best_cent = ub_ec; }
                }
                if best_cent < box_ub { box_ub = best_cent; }
            }
        }
        if box_ub.is_nan() { return f64::INFINITY; }
        if box_ub > global_ub { global_ub = box_ub; }
    }
    global_ub
}

#[no_mangle]
pub extern "C" fn rs_verify_staying_barrier_bb_ext(
    ks_l_ptr: *const f64, lks_l_ptr: *const f64, vals_l_ptr: *const f64, slopes_l_ptr: *const f64,
    nk_l: usize, s_lo_l: f64, s_hi_l: f64,
    ks_e_ptr: *const f64, lks_e_ptr: *const f64, vals_e_ptr: *const f64, slopes_e_ptr: *const f64,
    nk_e: usize, s_lo_e: f64, s_hi_e: f64,
    b_m: f64, h_m: f64,
    a_hi: f64, q_hi: f64, b_lo: f64, b_hi: f64, e_lo: f64, e_hi: f64,
    p_ruin: f64, v_ruin: f64,
    tol: f64, max_iter: usize,
    ce_out: *mut f64, max_ce: usize,
) -> BbOut {
    let ks_l = unsafe { slice::from_raw_parts(ks_l_ptr, nk_l) };
    let lks_l = unsafe { slice::from_raw_parts(lks_l_ptr, nk_l) };
    let vals_l = unsafe { slice::from_raw_parts(vals_l_ptr, nk_l) };
    let slopes_l = unsafe { slice::from_raw_parts(slopes_l_ptr, nk_l - 1) };
    let b_lhs = Pwl::new(ks_l, lks_l, vals_l, slopes_l, s_lo_l, s_hi_l);

    let ks_e = unsafe { slice::from_raw_parts(ks_e_ptr, nk_e) };
    let lks_e = unsafe { slice::from_raw_parts(lks_e_ptr, nk_e) };
    let vals_e = unsafe { slice::from_raw_parts(vals_e_ptr, nk_e) };
    let slopes_e = unsafe { slice::from_raw_parts(slopes_e_ptr, nk_e - 1) };
    let b_ev = Pwl::new(ks_e, lks_e, vals_e, slopes_e, s_lo_e, s_hi_e);

    let omp = 1.0 - p_ruin;
    let pv = p_ruin * v_ruin;

    let mut xg = Vec::with_capacity(45);
    push_linspace(&mut xg, b_m, h_m, 45, true);
    let mut yg = Vec::with_capacity(45);
    push_linspace(&mut yg, b_m, h_m, 45, true);
    let mut lg = Vec::with_capacity(31);
    lg.push(0.0);
    push_linspace(&mut lg, 0.05, 0.999, 30, true);

    let bx_g: Vec<f64> = xg.iter().map(|&x| b_lhs.eval_f64(x)).collect();
    let by_term: Vec<f64> = yg.iter().map(|&y| {
        let cb = omp * b_ev.eval_f64(y) + pv;
        (if cb < 0.0 { b_lo } else { b_hi }) * cb
    }).collect();

    let mut best_lb = -1e9f64;
    let mut worst_pt = (b_m, b_m, 0.5);
    for (ix, &xv) in xg.iter().enumerate() {
        let bxv = bx_g[ix];
        for &lv in &lg {
            let y_tot = q_hi * xv + f_a(a_hi, xv, lv);
            let ll = (1.0 - lv).ln();
            for (iy, &yv) in yg.iter().enumerate() {
                let c = y_tot - yv;
                if c > 1e-15 {
                    let ec = if c < 1.0 { e_lo } else { e_hi };
                    let v = ec * c.ln() + (1.0 - e_hi) * ll + by_term[iy] - bxv;
                    if v > best_lb {
                        best_lb = v;
                        worst_pt = (xv, yv, lv);
                    }
                }
            }
        }
    }
    let mut target = if best_lb < -tol { (best_lb + tol).max(-2.0e-4) } else { best_lb + tol };
    let mut ces: Vec<[f64; 4]> = vec![[worst_pt.0, worst_pt.1, worst_pt.2, best_lb]];

    let mut xs_b = Vec::new();
    xs_b.push(b_m);
    for &kv in ks_l {
        if kv > b_m && kv < h_m { xs_b.push(kv); }
    }
    xs_b.push(h_m);
    push_linspace(&mut xs_b, b_m, h_m, 19, true);
    let xs_b = sorted_dedup(xs_b);

    let mut ys_b = Vec::new();
    ys_b.push(b_m);
    for &kv in ks_e {
        if kv > b_m && kv < h_m { ys_b.push(kv); }
    }
    ys_b.push(h_m);
    push_linspace(&mut ys_b, b_m, h_m, 19, true);
    let ys_b = sorted_dedup(ys_b);

    let ls_b = [0.0, 0.15, 0.35, 0.55, 0.72, 0.85, 0.94, 0.985, 0.998, 1.0];

    let cap = (xs_b.len() - 1) * (ys_b.len() - 1) * (ls_b.len() - 1);
    let mut bxL = Vec::with_capacity(cap); let mut bxR = Vec::with_capacity(cap);
    let mut byL = Vec::with_capacity(cap); let mut byR = Vec::with_capacity(cap);
    let mut bLL = Vec::with_capacity(cap); let mut bLR = Vec::with_capacity(cap);
    for ix in 0..xs_b.len() - 1 {
        for iy in 0..ys_b.len() - 1 {
            for il in 0..ls_b.len() - 1 {
                bxL.push(xs_b[ix]); bxR.push(xs_b[ix + 1]);
                byL.push(ys_b[iy]); byR.push(ys_b[iy + 1]);
                bLL.push(ls_b[il]); bLR.push(ls_b[il + 1]);
            }
        }
    }

    let mut leaf_xL = Vec::new(); let mut leaf_xR = Vec::new();
    let mut leaf_yL = Vec::new(); let mut leaf_yR = Vec::new();
    let mut leaf_LL = Vec::new(); let mut leaf_LR = Vec::new();
    let mut d_ub: Option<f64> = None;
    let mut last_max_ub = 1e9f64;

    for _it in 0..max_iter {
        let n = bxL.len();
        let mut nxL = Vec::new(); let mut nxR = Vec::new();
        let mut nyL = Vec::new(); let mut nyR = Vec::new();
        let mut nLL = Vec::new(); let mut nLR = Vec::new();
        let mut kept_ub = Vec::new();
        let mut best_k_lb = f64::NEG_INFINITY;
        let mut best_k_pt = (0.0, 0.0, 0.0);
        last_max_ub = f64::NEG_INFINITY;

        for i in 0..n {
            let xL = bxL[i]; let xR = bxR[i];
            let yL = byL[i]; let yR = byR[i];
            let lL = bLL[i]; let lR = bLR[i];
            let y_min = q_hi * xL + f_a(a_hi, xL, lL);
            let y_max = q_hi * xR + f_a(a_hi, xR, lR);
            let c_max = y_max - yL;
            let c_min = y_min - yR;
            let infeasible = c_max <= 1e-15;

            let mut ub = -1e9f64;
            if !infeasible {
                let ec_max = if c_max < 1.0 { e_lo } else { e_hi };
                let (bx_min, _) = b_lhs.range_f64(xL, xR);
                let (by_min, by_max) = b_ev.range_f64(yL, yR);
                let cb_min = omp * by_min + pv;
                let cb_max = omp * by_max + pv;
                let b_by_max = ((if cb_min < 0.0 { b_lo } else { b_hi }) * cb_min)
                    .max((if cb_max < 0.0 { b_lo } else { b_hi }) * cb_max);
                ub = ec_max * c_max.max(1e-300).ln() + (1.0 - e_hi) * (1.0 - lL).max(1e-300).ln() + b_by_max - bx_min;

                let xm = 0.5 * (xL + xR);
                let ym = 0.5 * (yL + yR);
                let lm = 0.5 * (lL + lR);
                let cm = q_hi * xm + f_a(a_hi, xm, lm) - ym;
                if lR < 1.0 && c_min > 1e-10 {
                    let hx = 0.5 * (xR - xL);
                    let hy = 0.5 * (yR - yL);
                    let hl = 0.5 * (lR - lL);
                    let (yx_lo0, yx_hi0) = prod_dy_dk_bounds_f64(a_hi, xL, xR, lL, lR, false);
                    let yx_lo = q_hi + yx_lo0; let yx_hi = q_hi + yx_hi0;
                    let (yl_lo, yl_hi) = prod_dy_dl_bounds_f64(a_hi, xL, xR, lL, lR, false);
                    let (dbx_lo, dbx_hi) = b_lhs.deriv_bounds_f64(xL, xR);
                    let (dby_lo0, dby_hi0) = b_ev.deriv_bounds_f64(yL, yR);
                    let dby_lo = omp * dby_lo0;
                    let dby_hi = omp * dby_hi0;
                    let bx_m = b_lhs.eval_f64(xm);
                    let cb_m = omp * b_ev.eval_f64(ym) + pv;
                    let b_lo_v = if cb_max < 0.0 { b_lo } else { b_hi };
                    let b_hi_v = if cb_min >= 0.0 { b_hi } else { b_lo };
                    let b_eff_lo = b_lo_v.min(b_hi_v);
                    let b_eff_hi = b_lo_v.max(b_hi_v);
                    let cross_c1 = c_min < 1.0 && c_max >= 1.0;
                    let mut best_eta_ub = -1e9f64;
                    let b_m_ec = if cb_m < 0.0 { b_lo } else { b_hi };
                    let inv_c_lo = 1.0 / c_max;
                    let inv_c_hi = 1.0 / c_min;
                    let bdby_lo = (b_eff_lo * dby_lo).min(b_eff_hi * dby_lo);
                    let bdby_hi = (b_eff_lo * dby_hi).max(b_eff_hi * dby_hi);
                    for pass_idx in 0..2 {
                        if pass_idx == 0 && !(c_min < 1.0) { continue; }
                        if pass_idx == 1 && !(c_max >= 1.0) { continue; }
                        let ec = if pass_idx == 0 { e_lo } else { e_hi };
                        let ec_lo = if cross_c1 { e_lo } else { ec };
                        let ec_hi = if cross_c1 { e_hi } else { ec };
                        let hm = ec * cm.ln() + (1.0 - e_hi) * (1.0 - lm).ln() + b_m_ec * cb_m - bx_m;
                        let dx_lo = ec_lo * inv_c_lo * yx_lo - dbx_hi;
                        let dx_hi = ec_hi * inv_c_hi * yx_hi - dbx_lo;
                        let dy_lo = -ec_hi * inv_c_hi + bdby_lo;
                        let dy_hi = -ec_lo * inv_c_lo + bdby_hi;
                        let dl_lo = ec_lo * inv_c_lo * yl_lo - (1.0 - e_hi) / (1.0 - lR);
                        let dl_hi = ec_hi * inv_c_hi * yl_hi - (1.0 - e_hi) / (1.0 - lL);
                        let ub_ec = hm
                            + dx_lo.abs().max(dx_hi.abs()) * hx
                            + dy_lo.abs().max(dy_hi.abs()) * hy
                            + dl_lo.abs().max(dl_hi.abs()) * hl;
                        if ub_ec > best_eta_ub { best_eta_ub = ub_ec; }
                    }
                    if best_eta_ub < ub { ub = best_eta_ub; }
                }
            }

            if ub > last_max_ub { last_max_ub = ub; }
            if ub > target {
                let xm = 0.5 * (xL + xR);
                let ym = 0.5 * (yL + yR);
                let lm = 0.5 * (lL + lR);
                if lR < 1.0 {
                    let cm = q_hi * xm + f_a(a_hi, xm, lm) - ym;
                    if cm > 1e-15 {
                        let ecm = if cm < 1.0 { e_lo } else { e_hi };
                        let cbm = omp * b_ev.eval_f64(ym) + pv;
                        let lb_v = ecm * cm.ln() + (1.0 - e_hi) * (1.0 - lm).ln()
                            + (if cbm < 0.0 { b_lo } else { b_hi }) * cbm - b_lhs.eval_f64(xm);
                        if lb_v > best_k_lb {
                            best_k_lb = lb_v;
                            best_k_pt = (xm, ym, lm);
                        }
                    }
                }
                nxL.push(xL); nxR.push(xR);
                nyL.push(yL); nyR.push(yR);
                nLL.push(lL); nLR.push(lR);
                kept_ub.push(ub);
            } else {
                leaf_xL.push(xL); leaf_xR.push(xR);
                leaf_yL.push(yL); leaf_yR.push(yR);
                leaf_LL.push(lL); leaf_LR.push(lR);
            }
        }

        if nxL.is_empty() {
            d_ub = Some(target);
            break;
        }
        if best_k_lb > best_lb {
            best_lb = best_k_lb;
            target = if best_lb < -tol { (best_lb + tol).max(-2.0e-4) } else { best_lb + tol };
            ces.push([best_k_pt.0, best_k_pt.1, best_k_pt.2, best_lb]);
        }
        if nxL.len() > 250_000 {
            leaf_xL.extend_from_slice(&nxL); leaf_xR.extend_from_slice(&nxR);
            leaf_yL.extend_from_slice(&nyL); leaf_yR.extend_from_slice(&nyR);
            leaf_LL.extend_from_slice(&nLL); leaf_LR.extend_from_slice(&nLR);
            let max_kept = kept_ub.iter().copied().fold(f64::NEG_INFINITY, f64::max);
            d_ub = Some(max_kept);
            break;
        }

        bxL.clear(); bxR.clear(); byL.clear(); byR.clear(); bLL.clear(); bLR.clear();
        for i in 0..nxL.len() {
            let xL = nxL[i]; let xR = nxR[i];
            let yL = nyL[i]; let yR = nyR[i];
            let lL = nLL[i]; let lR = nLR[i];
            let xm = 0.5 * (xL + xR); let ym = 0.5 * (yL + yR); let lm = 0.5 * (lL + lR);
            let ex = (xR - xL) / xL;
            let ey = (yR - yL) / yL;
            let els = 0.25 * (lR - lL) / (1.0 - lR).max(1e-3);
            if ex >= ey && ex >= els {
                bxL.push(xL); bxR.push(xm); byL.push(yL); byR.push(yR); bLL.push(lL); bLR.push(lR);
                bxL.push(xm); bxR.push(xR); byL.push(yL); byR.push(yR); bLL.push(lL); bLR.push(lR);
            } else if ey >= els {
                bxL.push(xL); bxR.push(xR); byL.push(yL); byR.push(ym); bLL.push(lL); bLR.push(lR);
                bxL.push(xL); bxR.push(xR); byL.push(ym); byR.push(yR); bLL.push(lL); bLR.push(lR);
            } else {
                bxL.push(xL); bxR.push(xR); byL.push(yL); byR.push(yR); bLL.push(lL); bLR.push(lm);
                bxL.push(xL); bxR.push(xR); byL.push(yL); byR.push(yR); bLL.push(lm); bLR.push(lR);
            }
        }
        if _it + 1 == max_iter {
            let mut pairs: Vec<(usize, f64)> = kept_ub.iter().copied().enumerate().collect();
            pairs.sort_by(|a, b| b.1.total_cmp(&a.1));
            for &(idx, uv) in pairs.iter().take(8) {
                ces.push([0.5 * (nxL[idx] + nxR[idx]), 0.5 * (nyL[idx] + nyR[idx]), 0.5 * (nLL[idx] + nLR[idx]), uv]);
            }
            if leaf_xL.is_empty() {
                leaf_xL = nxL; leaf_xR = nxR;
                leaf_yL = nyL; leaf_yR = nyR;
                leaf_LL = nLL; leaf_LR = nLR;
            } else {
                leaf_xL.extend_from_slice(&nxL); leaf_xR.extend_from_slice(&nxR);
                leaf_yL.extend_from_slice(&nyL); leaf_yR.extend_from_slice(&nyR);
                leaf_LL.extend_from_slice(&nLL); leaf_LR.extend_from_slice(&nLR);
            }
            let max_kept = kept_ub.iter().copied().fold(f64::NEG_INFINITY, f64::max);
            d_ub = Some(max_kept);
        }
    }

    let d_ub_v = d_ub.unwrap_or(last_max_ub);
    let d_ub_iv = audit_staying_boxes_rs(
        &b_lhs, &b_ev, &leaf_xL, &leaf_xR, &leaf_yL, &leaf_yR, &leaf_LL, &leaf_LR,
        a_hi, q_hi, b_lo, b_hi, e_lo, e_hi, p_ruin, v_ruin,
    );
    let iv_cert = d_ub_iv <= 0.0;
    let cert = d_ub_v <= 0.0 && iv_cert;

    let n_write = ces.len().min(max_ce);
    if !ce_out.is_null() && n_write > 0 {
        let out_slice = unsafe { slice::from_raw_parts_mut(ce_out, n_write * 4) };
        for (i, c) in ces.iter().take(n_write).enumerate() {
            out_slice[4 * i] = c[0];
            out_slice[4 * i + 1] = c[1];
            out_slice[4 * i + 2] = c[2];
            out_slice[4 * i + 3] = c[3];
        }
    }

    BbOut {
        certified: if cert { 1 } else { 0 },
        iv_certified: if iv_cert { 1 } else { 0 },
        d_ub: d_ub_v,
        d_ub_iv,
        d_lb: best_lb,
        leaf_count: leaf_xL.len(),
        n_ce: n_write,
    }
}

#[no_mangle]
pub extern "C" fn rs_verify_staying_barrier_bb(
    ks_ptr: *const f64, lks_ptr: *const f64, vals_ptr: *const f64, slopes_ptr: *const f64,
    nk: usize, s_lo: f64, s_hi: f64,
    a_hi: f64, q_hi: f64, b_lo: f64, b_hi: f64, e_lo: f64, e_hi: f64,
    tol: f64, max_iter: usize,
    ce_out: *mut f64, max_ce: usize,
) -> BbOut {
    rs_verify_staying_barrier_bb_ext(
        ks_ptr, lks_ptr, vals_ptr, slopes_ptr, nk, s_lo, s_hi,
        ks_ptr, lks_ptr, vals_ptr, slopes_ptr, nk, s_lo, s_hi,
        B_M, H_M, a_hi, q_hi, b_lo, b_hi, e_lo, e_hi, 0.0, 0.0,
        tol, max_iter, ce_out, max_ce,
    )
}

#[no_mangle]
pub extern "C" fn rs_verify_super_barrier_bb_ext(
    ks_s_ptr: *const f64, lks_s_ptr: *const f64, vals_s_ptr: *const f64, slopes_s_ptr: *const f64,
    nk_s: usize, s_lo_s: f64, s_hi_s: f64,
    ks_e_ptr: *const f64, lks_e_ptr: *const f64, vals_e_ptr: *const f64, slopes_e_ptr: *const f64,
    nk_e: usize, s_lo_e: f64, s_hi_e: f64,
    av: f64, q_hi: f64, b_lo: f64, b_hi: f64, e_lo: f64, e_hi: f64,
    p_ruin: f64, v_ruin: f64, h_safe: f64,
    tail_max: f64, tol: f64, ak_mode_i: i32, max_iter: usize, max_boxes: usize,
    ce_out: *mut f64, max_ce: usize,
) -> BbOut {
    let ks_s = unsafe { slice::from_raw_parts(ks_s_ptr, nk_s) };
    let lks_s = unsafe { slice::from_raw_parts(lks_s_ptr, nk_s) };
    let vals_s = unsafe { slice::from_raw_parts(vals_s_ptr, nk_s) };
    let slopes_s = unsafe { slice::from_raw_parts(slopes_s_ptr, nk_s - 1) };
    let vs_pwl = Pwl::new(ks_s, lks_s, vals_s, slopes_s, s_lo_s, s_hi_s);

    let ks_e = unsafe { slice::from_raw_parts(ks_e_ptr, nk_e) };
    let lks_e = unsafe { slice::from_raw_parts(lks_e_ptr, nk_e) };
    let vals_e = unsafe { slice::from_raw_parts(vals_e_ptr, nk_e) };
    let slopes_e = unsafe { slice::from_raw_parts(slopes_e_ptr, nk_e - 1) };
    let ev_pwl = Pwl::new(ks_e, lks_e, vals_e, slopes_e, s_lo_e, s_hi_e);

    let ak_mode = ak_mode_i != 0;
    let x_lo = ks_s[0];
    let x_cut = ks_s[nk_s - 1];
    let omp = 1.0 - p_ruin;
    let pv = p_ruin * v_ruin;

    // Grid search lower bound
    let mut xg = Vec::with_capacity(64 + nk_s);
    push_geomspace(&mut xg, x_lo, x_cut, 64);
    xg.extend_from_slice(ks_s);
    let xg = sorted_dedup(xg);
    let mut lg = Vec::with_capacity(25);
    lg.push(0.0);
    push_geomspace(&mut lg, 1e-5, 0.999, 24);
    let mut sg = Vec::with_capacity(24);
    push_linspace(&mut sg, 0.05, 0.998, 24, true);

    let mut best_lb = -1e18f64;
    let mut worst_pt = (x_lo, 0.0, 0.5);
    for &xv in &xg {
        let vsx = vs_pwl.eval_f64(xv);
        let xr = p_ruin > 0.0 && xv < h_safe;
        for &lv in &lg {
            let y_tot = q_hi * xv + prod_y_f64(av, xv, lv, ak_mode);
            let ll = (1.0 - lv).ln();
            for &sv in &sg {
                let c = y_tot * (1.0 - sv);
                let ec = if c < 1.0 { e_lo } else { e_hi };
                let ev_raw = ev_pwl.eval_f64(y_tot * sv);
                let cb = if xr { omp * ev_raw + pv } else { ev_raw };
                let bv = if cb < 0.0 { b_lo } else { b_hi };
                let v = ec * c.ln() + (1.0 - e_hi) * ll + bv * cb - vsx;
                if v > best_lb {
                    best_lb = v;
                    worst_pt = (xv, lv, sv);
                }
            }
        }
    }
    if nk_s > 1 {
        let lms = [0.0, 0.37, 0.50, 0.62, 0.72, 0.85];
        let sms = [0.82, 0.90, 0.955, 0.985, 0.9979];
        for i in 0..nk_s - 1 {
            let xm = (ks_s[i] * ks_s[i + 1]).sqrt();
            let vsx = vs_pwl.eval_f64(xm);
            let xr = p_ruin > 0.0 && xm < h_safe;
            for &lv in &lms {
                let y_tot = q_hi * xm + prod_y_f64(av, xm, lv, ak_mode);
                let ll = (1.0 - lv).ln();
                for &sv in &sms {
                    let c = (y_tot * (1.0 - sv)).max(1e-300);
                    let ec = if c < 1.0 { e_lo } else { e_hi };
                    let ev_raw = ev_pwl.eval_f64(y_tot * sv);
                    let cb = if xr { omp * ev_raw + pv } else { ev_raw };
                    let bv = if cb < 0.0 { b_lo } else { b_hi };
                    let v = ec * c.ln() + (1.0 - e_hi) * ll + bv * cb - vsx;
                    if v > best_lb {
                        best_lb = v;
                        worst_pt = (xm, lv, sv);
                    }
                }
            }
        }
    }
    best_lb = best_lb.max(tail_max);
    let mut target = if best_lb < -tol { (best_lb + tol).max(-1.0e-4) } else { best_lb + tol };
    let mut ces: Vec<[f64; 4]> = vec![[worst_pt.0, worst_pt.1, worst_pt.2, best_lb]];

    // Build initial 3D grid
    let stride = (nk_s / 80).max(1);
    let mut xs_b = Vec::with_capacity(28 + nk_s + 4);
    push_geomspace(&mut xs_b, x_lo, x_cut, 28);
    for i in (0..nk_s).step_by(stride) {
        xs_b.push(ks_s[i]);
    }
    for &kv in ks_s {
        if kv >= 0.0008 && kv <= 0.006 {
            xs_b.push(kv);
        }
    }
    xs_b.push(x_cut);
    if ak_mode {
        xs_b.push(H_M);
    }
    if p_ruin > 0.0 && h_safe > x_lo && h_safe < x_cut {
        xs_b.push(h_safe);
    }
    let xs_b = sorted_dedup(xs_b);

    let mut ls_b = vec![0.0, 0.2, 0.5, 0.7];
    push_linspace(&mut ls_b, 0.8, 0.99, 6, false);
    ls_b.extend_from_slice(&[0.99, 0.999, 1.0]);

    let mut ss_b = vec![0.0, 0.3, 0.65];
    push_linspace(&mut ss_b, 0.75, 0.99, 8, false);
    ss_b.extend_from_slice(&[0.99, 0.996, 0.998, 0.999, 1.0]);

    let cap = (xs_b.len() - 1) * (ls_b.len() - 1) * (ss_b.len() - 1);
    let mut bxL = Vec::with_capacity(cap); let mut bxR = Vec::with_capacity(cap);
    let mut bLL = Vec::with_capacity(cap); let mut bLR = Vec::with_capacity(cap);
    let mut bsL = Vec::with_capacity(cap); let mut bsR = Vec::with_capacity(cap);
    for ix in 0..xs_b.len() - 1 {
        for il in 0..ls_b.len() - 1 {
            for is in 0..ss_b.len() - 1 {
                bxL.push(xs_b[ix]); bxR.push(xs_b[ix + 1]);
                bLL.push(ls_b[il]); bLR.push(ls_b[il + 1]);
                bsL.push(ss_b[is]); bsR.push(ss_b[is + 1]);
            }
        }
    }

    let mut leaf_xL = Vec::new(); let mut leaf_xR = Vec::new();
    let mut leaf_LL = Vec::new(); let mut leaf_LR = Vec::new();
    let mut leaf_sL = Vec::new(); let mut leaf_sR = Vec::new();
    let mut d_ub: Option<f64> = None;
    let max_boxes_eff = if ak_mode { max_boxes.max(2_000_000) } else { max_boxes };
    let mut last_kept_max = f64::NEG_INFINITY;

    for _it in 0..max_iter {
        let n = bxL.len();
        let mut nxL = Vec::new(); let mut nxR = Vec::new();
        let mut nLL = Vec::new(); let mut nLR = Vec::new();
        let mut nsL = Vec::new(); let mut nsR = Vec::new();
        let mut n_ex = Vec::new(); let mut n_el = Vec::new(); let mut n_es = Vec::new();
        let mut kept_ub = Vec::new();
        let mut lb_cand: Vec<(f64, f64, f64, f64)> = Vec::new();

        for i in 0..n {
            let xL = bxL[i]; let xR = bxR[i];
            let lL = bLL[i]; let lR = bLR[i];
            let sL = bsL[i]; let sR = bsR[i];
            let has_ruin = p_ruin > 0.0 && xR <= h_safe;
            let ruin_split_ok = p_ruin == 0.0 || xR <= h_safe || xL >= h_safe;

            let y_min = q_hi * xL + prod_y_f64(av, xL, lL, ak_mode);
            let y_max = q_hi * xR + prod_y_f64(av, xR, lR, ak_mode);
            let c_max = ((1.0 - sL) * y_max).max(1e-300);
            let ec_max = if c_max < 1.0 { e_lo } else { e_hi };
            let (vs_min, _) = vs_pwl.range_f64(xL, xR);
            let (ev_min, ev_max) = ev_pwl.range_f64(sL * y_min, sR * y_max);
            let cb_min = if has_ruin { omp * ev_min + pv } else { ev_min };
            let cb_max = if has_ruin { omp * ev_max + pv } else { ev_max };
            let b_ev_max = ((if cb_min < 0.0 { b_lo } else { b_hi }) * cb_min)
                .max((if cb_max < 0.0 { b_lo } else { b_hi }) * cb_max);
            let ub_mono = (if sL >= 1.0 { -1e9 } else { ec_max * c_max.ln() })
                + (1.0 - e_hi) * (1.0 - lL).max(1e-300).ln()
                + (if sR <= 0.0 { -1e9 } else { b_ev_max })
                - vs_min;

            let xm = 0.5 * (xL + xR);
            let lm = 0.5 * (lL + lR);
            let sm = 0.5 * (sL + sR);
            let hx = 0.5 * (xR - xL);
            let hl = 0.5 * (lR - lL);
            let hs = 0.5 * (sR - sL);
            let c_min = ((1.0 - sR) * y_min).max(1e-300);

            let valid_c = ruin_split_ok && ub_mono > target && lR < 1.0 && sL > 0.0 && sR < 1.0 && c_min > 1e-30
                && (!ak_mode || xR <= H_M || xL >= H_M);

            let mut ub = ub_mono;
            let mut ex = (xR - xL) / xL;
            let mut e_l_err = hl;
            let mut es = hs;

            if valid_c {
                let ym_tot = q_hi * xm + prod_y_f64(av, xm, lm, ak_mode);
                let cm = (1.0 - sm) * ym_tot;
                let y_min_k = sL * y_min;
                let y_max_k = sR * y_max;
                let (yx_lo0, yx_hi0) = prod_dy_dk_bounds_f64(av, xL, xR, lL, lR, ak_mode);
                let yx_lo = q_hi + yx_lo0; let yx_hi = q_hi + yx_hi0;
                let (yl_lo, yl_hi) = prod_dy_dl_bounds_f64(av, xL, xR, lL, lR, ak_mode);
                let (dev_lo0, dev_hi0) = ev_pwl.deriv_bounds_f64(y_min_k, y_max_k);
                let dev_lo = if has_ruin { omp * dev_lo0 } else { dev_lo0 };
                let dev_hi = if has_ruin { omp * dev_hi0 } else { dev_hi0 };
                let (dvs_lo, dvs_hi) = vs_pwl.deriv_bounds_f64(xL, xR);
                let b_lo_v = if cb_max < 0.0 { b_lo } else { b_hi };
                let b_hi_v = if cb_min >= 0.0 { b_hi } else { b_lo };
                let b_eff_lo = b_lo_v.min(b_hi_v);
                let b_eff_hi = b_lo_v.max(b_hi_v);
                let bdev_lo = (b_eff_lo * dev_lo).min(b_eff_hi * dev_lo);
                let bdev_hi = (b_eff_lo * dev_hi).max(b_eff_hi * dev_hi);

                let ev_m_raw = ev_pwl.eval_f64(sm * ym_tot);
                let cb_m = if has_ruin { omp * ev_m_raw + pv } else { ev_m_raw };
                let vs_m = vs_pwl.eval_f64(xm);
                let bm = if cb_m < 0.0 { b_lo } else { b_hi };
                let cross_c1 = c_min < 1.0 && c_max >= 1.0;

                let mut best_eta_ub = -1e9f64;
                let mut ex_v = 0.0f64;
                let mut el_v = 0.0f64;
                let mut es_v = 0.0f64;
                for pass_idx in 0..2 {
                    if pass_idx == 0 && !(c_min < 1.0) { continue; }
                    if pass_idx == 1 && !(c_max >= 1.0) { continue; }
                    let ec = if pass_idx == 0 { e_lo } else { e_hi };
                    let ec_lo = if cross_c1 { e_lo } else { ec };
                    let ec_hi = if cross_c1 { e_hi } else { ec };
                    let hm = ec * cm.ln() + (1.0 - e_hi) * (1.0 - lm).ln() + bm * cb_m - vs_m;
                    let a_lo_t = ec_lo / y_max + (sL * bdev_lo).min(sR * bdev_lo);
                    let a_hi_t = ec_hi / y_min + (sL * bdev_hi).max(sR * bdev_hi);
                    let p1x = a_lo_t * yx_lo; let p2x = a_lo_t * yx_hi; let p3x = a_hi_t * yx_lo; let p4x = a_hi_t * yx_hi;
                    let hx_lo = p1x.min(p2x).min(p3x.min(p4x)) - dvs_hi;
                    let hx_hi = p1x.max(p2x).max(p3x.max(p4x)) - dvs_lo;
                    let p1l = a_lo_t * yl_lo; let p2l = a_lo_t * yl_hi; let p3l = a_hi_t * yl_lo; let p4l = a_hi_t * yl_hi;
                    let hl_lo = p1l.min(p2l).min(p3l.min(p4l)) - (1.0 - e_hi) / (1.0 - lR);
                    let hl_hi = p1l.max(p2l).max(p3l.max(p4l)) - (1.0 - e_hi) / (1.0 - lL);
                    let p1s = y_min * bdev_lo; let p2s = y_min * bdev_hi; let p3s = y_max * bdev_lo; let p4s = y_max * bdev_hi;
                    let hs_lo = -ec_hi / (1.0 - sR) + p1s.min(p2s).min(p3s.min(p4s));
                    let hs_hi = -ec_lo / (1.0 - sL) + p1s.max(p2s).max(p3s.max(p4s));
                    let sx_e = hx_lo.abs().max(hx_hi.abs()) * hx;
                    let sl_e = hl_lo.abs().max(hl_hi.abs()) * hl;
                    let ss_e = hs_lo.abs().max(hs_hi.abs()) * hs;
                    let ub_ec = hm + sx_e + sl_e + ss_e;
                    if ub_ec > best_eta_ub { best_eta_ub = ub_ec; }
                    ex_v = ex_v.max(sx_e);
                    el_v = el_v.max(sl_e);
                    es_v = es_v.max(ss_e);
                }
                if best_eta_ub < ub { ub = best_eta_ub; }
                ex = ex_v; e_l_err = el_v; es = es_v;
            }

            if ub > target {
                if lR < 1.0 && sL > 0.0 && sR < 1.0 {
                    let ym_k = q_hi * xm + prod_y_f64(av, xm, lm, ak_mode);
                    let cm_k = (1.0 - sm) * ym_k;
                    if cm_k > 1e-30 {
                        let ecm = if cm_k < 1.0 { e_lo } else { e_hi };
                        let evk_raw = ev_pwl.eval_f64(sm * ym_k);
                        let cbk = if p_ruin > 0.0 && xm < h_safe { omp * evk_raw + pv } else { evk_raw };
                        let bk = if cbk < 0.0 { b_lo } else { b_hi };
                        let lbv = ecm * cm_k.ln() + (1.0 - e_hi) * (1.0 - lm).ln() + bk * cbk - vs_pwl.eval_f64(xm);
                        lb_cand.push((lbv, xm, lm, sm));
                    }
                }
                nxL.push(xL); nxR.push(xR);
                nLL.push(lL); nLR.push(lR);
                nsL.push(sL); nsR.push(sR);
                n_ex.push(ex); n_el.push(e_l_err); n_es.push(es);
                kept_ub.push(ub);
            } else {
                leaf_xL.push(xL); leaf_xR.push(xR);
                leaf_LL.push(lL); leaf_LR.push(lR);
                leaf_sL.push(sL); leaf_sR.push(sR);
            }
        }

        if nxL.is_empty() {
            d_ub = Some(target);
            break;
        }

        if !lb_cand.is_empty() {
            let mut ib = 0usize;
            for j in 1..lb_cand.len() {
                if lb_cand[j].0 > lb_cand[ib].0 { ib = j; }
            }
            if lb_cand[ib].0 > best_lb {
                best_lb = lb_cand[ib].0;
                target = if best_lb < -tol { (best_lb + tol).max(-1.0e-4) } else { best_lb + tol };
                ces.push([lb_cand[ib].1, lb_cand[ib].2, lb_cand[ib].3, best_lb]);
            }
            if best_lb > 0.0 && ces.len() < 40 {
                lb_cand.sort_by(|a, b| b.0.total_cmp(&a.0));
                for c in lb_cand.iter().take(4) {
                    if c.0 > 0.0 { ces.push([c.1, c.2, c.3, c.0]); }
                }
            }
        }

        let n_keep = nxL.len();
        last_kept_max = kept_ub.iter().copied().fold(f64::NEG_INFINITY, f64::max);

        if n_keep > max_boxes_eff || _it + 1 == max_iter {
            let mut order: Vec<usize> = (0..n_keep).collect();
            order.sort_by(|&a, &b| kept_ub[b].total_cmp(&kept_ub[a]));
            for &idx in order.iter().take(24) {
                ces.push([0.5 * (nxL[idx] + nxR[idx]), 0.5 * (nLL[idx] + nLR[idx]), 0.5 * (nsL[idx] + nsR[idx]), kept_ub[idx]]);
            }
            leaf_xL.extend_from_slice(&nxL); leaf_xR.extend_from_slice(&nxR);
            leaf_LL.extend_from_slice(&nLL); leaf_LR.extend_from_slice(&nLR);
            leaf_sL.extend_from_slice(&nsL); leaf_sR.extend_from_slice(&nsR);
            d_ub = Some(last_kept_max.max(tail_max));
            break;
        }

        bxL.clear(); bxR.clear(); bLL.clear(); bLR.clear(); bsL.clear(); bsR.clear();
        if n_keep <= 800 {
            bxL.reserve(n_keep * 8); bxR.reserve(n_keep * 8);
            bLL.reserve(n_keep * 8); bLR.reserve(n_keep * 8);
            bsL.reserve(n_keep * 8); bsR.reserve(n_keep * 8);
            for i in 0..n_keep {
                let xL = nxL[i]; let xR = nxR[i]; let xm = 0.5 * (xL + xR);
                let lL = nLL[i]; let lR = nLR[i]; let lm = 0.5 * (lL + lR);
                let sL = nsL[i]; let sR = nsR[i]; let sm = 0.5 * (sL + sR);
                for &(ax0, ax1) in &[(xL, xm), (xm, xR)] {
                    for &(al0, al1) in &[(lL, lm), (lm, lR)] {
                        for &(as0, as1) in &[(sL, sm), (sm, sR)] {
                            bxL.push(ax0); bxR.push(ax1);
                            bLL.push(al0); bLR.push(al1);
                            bsL.push(as0); bsR.push(as1);
                        }
                    }
                }
            }
        } else {
            bxL.reserve(n_keep * 2); bxR.reserve(n_keep * 2);
            bLL.reserve(n_keep * 2); bLR.reserve(n_keep * 2);
            bsL.reserve(n_keep * 2); bsR.reserve(n_keep * 2);
            for i in 0..n_keep {
                let xL = nxL[i]; let xR = nxR[i]; let xm = 0.5 * (xL + xR);
                let lL = nLL[i]; let lR = nLR[i]; let lm = 0.5 * (lL + lR);
                let sL = nsL[i]; let sR = nsR[i]; let sm = 0.5 * (sL + sR);
                if n_ex[i] >= n_el[i] && n_ex[i] >= n_es[i] {
                    bxL.push(xL); bxR.push(xm); bLL.push(lL); bLR.push(lR); bsL.push(sL); bsR.push(sR);
                    bxL.push(xm); bxR.push(xR); bLL.push(lL); bLR.push(lR); bsL.push(sL); bsR.push(sR);
                } else if n_el[i] >= n_es[i] {
                    bxL.push(xL); bxR.push(xR); bLL.push(lL); bLR.push(lm); bsL.push(sL); bsR.push(sR);
                    bxL.push(xL); bxR.push(xR); bLL.push(lm); bLR.push(lR); bsL.push(sL); bsR.push(sR);
                } else {
                    bxL.push(xL); bxR.push(xR); bLL.push(lL); bLR.push(lR); bsL.push(sL); bsR.push(sm);
                    bxL.push(xL); bxR.push(xR); bLL.push(lL); bLR.push(lR); bsL.push(sm); bsR.push(sR);
                }
            }
        }
    }

    let d_ub_v = d_ub.unwrap_or(last_kept_max).max(tail_max);
    let boxes_iv_hi = audit_super_boxes_rs(
        &vs_pwl, &ev_pwl, &leaf_xL, &leaf_xR, &leaf_LL, &leaf_LR, &leaf_sL, &leaf_sR,
        av, q_hi, b_lo, b_hi, e_lo, e_hi, ak_mode, p_ruin, v_ruin, h_safe,
    );
    let d_ub_iv = tail_max.max(boxes_iv_hi);
    let iv_cert = d_ub_iv <= 0.0;
    let cert = d_ub_v <= 0.0 && iv_cert;

    let n_write = ces.len().min(max_ce);
    if !ce_out.is_null() && n_write > 0 {
        let out_slice = unsafe { slice::from_raw_parts_mut(ce_out, n_write * 4) };
        for (i, c) in ces.iter().take(n_write).enumerate() {
            out_slice[4 * i] = c[0];
            out_slice[4 * i + 1] = c[1];
            out_slice[4 * i + 2] = c[2];
            out_slice[4 * i + 3] = c[3];
        }
    }

    BbOut {
        certified: if cert { 1 } else { 0 },
        iv_certified: if iv_cert { 1 } else { 0 },
        d_ub: d_ub_v,
        d_ub_iv,
        d_lb: best_lb,
        leaf_count: leaf_xL.len(),
        n_ce: n_write,
    }
}

#[no_mangle]
pub extern "C" fn rs_verify_super_barrier_bb(
    ks_s_ptr: *const f64, lks_s_ptr: *const f64, vals_s_ptr: *const f64, slopes_s_ptr: *const f64,
    nk_s: usize, s_lo_s: f64, s_hi_s: f64,
    ks_e_ptr: *const f64, lks_e_ptr: *const f64, vals_e_ptr: *const f64, slopes_e_ptr: *const f64,
    nk_e: usize, s_lo_e: f64, s_hi_e: f64,
    av: f64, q_hi: f64, b_lo: f64, b_hi: f64, e_lo: f64, e_hi: f64,
    tail_max: f64, tol: f64, ak_mode_i: i32, max_iter: usize, max_boxes: usize,
    ce_out: *mut f64, max_ce: usize,
) -> BbOut {
    rs_verify_super_barrier_bb_ext(
        ks_s_ptr, lks_s_ptr, vals_s_ptr, slopes_s_ptr, nk_s, s_lo_s, s_hi_s,
        ks_e_ptr, lks_e_ptr, vals_e_ptr, slopes_e_ptr, nk_e, s_lo_e, s_hi_e,
        av, q_hi, b_lo, b_hi, e_lo, e_hi, 0.0, 0.0, H_M,
        tail_max, tol, ak_mode_i, max_iter, max_boxes, ce_out, max_ce,
    )
}

#[inline(always)]
fn iv_f_a_iv(a: Iv, k: Iv, l: Iv) -> Iv {
    if l.hi <= 0.0 {
        return Iv::pt(0.0);
    }
    let num = Iv::pt(2.0).mul(k).mul(l);
    let den = k.add(l);
    a.mul(num.div(den).pow32())
}

#[inline(always)]
fn iv_e_plus_exact(a: f64, q: f64, k: Iv, a_exit: f64, l0: f64, e_lo: f64, e_hi: f64, ak_mode: bool) -> Iv {
    let a_iv = Iv::pt(a);
    let q_iv = Iv::pt(q);
    let l0_iv = Iv::pt(l0);
    let om_l0 = Iv::pt(1.0).sub(l0_iv);
    let two_32 = Iv::pt(2.0).pow32();
    let k52 = k.pow52();
    let l0_s = l0_iv.sqrt();
    let (t, s) = if !ak_mode || k.hi <= H_M {
        let kp_l52 = k.add(l0_iv).pow52();
        let t_v = Iv::pt(1.5).mul(a_iv).mul(two_32).mul(k52).mul(l0_s).div(kp_l52);
        let s_v = q_iv.mul(k).add(iv_f_a_iv(a_iv, k, l0_iv)).add(om_l0.mul(t_v));
        (t_v, s_v)
    } else {
        let h_iv = Iv::pt(H_M);
        let t_h = Iv::pt(1.5).mul(a_iv).mul(two_32).mul(h_iv.pow52()).mul(l0_s).div(h_iv.add(l0_iv).pow52());
        let f_h = iv_f_a_iv(a_iv, h_iv, l0_iv);
        let r = k.div(h_iv);
        let t_v = r.mul(t_h);
        let s_v = q_iv.mul(k).add(r.mul(f_h)).add(om_l0.mul(t_v));
        (t_v, s_v)
    };
    let c_sup = s.sub(Iv::pt(a_exit));
    let mut best_lo = f64::NEG_INFINITY;
    let mut best_hi = f64::NEG_INFINITY;
    for &ev in &[e_lo, e_hi] {
        let eta = Iv::pt(ev);
        let om_raw = Iv::pt(1.0).sub(eta).mul(c_sup).div(t);
        let om_l = Iv::raw(om_raw.lo.min(1.0), om_raw.hi.min(1.0));
        let c_opt = c_sup.sub(t.mul(om_l));
        let val = eta.mul(c_opt.ln()).add(Iv::pt(1.0).sub(eta).mul(om_l.ln()));
        if val.lo > best_lo { best_lo = val.lo; }
        if val.hi > best_hi { best_hi = val.hi; }
    }
    Iv::raw(best_lo, best_hi)
}

#[inline(always)]
fn iv_de_plus_dk(a: f64, q: f64, k: Iv, a_exit: f64, l0: f64, e_lo: f64, e_hi: f64, ak_mode: bool) -> Iv {
    let a_iv = Iv::pt(a);
    let q_iv = Iv::pt(q);
    let l0_iv = Iv::pt(l0);
    let om_l0 = Iv::pt(1.0).sub(l0_iv);
    let two_32 = Iv::pt(2.0).pow32();
    let l0_s = l0_iv.sqrt();
    let c15 = Iv::pt(1.5).mul(a_iv).mul(two_32);

    if !ak_mode || k.hi <= H_M {
        let t_at = |kp: f64| -> Iv {
            let k_pt = Iv::pt(kp);
            c15.mul(k_pt.pow52()).mul(l0_s).div(k_pt.add(l0_iv).pow52())
        };
        let t_at_lo = t_at(k.lo);
        let t_at_hi = t_at(k.hi);
        let t_iv = Iv::raw(t_at_lo.lo, t_at_hi.hi);
        let s_at_lo = q_iv.mul(Iv::pt(k.lo)).add(iv_f_a_iv(a_iv, Iv::pt(k.lo), l0_iv)).add(om_l0.mul(t_at_lo));
        let s_at_hi = q_iv.mul(Iv::pt(k.hi)).add(iv_f_a_iv(a_iv, Iv::pt(k.hi), l0_iv)).add(om_l0.mul(t_at_hi));
        let c_sup = Iv::raw(s_at_lo.sub(Iv::pt(a_exit)).lo, s_at_hi.sub(Iv::pt(a_exit)).hi);

        let t_prime = |kp: f64| -> Iv {
            let k_pt = Iv::pt(kp);
            t_at(kp).mul(Iv::pt(2.5).mul(l0_iv)).div(k_pt.mul(k_pt.add(l0_iv)))
        };
        let tp_a = t_prime(k.lo);
        let tp_b = t_prime(k.hi);
        let tp_lo = tp_a.lo.min(tp_b.lo);
        let mut tp_hi = tp_a.hi.max(tp_b.hi);
        let kp_tp = 0.75 * l0;
        if k.lo <= kp_tp && kp_tp <= k.hi {
            tp_hi = tp_hi.max(t_prime(kp_tp).hi);
        }
        let tp_iv = Iv::raw(tp_lo, tp_hi);
        let dfk_iv = iv_df_dk_box(a, k.lo, k.hi, l0, l0);
        let sp_iv = q_iv.add(dfk_iv).add(om_l0.mul(tp_iv));

        let ome_lo = Iv::pt(1.0).sub(Iv::pt(e_lo));
        let ome_hi = Iv::pt(1.0).sub(Iv::pt(e_hi));
        let om_max = ome_lo.mul(c_sup).div(t_iv);
        if om_max.hi < 1.0 {
            let t_log_d = Iv::pt(2.5).mul(l0_iv).div(k.mul(k.add(l0_iv)));
            let d1 = sp_iv.div(c_sup).sub(ome_lo.mul(t_log_d));
            let d2 = sp_iv.div(c_sup).sub(ome_hi.mul(t_log_d));
            return d1.hull(d2);
        }
        let mut out: Option<Iv> = None;
        for &ev in &[e_lo, e_hi] {
            let ome_v = Iv::pt(1.0).sub(Iv::pt(ev));
            let om_raw = ome_v.mul(c_sup).div(t_iv);
            let om_c = Iv::raw(om_raw.lo.clamp(0.0, 1.0), om_raw.hi.clamp(0.0, 1.0));
            let c_opt_use = if om_raw.hi <= 1.0 {
                Iv::pt(ev).mul(c_sup)
            } else if om_raw.lo >= 1.0 {
                c_sup.sub(t_iv)
            } else {
                Iv::pt(ev).mul(c_sup).hull(c_sup.sub(t_iv))
            };
            let dv = Iv::pt(ev).mul(sp_iv.sub(tp_iv.mul(om_c))).div(c_opt_use);
            out = Some(match out { None => dv, Some(p) => p.hull(dv) });
        }
        out.unwrap()
    } else {
        let h_iv = Iv::pt(H_M);
        let t_h = c15.mul(h_iv.pow52()).mul(l0_s).div(h_iv.add(l0_iv).pow52());
        let f_h = iv_f_a_iv(a_iv, h_iv, l0_iv);
        let r_tan = q_iv.add(f_h.div(h_iv)).add(om_l0.mul(t_h.div(h_iv)));
        let t_over_k = t_h.div(h_iv);
        let t_iv = k.mul(t_over_k);
        let ome_lo = Iv::pt(1.0).sub(Iv::pt(e_lo));
        let ome_hi = Iv::pt(1.0).sub(Iv::pt(e_hi));
        let c_sup = k.mul(r_tan).sub(Iv::pt(a_exit));
        let om_max = ome_lo.mul(c_sup).div(t_iv);
        if om_max.hi < 1.0 {
            let d1 = r_tan.div(c_sup).sub(ome_lo.div(k));
            let d2 = r_tan.div(c_sup).sub(ome_hi.div(k));
            return d1.hull(d2);
        }
        let mut out: Option<Iv> = None;
        for &ev in &[e_lo, e_hi] {
            let ome_v = Iv::pt(1.0).sub(Iv::pt(ev));
            let om_raw = ome_v.mul(c_sup).div(t_iv);
            let om_c = Iv::raw(om_raw.lo.clamp(0.0, 1.0), om_raw.hi.clamp(0.0, 1.0));
            let c_opt = c_sup.sub(t_iv.mul(om_c));
            let dv = Iv::pt(ev).mul(r_tan.sub(t_over_k.mul(om_c))).div(c_opt);
            out = Some(match out { None => dv, Some(p) => p.hull(dv) });
        }
        out.unwrap()
    }
}

fn audit_exit_seg_rs(
    w_pwl: &Pwl, iv_cont: Iv, a_hi: f64, q_hi: f64, a_exit: f64, l0: f64, e_lo: f64, e_hi: f64, ak_mode: bool,
    kL: f64, kR: f64, depth: u32,
) -> f64 {
    let k_iv = Iv::raw(kL, kR);
    let w_iv = w_pwl.iv_range(kL, kR);
    let e_iv = iv_e_plus_exact(a_hi, q_hi, k_iv, a_exit, l0, e_lo, e_hi, ak_mode);
    let gap_mono_lo = w_iv.sub(e_iv.add(iv_cont)).lo;
    if gap_mono_lo > 0.0 {
        return gap_mono_lo;
    }
    let xm = 0.5 * (kL + kR);
    let xm_iv = Iv::pt(xm);
    let hx_iv = Iv::pt(0.5 * (kR - kL));
    let gap_m_iv = w_pwl.iv_eval_pt(xm).sub(iv_e_plus_exact(a_hi, q_hi, xm_iv, a_exit, l0, e_lo, e_hi, ak_mode).add(iv_cont));
    let dw_iv = w_pwl.iv_deriv_bounds(kL, kR);
    let de_iv = iv_de_plus_dk(a_hi, q_hi, k_iv, a_exit, l0, e_lo, e_hi, ak_mode);
    let dg_iv = dw_iv.sub(de_iv);
    let gap_cent_lo = gap_m_iv.sub(Iv::pt(dg_iv.max_abs()).mul(hx_iv)).lo;
    let lb_seg = gap_mono_lo.max(gap_cent_lo);
    if (!lb_seg.is_finite() || lb_seg <= 0.0) && depth < 8 {
        let r1 = audit_exit_seg_rs(w_pwl, iv_cont, a_hi, q_hi, a_exit, l0, e_lo, e_hi, ak_mode, kL, xm, depth + 1);
        let r2 = audit_exit_seg_rs(w_pwl, iv_cont, a_hi, q_hi, a_exit, l0, e_lo, e_hi, ak_mode, xm, kR, depth + 1);
        return r1.min(r2);
    }
    if !lb_seg.is_finite() { -1e9 } else { lb_seg }
}

#[no_mangle]
pub extern "C" fn rs_verify_adverse_exit_bb(
    ks_ptr: *const f64, lks_ptr: *const f64, vals_ptr: *const f64, slopes_ptr: *const f64,
    nk: usize, s_lo: f64, s_hi: f64,
    e_psi_cont_val: f64, a_hi: f64, q_hi: f64, b_lo: f64, b_hi: f64, e_lo: f64, e_hi: f64,
    a_exit: f64, l0_exit: f64, k_a: f64, k_b: f64, ak_mode_i: i32,
    tol: f64, max_iter: usize, interval_check_i: i32,
    ce_out: *mut f64, max_ce: usize,
) -> BbOut {
    let ks = unsafe { slice::from_raw_parts(ks_ptr, nk) };
    let lks = unsafe { slice::from_raw_parts(lks_ptr, nk) };
    let vals = unsafe { slice::from_raw_parts(vals_ptr, nk) };
    let slopes = unsafe { slice::from_raw_parts(slopes_ptr, nk - 1) };
    let w_pwl = Pwl::new(ks, lks, vals, slopes, s_lo, s_hi);

    let ak_mode = ak_mode_i != 0;
    let beta_ep = if e_psi_cont_val < 0.0 { b_lo } else { b_hi };
    let cont_term = beta_ep * e_psi_cont_val;

    let t_h_ak = df_dl(a_hi, H_M, l0_exit);
    let f_h_ak = f_a(a_hi, H_M, l0_exit);
    let r_tan_ak = q_hi + f_h_ak / H_M + (1.0 - l0_exit) * (t_h_ak / H_M);

    let eval_gap = |k: f64| -> f64 {
        let wk = w_pwl.eval_f64(k);
        let (t, c_sup) = if !ak_mode || k <= H_M {
            let tv = df_dl(a_hi, k, l0_exit);
            (tv, q_hi * k + f_a(a_hi, k, l0_exit) + (1.0 - l0_exit) * tv - a_exit)
        } else {
            (k * (t_h_ak / H_M), k * r_tan_ak - a_exit)
        };
        let om0 = ((1.0 - e_lo) * c_sup / t).min(1.0);
        let v0 = e_lo * (c_sup - t * om0).ln() + (1.0 - e_lo) * om0.ln();
        let om1 = ((1.0 - e_hi) * c_sup / t).min(1.0);
        let v1 = e_hi * (c_sup - t * om1).ln() + (1.0 - e_hi) * om1.ln();
        wk - (v0.max(v1) + cont_term)
    };

    let mut ks_scan = Vec::with_capacity(81 + nk + 2);
    push_linspace(&mut ks_scan, k_a, k_b, 81, true);
    for &kv in ks {
        if kv >= k_a && kv <= k_b { ks_scan.push(kv); }
    }
    if ak_mode && k_a < H_M && H_M < k_b { ks_scan.push(H_M); }
    let ks_scan = sorted_dedup(ks_scan);

    let mut best_ub = f64::INFINITY;
    let mut best_k = k_a;
    for &kv in &ks_scan {
        let g = eval_gap(kv);
        if g < best_ub {
            best_ub = g;
            best_k = kv;
        }
    }
    let mut target = best_ub - tol;
    let mut ces: Vec<[f64; 2]> = vec![[best_k, best_ub]];

    let mut bxL = Vec::with_capacity(ks_scan.len());
    let mut bxR = Vec::with_capacity(ks_scan.len());
    for i in 0..ks_scan.len() - 1 {
        bxL.push(ks_scan[i]);
        bxR.push(ks_scan[i + 1]);
    }
    let mut done_L = Vec::new();
    let mut done_R = Vec::new();
    let mut m_lb: Option<f64> = None;
    let mut last_min_lb = f64::NEG_INFINITY;

    for _it in 0..max_iter {
        let mut nxL = Vec::new();
        let mut nxR = Vec::new();
        let mut nxm = Vec::new();
        let mut kept_lb = Vec::new();
        let mut min_k_gap = f64::INFINITY;
        let mut min_k_pt = k_a;
        last_min_lb = f64::INFINITY;

        for i in 0..bxL.len() {
            let xL = bxL[i];
            let xR = bxR[i];
            let xm = 0.5 * (xL + xR);
            let hx = 0.5 * (xR - xL);
            let gap_m = eval_gap(xm);
            let (dw_lo, dw_hi) = w_pwl.deriv_bounds_f64(xL, xR);

            let (t_l, c_sup_l, t_r, c_sup_r, ds_lo, ds_hi, tp_lo, tp_hi, t_log_lo, t_log_hi) = if !ak_mode || xR <= H_M {
                let tl = df_dl(a_hi, xL, l0_exit);
                let csl = q_hi * xL + f_a(a_hi, xL, l0_exit) + (1.0 - l0_exit) * tl - a_exit;
                let tr = df_dl(a_hi, xR, l0_exit);
                let csr = q_hi * xR + f_a(a_hi, xR, l0_exit) + (1.0 - l0_exit) * tr - a_exit;
                let c_const = 1.5 * a_hi * 2.8284271247461903 * l0_exit.powf(2.5);
                let dfk_hi = c_const * xR.sqrt() * (xL + l0_exit).powf(-2.5);
                let dfk_lo = c_const * xL.sqrt() * (xR + l0_exit).powf(-2.5);
                let c_tp = 1.5 * a_hi * 2.8284271247461903 * 2.5 * l0_exit.powf(1.5);
                let tp_h = c_tp * xR.powf(1.5) * (xL + l0_exit).powf(-3.5);
                let tp_l = c_tp * xL.powf(1.5) * (xR + l0_exit).powf(-3.5);
                (
                    tl, csl, tr, csr,
                    q_hi + dfk_lo + (1.0 - l0_exit) * tp_l,
                    q_hi + dfk_hi + (1.0 - l0_exit) * tp_h,
                    tp_l, tp_h,
                    (2.5 * l0_exit) / (xR * (xR + l0_exit)),
                    (2.5 * l0_exit) / (xL * (xL + l0_exit)),
                )
            } else {
                let tl = (xL / H_M) * t_h_ak;
                let tr = (xR / H_M) * t_h_ak;
                (
                    tl, xL * r_tan_ak - a_exit, tr, xR * r_tan_ak - a_exit,
                    r_tan_ak, r_tan_ak, t_h_ak / H_M, t_h_ak / H_M,
                    1.0 / xR, 1.0 / xL,
                )
            };

            let ep_r = {
                let om0 = ((1.0 - e_lo) * c_sup_r / t_r).min(1.0);
                let v0 = e_lo * (c_sup_r - t_r * om0).ln() + (1.0 - e_lo) * om0.ln();
                let om1 = ((1.0 - e_hi) * c_sup_r / t_r).min(1.0);
                let v1 = e_hi * (c_sup_r - t_r * om1).ln() + (1.0 - e_hi) * om1.ln();
                v0.max(v1)
            };
            let (w_lo, _) = w_pwl.range_f64(xL, xR);
            let lb_mono = w_lo - (ep_r + cont_term);

            let om_max = (1.0 - e_lo) * c_sup_r / t_l.max(1e-15);
            let (de_lo, de_hi) = if om_max < 1.0 {
                (ds_lo / c_sup_r.max(1e-12) - (1.0 - e_lo) * t_log_hi,
                 ds_hi / c_sup_l.max(1e-12) - (1.0 - e_hi) * t_log_lo)
            } else {
                let c_opt_l = (c_sup_l - t_r * ((1.0 - e_lo) * c_sup_r / t_l).min(1.0))
                    .min(c_sup_l - t_r * ((1.0 - e_hi) * c_sup_r / t_l).min(1.0));
                let c_opt_r = (c_sup_r - t_l * ((1.0 - e_lo) * c_sup_l / t_r).min(1.0))
                    .max(c_sup_r - t_l * ((1.0 - e_hi) * c_sup_l / t_r).min(1.0));
                let om_min_box = ((1.0 - e_hi) * c_sup_l / t_r.max(1e-15)).min(1.0);
                let om_max_box = om_max.min(1.0);
                let de_h = e_hi * (ds_hi - tp_lo * om_min_box).max(0.0) / c_opt_l.max(1e-12);
                let num_l = ds_lo - tp_hi * om_max_box;
                let den_l = if num_l >= 0.0 { c_opt_r.max(1e-12) } else { c_opt_l.max(1e-12) };
                (e_lo * num_l / den_l, de_h)
            };
            let dg_lo = dw_lo - de_hi;
            let dg_hi = dw_hi - de_lo;
            let lb_cent = gap_m - dg_lo.abs().max(dg_hi.abs()) * hx;
            let lb = lb_mono.max(lb_cent);
            if lb < last_min_lb { last_min_lb = lb; }

            if lb < target {
                if gap_m < min_k_gap {
                    min_k_gap = gap_m;
                    min_k_pt = xm;
                }
                nxL.push(xL); nxR.push(xR); nxm.push(xm); kept_lb.push(lb);
            } else {
                done_L.push(xL); done_R.push(xR);
            }
        }

        if nxL.is_empty() {
            m_lb = Some(target);
            break;
        }
        if min_k_gap < best_ub {
            best_ub = min_k_gap;
            target = best_ub - tol;
            ces.push([min_k_pt, best_ub]);
        }
        if nxL.len() > 80_000 || _it + 1 == max_iter {
            done_L.extend_from_slice(&nxL);
            done_R.extend_from_slice(&nxR);
            let min_k = kept_lb.iter().copied().fold(f64::INFINITY, f64::min);
            m_lb = Some(min_k);
            break;
        }
        bxL.clear(); bxR.clear();
        for i in 0..nxL.len() {
            bxL.push(nxL[i]); bxR.push(nxm[i]);
            bxL.push(nxm[i]); bxR.push(nxR[i]);
        }
    }

    let m_lb_v = m_lb.unwrap_or(last_min_lb);
    let mut iv_certified = false;
    let mut m_lb_iv = m_lb_v;
    if interval_check_i != 0 && m_lb_v > 0.0 && !done_L.is_empty() {
        let iv_cont = Iv::pt(beta_ep).mul(Iv::pt(e_psi_cont_val));
        let mut iv_min_gap = 1e9f64;
        for i in 0..done_L.len() {
            let rg = audit_exit_seg_rs(&w_pwl, iv_cont, a_hi, q_hi, a_exit, l0_exit, e_lo, e_hi, ak_mode, done_L[i], done_R[i], 0);
            if rg < iv_min_gap { iv_min_gap = rg; }
        }
        iv_certified = iv_min_gap > 0.0;
        m_lb_iv = iv_min_gap;
    }

    let n_write = ces.len().min(max_ce);
    if !ce_out.is_null() && n_write > 0 {
        let out_slice = unsafe { slice::from_raw_parts_mut(ce_out, n_write * 2) };
        for (i, c) in ces.iter().take(n_write).enumerate() {
            out_slice[2 * i] = c[0];
            out_slice[2 * i + 1] = c[1];
        }
    }

    BbOut {
        certified: if m_lb_v > 0.0 && (interval_check_i == 0 || iv_certified) { 1 } else { 0 },
        iv_certified: if iv_certified { 1 } else { 0 },
        d_ub: m_lb_v,
        d_ub_iv: m_lb_iv,
        d_lb: best_ub,
        leaf_count: done_L.len(),
        n_ce: n_write,
    }
}
