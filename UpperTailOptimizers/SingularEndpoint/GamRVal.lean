import UpperTailOptimizers.SingularEndpoint.GamAverage

/-!
# The subtracted gap `Γ_d(r_h)` is negligible (Section 7, `paper/singular_endpoint.tex`)

`eq:constant-comparison-identity` — proved as `KKTFamily.cost_gap_eq` — writes the cost
gap of the candidate as

```
I_{p_h}(W_h) - J_{p_h}(r_h) = (∫Γ_d(W_h) - Γ_d(r_h)) + Λ_h · (e(W_h) - r_h) .
```

`SingularEndpoint/GamAverage.lean` evaluated the first summand of the first bracket,
`∫Γ_d(W_h)/h⁴ → d³/3` (the averaged-gap display in the proof of
`lem:constant-graphon-comparison`).  This file disposes of the *subtracted*
term and therefore closes the first bracket:

```
(∫Γ_d(W_h) - Γ_d(r_h)) / h⁴  →  d³/3      as `h → 0`, `h ≠ 0`.
```

## Why `Γ_d(r_h)` is negligible

`Γ_d` vanishes to order four at `r_*` (`Gam_le_of_near`), so it is enough that the density
`r_h` approaches `r_*` faster than `h`, i.e. `r_h - r_* = o(h)`.  That is the content of
`eq:rank-one-parameter-expansions`, where `r_h = r_* + O(h²)`; only the `o(h)` half is needed
and it is proved here without any expansion.

The proof deliberately avoids differentiating the `rpow` in `r_h = q_h^{2/d}`.  Instead it
uses the *algebraic* relation `rVal_pow_d`, `r_h^d = q_h²`, together with the reverse
Lipschitz bound `pow_sub_pow_ge` for `x ↦ x^d`,

```
r_*^{d-1} · |r_h - r_*| ≤ |r_h^d - r_*^d| = |q_h² - q_0²| = |q_h + q_0| · |q_h - q_0| ,
```

`q_0 = u_*^d` (`qVal_zero`), `r_*^d = q_0²` (because `r_* = u_*²`).  So the rate of `r_h` is
controlled by the rate of `q_h`, and *that* is elementary calculus: `q_h` is differentiable
at `0` with

```
q'(0) = α'(0)u_*^d + ½·(-d u_*^{d-1}) - α'(0)u_*^d + ½·(+d u_*^{d-1}) = 0 ,
```

the two `α'(0)` contributions cancelling because the two nodes coalesce (`s_0 = t_0 = u_*`)
and the two node derivatives `∓d u_*^{d-1}` cancelling because `α_0 = ½`.  The only family
inputs are evenness of `u` (through `deriv_zero_of_even`), analyticity of `α`, and
`alph_zero`.

## Contents

* `hasDerivAt_qVal_zero` — `q_h` is differentiable at `0` with `q'(0) = 0`;
* `tendsto_qVal`, `tendsto_qVal_rate` — `q_h → u_*^d` and `(q_h - u_*^d)/h → 0`;
* `tendsto_rVal_rate` — **`r_h - r_* = o(h)`**, the transfer through `r_h^d = q_h²`;
* `tendsto_rVal` — `r_h → r_*`;
* `tendsto_Gam_rVal` — `Γ_d(r_h)/h⁴ → 0`;
* `tendsto_gamInt_sub_gamRVal` — the first bracket of `eq:constant-comparison-identity`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

variable {d : ℕ}

/-! ## The rate of the rank-one moment `q_h` -/

/-- **`q_h` is stationary at the coalescing point**: `q_h = α_h s_h^d + (1-α_h) t_h^d` is
differentiable at `0` with derivative `0`.

Both nodes are differentiable at `0` — `s_h = u_h - h` and `t_h = u_h + h` with `u'(0) = 0`
by `deriv_zero_of_even` — with derivatives `-1` and `+1`, and both take the value `u_*`
there.  Writing `a = α'(0)`, the product rule gives

```
q'(0) = a·u_*^d + ½·(d u_*^{d-1}·(-1)) + (-a)·u_*^d + ½·(d u_*^{d-1}·(+1)) = 0 :
```

the block-weight contributions cancel because the two nodes have *merged*, and the node
contributions cancel because the weight is exactly `½` at `h = 0`. -/
theorem hasDerivAt_qVal_zero (B : KKTFamily d) : HasDerivAt B.qVal 0 0 := by
  have h0mem : |(0 : ℝ)| < B.h₀ := by rw [abs_zero]; exact B.h₀_pos
  have hu : HasDerivAt B.u 0 0 := by
    have h : HasDerivAt B.u (deriv B.u 0) 0 :=
      ((B.analyticAt_u 0 h0mem).differentiableAt).hasDerivAt
    rwa [deriv_zero_of_even B.u_even h] at h
  have halph : HasDerivAt B.alph (deriv B.alph 0) 0 :=
    ((B.analyticAt_alph 0 h0mem).differentiableAt).hasDerivAt
  have hid : HasDerivAt (fun x : ℝ => x) 1 (0 : ℝ) := hasDerivAt_id (0 : ℝ)
  have hs : HasDerivAt (fun x : ℝ => B.sVal x) (-1) 0 := by
    have h := hu.sub hid
    rwa [zero_sub] at h
  have ht : HasDerivAt (fun x : ℝ => B.tVal x) 1 0 := by
    have h := hu.add hid
    rwa [zero_add] at h
  have hbeta : HasDerivAt (fun x : ℝ => 1 - B.alph x) (0 - deriv B.alph 0) 0 :=
    (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub halph
  have hsum := (halph.mul (hs.fun_pow d)).add (hbeta.mul (ht.fun_pow d))
  rw [KKTFamily.sVal_zero, KKTFamily.tVal_zero, B.alph_zero] at hsum
  exact hsum.congr_deriv (by ring)

/-- **The moment rate vanishes**: `(q_h - u_*^d)/h → 0` as `h → 0`, `h ≠ 0`.  This is
`hasDerivAt_qVal_zero` read through `hasDerivAt_iff_tendsto_slope`. -/
theorem tendsto_qVal_rate (B : KKTFamily d) :
    Tendsto (fun h : ℝ => (B.qVal h - uStar d ^ d) / h) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hsl : Tendsto (_root_.slope B.qVal 0) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_qVal_zero B)
  refine hsl.congr fun h => ?_
  rw [_root_.slope_def_field, B.qVal_zero, sub_zero]

/-- `q_h → u_*^d`, the value `qVal_zero` records at the coalescing point. -/
theorem tendsto_qVal (B : KKTFamily d) :
    Tendsto B.qVal (𝓝[≠] (0 : ℝ)) (𝓝 (uStar d ^ d)) :=
  tendsto_node_of_rate (tendsto_qVal_rate B)

/-! ## The rate of the density `r_h` -/

/-- **`r_h - r_* = o(h)`**, the `o(h)` half of the expansion `r_h = r_* + O(h²)` of
`eq:rank-one-parameter-expansions`.

No `rpow` is differentiated.  The defining relation `rVal_pow_d` says `r_h^d = q_h²`, and
`r_*^d = (u_*^d)²` because `r_* = u_*²`, so the reverse Lipschitz bound `pow_sub_pow_ge`
for `x ↦ x^d` at the base point `r_* > 0` gives

```
r_*^{d-1} |r_h - r_*| ≤ |r_h^d - r_*^d| = |q_h + u_*^d| · |q_h - u_*^d| .
```

Dividing by `r_*^{d-1}|h|` bounds `|(r_h - r_*)/h|` by
`(|q_h + u_*^d|/r_*^{d-1})·|(q_h - u_*^d)/h|`, whose first factor converges (`tendsto_qVal`)
and whose second tends to `0` (`tendsto_qVal_rate`). -/
theorem tendsto_rVal_rate (hd : 2 ≤ d) (B : KKTFamily d) :
    Tendsto (fun h : ℝ => (B.rVal h - rStar d) / h) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hC : (0 : ℝ) < rStar d ^ (d - 1) := pow_pos (rStar_pos hd) _
  have hCne : rStar d ^ (d - 1) ≠ 0 := ne_of_gt hC
  have hmaj : Tendsto (fun h : ℝ =>
      |B.qVal h + uStar d ^ d| * |(B.qVal h - uStar d ^ d) / h| / rStar d ^ (d - 1))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun h : ℝ => |B.qVal h + uStar d ^ d|) (𝓝[≠] (0 : ℝ))
        (𝓝 |uStar d ^ d + uStar d ^ d|) :=
      ((tendsto_qVal B).add tendsto_const_nhds).abs
    have h2 : Tendsto (fun h : ℝ => |(B.qVal h - uStar d ^ d) / h|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have h := (tendsto_qVal_rate B).abs
      rwa [abs_zero] at h
    have h := (h1.mul h2).div_const (rStar d ^ (d - 1))
    rwa [mul_zero, zero_div] at h
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [self_mem_nhdsWithin, eventually_abs_lt_h₀ B] with h hx hb
  have hxne : h ≠ 0 := hx
  have hane : |h| ≠ 0 := abs_ne_zero.mpr hxne
  have hge : rStar d ^ (d - 1) * |B.rVal h - rStar d|
      ≤ |B.qVal h + uStar d ^ d| * |B.qVal h - uStar d ^ d| := by
    have hrs : rStar d ^ d = (uStar d ^ d) ^ 2 := by
      rw [← uStar_sq hd, ← pow_mul, ← pow_mul, mul_comm]
    have hfac : B.rVal h ^ d - rStar d ^ d
        = (B.qVal h + uStar d ^ d) * (B.qVal h - uStar d ^ d) := by
      rw [KKTFamily.rVal_pow_d hd hb, hrs]; ring
    have hpp := pow_sub_pow_ge (KKTFamily.rVal_pos hd hb).le (rStar_pos hd).le
      (k := d) (by omega)
    rwa [hfac, abs_mul] at hpp
  have hstep : |B.rVal h - rStar d|
      ≤ |B.qVal h + uStar d ^ d| * |B.qVal h - uStar d ^ d| / rStar d ^ (d - 1) := by
    have hd' := div_le_div_of_nonneg_right hge hC.le
    have hcancel : rStar d ^ (d - 1) * |B.rVal h - rStar d| / rStar d ^ (d - 1)
        = |B.rVal h - rStar d| := by field_simp
    rwa [hcancel] at hd'
  have hdiv := div_le_div_of_nonneg_right hstep (abs_nonneg h)
  rw [Real.norm_eq_abs, abs_div]
  refine hdiv.trans (le_of_eq ?_)
  rw [abs_div]
  field_simp

/-- `r_h → r_*`: the density collapses onto the exceptional density. -/
theorem tendsto_rVal (hd : 2 ≤ d) (B : KKTFamily d) :
    Tendsto B.rVal (𝓝[≠] (0 : ℝ)) (𝓝 (rStar d)) :=
  tendsto_node_of_rate (tendsto_rVal_rate hd B)

/-! ## The subtracted gap -/

/-- **`Γ_d(r_h)/h⁴ → 0`**: the term subtracted in `eq:constant-comparison-identity` is
negligible at the order of the cost gap.

Exactly the squeeze used for the middle node in `SingularEndpoint/GamAverage.lean`: `r_h` may equal
`r_*` at isolated `h`, so no composition with `tendsto_Gam_div_pow_four` is available, but
`0 ≤ Γ_d(r_h) ≤ C(r_h - r_*)⁴` by `Gam_nonneg` and `Gam_le_of_near`, and after dividing by
`h⁴ > 0` the majorant is `C·((r_h - r_*)/h)⁴ → 0` by `tendsto_rVal_rate`. -/
theorem tendsto_Gam_rVal (hd : 2 ≤ d) (B : KKTFamily d) :
    Tendsto (fun h : ℝ => Gam d (B.rVal h) / h ^ 4) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, δ, _hC, hδ, hband⟩ := Gam_le_of_near hd
  have hrate := tendsto_rVal_rate hd B
  have hIcc : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      B.rVal h ∈ Set.Icc (rStar d - δ) (rStar d + δ) :=
    tendsto_rVal hd B (Icc_mem_nhds (by linarith) (by linarith))
  have hmaj : Tendsto (fun h : ℝ => C * ((B.rVal h - rStar d) / h) ^ 4)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h := (hrate.pow 4).const_mul C
    rwa [show (0 : ℝ) ^ 4 = 0 from by ring, mul_zero] at h
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [self_mem_nhdsWithin, eventually_abs_lt_h₀ B] with h hx hb
    have hxne : h ≠ 0 := hx
    have hpos : (0 : ℝ) < h ^ 4 := by positivity
    exact div_nonneg
      (Gam_nonneg hd (KKTFamily.rVal_pos hd hb).le
        (KKTFamily.rVal_lt_one hd hb).le) hpos.le
  · filter_upwards [self_mem_nhdsWithin, hIcc] with h hx hmem
    have hxne : h ≠ 0 := hx
    have hpos : (0 : ℝ) < h ^ 4 := by positivity
    have hrw : C * ((B.rVal h - rStar d) / h) ^ 4
        = C * (B.rVal h - rStar d) ^ 4 / h ^ 4 := by
      rw [div_pow, mul_div_assoc]
    rw [hrw]
    gcongr
    exact hband _ hmem

/-- **The first bracket of `eq:constant-comparison-identity`**:

```
(∫Γ_d(W_h) - Γ_d(r_h)) / h⁴  →  d³/3 .
```

`W_h = B.graphon hh` depends on a proof `hh : |h| < h₀`, so, exactly as in
`tendsto_gamInt_graphon`, the integral is represented by an arbitrary `F : ℝ → ℝ` agreeing
with it on the window.  The two summands are `tendsto_gamInt_graphon` (`d³/3`) and
`tendsto_Gam_rVal` (`0`). -/
theorem tendsto_gamInt_sub_gamRVal (hd : 2 ≤ d) (B : KKTFamily d) {F : ℝ → ℝ}
    (hF : ∀ (h : ℝ) (hh : |h| < B.h₀), F h = GamInt d (B.graphon hh)) :
    Tendsto (fun h : ℝ => (F h - Gam d (B.rVal h)) / h ^ 4) (𝓝[≠] (0 : ℝ))
      (𝓝 ((d : ℝ) ^ 3 / 3)) := by
  have h := (tendsto_gamInt_graphon hd B hF).sub (tendsto_Gam_rVal hd B)
  rw [sub_zero] at h
  exact h.congr fun x => by ring

end SingularEndpoint

end UpperTailOptimizers
