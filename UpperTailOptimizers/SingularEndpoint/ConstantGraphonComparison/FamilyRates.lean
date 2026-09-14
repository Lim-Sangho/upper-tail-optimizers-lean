import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Family

/-!
# The node rates along the coalescing family (Section 5, `paper/sections/singular.tex`)

The proof of `lem:constant-graphon-comparison` evaluates `∫Γ_d(W_h)` — the first half of
`eq:family-gap-expansion`, `∫Γ_d(W_h) = d³h⁴/3 + O_d(h⁶)` — by expanding `Γ_d` to fourth order at the
exceptional density `r_*`.  Since `Γ_d` vanishes to order exactly four there, the only family
data the expansion consumes are the *rates* at which the three block values

    `s_h² , s_h t_h , t_h²`,   `s_h = u_h - h`,  `t_h = u_h + h`,

approach `r_*`, together with the limit of the block weight `α_h`.  This file computes
those four limits.

The entire input to the three node rates is that the family midpoint `u_h` is **even** and
differentiable at `0` (`tendsto_alph` is separate, and uses `analyticAt_alph` and
`alph_zero` instead):
an even differentiable function has vanishing derivative at the origin
(`deriv_zero_of_even`), so `u_h = u_* + o(h)` and

    `(s_h² - r_*)/h → -2u_*`,  `(t_h² - r_*)/h → +2u_*`,  `(s_h t_h - r_*)/h → 0`.

No analysis beyond differentiability enters; in particular nothing here uses the KKT
equations, the fourth-order expansions, or the admissibility clause of
`lem:rank-one-kkt-family`.

## Contents

* `deriv_zero_of_even` — an even function differentiable at `0` has derivative `0` there;
* `tendsto_u_slope` — the midpoint slope `(u_h - u_*)/h → 0`;
* `tendsto_sVal_sq_rate`, `tendsto_tVal_sq_rate`, `tendsto_sVal_mul_tVal_rate` — the three
  node rates `-2u_*`, `+2u_*`, `0`;
* `tendsto_alph` — the block weight limit `α_h → 1/2`;
* `tendsto_u_punctured` — the midpoint limit `u_h → u_*` along `𝓝[≠] 0`;
* `tendsto_self_punctured` — the identity map tends to `0` along `𝓝[≠] 0`.  The last two are
  shared with `SingularEndpoint/ConstantGraphonComparison/FamilyQuadratic.lean`, `SingularEndpoint/ConstantGraphonComparison/Expansions.lean` and
  `SingularEndpoint/ConstantGraphonComparison/IncrementSum.lean`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

variable {d : ℕ}

/-! ## Evenness kills the first derivative -/

/-- **An even function differentiable at the origin has vanishing derivative there.**

Composing with `h ↦ -h` turns a derivative `c` at `0` into a derivative `-c` at `0`, and the
composite is the function itself; uniqueness of the derivative then forces `c = -c`. -/
theorem deriv_zero_of_even {v : ℝ → ℝ} {c : ℝ} (hv : ∀ h : ℝ, v (-h) = v h)
    (hd : HasDerivAt v c 0) : c = 0 := by
  have hd' : HasDerivAt v c (-(0 : ℝ)) := by rwa [neg_zero]
  have hneg : HasDerivAt (fun h : ℝ => v (-h)) (c * -1) 0 :=
    HasDerivAt.comp 0 hd' (hasDerivAt_neg' 0)
  have hneg' : HasDerivAt v (c * -1) 0 := by
    have heq : (fun h : ℝ => v (-h)) = v := funext hv
    rwa [heq] at hneg
  have := hd.unique hneg'
  linarith

/-! ## The midpoint slope -/

/-- **The midpoint slope vanishes**: `(u_h - u_*)/h → 0` as `h → 0`, `h ≠ 0`.

This is `deriv_zero_of_even` applied to `u`, which is even by `KKTFamily.u_even` and
differentiable at `0` because it is analytic there, read through
`hasDerivAt_iff_tendsto_slope`. -/
theorem tendsto_u_slope (B : KKTFamily d) :
    Tendsto (fun h : ℝ => (B.u h - uStar d) / h) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have h0mem : |(0 : ℝ)| < B.h₀ := by rw [abs_zero]; exact B.h₀_pos
  have hda : HasDerivAt B.u (deriv B.u 0) 0 :=
    ((B.analyticAt_u 0 h0mem).differentiableAt).hasDerivAt
  have hzero : deriv B.u 0 = 0 := deriv_zero_of_even B.u_even hda
  have hsl : Tendsto (_root_.slope B.u 0) (𝓝[≠] (0 : ℝ)) (𝓝 (deriv B.u 0)) :=
    hasDerivAt_iff_tendsto_slope.mp hda
  rw [hzero] at hsl
  refine hsl.congr fun h => ?_
  rw [_root_.slope_def_field, B.u_zero, sub_zero]

/-- The midpoint itself converges to `u_*` along the punctured neighbourhood. -/
theorem tendsto_u_punctured (B : KKTFamily d) :
    Tendsto B.u (𝓝[≠] (0 : ℝ)) (𝓝 (uStar d)) := by
  have h0mem : |(0 : ℝ)| < B.h₀ := by rw [abs_zero]; exact B.h₀_pos
  have h : Tendsto B.u (𝓝[≠] (0 : ℝ)) (𝓝 (B.u 0)) :=
    ((B.analyticAt_u 0 h0mem).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  rwa [B.u_zero] at h

/-- The quadratic remainder `(u_h - u_*)·(u_h - u_*)/h` is negligible: it is the product of
a factor tending to `0` and the slope, which also tends to `0`. -/
private theorem tendsto_u_sub_mul_slope (B : KKTFamily d) :
    Tendsto (fun h : ℝ => (B.u h - uStar d) * ((B.u h - uStar d) / h)) (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by
  have h1 : Tendsto (fun h : ℝ => B.u h - uStar d) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h := (tendsto_u_punctured B).sub (tendsto_const_nhds (x := uStar d))
    rwa [sub_self] at h
  have h2 := h1.mul (tendsto_u_slope B)
  rwa [mul_zero] at h2

/-- The identity map tends to `0` along the punctured neighbourhood of `0`. -/
theorem tendsto_self_punctured :
    Tendsto (fun h : ℝ => h) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
  tendsto_id.mono_left nhdsWithin_le_nhds

/-- Twice the midpoint slope, scaled by `2u_*`, is negligible. -/
private theorem tendsto_two_uStar_slope (B : KKTFamily d) :
    Tendsto (fun h : ℝ => 2 * uStar d * ((B.u h - uStar d) / h)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have h := (tendsto_u_slope B).const_mul (2 * uStar d)
  rwa [mul_zero] at h

/-! ## The three node rates -/

/-- **The lower node rate**: `(s_h² - r_*)/h → -2u_*`.

With `w_h = u_h - u_*` one has, for `h ≠ 0`,
`((u_h - h)² - u_*²)/h = w_h·(w_h/h) + 2u_*(w_h/h) - 2u_h + h`, whose four terms tend to
`0`, `0`, `-2u_*` and `0`. -/
theorem tendsto_sVal_sq_rate (hd : 2 ≤ d) (B : KKTFamily d) :
    Tendsto (fun h : ℝ => (B.sVal h ^ 2 - rStar d) / h) (𝓝[≠] (0 : ℝ))
      (𝓝 (-(2 * uStar d))) := by
  have hu : Tendsto (fun h : ℝ => 2 * B.u h) (𝓝[≠] (0 : ℝ)) (𝓝 (2 * uStar d)) :=
    (tendsto_u_punctured B).const_mul 2
  have hcomb :=
    (((tendsto_u_sub_mul_slope B).add (tendsto_two_uStar_slope B)).sub hu).add
      tendsto_self_punctured
  rw [show (0 : ℝ) + 0 - 2 * uStar d + 0 = -(2 * uStar d) from by ring] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := hh
  rw [KKTFamily.sVal, ← uStar_sq hd]
  field_simp
  ring

/-- **The upper node rate**: `(t_h² - r_*)/h → 2u_*`.  Same computation as
`tendsto_sVal_sq_rate` with `+h` in place of `-h`. -/
theorem tendsto_tVal_sq_rate (hd : 2 ≤ d) (B : KKTFamily d) :
    Tendsto (fun h : ℝ => (B.tVal h ^ 2 - rStar d) / h) (𝓝[≠] (0 : ℝ))
      (𝓝 (2 * uStar d)) := by
  have hu : Tendsto (fun h : ℝ => 2 * B.u h) (𝓝[≠] (0 : ℝ)) (𝓝 (2 * uStar d)) :=
    (tendsto_u_punctured B).const_mul 2
  have hcomb :=
    (((tendsto_u_sub_mul_slope B).add (tendsto_two_uStar_slope B)).add hu).add
      tendsto_self_punctured
  rw [show (0 : ℝ) + 0 + 2 * uStar d + 0 = 2 * uStar d from by ring] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := hh
  rw [KKTFamily.tVal, ← uStar_sq hd]
  field_simp
  ring

/-- **The cross node rate**: `(s_h t_h - r_*)/h → 0`.  Here the two `±h` contributions
cancel, leaving `(u_h² - h² - u_*²)/h = w_h·(w_h/h) + 2u_*(w_h/h) - h`. -/
theorem tendsto_sVal_mul_tVal_rate (hd : 2 ≤ d) (B : KKTFamily d) :
    Tendsto (fun h : ℝ => (B.sVal h * B.tVal h - rStar d) / h) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hcomb :=
    ((tendsto_u_sub_mul_slope B).add (tendsto_two_uStar_slope B)).sub tendsto_self_punctured
  rw [show (0 : ℝ) + 0 - 0 = 0 from by ring] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := hh
  rw [KKTFamily.sVal, KKTFamily.tVal, ← uStar_sq hd]
  field_simp
  ring

/-! ## The block weight -/

/-- **The block weight limit**: `α_h → 1/2` as `h → 0`.  The family weight is analytic,
hence continuous, at `0`, where its value is `1/2`. -/
theorem tendsto_alph (B : KKTFamily d) :
    Tendsto B.alph (𝓝 (0 : ℝ)) (𝓝 (1 / 2)) := by
  have h0mem : |(0 : ℝ)| < B.h₀ := by rw [abs_zero]; exact B.h₀_pos
  have h := (B.analyticAt_alph 0 h0mem).continuousAt.tendsto
  rwa [B.alph_zero] at h

end SingularEndpoint

end UpperTailOptimizers
