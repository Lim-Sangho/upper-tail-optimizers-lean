import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.LogSlope

/-!
# The analytic quotient by the node cubic (Section 5, `paper/sections/singular.tex`)

Section 5 divides the family function `𝓜_h'` by the **node cubic**

  `P(z) = (z - s_h²)(z - s_h t_h)(z - t_h²)`

(the paper's `D_h`), and calls the result `R`; the paper obtains `R` by an *analytic Weierstrass
division* (`eq:mh-factorization-proof`).  The `h⁴` order of the increments `A_h`, `B_h` (the two
differences in `eq:block-proportion-formula`) only needs a Lagrange
remainder (`SingularEndpoint/RankOneStationaryFamily/Order4.lean`), but the `h⁵` order — the coefficient that pins
`a₁ = α'(0) = 2 d² u_*/(3(d-1))` — needs the quotient itself, evaluated at a *known* point.

This file replaces the Weierstrass division by an elementary iteration of Mathlib's
difference quotient `dslope`.  `dslope f a` is `(f · - f a)/(· - a)` off `a` and `deriv f a`
at `a`, and it **preserves analyticity**: at the centre this is
`HasFPowerSeriesAt.has_fpower_series_dslope_fslope` (the same lemma that
`SingularEndpoint/RankOneStationaryFamily/LogSlope.lean` uses), and away from the centre `dslope f a` is literally a quotient
of analytic functions with a non-vanishing denominator.  Three iterations divide by the three
node factors, and no complex analysis is used anywhere.

## The confluent hypotheses

Vanishing of `f` at `z₁, z₂, z₃` is **not** enough when the roots coincide — `f z = z - a`
vanishes at `a, a, a` and is not divisible by `(z - a)³`.  The correct hypothesis, which
degenerates gracefully as the roots merge, is that the three *divided differences* vanish,

  `f z₁ = 0`,  `dslope f z₁ z₂ = 0`,  `dslope (dslope f z₁) z₂ z₃ = 0`.

For distinct roots this is exactly `f z₁ = f z₂ = f z₃ = 0`
(`exists_analytic_quotient_three_of_ne`), and for `z₁ = z₂ = z₃ = a` it is exactly
`f a = f' a = f'' a = 0` (`exists_analytic_quotient_three_confluent`).  Both faces are proved
below, and the factorisation identity itself holds at **every** real `z`, not only on `s`.

## Contents

* `analyticAt_dslope`, `analyticOnNhd_dslope` — `dslope` preserves analyticity;
* `quotient3` — the threefold difference quotient, the elementary `R`;
* `quotient3_factor`, `analyticOnNhd_quotient3`, `exists_analytic_quotient_three` — the
  factorisation `f z = (z - z₁)(z - z₂)(z - z₃) · R z` with `R` analytic;
* `exists_analytic_quotient_three_of_ne` — the distinct-root face;
* `iterate_dslope_self`, `quotient3_self` — the confluent value `R a = f'''(a)/6`;
* `exists_analytic_quotient_three_confluent` — the two combined, which is what identifies `R`
  at the base point of the coalescing family with `L_*'''(r_*)/6 = d⁵/(6(d-1)²)`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter

/-! ### `dslope` preserves analyticity -/

/-- **`dslope` preserves analyticity.**  If `f` is analytic both at the base point `a` and at
`x`, then the difference quotient `dslope f a` is analytic at `x`.

At `x = a` this is the removable singularity supplied by
`HasFPowerSeriesAt.has_fpower_series_dslope_fslope`; at `x ≠ a` the function `dslope f a`
agrees near `x` with the honest quotient `(f · - f a) / (· - a)`, whose denominator does not
vanish there. -/
theorem analyticAt_dslope {f : ℝ → ℝ} {a x : ℝ} (hfa : AnalyticAt ℝ f a)
    (hfx : AnalyticAt ℝ f x) : AnalyticAt ℝ (dslope f a) x := by
  rcases eq_or_ne x a with rfl | hx
  · obtain ⟨p, hp⟩ := hfa
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hden : AnalyticAt ℝ (fun z : ℝ => z - a) x := analyticAt_id.sub analyticAt_const
    have hq : AnalyticAt ℝ (fun z : ℝ => (f z - f a) * (z - a)⁻¹) x :=
      (hfx.sub analyticAt_const).mul (hden.inv (sub_ne_zero.2 hx))
    refine hq.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hx] with z hz
    rw [dslope_of_ne _ hz, slope_def_field, div_eq_mul_inv]

/-- Set version of `analyticAt_dslope`: if `f` is analytic on a neighbourhood of `s` and the
base point `a` lies in `s`, then so is `dslope f a`.  No openness of `s` is needed, because
`AnalyticOnNhd` already asks for analyticity on a neighbourhood of each point. -/
theorem analyticOnNhd_dslope {f : ℝ → ℝ} {s : Set ℝ} {a : ℝ} (hf : AnalyticOnNhd ℝ f s)
    (ha : a ∈ s) : AnalyticOnNhd ℝ (dslope f a) s :=
  fun x hx => analyticAt_dslope (hf a ha) (hf x hx)

/-- The defining identity of `dslope`, in the multiplicative form used below:
`(z - a) · dslope f a z = f z - f a`, valid at **every** `z`, including `z = a`. -/
theorem sub_mul_dslope (f : ℝ → ℝ) (a z : ℝ) : (z - a) * dslope f a z = f z - f a := by
  simpa using sub_smul_dslope f a z

/-- A divided difference of a function vanishing at both endpoints vanishes, provided the two
points are distinct.  This is what turns plain root conditions into the confluent hypotheses
of `exists_analytic_quotient_three`. -/
theorem dslope_eq_zero_of_ne {f : ℝ → ℝ} {a b : ℝ} (hba : b ≠ a) (ha : f a = 0)
    (hb : f b = 0) : dslope f a b = 0 := by
  rw [dslope_of_ne _ hba, slope_def_field, ha, hb, sub_zero, zero_div]

/-! ### The threefold quotient -/

/-- The elementary replacement for the paper's Weierstrass quotient: three iterated
difference quotients of `f`, based successively at the three nodes `z₁, z₂, z₃`. -/
noncomputable def quotient3 (f : ℝ → ℝ) (z₁ z₂ z₃ : ℝ) : ℝ → ℝ :=
  dslope (dslope (dslope f z₁) z₂) z₃

/-- **The factorisation.**  Under the three confluent (divided-difference) vanishing
hypotheses, `f` is the node cubic times `quotient3 f z₁ z₂ z₃`, at every real `z`.

No distinctness of `z₁, z₂, z₃` is assumed: the identity holds verbatim when the nodes
coalesce, which is the case `h = 0` of Section 5. -/
theorem quotient3_factor {f : ℝ → ℝ} {z₁ z₂ z₃ : ℝ} (h₁ : f z₁ = 0)
    (h₂ : dslope f z₁ z₂ = 0) (h₃ : dslope (dslope f z₁) z₂ z₃ = 0) (z : ℝ) :
    f z = (z - z₁) * (z - z₂) * (z - z₃) * quotient3 f z₁ z₂ z₃ z := by
  have e₃ : (z - z₃) * quotient3 f z₁ z₂ z₃ z = dslope (dslope f z₁) z₂ z := by
    simp only [quotient3]
    rw [sub_mul_dslope, h₃, sub_zero]
  have e₂ : (z - z₂) * dslope (dslope f z₁) z₂ z = dslope f z₁ z := by
    rw [sub_mul_dslope, h₂, sub_zero]
  have e₁ : (z - z₁) * dslope f z₁ z = f z := by
    rw [sub_mul_dslope, h₁, sub_zero]
  calc f z = (z - z₁) * ((z - z₂) * ((z - z₃) * quotient3 f z₁ z₂ z₃ z)) := by
        rw [e₃, e₂, e₁]
    _ = (z - z₁) * (z - z₂) * (z - z₃) * quotient3 f z₁ z₂ z₃ z := by ring

/-- The threefold quotient of a function analytic on a neighbourhood of `s` is again analytic
on a neighbourhood of `s`, as soon as the three nodes lie in `s`. -/
theorem analyticOnNhd_quotient3 {f : ℝ → ℝ} {s : Set ℝ} {z₁ z₂ z₃ : ℝ}
    (hf : AnalyticOnNhd ℝ f s) (h₁ : z₁ ∈ s) (h₂ : z₂ ∈ s) (h₃ : z₃ ∈ s) :
    AnalyticOnNhd ℝ (quotient3 f z₁ z₂ z₃) s :=
  analyticOnNhd_dslope (analyticOnNhd_dslope (analyticOnNhd_dslope hf h₁) h₂) h₃

/-- **The analytic division by the node cubic.**  An analytic `f` whose three divided
differences at `z₁, z₂, z₃ ∈ s` vanish factors as

  `f z = (z - z₁)(z - z₂)(z - z₃) · R z`

with `R` analytic on a neighbourhood of `s`.  The nodes need not be distinct. -/
theorem exists_analytic_quotient_three {f : ℝ → ℝ} {s : Set ℝ} {z₁ z₂ z₃ : ℝ}
    (hf : AnalyticOnNhd ℝ f s) (hz₁ : z₁ ∈ s) (hz₂ : z₂ ∈ s) (hz₃ : z₃ ∈ s)
    (h₁ : f z₁ = 0) (h₂ : dslope f z₁ z₂ = 0) (h₃ : dslope (dslope f z₁) z₂ z₃ = 0) :
    ∃ R : ℝ → ℝ, AnalyticOnNhd ℝ R s ∧
      ∀ z, f z = (z - z₁) * (z - z₂) * (z - z₃) * R z :=
  ⟨quotient3 f z₁ z₂ z₃, analyticOnNhd_quotient3 hf hz₁ hz₂ hz₃, quotient3_factor h₁ h₂ h₃⟩

/-- The distinct-node face of `exists_analytic_quotient_three`: for pairwise distinct nodes
the confluent hypotheses reduce to plain vanishing of `f` at the three nodes.  This is the
case `h ≠ 0` of Section 5, where `s_h², s_h t_h, t_h²` are three separate roots. -/
theorem exists_analytic_quotient_three_of_ne {f : ℝ → ℝ} {s : Set ℝ} {z₁ z₂ z₃ : ℝ}
    (hf : AnalyticOnNhd ℝ f s) (hz₁ : z₁ ∈ s) (hz₂ : z₂ ∈ s) (hz₃ : z₃ ∈ s)
    (h₂₁ : z₂ ≠ z₁) (h₃₁ : z₃ ≠ z₁) (h₃₂ : z₃ ≠ z₂)
    (h₁ : f z₁ = 0) (h₂ : f z₂ = 0) (h₃ : f z₃ = 0) :
    ∃ R : ℝ → ℝ, AnalyticOnNhd ℝ R s ∧
      ∀ z, f z = (z - z₁) * (z - z₂) * (z - z₃) * R z := by
  have d₂ : dslope f z₁ z₂ = 0 := dslope_eq_zero_of_ne h₂₁ h₁ h₂
  have d₃ : dslope f z₁ z₃ = 0 := dslope_eq_zero_of_ne h₃₁ h₁ h₃
  exact exists_analytic_quotient_three hf hz₁ hz₂ hz₃ h₁ d₂
    (dslope_eq_zero_of_ne h₃₂ d₂ d₃)

/-! ### The confluent value of the quotient -/

/-- **Iterated difference quotients read off Taylor coefficients.**  For `f` analytic at `a`,
the `n`-fold difference quotient of `f` based at `a`, evaluated at `a`, is the `n`-th Taylor
coefficient `f⁽ⁿ⁾(a)/n!`.

This is `HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope` combined with the
identification `AnalyticAt.hasFPowerSeriesAt` of the power series of an analytic function
with its Taylor series. -/
theorem iterate_dslope_self {f : ℝ → ℝ} {a : ℝ} (hf : AnalyticAt ℝ f a) (n : ℕ) :
    (Function.swap dslope a)^[n] f a = iteratedDeriv n f a / n.factorial := by
  set p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ (fun k => iteratedDeriv k f a / k.factorial) with hpdef
  have hp : HasFPowerSeriesAt f p a := hf.hasFPowerSeriesAt
  have hiter := hp.has_fpower_series_iterate_dslope_fslope n
  have h0 : (FormalMultilinearSeries.fslope^[n] p).coeff 0
      = (Function.swap dslope a)^[n] f a := hiter.coeff_zero 1
  rw [← h0, FormalMultilinearSeries.coeff_iterate_fslope, zero_add, hpdef,
    FormalMultilinearSeries.coeff_ofScalars]

/-- The threefold quotient based three times at the same point `a`. -/
theorem quotient3_same (f : ℝ → ℝ) (a : ℝ) :
    quotient3 f a a a = (Function.swap dslope a)^[3] f := rfl

/-- **The confluent value.**  When the three nodes coalesce at `a`, the quotient takes at `a`
the value `f'''(a)/6` — the third Taylor coefficient of `f`.  This is what identifies `R` at
the base point of the coalescing family with `L_*'''(r_*)/6 = d⁵/(6(d-1)²)`.

Note that no vanishing hypothesis is needed: the identity holds for every analytic `f`. -/
theorem quotient3_self {f : ℝ → ℝ} {a : ℝ} (hf : AnalyticAt ℝ f a) :
    quotient3 f a a a a = iteratedDeriv 3 f a / 6 := by
  rw [quotient3_same, iterate_dslope_self hf 3]
  norm_num

/-- **The confluent division, packaged.**  If `f` is analytic on a neighbourhood of `s` and
vanishes to order at least three at `a ∈ s`, then `f z = (z - a)³ · R z` for every real `z`,
with `R` analytic on a neighbourhood of `s` and `R a = f'''(a)/6`.

The second hypothesis is `deriv f a = 0` (see `iteratedDeriv_one`) and the third is
`f''(a) = 0`. -/
theorem exists_analytic_quotient_three_confluent {f : ℝ → ℝ} {s : Set ℝ} {a : ℝ}
    (hf : AnalyticOnNhd ℝ f s) (ha : a ∈ s) (h₀ : f a = 0)
    (h₁ : iteratedDeriv 1 f a = 0) (h₂ : iteratedDeriv 2 f a = 0) :
    ∃ R : ℝ → ℝ, AnalyticOnNhd ℝ R s ∧ (∀ z, f z = (z - a) ^ 3 * R z) ∧
      R a = iteratedDeriv 3 f a / 6 := by
  have hfa : AnalyticAt ℝ f a := hf a ha
  have d₁ : dslope f a a = 0 := by
    have := iterate_dslope_self hfa 1
    rw [h₁] at this
    simpa using this
  have d₂ : dslope (dslope f a) a a = 0 := by
    have := iterate_dslope_self hfa 2
    rw [h₂] at this
    simpa [Function.swap] using this
  refine ⟨quotient3 f a a a, analyticOnNhd_quotient3 hf ha ha ha, fun z => ?_,
    quotient3_self hfa⟩
  have := quotient3_factor h₀ d₁ d₂ z
  rw [this]
  ring

end SingularEndpoint

end UpperTailOptimizers
