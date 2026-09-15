import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Defs

/-!
# The analytic log slope (Section 5, `paper/sections/singular.tex`)

The one analytic tool that the construction of the rank-one KKT family
(`lem:rank-one-kkt-family`) needs.

The family equations of `eq:three-value-kkt` degenerate at `h = 0`, where the three
roots `s_h², s_h t_h, t_h²` merge, so the formalisation replaces them by their divided
differences (the paper instead extends its two divided slopes analytically; its "analytic
Weierstrass division" is the factorisation of `𝓜_h'` in `app:rank-one-kkt-family`).  Every
division that arises is by a power of
`h`, and every one of them can be performed **explicitly** once one knows that

  `x ↦ log(1 - x) / x`

extends analytically across `x = 0`.  That is a *one-variable* removable singularity, and
Mathlib supplies it: `dslope` divides an analytic function by `(· - a)` after subtracting
its value at `a` (`HasFPowerSeriesAt.has_fpower_series_dslope_fslope`), and `Real.log` is
analytic away from `0` (`analyticAt_log`).

The payoff is the single identity `log_one_sub_eq`,

  `log(1 - x) = -x · logSlope x`   for **every** real `x`,

with `logSlope` analytic at `0` and `logSlope 0 = 1`.  Every `h`-division in the family
equations is discharged by rewriting a logarithm with it and cancelling one factor of `h`
syntactically.

## Contents

* `logSlope` — the analytic extension of `x ↦ -log(1-x)/x`;
* `logSlope_zero`, `logSlope_eq`, `log_one_sub_eq`;
* `analyticAt_logSlope` and the composition helper `AnalyticAt.logSlope_comp`.
-/

namespace UpperTailOptimizers

open Real

/-- The analytic extension of `x ↦ -log(1-x)/x` across `x = 0`, where it takes the value
`1`.  Defined as (minus) the Mathlib difference quotient `dslope` of `y ↦ log(1-y)` based at
`0`, which is exactly what makes it analytic. -/
noncomputable def logSlope (x : ℝ) : ℝ := -dslope (fun y : ℝ => Real.log (1 - y)) 0 x

/-- `y ↦ log(1-y)` is analytic at `0`. -/
theorem analyticAt_logOneSub : AnalyticAt ℝ (fun y : ℝ => Real.log (1 - y)) 0 := by
  have hinner : AnalyticAt ℝ (fun y : ℝ => 1 - y) 0 :=
    analyticAt_const.sub analyticAt_id
  exact hinner.log (by norm_num)

/-- `y ↦ log(1-y)` has derivative `-1` at `0`. -/
private theorem hasDerivAt_logOneSub_zero :
    HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1) 0 := by
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_sub (hasDerivAt_id (0 : ℝ))
  have hne : (1 : ℝ) - (0 : ℝ) ≠ 0 := by norm_num
  have := (Real.hasDerivAt_log hne).comp 0 hsub
  simpa [Function.comp_def] using this

@[simp] theorem logSlope_zero : logSlope 0 = 1 := by
  rw [logSlope, dslope_same]
  rw [hasDerivAt_logOneSub_zero.deriv]
  norm_num

/-- Away from the origin, `logSlope` is the quotient it extends. -/
theorem logSlope_eq {x : ℝ} (hx : x ≠ 0) : logSlope x = -Real.log (1 - x) / x := by
  rw [logSlope, dslope_of_ne _ hx, slope_def_field]
  simp [Real.log_one, neg_div]

/-- **The identity every `h`-division is discharged by**:
`log(1 - x) = -x · logSlope x`, for every real `x`. -/
theorem log_one_sub_eq (x : ℝ) : Real.log (1 - x) = -x * logSlope x := by
  rcases eq_or_ne x 0 with rfl | hx
  · norm_num
  · rw [logSlope_eq hx]
    field_simp

/-- `logSlope` is analytic at the origin: this is the removable singularity, and it is what
makes the family equations of `lem:rank-one-kkt-family` analytic through `h = 0`. -/
theorem analyticAt_logSlope : AnalyticAt ℝ logSlope 0 := by
  obtain ⟨p, hp⟩ := analyticAt_logOneSub
  have hd : AnalyticAt ℝ (dslope (fun y : ℝ => Real.log (1 - y)) 0) 0 :=
    ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  exact hd.neg

/-- Composition rule: `logSlope ∘ g` is analytic wherever `g` is analytic and vanishes.
This is how the family equations are assembled — every argument of `logSlope` is an
analytic function of the parameters that vanishes at `h = 0`. -/
theorem AnalyticAt.logSlope_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {w : E} (hg : AnalyticAt ℝ g w) (hgw : g w = 0) :
    AnalyticAt ℝ (fun z => logSlope (g z)) w :=
  analyticAt_logSlope.fun_comp_of_eq hg hgw

end UpperTailOptimizers
