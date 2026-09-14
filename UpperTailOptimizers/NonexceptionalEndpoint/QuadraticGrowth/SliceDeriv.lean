import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Slice derivatives of functions of two variables

Generic lemmas on the `δ`-slice derivative of a function of `(r, δ)`, split off
`NonexceptionalEndpoint/QuadraticGrowth/AnalyticTools.lean` so that the bipodality development
(`Preliminaries/KRRSBipodality/SliceBounds.lean`) can use them without importing the Section 4.2 chain, which sits
downstream of `Preliminaries/KRRSAnalyticExtension/Main.lean`.

* `hasDerivAt_slice`, `analyticAt_deltaDeriv`, `dDelta`, `hasDerivAt_dDelta`,
  `analyticAt_dDelta` — the partial `δ`-derivative and its analyticity;
* `abs_sub_le_of_deriv_bound` — the two-sided Lipschitz bound from a derivative bound;
* `exists_lipschitz_bound_of_boundary_zero` — a uniform `O(δ)` bound from analyticity and a
  vanishing boundary value.
-/

namespace UpperTailOptimizers

open Real Set Filter Topology

/-- The `δ`-slice derivative of a two-variable function is the partial derivative
`fderiv ℝ F p (0,1)`. -/
theorem hasDerivAt_slice {F : ℝ × ℝ → ℝ} {r t : ℝ} (hF : DifferentiableAt ℝ F (r, t)) :
    HasDerivAt (fun s => F (r, s)) (fderiv ℝ F (r, t) ((0 : ℝ), (1 : ℝ))) t := by
  have hι : HasDerivAt (fun s : ℝ => ((r, s) : ℝ × ℝ)) (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) t :=
    (hasDerivAt_const t r).prodMk (hasDerivAt_id t)
  exact hF.hasFDerivAt.comp_hasDerivAt t hι

/-- The partial `δ`-derivative of an analytic function of two variables is analytic. -/
theorem analyticAt_deltaDeriv {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hF : AnalyticAt ℝ F p) :
    AnalyticAt ℝ (fun q => fderiv ℝ F q ((0 : ℝ), (1 : ℝ))) p :=
  ((ContinuousLinearMap.apply ℝ ℝ (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ)).analyticAt
    (fderiv ℝ F p)).comp hF.fderiv

/-- **The partial `δ`-derivative operator** on functions of `(r, δ)`.  Iterating it gives the
higher `δ`-derivatives of a chart function; `dDelta` keeps the statements of the chart lemmas
readable. -/
noncomputable def dDelta (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => fderiv ℝ F p ((0 : ℝ), (1 : ℝ))

/-- `dDelta F (r, t)` is the derivative of the `δ`-slice `s ↦ F (r, s)` at `t`. -/
theorem hasDerivAt_dDelta {F : ℝ × ℝ → ℝ} {r t : ℝ} (hF : DifferentiableAt ℝ F (r, t)) :
    HasDerivAt (fun s => F (r, s)) (dDelta F (r, t)) t := hasDerivAt_slice hF

/-- `dDelta` preserves analyticity. -/
theorem analyticAt_dDelta {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hF : AnalyticAt ℝ F p) :
    AnalyticAt ℝ (dDelta F) p := analyticAt_deltaDeriv hF

/-- **Two-sided Lipschitz bound from a derivative bound.**  If `f` has derivative `f'` on
`[-ρ, ρ]` with `|f'| ≤ Mc` there, then `|f δ - f 0| ≤ Mc |δ|` on `[-ρ, ρ]`.  (Used for the
`δ`-Lipschitz control of the chart's second derivative, on both sides of `δ = 0`.) -/
theorem abs_sub_le_of_deriv_bound {f f' : ℝ → ℝ} {ρ Mc : ℝ}
    (hd : ∀ t ∈ Set.Icc (-ρ) ρ, HasDerivAt f (f' t) t)
    (hM : ∀ t ∈ Set.Icc (-ρ) ρ, |f' t| ≤ Mc) :
    ∀ δ ∈ Set.Icc (-ρ) ρ, |f δ - f 0| ≤ Mc * |δ| := by
  intro δ hδ
  have hρ0 : (0:ℝ) ≤ ρ := by linarith [hδ.1, hδ.2]
  have h0mem : (0:ℝ) ∈ Set.Icc (-ρ) ρ := ⟨by linarith, hρ0⟩
  have hsub : Set.uIcc (0:ℝ) δ ⊆ Set.Icc (-ρ) ρ := Set.uIcc_subset_Icc h0mem hδ
  have hD : ∀ s ∈ Set.uIcc (0:ℝ) δ,
      HasDerivWithinAt f (f' s) (Set.uIcc (0:ℝ) δ) s :=
    fun s hs => (hd s (hsub hs)).hasDerivWithinAt
  have hB : ∀ s ∈ Set.uIcc (0:ℝ) δ, ‖f' s‖ ≤ Mc := fun s hs => by
    rw [Real.norm_eq_abs]; exact hM s (hsub hs)
  have := (convex_uIcc (0:ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le hD hB
    Set.left_mem_uIcc Set.right_mem_uIcc
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at this

/-- **A uniform `O(δ)` bound from analyticity and a vanishing boundary value.**  If `F` is
analytic on the box `|r - r₀| < w`, `|δ| ≤ ρ` and vanishes identically on the slice `δ = 0`,
then on the half-box it satisfies `|F(r,δ)| ≤ L |δ|` for one constant `L`.

This is the generic device behind the a-priori estimates on the Kenyon–Radin–Ren–Sadun
parameters: `c(ε,0) = 0` and `q₂₂(ε,0) = ε` turn into `c = O(δ)` and `q₂₂ - ε = O(δ)`, and
subtracting the boundary values of `q₁₂`, `q₁₁` does the same for those.  The proof is the
`Mc₀` pattern of the chart: `dDelta F` is analytic, hence continuous, hence bounded on the
compact box, and the mean value theorem in `δ` finishes. -/
theorem exists_lipschitz_bound_of_boundary_zero {F : ℝ × ℝ → ℝ} {r₀ w ρ : ℝ}
    (hw : 0 < w) (hρ : 0 < ρ)
    (hF : ∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ → AnalyticAt ℝ F (r, δ))
    (hF0 : ∀ r : ℝ, |r - r₀| < w → F (r, 0) = 0) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ r δ : ℝ, |r - r₀| ≤ w / 2 → |δ| ≤ ρ / 2 → |F (r, δ)| ≤ L * |δ| := by
  classical
  obtain ⟨S, hS_def⟩ : ∃ S : Set (ℝ × ℝ),
      S = Set.Icc (r₀ - w / 2) (r₀ + w / 2) ×ˢ Set.Icc (-(ρ / 2)) (ρ / 2) := ⟨_, rfl⟩
  have hScomp : IsCompact S := by rw [hS_def]; exact isCompact_Icc.prod isCompact_Icc
  have hSmem : ∀ r δ : ℝ, |r - r₀| ≤ w / 2 → |δ| ≤ ρ / 2 → ((r, δ) : ℝ × ℝ) ∈ S := by
    intro r δ hr hδ
    rw [hS_def]
    have h1 := abs_le.mp hr
    have h2 := abs_le.mp hδ
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨h2.1, h2.2⟩⟩
  have hSbox : ∀ q ∈ S, |q.1 - r₀| < w ∧ |q.2| ≤ ρ := by
    intro q hq
    rw [hS_def] at hq
    obtain ⟨hq1, hq2⟩ := hq
    refine ⟨abs_lt.mpr ⟨by linarith [hq1.1], by linarith [hq1.2]⟩, ?_⟩
    exact abs_le.mpr ⟨by linarith [hq2.1], by linarith [hq2.2]⟩
  have hFA : ∀ q ∈ S, AnalyticAt ℝ F q := by
    intro q hq
    obtain ⟨h1, h2⟩ := hSbox q hq
    have := hF q.1 q.2 h1 h2
    rwa [Prod.mk.eta] at this
  obtain ⟨L₀, hL₀⟩ := hScomp.exists_bound_of_continuousOn
    (fun q hq => ((analyticAt_dDelta (hFA q hq)).continuousAt).continuousWithinAt)
  obtain ⟨L, hL_def⟩ : ∃ x : ℝ, x = max L₀ 0 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL_def]; exact le_max_right _ _
  refine ⟨L, hL0, ?_⟩
  intro r δ hr hδ
  have hrw : |r - r₀| < w := lt_of_le_of_lt hr (by linarith)
  have hdiff : ∀ t ∈ Set.Icc (-(ρ / 2)) (ρ / 2),
      HasDerivAt (fun s => F (r, s)) (dDelta F (r, t)) t := by
    intro t ht
    have htρ : |t| ≤ ρ := le_trans (abs_le.mpr ⟨ht.1, ht.2⟩) (by linarith)
    exact hasDerivAt_dDelta (hF r t hrw htρ).differentiableAt
  have hbd : ∀ t ∈ Set.Icc (-(ρ / 2)) (ρ / 2), |dDelta F (r, t)| ≤ L := by
    intro t ht
    have hmem : ((r, t) : ℝ × ℝ) ∈ S := hSmem r t hr (abs_le.mpr ⟨ht.1, ht.2⟩)
    have := hL₀ _ hmem
    rw [Real.norm_eq_abs] at this
    rw [hL_def]
    exact le_trans this (le_max_left _ _)
  have hmain := abs_sub_le_of_deriv_bound (f := fun s => F (r, s))
    (f' := fun s => dDelta F (r, s)) hdiff hbd δ (Set.mem_Icc.mpr (abs_le.mp hδ))
  rwa [hF0 r hrw, sub_zero] at hmain

end UpperTailOptimizers
