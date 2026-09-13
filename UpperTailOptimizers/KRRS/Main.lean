import UpperTailOptimizers.Bipodality.Optimal

/-!
# Appendix A: the compact-uniform Kenyon–Radin–Ren–Sadun theorem

This file is the final assembly of Appendix A of `paper/bipodal_optimizer.tex`.  It proves the
master rectangle theorem `krrs_rectangle` and the four public forms of
`thm:krrs-analytic-extension` (`kenyonRadinRenSadun`, `kenyonRadinRenSadunAnalytic`,
`kenyonRadinRenSadunStrip`, `kenyonRadinRenSadunUniform`), with no Kenyon–Radin–Ren–Sadun
input: the bipodality of fixed-density entropy maximizers (`thm:krrs-bipodality`, KRR–S
Theorem 1.1) is proved for `d`-regular `H` in `UpperTailOptimizers/Bipodality/`.

## The argument

1. **The family** (`KRRS/FamilyCore.lean`).  The base point is `(ε₀, a₀, b₀, 0)` with
   `b₀ = ζ_d(ε₀)` (`KRRS/PsiExists.lean`) and `a₀ = a_d(ε₀)` the unique solution of
   `F₁(ε₀,·,b₀,0) = 0` (`KRRS/BasePoint.lean`).  The pode-size chart `exists_C_chart` and
   `exists_stationary_family` give the two-sided analytic family `(q₁₁, q₁₂, c)` of stationary
   bipodal parameters with its local uniqueness, packaged as `KRRSFamily`
   (`krrs_family_exists`).
2. **Optimality** (`Bipodality/Optimal.lean`).  For `ε` near `ε₀` and small `ϑ > 0`, every
   entropy maximizer at `(ε, ε^m + ϑ)` is a relabelling of the family's bipodal graphon
   (`KRRSFamily.isOptimal`).  The proof runs through the Euler–Lagrange equation, row balance,
   the two-cluster structure forced by `Γ^gap`, a contraction estimate making the rows of each
   cluster equal, and the local uniqueness of stationary bipodal parameters (draft
   `paper/sections/krrs_bipodality_draft.tex`).
3. `krrs_rectangle_of_isOptimal` (`KRRS/FamilyCore.lean`) turns optimality into the rectangle
   theorem, and the public forms are corollaries.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Filter Topology

/-! ### The master rectangle theorem -/

/-- **The master rectangle theorem of Appendix A.**  Near a nonexceptional edge density
`ε₀` there are a window `U ∋ ε₀`, a surplus bound `Δ > 0`, and four functions of
`(ε, ϑ = τ - ε^m)` — real-analytic at every point of the two-sided strip
`{(ε, ϑ) : ε ∈ U, |ϑ| < Δ}` — such that on the
positive-surplus regime the entropy maximizer at `(ε, τ)` is the bipodal graphon with those
parameters, and is unique up to relabelling; at `ϑ = 0` the parameters take the degenerate
values `c = 0`, `q₂₂ = ε`, `q₁₂ = ζ_d(ε) ≠ ε`, `q₁₁ = a_d(ε)`.

The boundary clause states the property that defines the cross value: `q₁₂(ε,0)` maximises
`ψ_d(ε,·)` over `(0,1) ∖ {ε}`.

All four public forms of `thm:krrs-analytic-extension` and `zeta_analytic` are immediate
corollaries. -/
theorem krrs_rectangle {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hε₀ : ε₀ ≠ rStar d) :
    ∃ (U : Set ℝ) (Δ : ℝ) (q11 q12 q22 c : ℝ → ℝ → ℝ), IsOpen U ∧ ε₀ ∈ U ∧ 0 < Δ ∧
      (∀ ε ∈ U, ∀ ϑ : ℝ, |ϑ| < Δ →
        AnalyticAt ℝ (fun p : ℝ × ℝ => q11 p.1 p.2) (ε, ϑ) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q12 p.1 p.2) (ε, ϑ) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q22 p.1 p.2) (ε, ϑ) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => c p.1 p.2) (ε, ϑ)) ∧
      (∀ ε ∈ U, c ε 0 = 0 ∧ q22 ε 0 = ε ∧
        q11 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ≠ ε ∧
        (∀ w ∈ Set.Ioo (0:ℝ) 1, w ≠ ε → psiD d ε w ≤ psiD d ε (q12 ε 0))) ∧
      (∀ ε ∈ U, ∀ τ : ℝ, 0 < τ - ε ^ H.edgeFinset.card →
        τ - ε ^ H.edgeFinset.card < Δ →
        q11 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
        q12 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
        q22 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
        c ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
        ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧ IsBipodal W ∧
          (∀ᵐ z ∂gμ, W.toFun z.1 z.2
            = bipodalValue (Set.Icc 0 (c ε (τ - ε ^ H.edgeFinset.card)))
                (q11 ε (τ - ε ^ H.edgeFinset.card))
                (q12 ε (τ - ε ^ H.edgeFinset.card))
                (q22 ε (τ - ε ^ H.edgeFinset.card)) z) ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
            W'.entropy ≤ W.entropy) ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
            W'.entropy = W.entropy →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2))) :=
  krrs_rectangle_of_isOptimal H hd hreg hm hε₀0 hε₀1 hε₀ fun F =>
    F.isOptimal hd hreg hm ⟨hε₀0, hε₀1⟩ hε₀

/-! ### The public forms of `thm:krrs-analytic-extension` -/

/-- **`thm:krrs-analytic-extension`**, proved in Appendix A style; the bipodality input is
`KRRSFamily.isOptimal`.

Away from the exceptional density `(d-1)/d`, the entropy maximizer at fixed edge density
`ε` and fixed `H`-density `τ = ε^m + δ` (small `δ > 0`) exists, is bipodal, and is unique up
to relabelling: any other maximizer `W'` equals `W` relabelled by a measure-preserving
transformation `σ` of `[0,1]`.

(Kenyon–Radin–Ren–Sadun, arXiv:1509.05370, `thm:krrs-bipodality`; the compact-uniform organisation is
Appendix A of `paper/bipodal_optimizer.tex`.) -/
theorem kenyonRadinRenSadun {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₀ : ε₀ ≠ rStar d) :
    ∃ (U : Set ℝ) (Δ : ℝ), IsOpen U ∧ ε₀ ∈ U ∧ 0 < Δ ∧
      ∀ ε ∈ U, ∀ τ : ℝ, 0 < τ - ε ^ (H.edgeFinset.card) →
        τ - ε ^ (H.edgeFinset.card) < Δ →
        ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧ IsBipodal W ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ → W'.entropy ≤ W.entropy) ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ → W'.entropy = W.entropy →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) := by
  obtain ⟨U, Δ, q11, q12, q22, c, hUopen, hε₀U, hΔ0, -, -, hmain⟩ :=
    krrs_rectangle H hd hreg hm hε₀0 hε₀1 hε₀
  refine ⟨U, Δ, hUopen, hε₀U, hΔ0, fun ε hε τ h1 h2 => ?_⟩
  obtain ⟨-, -, -, -, W, hWe, hWt, hWbip, -, hWmax, hWuniq⟩ := hmain ε hε τ h1 h2
  exact ⟨W, hWe, hWt, hWbip, hWmax, hWuniq⟩

/-- **`thm:krrs-analytic-extension`, analytic-parametrization clause**, proved in
`krrs_rectangle` above from the analytic inverse function theorem and the optimality of the
analytic family (Appendix A of `paper/bipodal_optimizer.tex`).

The bipodal parameters `(q₁₁, q₁₂, q₂₂, c)` of the fixed-`(e, t_H)` entropy maximizer are
jointly real-analytic in `(ε, δ)` at the degenerate boundary `δ = 0`, with degenerate values
`c(ε,0) = 0`, `q₂₂(ε,0) = ε`, `q₁₂(ε,0) = ζ_d(ε) ≠ ε` and `q₁₁(ε,0) = a_d(ε)`, all block
densities being interior there.  The cross value is stated through its defining property:
`q₁₂(ε,0)` maximises `ψ_d(ε,·)` over `(0,1) ∖ {ε}`.  See `krrs_rectangle`.
Analyticity is stated here only on the boundary slice `δ = 0`, which is what the consumers
use; `kenyonRadinRenSadunStrip` below carries the paper's full strip `U × (−Δ, Δ)`.
On `0 < δ < Δ` the concrete two-block graphon with these
parameters and block `A = [0,c]` is an entropy maximizer at `(e, t_H) = (ε, τ)`.  The
paper's clause `c(ε,δ) = O(δ)` is not restated here: analyticity and `c(ε,0) = 0` give it
*locally* uniformly in `ε`, but `\Cref{thm:krrs-analytic-extension}` asks for it uniformly on `U`.  That form is
`kenyonRadinRenSadunUniform` below, which carries every clause of this theorem together with a
single constant, on a possibly smaller rectangle. -/
theorem kenyonRadinRenSadunAnalytic {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₀ : ε₀ ≠ rStar d) :
    ∃ (U : Set ℝ) (Δ : ℝ) (q11 q12 q22 c : ℝ → ℝ → ℝ), IsOpen U ∧ ε₀ ∈ U ∧ 0 < Δ ∧
      (∀ ε ∈ U,
        AnalyticAt ℝ (fun p : ℝ × ℝ => q11 p.1 p.2) (ε, 0) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q12 p.1 p.2) (ε, 0) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q22 p.1 p.2) (ε, 0) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => c p.1 p.2) (ε, 0)) ∧
      (∀ ε ∈ U, c ε 0 = 0 ∧ q22 ε 0 = ε ∧
        q11 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ≠ ε ∧
        (∀ w ∈ Set.Ioo (0:ℝ) 1, w ≠ ε → psiD d ε w ≤ psiD d ε (q12 ε 0))) ∧
      (∀ ε ∈ U, ∀ τ : ℝ, 0 < τ - ε ^ (H.edgeFinset.card) →
        τ - ε ^ (H.edgeFinset.card) < Δ →
        q11 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        q12 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        q22 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        c ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
            W'.entropy ≤ W.entropy) ∧
          (∀ᵐ z ∂gμ, W.toFun z.1 z.2
            = bipodalValue (Set.Icc 0 (c ε (τ - ε ^ H.edgeFinset.card)))
                (q11 ε (τ - ε ^ H.edgeFinset.card))
                (q12 ε (τ - ε ^ H.edgeFinset.card))
                (q22 ε (τ - ε ^ H.edgeFinset.card)) z)) := by
  obtain ⟨U, Δ, q11, q12, q22, c, hUopen, hε₀U, hΔ0, hana, hbdry, hmain⟩ :=
    krrs_rectangle H hd hreg hm hε₀0 hε₀1 hε₀
  refine ⟨U, Δ, q11, q12, q22, c, hUopen, hε₀U, hΔ0,
    fun ε hε => hana ε hε 0 (by rw [abs_zero]; exact hΔ0), hbdry, fun ε hε τ h1 h2 => ?_⟩
  obtain ⟨g11, g12, g22, gc, W, hWe, hWt, -, hWae, hWmax, -⟩ := hmain ε hε τ h1 h2
  exact ⟨Set.Ioo_subset_Icc_self g11, Set.Ioo_subset_Icc_self g12,
    Set.Ioo_subset_Icc_self g22, Set.Ioo_subset_Icc_self gc, W, hWe, hWt, hWmax, hWae⟩

/-- **`thm:krrs-analytic-extension`, the two-sided continuation as the paper states it.**

`thm:krrs-analytic-extension` asserts that the parameter map "extends real-analytically to `U × (−Δ, Δ)`", and
that extension *is* what the theorem adds to Kenyon–Radin–Ren–Sadun, who define the map only
for `ϑ > 0`.  The paper needs it because the later analysis differentiates the map and
Taylor-expands it at the boundary `ϑ = 0`.

`kenyonRadinRenSadunAnalytic` states the analyticity only on the boundary slice `U × {0}`,
which is all its consumers use.  This is the strip, on the same `U` and `Δ` those two theorems
take from `krrs_rectangle`: analyticity at *every* point of `U × (−Δ, Δ)`, which is
`AnalyticOnNhd ℝ · (U ×ˢ Set.Ioo (-Δ) Δ)` written pointwise.

For `ϑ < 0` the values are only the analytic continuation — as `paper/bipodal_optimizer.tex` says
immediately after the theorem, they describe no entropy maximizer, and nothing here claims
they do — this theorem states no maximizer clause at all.  The positive-surplus maximizer is
`kenyonRadinRenSadun` / `kenyonRadinRenSadunAnalytic`, built from the same `krrs_rectangle`
witnesses `U` and `Δ`. -/
theorem kenyonRadinRenSadunStrip {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₀ : ε₀ ≠ rStar d) :
    ∃ (U : Set ℝ) (Δ : ℝ) (q11 q12 q22 c : ℝ → ℝ → ℝ), IsOpen U ∧ ε₀ ∈ U ∧ 0 < Δ ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => q11 p.1 p.2) (U ×ˢ Set.Ioo (-Δ) Δ) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => q12 p.1 p.2) (U ×ˢ Set.Ioo (-Δ) Δ) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => q22 p.1 p.2) (U ×ˢ Set.Ioo (-Δ) Δ) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => c p.1 p.2) (U ×ˢ Set.Ioo (-Δ) Δ) ∧
      (∀ ε ∈ U, c ε 0 = 0 ∧ q22 ε 0 = ε ∧
        q11 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ≠ ε ∧
        (∀ w ∈ Set.Ioo (0:ℝ) 1, w ≠ ε → psiD d ε w ≤ psiD d ε (q12 ε 0))) := by
  obtain ⟨U, Δ, q11, q12, q22, c, hUopen, hε₀U, hΔ0, hana, hbdry, -⟩ :=
    krrs_rectangle H hd hreg hm hε₀0 hε₀1 hε₀
  have habs : ∀ p : ℝ × ℝ, p ∈ U ×ˢ Set.Ioo (-Δ) Δ → p.1 ∈ U ∧ |p.2| < Δ := by
    rintro ⟨ε, ϑ⟩ ⟨hε, hϑ1, hϑ2⟩
    exact ⟨hε, abs_lt.mpr ⟨hϑ1, hϑ2⟩⟩
  exact ⟨U, Δ, q11, q12, q22, c, hUopen, hε₀U, hΔ0,
    fun p hp => (hana p.1 (habs p hp).1 p.2 (habs p hp).2).1,
    fun p hp => (hana p.1 (habs p hp).1 p.2 (habs p hp).2).2.1,
    fun p hp => (hana p.1 (habs p hp).1 p.2 (habs p hp).2).2.2.1,
    fun p hp => (hana p.1 (habs p hp).1 p.2 (habs p hp).2).2.2.2,
    hbdry⟩

/-! ## The uniform `c = O(ϑ)` clause

`\Cref{thm:krrs-analytic-extension}` asserts `c(ε,ϑ) = O(ϑ)` as `ϑ ↓ 0` **uniformly for `ε ∈ U`**.  Analyticity
together with `c(ε,0) = 0` gives this only *locally* uniformly, which is why the clause was
long left unstated.  But the theorem is free to shrink `U`, and after shrinking to a ball whose
closure sits inside the analytic region the bound is genuinely uniform: `fderiv c` is analytic
there, hence continuous, hence bounded on the compact closed ball, and the mean value
inequality along the segment from `(ε,0)` to `(ε,ϑ)` — which stays in the ball, the ball being
convex — turns that bound into `|c(ε,ϑ)| ≤ C|ϑ|`. -/

/-- **An analytic function vanishing on a horizontal slice is uniformly `O` of the second
coordinate.**  This is the shrinking argument, isolated from the KRR–S setting. -/
theorem exists_uniform_linear_bound {f : ℝ × ℝ → ℝ} {x₀ : ℝ}
    (hf : AnalyticAt ℝ f (x₀, 0)) (hzero : ∀ᶠ x in nhds x₀, f (x, 0) = 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ x y : ℝ, |x - x₀| < r → |y| < r → |f (x, y)| ≤ C * |y| := by
  -- a ball on which `f` is analytic at every point
  obtain ⟨r₁, hr₁0, hr₁⟩ :=
    Metric.mem_nhds_iff.mp (hf.eventually_analyticAt)
  -- a ball on which the slice vanishes
  obtain ⟨r₂, hr₂0, hr₂⟩ := Metric.mem_nhds_iff.mp hzero
  obtain ⟨r, hrdef⟩ : ∃ t : ℝ, t = min (r₁ / 2) (r₂ / 2) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; exact lt_min (by linarith) (by linarith)
  have hrr₁ : r < r₁ := by rw [hrdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrr₂ : r < r₂ := by rw [hrdef]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨S, hSdef⟩ : ∃ T : Set (ℝ × ℝ), T = Metric.closedBall ((x₀, 0) : ℝ × ℝ) r := ⟨_, rfl⟩
  have hSsub : S ⊆ Metric.ball ((x₀, 0) : ℝ × ℝ) r₁ := by
    rw [hSdef]
    exact fun p hp => Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hp) hrr₁)
  have hana : AnalyticOnNhd ℝ f (Metric.ball ((x₀, 0) : ℝ × ℝ) r₁) := fun p hp => hr₁ hp
  -- `fderiv f` is analytic, hence continuous, on the same ball
  have hfd : AnalyticOnNhd ℝ (fderiv ℝ f) (Metric.ball ((x₀, 0) : ℝ × ℝ) r₁) :=
    hana.fderiv_of_isOpen Metric.isOpen_ball
  have hcont : ContinuousOn (fderiv ℝ f) S :=
    (hfd.continuousOn).mono hSsub
  obtain ⟨C₀, hC₀⟩ := (by rw [hSdef]; exact isCompact_closedBall _ _ : IsCompact S)
    |>.exists_bound_of_continuousOn hcont
  obtain ⟨C, hCdef⟩ : ∃ t : ℝ, t = max C₀ 1 := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hCdef]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨r, C, hr0, hC0, fun x y hx hy => ?_⟩
  -- the two endpoints of the segment lie in `S`
  have hmem0 : ((x, 0) : ℝ × ℝ) ∈ S := by
    rw [hSdef, Metric.mem_closedBall, Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero, abs_zero]
    exact max_le hx.le (by linarith [abs_nonneg (x - x₀)])
  have hmemy : ((x, y) : ℝ × ℝ) ∈ S := by
    rw [hSdef, Metric.mem_closedBall, Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero]
    exact max_le hx.le hy.le
  -- the slice vanishes at `x`
  have hslice : f (x, 0) = 0 := by
    refine hr₂ (Metric.mem_ball.mpr ?_)
    rw [Real.dist_eq]
    exact lt_trans hx hrr₂
  -- the mean value inequality on the convex ball
  have hdiff : ∀ p ∈ S, DifferentiableAt ℝ f p := fun p hp => (hana p (hSsub hp)).differentiableAt
  have hbound : ∀ p ∈ S, ‖fderiv ℝ f p‖ ≤ C := fun p hp =>
    le_trans (hC₀ p hp) (by rw [hCdef]; exact le_max_left _ _)
  have hconv : Convex ℝ S := by rw [hSdef]; exact convex_closedBall _ _
  have hmv := hconv.norm_image_sub_le_of_norm_fderiv_le hdiff hbound hmem0 hmemy
  have hnorm : ‖((x, y) : ℝ × ℝ) - ((x, 0) : ℝ × ℝ)‖ = |y| := by
    rw [Prod.norm_def]
    simp
  rw [hslice, sub_zero, Real.norm_eq_abs, hnorm] at hmv
  exact hmv

/-- **`thm:krrs-analytic-extension`, full form.**

`kenyonRadinRenSadunAnalytic` together with the paper's uniform smallness clause

`c(ε,ϑ) = O(ϑ)  (ϑ ↓ 0),  uniformly for ε ∈ U`,

on a possibly smaller rectangle.  `\Cref{thm:krrs-analytic-extension}` asks for uniformity over the whole of `U`,
not merely local uniformity, and analyticity alone does not give that — but the theorem chooses
`U`, so shrinking it to a ball with compact closure inside the analytic region is free, and
`exists_uniform_linear_bound` then supplies a single constant.  Every other clause is of the
form `∀ ε ∈ U, …` or `∀ ε ∈ U, ∀ τ, … < Δ → …`, so all of them survive the shrinking. -/
theorem kenyonRadinRenSadunUniform {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₀ : ε₀ ≠ rStar d) :
    ∃ (U : Set ℝ) (Δ C : ℝ) (q11 q12 q22 c : ℝ → ℝ → ℝ),
      IsOpen U ∧ ε₀ ∈ U ∧ 0 < Δ ∧ 0 < C ∧
      (∀ ε ∈ U,
        AnalyticAt ℝ (fun p : ℝ × ℝ => q11 p.1 p.2) (ε, 0) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q12 p.1 p.2) (ε, 0) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q22 p.1 p.2) (ε, 0) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => c p.1 p.2) (ε, 0)) ∧
      (∀ ε ∈ U, c ε 0 = 0 ∧ q22 ε 0 = ε ∧
        q11 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ≠ ε ∧
        (∀ w ∈ Set.Ioo (0:ℝ) 1, w ≠ ε → psiD d ε w ≤ psiD d ε (q12 ε 0))) ∧
      (∀ ε ∈ U, ∀ ϑ : ℝ, 0 ≤ ϑ → ϑ < Δ → |c ε ϑ| ≤ C * ϑ) ∧
      (∀ ε ∈ U, ∀ τ : ℝ, 0 < τ - ε ^ (H.edgeFinset.card) →
        τ - ε ^ (H.edgeFinset.card) < Δ →
        q11 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        q12 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        q22 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        c ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
            W'.entropy ≤ W.entropy) ∧
          (∀ᵐ z ∂gμ, W.toFun z.1 z.2
            = bipodalValue (Set.Icc 0 (c ε (τ - ε ^ H.edgeFinset.card)))
                (q11 ε (τ - ε ^ H.edgeFinset.card))
                (q12 ε (τ - ε ^ H.edgeFinset.card))
                (q22 ε (τ - ε ^ H.edgeFinset.card)) z)) := by
  obtain ⟨U₀, Δ₀, q11, q12, q22, c, hU₀open, hε₀U₀, hΔ₀0, hana, hbdry, hmain⟩ :=
    krrs_rectangle H hd hreg hm hε₀0 hε₀1 hε₀
  -- the shrinking argument, applied to `c`
  have hzero : ∀ᶠ x in nhds ε₀, (fun p : ℝ × ℝ => c p.1 p.2) (x, 0) = 0 :=
    Filter.eventually_of_mem (hU₀open.mem_nhds hε₀U₀) fun x hx => (hbdry x hx).1
  obtain ⟨r, C, hr0, hC0, hlin⟩ :=
    exists_uniform_linear_bound (f := fun p : ℝ × ℝ => c p.1 p.2)
      (hana ε₀ hε₀U₀ 0 (by rw [abs_zero]; exact hΔ₀0)).2.2.2 hzero
  refine ⟨U₀ ∩ Metric.ball ε₀ r, min Δ₀ r, C, q11, q12, q22, c,
    hU₀open.inter Metric.isOpen_ball, ⟨hε₀U₀, Metric.mem_ball_self hr0⟩,
    lt_min hΔ₀0 hr0, hC0,
    fun ε hε => hana ε hε.1 0 (by rw [abs_zero]; exact hΔ₀0),
    fun ε hε => hbdry ε hε.1, ?_, ?_⟩
  · intro ε hε ϑ hϑ0 hϑΔ
    have hx : |ε - ε₀| < r := by
      have := Metric.mem_ball.mp hε.2
      rwa [Real.dist_eq] at this
    have hy : |ϑ| < r := by
      rw [abs_of_nonneg hϑ0]
      exact lt_of_lt_of_le hϑΔ (min_le_right _ _)
    have := hlin ε ϑ hx hy
    rwa [abs_of_nonneg hϑ0] at this
  · intro ε hε τ h1 h2
    obtain ⟨g11, g12, g22, gc, W, hWe, hWt, -, hWae, hWmax, -⟩ :=
      hmain ε hε.1 τ h1 (lt_of_lt_of_le h2 (min_le_left _ _))
    exact ⟨Set.Ioo_subset_Icc_self g11, Set.Ioo_subset_Icc_self g12,
      Set.Ioo_subset_Icc_self g22, Set.Ioo_subset_Icc_self gc, W, hWe, hWt, hWmax, hWae⟩

/-! ### Real-analyticity of `ζ_d` -/

/-- **`ζ_d` is real-analytic on `(0,1) ∖ {(d-1)/d}`.**  This is `paper/bipodal_optimizer.tex`'s remark
that "\Cref{thm:krrs-analytic-extension} below also implies that `ζ_d` is real-analytic on
`(0,1) ∖ {(d-1)/d}`", read off `krrs_rectangle`: the boundary value `ε ↦ q₁₂(ε,0)` is
analytic (restrict the joint analyticity at `(ε,0)` to the horizontal slice) and it has the
defining property of `ζ_d(ε)` — it lies in `(0,1)`, differs from `ε`, and maximises
`ψ_d(ε,·)` off the diagonal.

The guard `w ≠ ε` is Lean's, not the paper's: `psiD d ε ε` is the junk value `0/0 = 0` rather
than the honest limit.

The selector produced here is *the* `ζ_d`: `zetaFun_isMax` gives `psiD d ε (zeta ε) ≤
psiD d ε (zetaFun d ε)` and the clause below gives the reverse, so the two agree because the
maximizer is unique (`thm:krrs-cross-density`). -/
theorem zeta_analytic {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₀ : ε₀ ≠ rStar d) :
    ∃ (U : Set ℝ) (zeta : ℝ → ℝ), IsOpen U ∧ ε₀ ∈ U ∧
      ∀ ε ∈ U, AnalyticAt ℝ zeta ε ∧ zeta ε ∈ Set.Ioo (0:ℝ) 1 ∧ zeta ε ≠ ε ∧
        ∀ w ∈ Set.Ioo (0:ℝ) 1, w ≠ ε → psiD d ε w ≤ psiD d ε (zeta ε) := by
  obtain ⟨U, Δ, q11, q12, q22, c, hUopen, hε₀U, hΔ0, hana, hbdry, -⟩ :=
    krrs_rectangle H hd hreg hm hε₀0 hε₀1 hε₀
  refine ⟨U, fun ε => q12 ε 0, hUopen, hε₀U, fun ε hε => ?_⟩
  obtain ⟨-, -, -, h12, hne, hmax⟩ := hbdry ε hε
  exact ⟨(hana ε hε 0 (by rw [abs_zero]; exact hΔ0)).2.1.fun_comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl,
    h12, hne, hmax⟩

end UpperTailOptimizers
