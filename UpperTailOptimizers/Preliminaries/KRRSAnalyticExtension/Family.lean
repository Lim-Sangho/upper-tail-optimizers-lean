import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.Stationarity
import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.CChart

/-!
# `eq:krrs-stationary-densities`: the analytic stationary family `a_*(ε,ϑ)`, `b_*(ε,ϑ)`

Paragraph 3 of Appendix B of `paper/paper.tex` solves its stationarity system
`𝓕₁ = 𝓕₂ = 0` (`eq:krrs-small-block-stationarity`, `eq:krrs-cross-block-stationarity`) for
`(a,b)` as real-analytic functions of `(ε,ϑ)` on a **two-sided** window around `(ε₀, 0)`.
Here the same step is run on the `c`-normalised system `F₁, F₂` of `Preliminaries/KRRSAnalyticExtension/Stationarity.lean`,
into which the pode size chart `c = C(ε,a,b,ϑ)` of `eq:krrs-density-constraint` is substituted,
giving a `2 × 2` system in `(a,b)` with parameters `(ε,ϑ)`.

## Why the inverse function theorem again

As in `Preliminaries/KRRSAnalyticExtension/CChart.lean`, `analytic_inverse` is used rather than a bare implicit function
theorem: the appendix needs the *uniqueness* of the family inside the source window (that
is what pins the parameters of the KRR–S maximizer), and `analytic_inverse` supplies it as
`Set.InjOn`.  The map inverted is

  `Ψ(ε,a,b,ϑ) = (ε, F̃₁(ε,a,b,ϑ), F̃₂(ε,a,b,ϑ), ϑ)`   (`familyPsi`),
  `F̃ᵢ(ε,a,b,ϑ) := Fᵢ(ε, a, b, C(ε,a,b,ϑ))`.

## Why the Jacobian is triangular

`C(ε,a,b,0) = 0` holds *pointwise on the whole `ϑ = 0` slice* of the chart's source window,
not merely at the base point (`exists_C_chart`).  Hence `a ↦ C(ε₀,a,b₀,0)` and
`b ↦ C(ε₀,a₀,b,0)` are locally constant `0`, so along the `ϑ = 0` slice the chain rule
contributes nothing through `C` and

  `∂_aF̃₁ = ∂_aF₁|_{c=0}`,  `∂_aF̃₂ = ∂_aF₂|_{c=0}`,  `∂_bF̃₂ = ∂_bF₂|_{c=0}`,

which are the counterparts of `eq:krrs-jacobian-aa`, `eq:krrs-jacobian-ba`, `eq:krrs-jacobian-bb`
(in the normalisation of `Preliminaries/KRRSAnalyticExtension/Stationarity.lean`) as evaluated by
`F_jacobian_nondegenerate`: the `(a,b)`-block of `DΨ` is `[[A, B], [0, D]]` with
`A = S₀''(a₀)𝒜(ε₀,b₀) ≠ 0` and `D = n ε₀^{m-d} dWr_d(ε₀,b₀) ≠ 0`, so `DΨ` is invertible and
its inverse is written down by back-substitution.

## Contents

* `exists_stationary_family` — **`eq:krrs-stationary-densities`**: the analytic family `a_*`, `b_*` on a
  two-sided rectangle `|ε - ε₀| < r`, `|ϑ| < r`, solving `F̃₁ = F̃₂ = 0`, together with its
  local uniqueness inside the source window `S`.

That is the whole interface.  The map `Ψ` itself, its joint analyticity, the analyticity of
the chart substitution and of `F̃₁`, `F̃₂`, and the invertible linearisation `DΨ` at
`(ε₀,a₀,b₀,0)` are all file-private: they exist only to feed `analytic_inverse`.

The chart `C` is taken as an explicit hypothesis (its analyticity and the identity
`C(·,·,·,0) = 0` near the base point), rather than re-derived: both clauses are literally
two of the conclusions of `exists_C_chart`, and passing them keeps the statements readable.
The first-equation base condition `F₁(ε₀,a₀,b₀,0) = 0` is likewise a hypothesis.  The paper
takes `a₀ = a_d(ε₀)`, the limiting first-block density of `thm:krrs-bipodality`, and obtains
`𝓕₁ = 𝓕₂ = 0` at the base point (`eq:krrs-boundary-stationarity`) by letting `ϑ ↓ 0` along
the KRR–S maximizers; here `F₁ = 0` is instead the defining property of the explicit base
point `baseA` of `Preliminaries/KRRSAnalyticExtension/BasePoint.lean`, while `F₂(ε₀,a₀,b₀,0) = 0` follows from the
critical-point property of `b₀` (`F_jacobian_nondegenerate`).
-/

namespace UpperTailOptimizers

open Filter Topology

/-! ### The composed stationarity map `Ψ` -/

/-- **The composed stationarity map of `eq:krrs-stationary-densities`**,
`Ψ(ε,a,b,ϑ) = (ε, F₁(ε,a,b,C(ε,a,b,ϑ)), F₂(ε,a,b,C(ε,a,b,ϑ)), ϑ)`.

Solving the desingularized stationarity system along the chart is inverting `Ψ`: the second
and third coordinates of `Ψ` are the two equations, and the parameters `(ε,ϑ)` are carried
along unchanged in the first and fourth. -/
private noncomputable def familyPsi {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (C : ℝ → ℝ → ℝ → ℝ → ℝ) (w : ℝ × ℝ × ℝ × ℝ) :
    ℝ × ℝ × ℝ × ℝ :=
  (w.1, F1 H d w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2),
    F2 H d w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2), w.2.2.2)

/-- The chart substitution `w ↦ (ε, a, b, C(ε,a,b,ϑ))` of `eq:krrs-density-constraint` is analytic
at the degenerate base point, since `C` is. -/
private theorem analyticAt_chartSub {C : ℝ → ℝ → ℝ → ℝ → ℝ} {ε₀ a₀ b₀ : ℝ}
    (hCana : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => C w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ)) :
    AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ =>
      ((w.1, w.2.1, w.2.2.1, C w.1 w.2.1 w.2.2.1 w.2.2.2) : ℝ × ℝ × ℝ × ℝ))
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) :=
  (analyticAt_fst4 _).prod ((analyticAt_snd4 _).prod ((analyticAt_thd4 _).prod hCana))

/-- The chart substitution fixes the degenerate base point, because `C(ε₀,a₀,b₀,0) = 0`. -/
private theorem chartSub_base {C : ℝ → ℝ → ℝ → ℝ → ℝ} {ε₀ a₀ b₀ : ℝ} (hC00 : C ε₀ a₀ b₀ 0 = 0) :
    (fun w : ℝ × ℝ × ℝ × ℝ =>
      ((w.1, w.2.1, w.2.2.1, C w.1 w.2.1 w.2.2.1 w.2.2.2) : ℝ × ℝ × ℝ × ℝ))
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) = ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
  show ((ε₀, a₀, b₀, C ε₀ a₀ b₀ 0) : ℝ × ℝ × ℝ × ℝ) = ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ)
  rw [hC00]

/-- `F̃₁ = F₁ ∘ (chart substitution)` is jointly real-analytic at the degenerate base point.
The inner point is `(ε₀,a₀,b₀,0)` itself, where `Q = ε₀ ∈ (0,1)` by `Qmap_zero`, so
`analyticAt_F1` applies. -/
private theorem analyticAt_F1_chart {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) {C : ℝ → ℝ → ℝ → ℝ → ℝ} {ε₀ a₀ b₀ : ℝ}
    (hε0 : 0 < ε₀) (hε1 : ε₀ < 1) (ha0 : 0 < a₀) (ha1 : a₀ < 1)
    (hb0 : 0 < b₀) (hb1 : b₀ < 1)
    (hCana : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => C w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ))
    (hC00 : C ε₀ a₀ b₀ 0 = 0) :
    AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ =>
      F1 H d w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2))
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
  have hF : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => F1 H d w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) :=
    analyticAt_F1 H d (p := ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ)) (by norm_num) ha0 ha1 hb0 hb1
      (by simpa using hε0) (by simpa using hε1)
  exact hF.fun_comp_of_eq (analyticAt_chartSub hCana) (chartSub_base hC00)

/-- `F̃₂ = F₂ ∘ (chart substitution)` is jointly real-analytic at the degenerate base
point; the companion of `analyticAt_F1_chart`. -/
private theorem analyticAt_F2_chart {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) {C : ℝ → ℝ → ℝ → ℝ → ℝ} {ε₀ a₀ b₀ : ℝ}
    (hε0 : 0 < ε₀) (hε1 : ε₀ < 1) (ha0 : 0 < a₀) (ha1 : a₀ < 1)
    (hb0 : 0 < b₀) (hb1 : b₀ < 1)
    (hCana : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => C w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ))
    (hC00 : C ε₀ a₀ b₀ 0 = 0) :
    AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ =>
      F2 H d w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2))
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
  have hF : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => F2 H d w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) :=
    analyticAt_F2 H d (p := ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ)) (by norm_num) ha0 ha1 hb0 hb1
      (by simpa using hε0) (by simpa using hε1)
  exact hF.fun_comp_of_eq (analyticAt_chartSub hCana) (chartSub_base hC00)

/-- **`Ψ` is jointly real-analytic** at the degenerate base point: the first and fourth
coordinates are projections, the second and third are `analyticAt_F1_chart`,
`analyticAt_F2_chart`. -/
private theorem analyticAt_familyPsi {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) {C : ℝ → ℝ → ℝ → ℝ → ℝ} {ε₀ a₀ b₀ : ℝ}
    (hε0 : 0 < ε₀) (hε1 : ε₀ < 1) (ha0 : 0 < a₀) (ha1 : a₀ < 1)
    (hb0 : 0 < b₀) (hb1 : b₀ < 1)
    (hCana : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => C w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ))
    (hC00 : C ε₀ a₀ b₀ 0 = 0) :
    AnalyticAt ℝ (familyPsi H d C) ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
  have heq : familyPsi H d C = fun w : ℝ × ℝ × ℝ × ℝ =>
      ((w.1, F1 H d w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2),
        F2 H d w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2),
        w.2.2.2) : ℝ × ℝ × ℝ × ℝ) := rfl
  rw [heq]
  exact (analyticAt_fst4 _).prod
    ((analyticAt_F1_chart H d hε0 hε1 ha0 ha1 hb0 hb1 hCana hC00).prod
      ((analyticAt_F2_chart H d hε0 hε1 ha0 ha1 hb0 hb1 hCana hC00).prod (analyticAt_fth4 _)))

/-! ### The invertible linearisation of `Ψ` -/

/-- **The Jacobian of `Ψ` at `(ε₀,a₀,b₀,0)` is invertible.**

`Ψ` is the identity in the parameter slots `1` and `4`, and its `(a,b)`-block is triangular:
writing `DF̃₁(v) = p₁v₁ + p₂v₂ + p₃v₃ + p₄v₄` and `DF̃₂(v) = q₁v₁ + q₂v₂ + q₃v₃ + q₄v₄`,

* `p₂ = ∂_aF₁|_{c=0} = S₀''(a₀)𝒜(ε₀,b₀) ≠ 0` `eq:krrs-jacobian-aa`,
* `q₂ = ∂_aF₂|_{c=0} = 0` `eq:krrs-jacobian-ba`,
* `q₃ = ∂_bF₂|_{c=0} = n ε₀^{m-d} dWr_d(ε₀,b₀) ≠ 0` `eq:krrs-jacobian-bb`,

because `C(ε,a,b,0) = 0` identically near the base point, so the `a`- and `b`-lines through
the base point inside the slice `ϑ = 0` see `Fᵢ(ε₀,·,·,0)` verbatim.  The inverse is then
back-substitution: `v₃` from the third equation, then `v₂` from the second.  The remaining
partials `p₁,p₃,p₄,q₁,q₄` are carried abstractly and never inspected. -/
private theorem exists_familyPsi_strictFDeriv {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {C : ℝ → ℝ → ℝ → ℝ → ℝ} {ε₀ a₀ b₀ : ℝ}
    (hε0 : 0 < ε₀) (hε1 : ε₀ < 1) (ha0 : 0 < a₀) (ha1 : a₀ < 1)
    (hb0 : 0 < b₀) (hb1 : b₀ < 1) (hbε : b₀ ≠ ε₀) (hbstar : b₀ ≠ rStar d)
    (hmax : ∀ w, 0 < w → w < 1 → w ≠ ε₀ → psiD d ε₀ w ≤ psiD d ε₀ b₀)
    (hCana : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => C w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ))
    (hC0 : ∀ᶠ w in 𝓝 ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ), C w.1 w.2.1 w.2.2.1 0 = 0) :
    ∃ L : (ℝ × ℝ × ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ × ℝ × ℝ),
      HasStrictFDerivAt (familyPsi H d C) (L : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ × ℝ))
        ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
  classical
  have hC00 : C ε₀ a₀ b₀ 0 = 0 := hC0.self_of_nhds
  -- the four coordinate functionals of `ℝ × ℝ × ℝ × ℝ`
  set Q1 : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ) with hQ1
  set Q2 : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)) with hQ2
  set Q3 : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))) with hQ3
  set Q4 : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))) with hQ4
  -- the two nontrivial coordinates of `Ψ` and their Fréchet derivatives
  have hG1ana : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ =>
      F1 H d w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2))
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) :=
    analyticAt_F1_chart H d hε0 hε1 ha0 ha1 hb0 hb1 hCana hC00
  have hG2ana : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ =>
      F2 H d w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2))
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) :=
    analyticAt_F2_chart H d hε0 hε1 ha0 ha1 hb0 hb1 hCana hC00
  set DG1 : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (fun w : ℝ × ℝ × ℝ × ℝ =>
      F1 H d w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2))
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) with hDG1
  set DG2 : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (fun w : ℝ × ℝ × ℝ × ℝ =>
      F2 H d w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2))
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) with hDG2
  have hG1strict : HasStrictFDerivAt (fun w : ℝ × ℝ × ℝ × ℝ =>
      F1 H d w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2)) DG1
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
    rw [hDG1]; exact hG1ana.hasStrictFDerivAt
  have hG2strict : HasStrictFDerivAt (fun w : ℝ × ℝ × ℝ × ℝ =>
      F2 H d w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2)) DG2
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
    rw [hDG2]; exact hG2ana.hasStrictFDerivAt
  -- the eight partials, of which only three are needed in closed form
  obtain ⟨p1, hp1⟩ : ∃ x : ℝ, x = DG1 ((1, 0, 0, 0) : ℝ × ℝ × ℝ × ℝ) := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ x : ℝ, x = DG1 ((0, 1, 0, 0) : ℝ × ℝ × ℝ × ℝ) := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ x : ℝ, x = DG1 ((0, 0, 1, 0) : ℝ × ℝ × ℝ × ℝ) := ⟨_, rfl⟩
  obtain ⟨p4, hp4⟩ : ∃ x : ℝ, x = DG1 ((0, 0, 0, 1) : ℝ × ℝ × ℝ × ℝ) := ⟨_, rfl⟩
  obtain ⟨q1, hq1⟩ : ∃ x : ℝ, x = DG2 ((1, 0, 0, 0) : ℝ × ℝ × ℝ × ℝ) := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ x : ℝ, x = DG2 ((0, 1, 0, 0) : ℝ × ℝ × ℝ × ℝ) := ⟨_, rfl⟩
  obtain ⟨q3, hq3⟩ : ∃ x : ℝ, x = DG2 ((0, 0, 1, 0) : ℝ × ℝ × ℝ × ℝ) := ⟨_, rfl⟩
  obtain ⟨q4, hq4⟩ : ∃ x : ℝ, x = DG2 ((0, 0, 0, 1) : ℝ × ℝ × ℝ × ℝ) := ⟨_, rfl⟩
  have hsplit : ∀ v1 v2 v3 v4 : ℝ, ((v1, v2, v3, v4) : ℝ × ℝ × ℝ × ℝ)
      = v1 • ((1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ))
        + v2 • ((0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ))
        + v3 • ((0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ))
        + v4 • ((0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    intro v1 v2 v3 v4; simp
  have hDG1apply : ∀ v1 v2 v3 v4 : ℝ,
      DG1 ((v1, v2, v3, v4) : ℝ × ℝ × ℝ × ℝ) = p1 * v1 + p2 * v2 + p3 * v3 + p4 * v4 := by
    intro v1 v2 v3 v4
    rw [hp1, hp2, hp3, hp4, hsplit v1 v2 v3 v4]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have hDG2apply : ∀ v1 v2 v3 v4 : ℝ,
      DG2 ((v1, v2, v3, v4) : ℝ × ℝ × ℝ × ℝ) = q1 * v1 + q2 * v2 + q3 * v3 + q4 * v4 := by
    intro v1 v2 v3 v4
    rw [hq1, hq2, hq3, hq4, hsplit v1 v2 v3 v4]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  -- the chart vanishes identically on the `ϑ = 0` slice, along both coordinate lines
  have hCa : ∀ᶠ t in 𝓝 a₀, C ε₀ t b₀ 0 = 0 := by
    have hcont : ContinuousAt (fun t : ℝ => ((ε₀, t, b₀, 0) : ℝ × ℝ × ℝ × ℝ)) a₀ := by
      fun_prop
    simpa using hcont.eventually hC0
  have hCb : ∀ᶠ t in 𝓝 b₀, C ε₀ a₀ t 0 = 0 := by
    have hcont : ContinuousAt (fun t : ℝ => ((ε₀, a₀, t, 0) : ℝ × ℝ × ℝ × ℝ)) b₀ := by
      fun_prop
    simpa using hcont.eventually hC0
  -- the two coordinate lines through the base point inside the slice `ϑ = 0`
  have hlinea : HasDerivAt (fun t : ℝ => ((ε₀, t, b₀, 0) : ℝ × ℝ × ℝ × ℝ))
      ((0, 1, 0, 0) : ℝ × ℝ × ℝ × ℝ) a₀ :=
    (hasDerivAt_const a₀ ε₀).prodMk ((hasDerivAt_id a₀).prodMk
      ((hasDerivAt_const a₀ b₀).prodMk (hasDerivAt_const a₀ (0 : ℝ))))
  have hlineb : HasDerivAt (fun t : ℝ => ((ε₀, a₀, t, 0) : ℝ × ℝ × ℝ × ℝ))
      ((0, 0, 1, 0) : ℝ × ℝ × ℝ × ℝ) b₀ :=
    (hasDerivAt_const b₀ ε₀).prodMk ((hasDerivAt_const b₀ a₀).prodMk
      ((hasDerivAt_id b₀).prodMk (hasDerivAt_const b₀ (0 : ℝ))))
  -- the three Jacobian entries of `eq:krrs-jacobian-aa`, `eq:krrs-jacobian-ba`, `eq:krrs-jacobian-bb`
  obtain ⟨-, hF1a, hF1ane, hF2a, hF2b, hF2bne⟩ :=
    F_jacobian_nondegenerate H hd hreg hm hε0 hε1 ⟨ha0, ha1⟩ ⟨hb0, hb1⟩ hbε hbstar hmax
  have hchain1a : HasDerivAt (fun t : ℝ => F1 H d ε₀ t b₀ (C ε₀ t b₀ 0))
      (DG1 ((0, 1, 0, 0) : ℝ × ℝ × ℝ × ℝ)) a₀ := by
    have h := hG1strict.hasFDerivAt.comp_hasDerivAt a₀ hlinea
    exact h
  have hchain2a : HasDerivAt (fun t : ℝ => F2 H d ε₀ t b₀ (C ε₀ t b₀ 0))
      (DG2 ((0, 1, 0, 0) : ℝ × ℝ × ℝ × ℝ)) a₀ := by
    have h := hG2strict.hasFDerivAt.comp_hasDerivAt a₀ hlinea
    exact h
  have hchain2b : HasDerivAt (fun t : ℝ => F2 H d ε₀ a₀ t (C ε₀ a₀ t 0))
      (DG2 ((0, 0, 1, 0) : ℝ × ℝ × ℝ × ℝ)) b₀ := by
    have h := hG2strict.hasFDerivAt.comp_hasDerivAt b₀ hlineb
    exact h
  have heqa1 : (fun t : ℝ => F1 H d ε₀ t b₀ 0) =ᶠ[𝓝 a₀]
      fun t : ℝ => F1 H d ε₀ t b₀ (C ε₀ t b₀ 0) := by
    filter_upwards [hCa] with t ht; rw [ht]
  have heqa2 : (fun t : ℝ => F2 H d ε₀ t b₀ 0) =ᶠ[𝓝 a₀]
      fun t : ℝ => F2 H d ε₀ t b₀ (C ε₀ t b₀ 0) := by
    filter_upwards [hCa] with t ht; rw [ht]
  have heqb2 : (fun t : ℝ => F2 H d ε₀ a₀ t 0) =ᶠ[𝓝 b₀]
      fun t : ℝ => F2 H d ε₀ a₀ t (C ε₀ a₀ t 0) := by
    filter_upwards [hCb] with t ht; rw [ht]
  have hp2eq : p2 = (-1 / (2 * (a₀ * (1 - a₀)))) * Afun H d ε₀ b₀ := by
    rw [hp2]; exact (hchain1a.congr_of_eventuallyEq heqa1).unique hF1a
  have hq2eq : q2 = 0 := by
    rw [hq2]; exact (hchain2a.congr_of_eventuallyEq heqa2).unique hF2a
  have hq3eq : q3
      = (Fintype.card V : ℝ) * ε₀ ^ (H.edgeFinset.card - d) * dWr d ε₀ b₀ := by
    rw [hq3]; exact (hchain2b.congr_of_eventuallyEq heqb2).unique hF2b
  have hp2ne : p2 ≠ 0 := by rw [hp2eq]; exact hF1ane
  have hq3ne : q3 ≠ 0 := by rw [hq3eq]; exact hF2bne
  -- the linearisation and its explicit inverse, by back-substitution
  set M : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ × ℝ) :=
    Q1.prod (DG1.prod (DG2.prod Q4)) with hM
  set V3 : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] ℝ := q3⁻¹ • (Q3 - q1 • Q1 - q4 • Q4) with hV3
  set V2 : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
    p2⁻¹ • (Q2 - p1 • Q1 - p4 • Q4 - p3 • V3) with hV2
  set N : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ × ℝ) :=
    Q1.prod (V2.prod (V3.prod Q4)) with hN
  have hMapply : ∀ v1 v2 v3 v4 : ℝ,
      M ((v1, v2, v3, v4) : ℝ × ℝ × ℝ × ℝ)
        = (v1, DG1 ((v1, v2, v3, v4) : ℝ × ℝ × ℝ × ℝ),
            DG2 ((v1, v2, v3, v4) : ℝ × ℝ × ℝ × ℝ), v4) := by
    intro v1 v2 v3 v4; rw [hM]; rfl
  have hNapply : ∀ w1 w2 w3 w4 : ℝ,
      N ((w1, w2, w3, w4) : ℝ × ℝ × ℝ × ℝ)
        = (w1,
            p2⁻¹ * (w2 - p1 * w1 - p4 * w4 - p3 * (q3⁻¹ * (w3 - q1 * w1 - q4 * w4))),
            q3⁻¹ * (w3 - q1 * w1 - q4 * w4), w4) := by
    intro w1 w2 w3 w4; rw [hN, hV2, hV3]; rfl
  have hleft : Function.LeftInverse N M := by
    intro v
    obtain ⟨v1, v2, v3, v4⟩ := v
    rw [hMapply, hNapply, hDG1apply, hDG2apply]
    have e3 : q3⁻¹ * (q1 * v1 + q2 * v2 + q3 * v3 + q4 * v4 - q1 * v1 - q4 * v4) = v3 := by
      rw [hq2eq]
      have hy : q1 * v1 + 0 * v2 + q3 * v3 + q4 * v4 - q1 * v1 - q4 * v4 = q3 * v3 := by
        ring
      rw [hy, inv_mul_cancel_left₀ hq3ne]
    rw [e3]
    have e2 : p2⁻¹ * (p1 * v1 + p2 * v2 + p3 * v3 + p4 * v4
        - p1 * v1 - p4 * v4 - p3 * v3) = v2 := by
      have hy : p1 * v1 + p2 * v2 + p3 * v3 + p4 * v4
          - p1 * v1 - p4 * v4 - p3 * v3 = p2 * v2 := by ring
      rw [hy, inv_mul_cancel_left₀ hp2ne]
    rw [e2]
  have hright : Function.RightInverse N M := by
    intro w
    obtain ⟨w1, w2, w3, w4⟩ := w
    rw [hNapply, hMapply, hDG1apply, hDG2apply]
    have e3 : ∀ X : ℝ, q1 * w1 + q2 * X + q3 * (q3⁻¹ * (w3 - q1 * w1 - q4 * w4))
        + q4 * w4 = w3 := by
      intro X
      rw [hq2eq, mul_inv_cancel_left₀ hq3ne]; ring
    have e2 : ∀ Y : ℝ, p1 * w1 + p2 * (p2⁻¹ * (w2 - p1 * w1 - p4 * w4 - p3 * Y))
        + p3 * Y + p4 * w4 = w2 := by
      intro Y
      rw [mul_inv_cancel_left₀ hp2ne]; ring
    rw [e2, e3]
  -- `Ψ` is strictly differentiable with derivative `M`
  have hQ1s : HasStrictFDerivAt (fun w : ℝ × ℝ × ℝ × ℝ => w.1) Q1
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by rw [hQ1]; exact hasStrictFDerivAt_fst
  have hSnd : HasStrictFDerivAt (fun w : ℝ × ℝ × ℝ × ℝ => w.2)
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)) ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) :=
    hasStrictFDerivAt_snd
  have hSnd2 : HasStrictFDerivAt (fun w : ℝ × ℝ × ℝ × ℝ => w.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)))
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) :=
    (hasStrictFDerivAt_snd (p := ((a₀, b₀, (0 : ℝ)) : ℝ × ℝ × ℝ))).comp
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) hSnd
  have hQ4s : HasStrictFDerivAt (fun w : ℝ × ℝ × ℝ × ℝ => w.2.2.2) Q4
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
    rw [hQ4]
    exact (hasStrictFDerivAt_snd (p := ((b₀, (0 : ℝ)) : ℝ × ℝ))).comp
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) hSnd2
  have hMstrict : HasStrictFDerivAt (familyPsi H d C) M
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
    have heq : familyPsi H d C = fun w : ℝ × ℝ × ℝ × ℝ =>
        ((w.1, F1 H d w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2),
          F2 H d w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2),
          w.2.2.2) : ℝ × ℝ × ℝ × ℝ) := rfl
    rw [heq, hM]
    exact hQ1s.prodMk (hG1strict.prodMk (hG2strict.prodMk hQ4s))
  refine ⟨ContinuousLinearEquiv.equivOfInverse M N hleft hright, ?_⟩
  have hcoe : ((ContinuousLinearEquiv.equivOfInverse M N hleft hright :
      (ℝ × ℝ × ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ × ℝ × ℝ)) :
        (ℝ × ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ × ℝ)) = M := rfl
  rw [hcoe]
  exact hMstrict

/-! ### The family -/

/-- **`eq:krrs-stationary-densities`.**  On a two-sided rectangle `|ε - ε₀| < r`, `|ϑ| < r` around the
degenerate base point there are real-analytic block densities `a_*(ε,ϑ)`, `b_*(ε,ϑ)`
through `(a₀, b₀)` solving the chart-composed stationarity system

  `F₁(ε, a_*, b_*, C(ε,a_*,b_*,ϑ)) = 0`,   `F₂(ε, a_*, b_*, C(ε,a_*,b_*,ϑ)) = 0`,

and they are the **unique** such pair inside the source window `S`.

The rectangle is genuinely two-sided in `ϑ`: `S` and the target window are open, so the
family extends analytically to `ϑ < 0`.  That analytic continuation across the degenerate
boundary is the whole point of `thm:krrs-analytic-extension`'s analytic clause.

Hypotheses beyond those of `F_jacobian_nondegenerate`: the chart data `hCana`, `hC0` — two
of the conclusions of `exists_C_chart` `eq:krrs-density-constraint` — and the base-point first
equation `hF1`, which is the defining property of the appendix's `a₀ = q₁₁⁰(ε₀)`.
(`F₂(ε₀,a₀,b₀,0) = 0` is not assumed; it is supplied by `F_jacobian_nondegenerate`.) -/
theorem exists_stationary_family {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {C : ℝ → ℝ → ℝ → ℝ → ℝ} {ε₀ a₀ b₀ : ℝ}
    (hε0 : 0 < ε₀) (hε1 : ε₀ < 1) (ha0 : 0 < a₀) (ha1 : a₀ < 1)
    (hb0 : 0 < b₀) (hb1 : b₀ < 1) (hbε : b₀ ≠ ε₀) (hbstar : b₀ ≠ rStar d)
    (hmax : ∀ w, 0 < w → w < 1 → w ≠ ε₀ → psiD d ε₀ w ≤ psiD d ε₀ b₀)
    (hCana : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => C w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ))
    (hC0 : ∀ᶠ w in 𝓝 ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ), C w.1 w.2.1 w.2.2.1 0 = 0)
    (hF1 : F1 H d ε₀ a₀ b₀ 0 = 0) :
    ∃ (S : Set (ℝ × ℝ × ℝ × ℝ)) (r : ℝ) (astar bstar : ℝ → ℝ → ℝ),
      IsOpen S ∧ ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) ∈ S ∧ 0 < r ∧
      astar ε₀ 0 = a₀ ∧ bstar ε₀ 0 = b₀ ∧
      AnalyticAt ℝ (fun p : ℝ × ℝ => astar p.1 p.2) ((ε₀, 0) : ℝ × ℝ) ∧
      AnalyticAt ℝ (fun p : ℝ × ℝ => bstar p.1 p.2) ((ε₀, 0) : ℝ × ℝ) ∧
      (∀ ε ϑ : ℝ, |ε - ε₀| < r → |ϑ| < r →
        ((ε, astar ε ϑ, bstar ε ϑ, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ S ∧
        F1 H d ε (astar ε ϑ) (bstar ε ϑ) (C ε (astar ε ϑ) (bstar ε ϑ) ϑ) = 0 ∧
        F2 H d ε (astar ε ϑ) (bstar ε ϑ) (C ε (astar ε ϑ) (bstar ε ϑ) ϑ) = 0) ∧
      (∀ ε a b ϑ : ℝ, ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ S → |ε - ε₀| < r → |ϑ| < r →
        F1 H d ε a b (C ε a b ϑ) = 0 → F2 H d ε a b (C ε a b ϑ) = 0 →
        a = astar ε ϑ ∧ b = bstar ε ϑ) := by
  classical
  have hC00 : C ε₀ a₀ b₀ 0 = 0 := hC0.self_of_nhds
  obtain ⟨hF2, -, -, -, -, -⟩ :=
    F_jacobian_nondegenerate H hd hreg hm hε0 hε1 ⟨ha0, ha1⟩ ⟨hb0, hb1⟩ hbε hbstar hmax
  obtain ⟨L, hL⟩ :=
    exists_familyPsi_strictFDeriv H hd hreg hm hε0 hε1 ha0 ha1 hb0 hb1 hbε hbstar hmax
      hCana hC0
  have hana : AnalyticAt ℝ (familyPsi H d C) ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) :=
    analyticAt_familyPsi H d hε0 hε1 ha0 ha1 hb0 hb1 hCana hC00
  -- the base point maps to the origin of the two equations
  have hbase : familyPsi H d C ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ)
      = ((ε₀, 0, 0, 0) : ℝ × ℝ × ℝ × ℝ) := by
    show ((ε₀, F1 H d ε₀ a₀ b₀ (C ε₀ a₀ b₀ 0), F2 H d ε₀ a₀ b₀ (C ε₀ a₀ b₀ 0),
      (0 : ℝ)) : ℝ × ℝ × ℝ × ℝ) = ((ε₀, 0, 0, 0) : ℝ × ℝ × ℝ × ℝ)
    rw [hC00, hF1, hF2]
  obtain ⟨S, T, Γ, hSopen, hbS, hTopen, hbT, -, hTS, hlinv, hrinv, hinj, hΓana⟩ :=
    analytic_inverse hana L hL
  rw [hbase] at hbT hΓana
  -- the two-sided rectangle in `(ε, ϑ)`
  have hjcont : Continuous (fun p : ℝ × ℝ => ((p.1, (0 : ℝ), (0 : ℝ), p.2) :
      ℝ × ℝ × ℝ × ℝ)) := by fun_prop
  have hWopen : IsOpen ((fun p : ℝ × ℝ => ((p.1, (0 : ℝ), (0 : ℝ), p.2) :
      ℝ × ℝ × ℝ × ℝ)) ⁻¹' T) := hTopen.preimage hjcont
  have hWmem : ((ε₀, 0) : ℝ × ℝ) ∈ (fun p : ℝ × ℝ => ((p.1, (0 : ℝ), (0 : ℝ), p.2) :
      ℝ × ℝ × ℝ × ℝ)) ⁻¹' T := hbT
  obtain ⟨r, hr0, hrsub⟩ := Metric.isOpen_iff.mp hWopen ((ε₀, 0) : ℝ × ℝ) hWmem
  have hrect : ∀ ε ϑ : ℝ, |ε - ε₀| < r → |ϑ| < r →
      ((ε, (0 : ℝ), (0 : ℝ), ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ T := by
    intro ε ϑ hε hϑ
    have hmem : ((ε, ϑ) : ℝ × ℝ) ∈ Metric.ball ((ε₀, 0) : ℝ × ℝ) r := by
      rw [Metric.mem_ball, Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [Real.dist_eq]; exact hε
      · rw [Real.dist_eq]; simpa using hϑ
    exact hrsub hmem
  -- the family
  refine ⟨S, r, fun ε ϑ => (Γ ((ε, 0, 0, ϑ) : ℝ × ℝ × ℝ × ℝ)).2.1,
    fun ε ϑ => (Γ ((ε, 0, 0, ϑ) : ℝ × ℝ × ℝ × ℝ)).2.2.1,
    hSopen, hbS, hr0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `a_*(ε₀,0) = a₀`
    have h := hlinv _ hbS
    rw [hbase] at h
    exact congrArg (fun z : ℝ × ℝ × ℝ × ℝ => z.2.1) h
  · -- `b_*(ε₀,0) = b₀`
    have h := hlinv _ hbS
    rw [hbase] at h
    exact congrArg (fun z : ℝ × ℝ × ℝ × ℝ => z.2.2.1) h
  · -- analyticity of `a_*` at `(ε₀,0)`
    exact analyticAt_fst.comp (analyticAt_snd.comp
      (hΓana.fun_comp_of_eq (analyticAt_fst.prod
        (analyticAt_const.prod (analyticAt_const.prod analyticAt_snd))) rfl))
  · -- analyticity of `b_*` at `(ε₀,0)`
    exact analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp
      (hΓana.fun_comp_of_eq (analyticAt_fst.prod
        (analyticAt_const.prod (analyticAt_const.prod analyticAt_snd))) rfl)))
  · -- the family lies in `S` and solves both equations
    intro ε ϑ hε hϑ
    have hy : ((ε, (0 : ℝ), (0 : ℝ), ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ T := hrect ε ϑ hε hϑ
    have h := hrinv _ hy
    simp only [familyPsi, Prod.ext_iff] at h
    obtain ⟨e1, e2, e3, e4⟩ := h
    rw [e1, e4] at e2 e3
    refine ⟨?_, e2, e3⟩
    have hΓS : Γ ((ε, (0 : ℝ), (0 : ℝ), ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ S := hTS hy
    have hshape : Γ ((ε, (0 : ℝ), (0 : ℝ), ϑ) : ℝ × ℝ × ℝ × ℝ)
        = ((ε, (Γ ((ε, (0 : ℝ), (0 : ℝ), ϑ) : ℝ × ℝ × ℝ × ℝ)).2.1,
            (Γ ((ε, (0 : ℝ), (0 : ℝ), ϑ) : ℝ × ℝ × ℝ × ℝ)).2.2.1, ϑ) :
              ℝ × ℝ × ℝ × ℝ) := by
      simp only [Prod.ext_iff]
      refine ⟨e1, ?_, ?_, e4⟩ <;> trivial
    rw [hshape] at hΓS
    exact hΓS
  · -- local uniqueness
    intro ε a b ϑ hmemS hε hϑ hE1 hE2
    have hy : ((ε, (0 : ℝ), (0 : ℝ), ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ T := hrect ε ϑ hε hϑ
    have h1 : familyPsi H d C ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ)
        = ((ε, (0 : ℝ), (0 : ℝ), ϑ) : ℝ × ℝ × ℝ × ℝ) := by
      show ((ε, F1 H d ε a b (C ε a b ϑ), F2 H d ε a b (C ε a b ϑ), ϑ) : ℝ × ℝ × ℝ × ℝ)
        = ((ε, (0 : ℝ), (0 : ℝ), ϑ) : ℝ × ℝ × ℝ × ℝ)
      rw [hE1, hE2]
    have h2 : ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ)
        = Γ ((ε, (0 : ℝ), (0 : ℝ), ϑ) : ℝ × ℝ × ℝ × ℝ) :=
      hinj hmemS (hTS hy) (by rw [h1, hrinv _ hy])
    exact ⟨congrArg (fun z : ℝ × ℝ × ℝ × ℝ => z.2.1) h2,
      congrArg (fun z : ℝ × ℝ × ℝ × ℝ => z.2.2.1) h2⟩

end UpperTailOptimizers
