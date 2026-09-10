import UpperTailOptimizers.KRRS.TCalc
import UpperTailOptimizers.LZBoundary.AnalyticIFT

/-!
# The pode-size chart `C(ε,a,b,ϑ)` of Appendix A

Paragraph 2 of Appendix A of `paper/bipodal_optimizer.tex` (Appendix A) solves the
`H`-density constraint

  `𝒯̂(ε,a,b,c) = ε^m + ϑ`,   `m = |E(H)|`,

for the pode size `c`, producing the real-analytic chart `c = C(ε,a,b,ϑ)` of
`eq:krrs-density-constraint`.  The chart satisfies `C(ε,a,b,0) = 0` and is the *unique* solution
of the constraint in a neighbourhood of the degenerate base point `(ε₀,a₀,b₀,0)`.

## Why the inverse function theorem and not the implicit function theorem

`analytic_implicit_scalar` of `LZBoundary/AnalyticIFT.lean` would give existence of the chart
only.  The appendix needs two further things:

* **uniqueness** — paragraph 4 pins the pode size of the KRR–S maximizer by "the
  uniqueness part of the implicit function theorem";
* the identity **`C(ε,a,b,0) = 0` for every nearby `(ε,a,b)`**, not merely at the base
  point.

Both fall out of applying the *inverse* function theorem `analytic_inverse` to

  `Φ(ε,a,b,c) = (ε, a, b, 𝒯̂(ε,a,b,c) - ε^m)`   (`CPhi`).

Injectivity of `Φ` on the source neighbourhood `S` *is* the uniqueness clause, and
`Φ(ε,a,b,0) = (ε,a,b,0)` (`CPhi_zero`, from `That_zero`) turns the left-inverse clause
`Γ(Φ z) = z` into `Γ(ε,a,b,0) = (ε,a,b,0)`, whose fourth component is `C(ε,a,b,0) = 0`.

## Contents

* `exists_C_chart` — **`eq:krrs-density-constraint`**, the full package: openness of the source
  and target windows, joint analyticity of `C`, the constraint, `C(·,·,·,0) = 0`, and
  local uniqueness.

That is the whole interface.  The constraint map `Φ`, its two basic properties, and its
linearisation at `(ε₀,a₀,b₀,0)` are file-private.  The linearisation is where the work is:
`Φ` is triangular — the identity in the first three coordinates, with the `c`-partial of
the last equal to `𝒜(ε₀,b₀) ≠ 0` (`eq:krrs-density-derivative`, `Afun_pos` of
`KRRS/TCalc.lean`) — so the inverse is written down explicitly and the two round-trip
identities are `field_simp`.
-/

namespace UpperTailOptimizers

open Filter Topology

/-! ### The constraint map `Φ` -/

/-- The constraint map of `eq:krrs-density-constraint`,
`Φ(ε,a,b,c) = (ε, a, b, 𝒯̂(ε,a,b,c) - ε^m)`.

Solving `𝒯̂(ε,a,b,c) = ε^m + ϑ` for `c` is inverting `Φ`: the fourth coordinate of
`Φ(ε,a,b,c)` is the surplus `ϑ`, and the first three are carried along unchanged. -/
private noncomputable def CPhi {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (w : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (w.1, w.2.1, w.2.2.1, That H w.1 w.2.1 w.2.2.1 w.2.2.2 - w.1 ^ H.edgeFinset.card)

/-- **`Φ` fixes the degenerate slice `c = 0` pointwise.**  This is `That_zero`
(`𝒯̂(ε,a,b,0) = ε^m`), and it is what makes `C(ε,a,b,0) = 0` free of charge. -/
@[simp] private theorem CPhi_zero {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (ε a b : ℝ) :
    CPhi H (ε, a, b, 0) = (ε, a, b, 0) := by
  simp [CPhi]

/-- `Φ` is jointly real-analytic away from `c = 1`, since `𝒯̂` is (`analyticAt_That`). -/
private theorem analyticAt_CPhi {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {p : ℝ × ℝ × ℝ × ℝ} (hc : p.2.2.2 ≠ 1) :
    AnalyticAt ℝ (CPhi H) p := by
  have h1 := analyticAt_fst4 p
  have h4 : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ =>
      That H w.1 w.2.1 w.2.2.1 w.2.2.2 - w.1 ^ H.edgeFinset.card) p :=
    (analyticAt_That H hc).sub (h1.pow _)
  exact h1.prod ((analyticAt_snd4 p).prod ((analyticAt_thd4 p).prod h4))

/-! ### The linearisation of `Φ` at the degenerate base point -/

/-- **The Jacobian of `Φ` at `(ε₀,a₀,b₀,0)` is invertible.**

`Φ` is triangular: it is the identity in the first three coordinates, and the gradient of
its last coordinate is `(g₁,g₂,g₃,g₄)` with
`g₄ = ∂_c𝒯̂|_{c=0} = 𝒜(ε₀,b₀)` (`hasDerivAt_That_c_zero`, `eq:krrs-density-derivative`),
which is nonzero by `Afun_pos`.  So

  `L(v₁,v₂,v₃,v₄) = (v₁, v₂, v₃, g₁v₁ + g₂v₂ + g₃v₃ + g₄v₄)`,
  `L⁻¹(w₁,w₂,w₃,w₄) = (w₁, w₂, w₃, (w₄ - g₁w₁ - g₂w₂ - g₃w₃)/g₄)`.

Only `g₄ ≠ 0` matters; `g₁, g₂, g₃` are carried abstractly as the values of the Fréchet
derivative on the remaining basis vectors. -/
private theorem exists_CPhi_strictFDeriv {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε₀ a₀ b₀ : ℝ} (hε₀ : 0 < ε₀) (hb0 : 0 ≤ b₀)
    (hb : b₀ ≠ ε₀) :
    ∃ L : (ℝ × ℝ × ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ × ℝ × ℝ),
      HasStrictFDerivAt (CPhi H) (L : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ × ℝ))
        (ε₀, a₀, b₀, 0) := by
  classical
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
  -- the last coordinate of `Φ` and its Fréchet derivative
  have hGana : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ =>
      That H w.1 w.2.1 w.2.2.1 w.2.2.2 - w.1 ^ H.edgeFinset.card)
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) :=
    (analyticAt_That H (p := ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ)) (by norm_num)).sub
      (analyticAt_fst.pow _)
  set DG : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (fun w : ℝ × ℝ × ℝ × ℝ =>
      That H w.1 w.2.1 w.2.2.1 w.2.2.2 - w.1 ^ H.edgeFinset.card)
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) with hDG
  have hGstrict : HasStrictFDerivAt (fun w : ℝ × ℝ × ℝ × ℝ =>
      That H w.1 w.2.1 w.2.2.1 w.2.2.2 - w.1 ^ H.edgeFinset.card) DG
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
    rw [hDG]; exact hGana.hasStrictFDerivAt
  -- the four partials, of which only the last is needed in closed form
  obtain ⟨g1, hg1⟩ : ∃ x : ℝ, x = DG ((1, 0, 0, 0) : ℝ × ℝ × ℝ × ℝ) := ⟨_, rfl⟩
  obtain ⟨g2, hg2⟩ : ∃ x : ℝ, x = DG ((0, 1, 0, 0) : ℝ × ℝ × ℝ × ℝ) := ⟨_, rfl⟩
  obtain ⟨g3, hg3⟩ : ∃ x : ℝ, x = DG ((0, 0, 1, 0) : ℝ × ℝ × ℝ × ℝ) := ⟨_, rfl⟩
  obtain ⟨g4, hg4⟩ : ∃ x : ℝ, x = DG ((0, 0, 0, 1) : ℝ × ℝ × ℝ × ℝ) := ⟨_, rfl⟩
  have hDGapply : ∀ v1 v2 v3 v4 : ℝ,
      DG ((v1, v2, v3, v4) : ℝ × ℝ × ℝ × ℝ) = g1 * v1 + g2 * v2 + g3 * v3 + g4 * v4 := by
    intro v1 v2 v3 v4
    have hsplit : ((v1, v2, v3, v4) : ℝ × ℝ × ℝ × ℝ)
        = v1 • ((1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ))
          + v2 • ((0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ))
          + v3 • ((0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ))
          + v4 • ((0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
      simp
    rw [hg1, hg2, hg3, hg4, hsplit]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  -- `g₄ = 𝒜(ε₀,b₀) ≠ 0` by `eq:krrs-density-derivative`
  have hlineD : HasDerivAt (fun t : ℝ => ((ε₀, a₀, b₀, t) : ℝ × ℝ × ℝ × ℝ))
      ((0, 0, 0, 1) : ℝ × ℝ × ℝ × ℝ) 0 :=
    (hasDerivAt_const (0 : ℝ) ε₀).prodMk ((hasDerivAt_const (0 : ℝ) a₀).prodMk
      ((hasDerivAt_const (0 : ℝ) b₀).prodMk (hasDerivAt_id (0 : ℝ))))
  have hchain : HasDerivAt (fun t : ℝ => That H ε₀ a₀ b₀ t - ε₀ ^ H.edgeFinset.card)
      (DG ((0, 0, 0, 1) : ℝ × ℝ × ℝ × ℝ)) 0 := by
    have h := hGstrict.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hlineD
    exact h
  have hTd : HasDerivAt (fun t : ℝ => That H ε₀ a₀ b₀ t - ε₀ ^ H.edgeFinset.card)
      (Afun H d ε₀ b₀) 0 :=
    (hasDerivAt_That_c_zero H hd hreg hm ε₀ a₀ b₀).sub_const _
  have hg4A : g4 = Afun H d ε₀ b₀ := by rw [hg4]; exact hchain.unique hTd
  have hg4ne : g4 ≠ 0 := by
    rw [hg4A]
    exact ne_of_gt (Afun_pos H hd (by omega) hε₀ hb0 hb)
  -- the linearisation and its explicit inverse
  set M : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ × ℝ) :=
    Q1.prod (Q2.prod (Q3.prod DG)) with hM
  set N : (ℝ × ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ × ℝ) :=
    Q1.prod (Q2.prod (Q3.prod (g4⁻¹ • (Q4 - g1 • Q1 - g2 • Q2 - g3 • Q3)))) with hN
  have hMapply : ∀ v1 v2 v3 v4 : ℝ,
      M ((v1, v2, v3, v4) : ℝ × ℝ × ℝ × ℝ)
        = (v1, v2, v3, DG ((v1, v2, v3, v4) : ℝ × ℝ × ℝ × ℝ)) := by
    intro v1 v2 v3 v4; rw [hM]; rfl
  have hNapply : ∀ w1 w2 w3 w4 : ℝ,
      N ((w1, w2, w3, w4) : ℝ × ℝ × ℝ × ℝ)
        = (w1, w2, w3, g4⁻¹ * (w4 - g1 * w1 - g2 * w2 - g3 * w3)) := by
    intro w1 w2 w3 w4; rw [hN]; rfl
  have hleft : Function.LeftInverse N M := by
    intro v
    obtain ⟨v1, v2, v3, v4⟩ := v
    rw [hMapply, hDGapply, hNapply]
    have hx : g4⁻¹ * (g1 * v1 + g2 * v2 + g3 * v3 + g4 * v4
        - g1 * v1 - g2 * v2 - g3 * v3) = v4 := by
      have hy : g1 * v1 + g2 * v2 + g3 * v3 + g4 * v4
          - g1 * v1 - g2 * v2 - g3 * v3 = g4 * v4 := by ring
      rw [hy, inv_mul_cancel_left₀ hg4ne]
    rw [hx]
  have hright : Function.RightInverse N M := by
    intro w
    obtain ⟨w1, w2, w3, w4⟩ := w
    rw [hNapply, hMapply, hDGapply]
    have hx : g1 * w1 + g2 * w2 + g3 * w3
        + g4 * (g4⁻¹ * (w4 - g1 * w1 - g2 * w2 - g3 * w3)) = w4 := by
      rw [mul_inv_cancel_left₀ hg4ne]; ring
    rw [hx]
  -- `Φ` is strictly differentiable with derivative `M`
  have hQ1s : HasStrictFDerivAt (fun w : ℝ × ℝ × ℝ × ℝ => w.1) Q1
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by rw [hQ1]; exact hasStrictFDerivAt_fst
  have hSnd : HasStrictFDerivAt (fun w : ℝ × ℝ × ℝ × ℝ => w.2)
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)) ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) :=
    hasStrictFDerivAt_snd
  have hQ2s : HasStrictFDerivAt (fun w : ℝ × ℝ × ℝ × ℝ => w.2.1) Q2
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
    rw [hQ2]
    exact (hasStrictFDerivAt_fst (p := ((a₀, b₀, (0 : ℝ)) : ℝ × ℝ × ℝ))).comp
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) hSnd
  have hSnd2 : HasStrictFDerivAt (fun w : ℝ × ℝ × ℝ × ℝ => w.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)))
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) :=
    (hasStrictFDerivAt_snd (p := ((a₀, b₀, (0 : ℝ)) : ℝ × ℝ × ℝ))).comp
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) hSnd
  have hQ3s : HasStrictFDerivAt (fun w : ℝ × ℝ × ℝ × ℝ => w.2.2.1) Q3
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
    rw [hQ3]
    exact (hasStrictFDerivAt_fst (p := ((b₀, (0 : ℝ)) : ℝ × ℝ))).comp
      ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) hSnd2
  have hMstrict : HasStrictFDerivAt (CPhi H) M ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
    rw [hM]
    exact hQ1s.prodMk (hQ2s.prodMk (hQ3s.prodMk hGstrict))
  refine ⟨ContinuousLinearEquiv.equivOfInverse M N hleft hright, ?_⟩
  have hcoe : ((ContinuousLinearEquiv.equivOfInverse M N hleft hright :
      (ℝ × ℝ × ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ × ℝ × ℝ)) :
        (ℝ × ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ × ℝ)) = M := rfl
  rw [hcoe]
  exact hMstrict

/-! ### The chart `C` -/

/-- **`eq:krrs-density-constraint`.**  Near the degenerate base point `(ε₀,a₀,b₀,0)` the
`H`-density constraint `𝒯̂(ε,a,b,c) = ε^m + ϑ` is solved by a real-analytic pode size
`c = C(ε,a,b,ϑ)`, which vanishes identically on `ϑ = 0` and is the unique solution in the
source window `S`.

The package returns a source window `S` (in the variables `(ε,a,b,c)`) and a target window
`T` (in the variables `(ε,a,b,ϑ)`), both open and containing `(ε₀,a₀,b₀,0)`, together with:

* `AnalyticAt` — joint real-analyticity of `C` in all four variables at the base point;
* `Γ`-image — `(ε,a,b,C ε a b ϑ) ∈ S` for every `(ε,a,b,ϑ) ∈ T`;
* the constraint, pointwise on `T` and hence eventually near the base point;
* `C(ε,a,b,0) = 0`, pointwise on the slice `{c = 0}` of `S` and hence eventually;
* **local uniqueness** — a solution `c ∈ S` of the constraint with surplus `ϑ ∈ T` equals
  `C ε a b ϑ`.  This is `Set.InjOn (CPhi H) S` from `analytic_inverse`, and it is what
  paragraph 4 uses to pin the pode size of the KRR–S maximizer. -/
theorem exists_C_chart {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε₀ a₀ b₀ : ℝ} (hε₀ : 0 < ε₀)
    (hb0 : 0 ≤ b₀) (hb : b₀ ≠ ε₀) :
    ∃ (S T : Set (ℝ × ℝ × ℝ × ℝ)) (C : ℝ → ℝ → ℝ → ℝ → ℝ),
      IsOpen S ∧ ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) ∈ S ∧
      IsOpen T ∧ ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) ∈ T ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => C w.1 w.2.1 w.2.2.1 w.2.2.2)
        ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) ∧
      (∀ ε a b ϑ : ℝ, ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ T →
        ((ε, a, b, C ε a b ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ S) ∧
      (∀ ε a b ϑ : ℝ, ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ T →
        That H ε a b (C ε a b ϑ) = ε ^ H.edgeFinset.card + ϑ) ∧
      (∀ᶠ w in 𝓝 ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ),
        That H w.1 w.2.1 w.2.2.1 (C w.1 w.2.1 w.2.2.1 w.2.2.2)
          = w.1 ^ H.edgeFinset.card + w.2.2.2) ∧
      (∀ ε a b : ℝ, ((ε, a, b, 0) : ℝ × ℝ × ℝ × ℝ) ∈ S → C ε a b 0 = 0) ∧
      (∀ᶠ w in 𝓝 ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ), C w.1 w.2.1 w.2.2.1 0 = 0) ∧
      (∀ ε a b c ϑ : ℝ, ((ε, a, b, c) : ℝ × ℝ × ℝ × ℝ) ∈ S →
        ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ T →
        That H ε a b c = ε ^ H.edgeFinset.card + ϑ → c = C ε a b ϑ) := by
  classical
  obtain ⟨L, hL⟩ := exists_CPhi_strictFDeriv H hd hreg hm hε₀ hb0 hb
  have hana : AnalyticAt ℝ (CPhi H) ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) :=
    analyticAt_CPhi H (by norm_num)
  obtain ⟨S, T, Γ, hSopen, hθS, hTopen, hθT, -, hTS, hlinv, hrinv, hinj, hΓana⟩ :=
    analytic_inverse hana L hL
  rw [CPhi_zero] at hθT hΓana
  -- On the target window `Γ` is the identity in the first three coordinates, and its
  -- fourth coordinate solves the `H`-density constraint.
  have hkey : ∀ y ∈ T, (Γ y).1 = y.1 ∧ (Γ y).2.1 = y.2.1 ∧ (Γ y).2.2.1 = y.2.2.1 ∧
      That H y.1 y.2.1 y.2.2.1 (Γ y).2.2.2 = y.1 ^ H.edgeFinset.card + y.2.2.2 := by
    intro y hy
    have h := hrinv y hy
    simp only [CPhi, Prod.ext_iff] at h
    obtain ⟨e1, e2, e3, e4⟩ := h
    refine ⟨e1, e2, e3, ?_⟩
    rw [e1, e2, e3] at e4
    linarith
  have hshape : ∀ y ∈ T, Γ y = ((y.1, y.2.1, y.2.2.1, (Γ y).2.2.2) : ℝ × ℝ × ℝ × ℝ) := by
    intro y hy
    obtain ⟨e1, e2, e3, -⟩ := hkey y hy
    simp only [Prod.ext_iff]
    exact ⟨e1, e2, e3, trivial⟩
  refine ⟨S, T, fun ε a b ϑ => (Γ ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ)).2.2.2,
    hSopen, hθS, hTopen, hθT, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- joint analyticity of `C` at the base point
    exact analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp hΓana))
  · -- `Γ` lands in `S`, in the shape `(ε, a, b, C ε a b ϑ)`
    intro ε a b ϑ hy
    have h := hshape _ hy
    rw [← h]
    exact hTS hy
  · -- the constraint, pointwise on `T`
    intro ε a b ϑ hy
    exact (hkey _ hy).2.2.2
  · -- the constraint, eventually near the base point
    filter_upwards [hTopen.mem_nhds hθT] with w hw
    exact (hkey w hw).2.2.2
  · -- `C(ε,a,b,0) = 0` on the degenerate slice of `S`
    intro ε a b hmem
    have h := hlinv _ hmem
    rw [CPhi_zero] at h
    exact congrArg (fun z : ℝ × ℝ × ℝ × ℝ => z.2.2.2) h
  · -- `C(·,·,·,0) = 0` eventually near the base point
    have hcont : Continuous
        (fun w : ℝ × ℝ × ℝ × ℝ => ((w.1, w.2.1, w.2.2.1, (0 : ℝ)) : ℝ × ℝ × ℝ × ℝ)) := by
      fun_prop
    have hpre : (fun w : ℝ × ℝ × ℝ × ℝ =>
        ((w.1, w.2.1, w.2.2.1, (0 : ℝ)) : ℝ × ℝ × ℝ × ℝ)) ⁻¹' S
          ∈ 𝓝 ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) :=
      hcont.continuousAt.preimage_mem_nhds (hSopen.mem_nhds hθS)
    filter_upwards [hpre] with w hw
    have h := hlinv _ hw
    rw [CPhi_zero] at h
    exact congrArg (fun z : ℝ × ℝ × ℝ × ℝ => z.2.2.2) h
  · -- local uniqueness
    intro ε a b c ϑ hcS hϑT hEq
    have h1 : CPhi H ((ε, a, b, c) : ℝ × ℝ × ℝ × ℝ) = ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ) := by
      have hx : That H ε a b c - ε ^ H.edgeFinset.card = ϑ := by rw [hEq]; ring
      show ((ε, a, b, That H ε a b c - ε ^ H.edgeFinset.card) : ℝ × ℝ × ℝ × ℝ)
        = ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ)
      rw [hx]
    have h2 : CPhi H (Γ ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ)) = ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ) :=
      hrinv _ hϑT
    have h3 : Γ ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ S := hTS hϑT
    have h4 : ((ε, a, b, c) : ℝ × ℝ × ℝ × ℝ) = Γ ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ) :=
      hinj hcS h3 (by rw [h1, h2])
    exact congrArg (fun z : ℝ × ℝ × ℝ × ℝ => z.2.2.2) h4

end UpperTailOptimizers
