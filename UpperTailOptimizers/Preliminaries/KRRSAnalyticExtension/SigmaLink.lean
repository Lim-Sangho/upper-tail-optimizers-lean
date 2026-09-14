import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.Stationarity
import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.LocalMax

/-!
# Local maximality of `Σ` gives `F₁ = F₂ = 0` (Appendix B, paragraphs 3 and 4)

Paragraph 3 of Appendix B of `paper/paper.tex`, in the proof of
`eq:krrs-boundary-stationarity`, reads in part:

> Hence, by continuity of `C` and `Q`, every sufficiently nearby pair `(ã,b̃)`, with `c` and
> `q` supplied by `C` and `Q`, yields an admissible bipodal graphon with the same two
> constraints and entropy `Σ(ε₀,ã,b̃,ϑ)`.  Since `W_ϑ` maximizes entropy among all graphons
> with these constraints, `(a,b)(ϑ)` is an interior local maximizer of `Σ(ε₀,·,·,ϑ)` and
> therefore satisfies `𝓕₁ = 𝓕₂ = 0`.

and paragraph 4 repeats this argument.  `Preliminaries/KRRSAnalyticExtension/LocalMax.lean` supplies everything up to
"interior local maximizer" (`isLocalMax_reduced_entropy`) and the
raw calculus fact (`partials_eq_zero_of_isLocalMax`).  This file supplies the *link*
between them: the computation of the two partial derivatives of the reduced entropy

`Σ(ε,a,b,ϑ) = Ŝ(ε,a,b,C(ε,a,b,ϑ))`   `eq:krrs-constrained-entropy`

in terms of the desingularized stationarity functions `F₁`, `F₂` of `Preliminaries/KRRSAnalyticExtension/Stationarity.lean`
(`eq:krrs-small-block-stationarity`, `eq:krrs-cross-block-stationarity`).

## The computation

Write `c = C(ε,a,b,ϑ)`.  Differentiating the chart identity
`𝒯̂(ε,a,b,C(ε,a,b,ϑ)) = ε^m + ϑ` `eq:krrs-density-constraint` in `a` gives, by the chain rule,
`∂_a𝒯̂ + ∂_c𝒯̂ · ∂_aC = 0`, hence `∂_aC = -∂_a𝒯̂/∂_c𝒯̂` whenever `∂_c𝒯̂ ≠ 0`.  Therefore

`∂_aΣ = ∂_aŜ + ∂_cŜ·∂_aC = (∂_aŜ·∂_c𝒯̂ - ∂_cŜ·∂_a𝒯̂)/∂_c𝒯̂ = c²·F₁/∂_c𝒯̂`,

using the *exact* factorisations `∂_aŜ = c²(S₀'(a) - S₀'(Q))` (`hasDerivAt_Shat_a`) and
`∂_a𝒯̂ = c²·Rda` (`hasDerivAt_That_a`).  Identically, from
`∂_bŜ = 2c(1-c)(S₀'(b) - S₀'(Q))` and `∂_b𝒯̂ = c·Rdb`,

`∂_bΣ = c·F₂/∂_c𝒯̂`.

So a local maximum of `Σ(ε,·,·,ϑ)` at `(a,b)` forces `c²F₁ = cF₂ = 0`, and the strict
positivity of the pode size `c` (from the positive excess `ϑ > 0`) cancels the powers of
`c`.  The nonvanishing `∂_c𝒯̂ ≠ 0` holds near the base point because `∂_c𝒯̂|_{c=0} = 𝒜(ε,b)`
(`partialC_That_zero`) and `𝒜(ε₀,z₀) > 0` (`Afun_pos`).  The paper normalises by the excess
instead: through the quotient `L` of `eq:krrs-entropy-quotient` it has `∂_aΣ = ϑ²𝓕₁` and
`∂_bΣ = ϑ𝓕₂`, with `ϑ > 0`.

## Contents

* `C_deriv_a_eq`, `C_deriv_b_eq` — **implicit differentiation of the chart**:
  `∂_aC = -∂_a𝒯̂/∂_c𝒯̂` and `∂_bC = -∂_b𝒯̂/∂_c𝒯̂`.
* `hasDerivAt_Sigma_a`, `hasDerivAt_Sigma_b` — `∂_aΣ = c²F₁/∂_c𝒯̂` and `∂_bΣ = cF₂/∂_c𝒯̂`.
* `F_eq_zero_of_isLocalMax` — **the payoff paragraphs 3 and 4 consume**: local maximality of
  `Σ` gives `F₁ = F₂ = 0`.

Two groups of helpers are file-private: the four `(a,b)`-partials of `Preliminaries/KRRSAnalyticExtension/SCalc.lean` and
`Preliminaries/KRRSAnalyticExtension/TCalc.lean`/`Preliminaries/KRRSAnalyticExtension/TCalcAB.lean` restated in the Fréchet `partialA`/`partialB`
normalisation used by `F1` and `F2`, and the two-variable chain rule for
`x ↦ Φ(ε,x,b,C(ε,x,b,ϑ))` at a jointly analytic `Φ`.

The chart `C` enters only through hypotheses: its differentiability and the constraint it
satisfies are taken as assumptions (the caller gets both from `exists_C_chart` of
`Preliminaries/KRRSAnalyticExtension/CChart.lean`), so nothing here depends on the implicit function theorem.
-/

namespace UpperTailOptimizers

open Real Filter Topology

/-! ### The four `(a,b)`-partials in Fréchet normalisation -/

/-- `∂_a𝒯̂ = c²·Rda` in `partialA` form: `hasDerivAt_That_a` of `Preliminaries/KRRSAnalyticExtension/TCalc.lean` transported
along uniqueness of the derivative. -/
private theorem partialA_That_eq {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) {ε a b c : ℝ} (hc : c ≠ 1) :
    partialA (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c)
      = c ^ 2 * Rda H d ε a b c :=
  (hasDerivAt_partialA (Φ := fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2)
    (analyticAt_That H (p := ((ε, a, b, c) : ℝ × ℝ × ℝ × ℝ)) hc)).unique
    (hasDerivAt_That_a H hreg hc)

/-- `∂_b𝒯̂ = c·Rdb` in `partialB` form: `hasDerivAt_That_b` of `Preliminaries/KRRSAnalyticExtension/TCalcAB.lean`
transported along uniqueness of the derivative. -/
private theorem partialB_That_eq {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) {ε a b c : ℝ} (hc : c ≠ 1) :
    partialB (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c)
      = c * Rdb H d ε a b c :=
  (hasDerivAt_partialB (Φ := fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2)
    (analyticAt_That H (p := ((ε, a, b, c) : ℝ × ℝ × ℝ × ℝ)) hc)).unique
    (hasDerivAt_That_b H hreg hc)

/-- `∂_aŜ = c²[S₀'(a) - S₀'(Q)]` in `partialA` form (`hasDerivAt_Shat_a` of
`Preliminaries/KRRSAnalyticExtension/SCalc.lean`). -/
private theorem partialA_Shat_eq {ε a b c : ℝ} (hc : c ≠ 1) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hb : b ∈ Set.Ioo (0 : ℝ) 1) (hQ : Qmap ε a b c ∈ Set.Ioo (0 : ℝ) 1) :
    partialA (fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c)
      = c ^ 2 * (dS0 a - dS0 (Qmap ε a b c)) :=
  (hasDerivAt_partialA (Φ := fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2)
    (analyticAt_Shat (p := ((ε, a, b, c) : ℝ × ℝ × ℝ × ℝ)) hc ha.1 ha.2 hb.1 hb.2
      hQ.1 hQ.2)).unique
    (hasDerivAt_Shat_a hc ha.1.ne' ha.2.ne hQ.1.ne' hQ.2.ne)

/-- `∂_bŜ = 2c(1-c)[S₀'(b) - S₀'(Q)]` in `partialB` form (`hasDerivAt_Shat_b` of
`Preliminaries/KRRSAnalyticExtension/SCalc.lean`). -/
private theorem partialB_Shat_eq {ε a b c : ℝ} (hc : c ≠ 1) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hb : b ∈ Set.Ioo (0 : ℝ) 1) (hQ : Qmap ε a b c ∈ Set.Ioo (0 : ℝ) 1) :
    partialB (fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c)
      = 2 * c * (1 - c) * (dS0 b - dS0 (Qmap ε a b c)) :=
  (hasDerivAt_partialB (Φ := fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2)
    (analyticAt_Shat (p := ((ε, a, b, c) : ℝ × ℝ × ℝ × ℝ)) hc ha.1 ha.2 hb.1 hb.2
      hQ.1 hQ.2)).unique
    (hasDerivAt_Shat_b hc hb.1.ne' hb.2.ne hQ.1.ne' hQ.2.ne)

/-! ### The chain rule along the chart -/

/-- **The `a`-chain rule along the chart `C`.**  For a jointly analytic `Φ` of the four
appendix parameters and a chart `C` differentiable in `a`,

`d/da Φ(ε,a,b,C(ε,a,b,ϑ)) = ∂_aΦ + (∂_aC)·∂_cΦ`.

This is the chain rule used below to differentiate `Σ(ε,·,b,ϑ)` (a Lean-side computation; the
paper reads the partials of `Σ` off `eq:krrs-entropy-quotient` instead), obtained by composing
the Fréchet derivative of `Φ` with the curve `x ↦ (ε,x,b,C(ε,x,b,ϑ))`, whose velocity is `(0,1,0,∂_aC)`;
splitting that velocity as `(0,1,0,0) + (∂_aC)·(0,0,0,1)` is what produces the two partials
`partialA` and `partialC`. -/
private theorem hasDerivAt_chart_comp_a {Φ : ℝ × ℝ × ℝ × ℝ → ℝ} {C : ℝ → ℝ → ℝ → ℝ → ℝ}
    {ε a b ϑ dC : ℝ} (hΦ : AnalyticAt ℝ Φ ((ε, a, b, C ε a b ϑ) : ℝ × ℝ × ℝ × ℝ))
    (hC : HasDerivAt (fun x => C ε x b ϑ) dC a) :
    HasDerivAt (fun x => Φ ((ε, x, b, C ε x b ϑ) : ℝ × ℝ × ℝ × ℝ))
      (partialA Φ (ε, a, b, C ε a b ϑ) + dC * partialC Φ (ε, a, b, C ε a b ϑ)) a := by
  have h := hasDerivAt_partialSlot hΦ ((hasDerivAt_const a ε).prodMk ((hasDerivAt_id a).prodMk
    ((hasDerivAt_const a b).prodMk hC))) rfl
  have hlin : partialSlot ((0, 1, 0, dC) : ℝ × ℝ × ℝ × ℝ) Φ (ε, a, b, C ε a b ϑ)
      = partialA Φ (ε, a, b, C ε a b ϑ) + dC * partialC Φ (ε, a, b, C ε a b ϑ) := by
    have hsplit : ((0, 1, 0, dC) : ℝ × ℝ × ℝ × ℝ)
        = ((0, 1, 0, 0) : ℝ × ℝ × ℝ × ℝ) + dC • ((0, 0, 0, 1) : ℝ × ℝ × ℝ × ℝ) := by
      simp
    simp only [partialSlot, hsplit, map_add, map_smul, smul_eq_mul]
  rwa [hlin] at h

/-- **The `b`-chain rule along the chart `C`**, the companion of
`hasDerivAt_chart_comp_a`: `d/db Φ(ε,a,b,C(ε,a,b,ϑ)) = ∂_bΦ + (∂_bC)·∂_cΦ`. -/
private theorem hasDerivAt_chart_comp_b {Φ : ℝ × ℝ × ℝ × ℝ → ℝ} {C : ℝ → ℝ → ℝ → ℝ → ℝ}
    {ε a b ϑ dC : ℝ} (hΦ : AnalyticAt ℝ Φ ((ε, a, b, C ε a b ϑ) : ℝ × ℝ × ℝ × ℝ))
    (hC : HasDerivAt (fun y => C ε a y ϑ) dC b) :
    HasDerivAt (fun y => Φ ((ε, a, y, C ε a y ϑ) : ℝ × ℝ × ℝ × ℝ))
      (partialB Φ (ε, a, b, C ε a b ϑ) + dC * partialC Φ (ε, a, b, C ε a b ϑ)) b := by
  have h := hasDerivAt_partialSlot hΦ ((hasDerivAt_const b ε).prodMk
    ((hasDerivAt_const b a).prodMk ((hasDerivAt_id b).prodMk hC))) rfl
  have hlin : partialSlot ((0, 0, 1, dC) : ℝ × ℝ × ℝ × ℝ) Φ (ε, a, b, C ε a b ϑ)
      = partialB Φ (ε, a, b, C ε a b ϑ) + dC * partialC Φ (ε, a, b, C ε a b ϑ) := by
    have hsplit : ((0, 0, 1, dC) : ℝ × ℝ × ℝ × ℝ)
        = ((0, 0, 1, 0) : ℝ × ℝ × ℝ × ℝ) + dC • ((0, 0, 0, 1) : ℝ × ℝ × ℝ × ℝ) := by
      simp
    simp only [partialSlot, hsplit, map_add, map_smul, smul_eq_mul]
  rwa [hlin] at h

/-! ### Implicit differentiation of the chart -/

/-- **`∂_aC = -∂_a𝒯̂/∂_c𝒯̂`.**  Differentiating the chart identity
`𝒯̂(ε,a,b,C(ε,a,b,ϑ)) = ε^m + ϑ` `eq:krrs-density-constraint` in `a`: the left side is constant
on a neighbourhood of `a`, so its derivative `∂_a𝒯̂ + ∂_c𝒯̂·∂_aC` vanishes, and the
nondegeneracy `∂_c𝒯̂ ≠ 0` lets one solve for `∂_aC`.

The numerator is written in the desingularized form `c²·Rda` of `hasDerivAt_That_a`. -/
theorem C_deriv_a_eq {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) {C : ℝ → ℝ → ℝ → ℝ → ℝ}
    {ε a b ϑ c dC : ℝ} (hcdef : c = C ε a b ϑ) (hc1 : c ≠ 1)
    (hC : HasDerivAt (fun x => C ε x b ϑ) dC a)
    (hcon : ∀ᶠ x in 𝓝 a, That H ε x b (C ε x b ϑ) = ε ^ H.edgeFinset.card + ϑ)
    (hTc : partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c)
      ≠ 0) :
    dC = -(c ^ 2 * Rda H d ε a b c)
      / partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c) := by
  subst hcdef
  have hchain := hasDerivAt_chart_comp_a
    (Φ := fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2)
    (analyticAt_That H (p := ((ε, a, b, C ε a b ϑ) : ℝ × ℝ × ℝ × ℝ)) hc1) hC
  have hconst : HasDerivAt (fun x => That H ε x b (C ε x b ϑ)) 0 a :=
    (hasDerivAt_const a (ε ^ H.edgeFinset.card + ϑ)).congr_of_eventuallyEq hcon
  have hzero := hchain.unique hconst
  rw [partialA_That_eq H hreg hc1] at hzero
  field_simp
  linarith [hzero]

/-- **`∂_bC = -∂_b𝒯̂/∂_c𝒯̂`**, the companion of `C_deriv_a_eq`; the numerator is in the
desingularized form `c·Rdb` of `hasDerivAt_That_b`. -/
theorem C_deriv_b_eq {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) {C : ℝ → ℝ → ℝ → ℝ → ℝ}
    {ε a b ϑ c dC : ℝ} (hcdef : c = C ε a b ϑ) (hc1 : c ≠ 1)
    (hC : HasDerivAt (fun y => C ε a y ϑ) dC b)
    (hcon : ∀ᶠ y in 𝓝 b, That H ε a y (C ε a y ϑ) = ε ^ H.edgeFinset.card + ϑ)
    (hTc : partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c)
      ≠ 0) :
    dC = -(c * Rdb H d ε a b c)
      / partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c) := by
  subst hcdef
  have hchain := hasDerivAt_chart_comp_b
    (Φ := fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2)
    (analyticAt_That H (p := ((ε, a, b, C ε a b ϑ) : ℝ × ℝ × ℝ × ℝ)) hc1) hC
  have hconst : HasDerivAt (fun y => That H ε a y (C ε a y ϑ)) 0 b :=
    (hasDerivAt_const b (ε ^ H.edgeFinset.card + ϑ)).congr_of_eventuallyEq hcon
  have hzero := hchain.unique hconst
  rw [partialB_That_eq H hreg hc1] at hzero
  field_simp
  linarith [hzero]

/-! ### The two derivatives of the reduced entropy -/

/-- **`∂_aΣ = c²·F₁/∂_c𝒯̂`** (`eq:krrs-constrained-entropy`, `eq:krrs-small-block-stationarity`).

The `a`-derivative of `Σ(ε,·,b,ϑ) = Ŝ(ε,·,b,C(ε,·,b,ϑ))` is `∂_aŜ + ∂_cŜ·∂_aC`; feeding in
`∂_aC = -c²Rda/∂_c𝒯̂` (`C_deriv_a_eq`) and `∂_aŜ = c²(S₀'(a) - S₀'(Q))`
(`partialA_Shat_eq`) collects the numerator into exactly `c²` times

`F₁ = (S₀'(a) - S₀'(Q))·∂_c𝒯̂ - ∂_cŜ·Rda`. -/
theorem hasDerivAt_Sigma_a {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) {C : ℝ → ℝ → ℝ → ℝ → ℝ}
    {ε a b ϑ c dC : ℝ} (hcdef : c = C ε a b ϑ) (hc1 : c ≠ 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hQ : Qmap ε a b c ∈ Set.Ioo (0 : ℝ) 1)
    (hC : HasDerivAt (fun x => C ε x b ϑ) dC a)
    (hcon : ∀ᶠ x in 𝓝 a, That H ε x b (C ε x b ϑ) = ε ^ H.edgeFinset.card + ϑ)
    (hTc : partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c)
      ≠ 0) :
    HasDerivAt (fun x => Shat ε x b (C ε x b ϑ))
      (c ^ 2 * F1 H d ε a b c
        / partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c))
      a := by
  have hdC := C_deriv_a_eq H hreg hcdef hc1 hC hcon hTc
  subst hcdef
  have hchain := hasDerivAt_chart_comp_a
    (Φ := fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2)
    (analyticAt_Shat (p := ((ε, a, b, C ε a b ϑ) : ℝ × ℝ × ℝ × ℝ)) hc1 ha.1 ha.2 hb.1 hb.2
      hQ.1 hQ.2) hC
  rw [partialA_Shat_eq hc1 ha hb hQ, hdC] at hchain
  convert hchain using 1
  rw [F1]
  field_simp
  ring

/-- **`∂_bΣ = c·F₂/∂_c𝒯̂`** (`eq:krrs-constrained-entropy`, `eq:krrs-cross-block-stationarity`).

The `b`-analogue of `hasDerivAt_Sigma_a`: `∂_bŜ = 2c(1-c)(S₀'(b) - S₀'(Q))` and
`∂_bC = -cRdb/∂_c𝒯̂` collect into exactly `c` times

`F₂ = 2(1-c)(S₀'(b) - S₀'(Q))·∂_c𝒯̂ - ∂_cŜ·Rdb`. -/
theorem hasDerivAt_Sigma_b {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) {C : ℝ → ℝ → ℝ → ℝ → ℝ}
    {ε a b ϑ c dC : ℝ} (hcdef : c = C ε a b ϑ) (hc1 : c ≠ 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hQ : Qmap ε a b c ∈ Set.Ioo (0 : ℝ) 1)
    (hC : HasDerivAt (fun y => C ε a y ϑ) dC b)
    (hcon : ∀ᶠ y in 𝓝 b, That H ε a y (C ε a y ϑ) = ε ^ H.edgeFinset.card + ϑ)
    (hTc : partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c)
      ≠ 0) :
    HasDerivAt (fun y => Shat ε a y (C ε a y ϑ))
      (c * F2 H d ε a b c
        / partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c))
      b := by
  have hdC := C_deriv_b_eq H hreg hcdef hc1 hC hcon hTc
  subst hcdef
  have hchain := hasDerivAt_chart_comp_b
    (Φ := fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2)
    (analyticAt_Shat (p := ((ε, a, b, C ε a b ϑ) : ℝ × ℝ × ℝ × ℝ)) hc1 ha.1 ha.2 hb.1 hb.2
      hQ.1 hQ.2) hC
  rw [partialB_Shat_eq hc1 ha hb hQ, hdC] at hchain
  convert hchain using 1
  rw [F2]
  field_simp
  ring

/-! ### The payoff -/

/-- **A local maximizer of `Σ` satisfies `F₁ = F₂ = 0` (Appendix B, paragraphs 3 and 4).**

If `(a,b)` is a local maximizer of the reduced entropy
`Σ(ε,·,·,ϑ) = Ŝ(ε,·,·,C(ε,·,·,ϑ))` `eq:krrs-constrained-entropy` — which is what
`isLocalMax_reduced_entropy` of `Preliminaries/KRRSAnalyticExtension/LocalMax.lean` delivers from graphon maximality — then
both desingularized stationarity functions of `eq:krrs-small-block-stationarity` and
`eq:krrs-cross-block-stationarity` vanish at `(ε,a,b,c)`, `c = C(ε,a,b,ϑ)`.

The two hypotheses that make the division legitimate:

* `0 < c`, which comes from the positive excess `ϑ > 0`: it cancels the desingularizing powers
  `c²` and `c` (the paper normalises by `ϑ` instead: `∂_aΣ = ϑ²𝓕₁`, `∂_bΣ = ϑ𝓕₂`, with
  `ϑ > 0`);
* `∂_c𝒯̂ ≠ 0`, which holds near the base point because `∂_c𝒯̂|_{c=0} = 𝒜(ε,b)`
  (`partialC_That_zero`) and `𝒜(ε₀,z₀) > 0` (`Afun_pos`) — the positivity the paper uses to
  solve the `H`-density constraint for `c`.

`hcon` is the chart identity `eq:krrs-density-constraint` on a neighbourhood of `(a,b)`; the two
derivatives `dCa`, `dCb` come from the analyticity clause of `exists_C_chart`. -/
theorem F_eq_zero_of_isLocalMax {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) {C : ℝ → ℝ → ℝ → ℝ → ℝ}
    {ε a b ϑ c dCa dCb : ℝ} (hcdef : c = C ε a b ϑ) (hcpos : 0 < c) (hc1 : c ≠ 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hQ : Qmap ε a b c ∈ Set.Ioo (0 : ℝ) 1)
    (hCa : HasDerivAt (fun x => C ε x b ϑ) dCa a)
    (hCb : HasDerivAt (fun y => C ε a y ϑ) dCb b)
    (hcon : ∀ᶠ p in 𝓝 ((a, b) : ℝ × ℝ),
      That H ε p.1 p.2 (C ε p.1 p.2 ϑ) = ε ^ H.edgeFinset.card + ϑ)
    (hTc : partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c)
      ≠ 0)
    (hmax : IsLocalMax (fun p : ℝ × ℝ => Shat ε p.1 p.2 (C ε p.1 p.2 ϑ)) (a, b)) :
    F1 H d ε a b c = 0 ∧ F2 H d ε a b c = 0 := by
  -- Restrict the two-dimensional chart identity to the two coordinate lines.
  have hlinea : ContinuousAt (fun x : ℝ => ((x, b) : ℝ × ℝ)) a := by fun_prop
  have hlineb : ContinuousAt (fun y : ℝ => ((a, y) : ℝ × ℝ)) b := by fun_prop
  have hcona : ∀ᶠ x in 𝓝 a, That H ε x b (C ε x b ϑ) = ε ^ H.edgeFinset.card + ϑ :=
    hlinea.tendsto.eventually hcon
  have hconb : ∀ᶠ y in 𝓝 b, That H ε a y (C ε a y ϑ) = ε ^ H.edgeFinset.card + ϑ :=
    hlineb.tendsto.eventually hcon
  -- The two derivatives of `Σ` and the calculus step of `Preliminaries/KRRSAnalyticExtension/LocalMax.lean`.
  obtain ⟨h1, h2⟩ := partials_eq_zero_of_isLocalMax hmax
    (hasDerivAt_Sigma_a H hreg hcdef hc1 ha hb hQ hCa hcona hTc)
    (hasDerivAt_Sigma_b H hreg hcdef hc1 ha hb hQ hCb hconb hTc)
  -- Cancel `∂_c𝒯̂ ≠ 0` and the desingularizing powers of `c ≠ 0`.
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hcne
  rcases div_eq_zero_iff.mp h1 with h | h
  · rcases div_eq_zero_iff.mp h2 with h' | h'
    · exact ⟨by simpa [hc2] using h, by simpa [hcne] using h'⟩
    · exact absurd h' hTc
  · exact absurd h hTc

end UpperTailOptimizers
