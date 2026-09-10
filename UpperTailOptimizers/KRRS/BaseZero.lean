import UpperTailOptimizers.KRRS.Inputs
import UpperTailOptimizers.KRRS.SigmaLink
import UpperTailOptimizers.KRRS.CChart

/-!
# `eq:krrs-boundary-stationarity`: passage to the limit `ϑ ↓ 0`

Paragraph 4 of Appendix A of `paper/bipodal_optimizer.tex` (Appendix A) ends with

> Letting `ϑ ↓ 0` and using the continuity of `F₁`, `F₂` and of the KRR–S parameters, we
> obtain `F₁(ε, q₁₁⁰(ε), ζ_d(ε), 0) = F₂(ε, q₁₁⁰(ε), ζ_d(ε), 0) = 0`.

This file is that sentence.  It is the last missing piece of the rewritten appendix: the
first equation `F₁(ε₀,a₀,b₀,0) = 0` is exactly the hypothesis `hF1` of
`exists_stationary_family` (`KRRS/Family.lean`), and it has no other derivation — it *is*
the defining property of the appendix's degenerate first-pode density `a₀ = q₁₁⁰(ε₀)`.

## The two steps

**Step A** (`F_eq_zero_of_maximizer`, and its file-private `𝓝[>] (0:ℝ)`-eventual form for
the KRR–S parameters).  For a
positive surplus `ϑ` close to the degenerate boundary the KRR–S parameters
`(q₁₁, q₁₂, q₂₂, c)(ε,ϑ)` of `KRRSOptimizer` are stationary:

1. `KRRSOptimizer.optimizer` supplies a maximizer `W` at `(ε, ε^m + ϑ)` which is a.e. the
   bipodal kernel with those parameters — with *no* relabelling, so `bipodal_transfer` is
   applied with `σ = id`;
2. `bipodal_transfer` converts `e(W) = ε` into `E(θ) = ε` and `t(H,W) = ε^m + ϑ` into
   `T_H(θ) = ε^m + ϑ`;
3. `E(θ) = ε` together with `c ≠ 1` *solves* for the second-pode density,
   `q₂₂ = Q(ε,q₁₁,q₁₂,c)` `eq:krrs-edge-constraint` — the converse of `bipEdge_Qmap`;
4. substituting, `𝒯̂(ε,q₁₁,q₁₂,c) = ε^m + ϑ` (`That_eq_bipTd`);
5. the **uniqueness** clause of the pode-size chart (`exists_C_chart`,
   `eq:krrs-density-constraint`) then pins `c = C(ε,q₁₁,q₁₂,ϑ)`;
6. `isLocalMax_reduced_entropy` (`KRRS/LocalMax.lean`) turns graphon maximality into local
   maximality of the reduced entropy `Σ(ε,·,·,ϑ)`, and
7. `F_eq_zero_of_isLocalMax` (`KRRS/SigmaLink.lean`) turns that into `F₁ = F₂ = 0`.

The strict positivity `0 < c` needed in step 7 comes from the strict surplus: a bipodal
graphon with a null first pode is constant (`tBip_zero`), so its `H`-density would be
`ε^m`, contradicting `ϑ > 0`.  All the "close enough to the base point" side conditions are
assembled in the filter `𝓝[>] (0:ℝ)` from the one-sided limits
`KRRSOptimizer.tendsto_q11/q12/q22/c` and the openness of the chart windows.

**Step B** (`F1_base_zero`).  `F₁` is real-analytic — hence continuous — at the degenerate
base point `(ε, q₁₁⁰(ε), ζ_d(ε), 0)`, where the edge-density solve is `Q = ε ∈ (0,1)`
(`Qmap_zero`).  So the composite `ϑ ↦ F₁(ε, q₁₁, q₁₂, c)(ϑ)` tends to
`F₁(ε, q₁₁⁰(ε), ζ_d(ε), 0)` along `𝓝[>] (0:ℝ)`, while by Step A it is eventually the
constant `0`.  The filter `𝓝[>] (0:ℝ)` is nontrivial, so the two limits agree.

Only the first equation is extracted: `F₂(ε₀,a₀,b₀,0) = 0` is supplied independently by
`F_jacobian_nondegenerate` (`KRRS/Stationarity.lean`), so the appendix never needs a limit
argument for it.

## Contents

* `tendsto_krrsParams_c`, `tendsto_krrsParams_theta` — the two parameter curves
  `ϑ ↦ (ε, q₁₁, q₁₂, c)` and `ϑ ↦ (ε, q₁₁, q₁₂, ϑ)` converge to the base point.
* `F_eq_zero_of_maximizer` — Step A at a *fixed* surplus, stated for abstract parameters.
* `F1_base_zero` — **`eq:krrs-boundary-stationarity`**, first equation.

The `𝓝[>] (0:ℝ)`-eventual form of Step A for the KRR–S parameters is file-private: it is
consumed only by `F1_base_zero`.

The pode-size chart is taken as explicit hypotheses (`S`, `T`, `C` and five of the
conclusions of `exists_C_chart`), exactly as `KRRS/Family.lean` does.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Filter Topology

/-! ### The two parameter curves -/

/-- The KRR–S parameter curve `ϑ ↦ (ε, q₁₁(ε,ϑ), q₁₂(ε,ϑ), c(ε,ϑ))` converges, as `ϑ ↘ 0`,
to the degenerate base point `(ε, q₁₁⁰(ε), ζ_d(ε), 0)` of Appendix A.  This is
`KRRSOptimizer.tendsto_q11`, `tendsto_q12` and `tendsto_c` bundled. -/
theorem tendsto_krrsParams_c {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    [DecidableRel H.Adj] {d : ℕ} {Z : KRRSZeta d} (O : KRRSOptimizer H d Z) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0:ℝ) 1) (hne : ε ≠ rStar d) :
    Tendsto (fun ϑ : ℝ => ((ε, O.q11 ε ϑ, O.q12 ε ϑ, O.cpar ε ϑ) : ℝ × ℝ × ℝ × ℝ))
      (𝓝[>] (0:ℝ)) (𝓝 ((ε, O.q110 ε, Z.zeta ε, 0) : ℝ × ℝ × ℝ × ℝ)) :=
  tendsto_const_nhds.prodMk_nhds ((O.tendsto_q11 ε hε hne).prodMk_nhds
    ((O.tendsto_q12 ε hε hne).prodMk_nhds (O.tendsto_c ε hε hne)))

/-- The companion curve `ϑ ↦ (ε, q₁₁(ε,ϑ), q₁₂(ε,ϑ), ϑ)` in the chart's *target* variables,
which converges to the same base point. -/
theorem tendsto_krrsParams_theta {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    [DecidableRel H.Adj] {d : ℕ} {Z : KRRSZeta d} (O : KRRSOptimizer H d Z) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0:ℝ) 1) (hne : ε ≠ rStar d) :
    Tendsto (fun ϑ : ℝ => ((ε, O.q11 ε ϑ, O.q12 ε ϑ, ϑ) : ℝ × ℝ × ℝ × ℝ))
      (𝓝[>] (0:ℝ)) (𝓝 ((ε, O.q110 ε, Z.zeta ε, 0) : ℝ × ℝ × ℝ × ℝ)) :=
  tendsto_const_nhds.prodMk_nhds ((O.tendsto_q11 ε hε hne).prodMk_nhds
    ((O.tendsto_q12 ε hε hne).prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds)))

/-! ### Step A at a fixed positive surplus -/

/-- **Steps 1–7 of Appendix A, paragraph 4, at a single surplus `ϑ > 0`.**

A graphon `W` that maximises the entropy at `(ε, ε^m + ϑ)` and is a.e. the bipodal kernel
with interior parameters `(a, b, q, c)`, `0 ≤ c < 1`, satisfies the desingularized
stationarity system at `(ε, a, b, c)`.

The proof runs the chain of the module docstring: `bipodal_transfer` reads the two
constraints off the block formulas, the edge-density constraint *solves* for `q` as
`Q(ε,a,b,c)`, the chart's uniqueness clause pins `c = C(ε,a,b,ϑ)`, and then
`isLocalMax_reduced_entropy` followed by `F_eq_zero_of_isLocalMax` gives `F₁ = F₂ = 0`.
The strict surplus `0 < ϑ` is what forces `0 < c` (`tBip_zero`), which is in turn what
cancels the desingularizing powers of `c`. -/
theorem F_eq_zero_of_maximizer {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d)
    {S T : Set (ℝ × ℝ × ℝ × ℝ)} {C : ℝ → ℝ → ℝ → ℝ → ℝ} {ε a b q c ϑ : ℝ}
    (hTopen : IsOpen T)
    (hCcon : ∀ x u v t : ℝ, ((x, u, v, t) : ℝ × ℝ × ℝ × ℝ) ∈ T →
      That H x u v (C x u v t) = x ^ H.edgeFinset.card + t)
    (hCuniq : ∀ x u v w t : ℝ, ((x, u, v, w) : ℝ × ℝ × ℝ × ℝ) ∈ S →
      ((x, u, v, t) : ℝ × ℝ × ℝ × ℝ) ∈ T →
      That H x u v w = x ^ H.edgeFinset.card + t → w = C x u v t)
    (hCana : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => C w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ))
    (hS : ((ε, a, b, c) : ℝ × ℝ × ℝ × ℝ) ∈ S) (hT : ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ T)
    (hTc : partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c)
      ≠ 0)
    (ha : a ∈ Set.Ioo (0:ℝ) 1) (hb : b ∈ Set.Ioo (0:ℝ) 1) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hϑ : 0 < ϑ)
    {W : Graphon} (hWe : W.edgeDensity = ε)
    (hWt : W.tDensity H = ε ^ H.edgeFinset.card + ϑ)
    (hWmax : ∀ W' : Graphon, W'.edgeDensity = ε →
      W'.tDensity H = ε ^ H.edgeFinset.card + ϑ → W'.entropy ≤ W.entropy)
    (hWae : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = bipodalValue (Set.Icc 0 c) a b q z) :
    F1 H d ε a b c = 0 ∧ F2 H d ε a b c = 0 := by
  classical
  -- Step 1–2: transfer the two constraints to the block formulas, with `σ = id`.
  have hae : ∀ᵐ z ∂gμ, W.toFun z.1 z.2
      = bipodalValue (Set.Icc 0 ((a, b, q, c) : Theta).2.2.2) ((a, b, q, c) : Theta).1
          ((a, b, q, c) : Theta).2.1 ((a, b, q, c) : Theta).2.2.1 (id z.1, id z.2) := by
    filter_upwards [hWae] with z hz
    simpa using hz
  have htr := bipodal_transfer H (θ := ((a, b, q, c) : Theta))
    (Set.Ioo_subset_Icc_self ha) (Set.Ioo_subset_Icc_self hb) (Set.Ioo_subset_Icc_self hq)
    (Set.mem_Icc.mpr ⟨hc0, hc1.le⟩) isRelabelling_id hae
  have hE : bipEdge ((a, b, q, c) : Theta) = ε := by rw [← htr.1]; exact hWe
  have hTd : bipTd H ((a, b, q, c) : Theta) = ε ^ H.edgeFinset.card + ϑ := by
    rw [← htr.2.1]; exact hWt
  -- `0 < c`: a null first pode makes the graphon constant, so the surplus would vanish.
  have hcpos : 0 < c := by
    rcases lt_or_eq_of_le hc0 with h | h
    · exact h
    · exfalso
      have hc00 : c = 0 := h.symm
      have hEq : q = ε := by
        have hqE : bipEdge ((a, b, q, c) : Theta) = q := by simp [bipEdge, hc00]
        rw [← hqE]; exact hE
      have hTq : bipTd H ((a, b, q, c) : Theta) = q ^ H.edgeFinset.card := by
        show tBip H a b q c = _
        rw [hc00, tBip_zero]
      rw [hTq, hEq] at hTd
      linarith
  -- Step 3: the edge-density constraint solves for the second-pode density.
  have hc1' : (1:ℝ) - c ≠ 0 := sub_ne_zero.mpr (ne_of_lt hc1).symm
  have hEexp : a * c ^ 2 + b * (2 * c * (1 - c)) + q * (1 - c) ^ 2 = ε := hE
  have hQq : Qmap ε a b c = q := by
    unfold Qmap
    rw [div_eq_iff (pow_ne_zero 2 hc1')]
    linear_combination (-1 : ℝ) * hEexp
  -- Step 4: the `H`-density constraint in the reduced coordinates.
  have hThat : That H ε a b c = ε ^ H.edgeFinset.card + ϑ := by
    rw [That_eq_bipTd, hQq]; exact hTd
  -- Step 5: the chart's uniqueness clause pins the pode size.
  have hCeq : C ε a b ϑ = c := (hCuniq ε a b c ϑ hS hT hThat).symm
  -- Step 6: graphon maximality becomes a finite-dimensional local maximum.
  have hlm : IsLocalMax (fun p : ℝ × ℝ => Shat ε p.1 p.2 (C ε p.1 p.2 ϑ)) (a, b) := by
    refine isLocalMax_reduced_entropy H hTopen hCcon hCana.continuousAt hT ha hb ?_ ?_
      hWmax isRelabelling_id ?_
    · rw [hCeq, hQq]; exact hq
    · rw [hCeq]; exact ⟨hcpos, hc1⟩
    · rw [hCeq, hQq]; exact hae
  -- Step 7: local maximality gives `F₁ = F₂ = 0`.
  have hins : Continuous (fun p : ℝ × ℝ => ((ε, p.1, p.2, ϑ) : ℝ × ℝ × ℝ × ℝ)) := by
    fun_prop
  have hcon : ∀ᶠ p in 𝓝 ((a, b) : ℝ × ℝ),
      That H ε p.1 p.2 (C ε p.1 p.2 ϑ) = ε ^ H.edgeFinset.card + ϑ := by
    filter_upwards [hins.continuousAt.eventually_mem (hTopen.mem_nhds hT)] with p hp
    exact hCcon ε p.1 p.2 ϑ hp
  exact F_eq_zero_of_isLocalMax H hreg hCeq.symm hcpos (ne_of_lt hc1) ha hb
    (by rw [hQq]; exact hq) (hasDerivAt_partialA hCana) (hasDerivAt_partialB hCana) hcon
    hTc hlm

/-! ### Step A for the KRR–S parameters, eventually in the surplus -/

/-- **Appendix A, paragraph 4, for the KRR–S optimizer.**  For all sufficiently small
positive surpluses `ϑ` the KRR–S parameters `(q₁₁, q₁₂, c)(ε,ϑ)` solve the desingularized
stationarity system `eq:krrs-small-block-stationarity`, `eq:krrs-cross-block-stationarity`.

All the "sufficiently small" side conditions are assembled in the filter `𝓝[>] (0:ℝ)`:
interiority of `q₁₁`, `q₁₂`, `q₂₂` and `c < 1` from the one-sided limits
`KRRSOptimizer.tendsto_q11/q12/q22/c`; membership in the two chart windows from their
openness; analyticity of `C` at the moving point from
`AnalyticAt.eventually_analyticAt`; and `∂_c𝒯̂ ≠ 0` from
`eventually_partialC_That_ne_zero` (`∂_c𝒯̂|_{c=0} = 𝒜(ε,ζ_d(ε)) > 0`).

The chart data are the hypotheses `hSopen`–`hCuniq`, all of them conclusions of
`exists_C_chart` at the base point `(ε, q₁₁⁰(ε), ζ_d(ε), 0)`. -/
private theorem eventually_F_eq_zero_of_krrsOptimizer {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {Z : KRRSZeta d} (O : KRRSOptimizer H d Z) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0:ℝ) 1) (hne : ε ≠ rStar d)
    {S T : Set (ℝ × ℝ × ℝ × ℝ)} {C : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hSopen : IsOpen S) (hSmem : ((ε, O.q110 ε, Z.zeta ε, 0) : ℝ × ℝ × ℝ × ℝ) ∈ S)
    (hTopen : IsOpen T) (hTmem : ((ε, O.q110 ε, Z.zeta ε, 0) : ℝ × ℝ × ℝ × ℝ) ∈ T)
    (hCana : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => C w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((ε, O.q110 ε, Z.zeta ε, 0) : ℝ × ℝ × ℝ × ℝ))
    (hCcon : ∀ x u v t : ℝ, ((x, u, v, t) : ℝ × ℝ × ℝ × ℝ) ∈ T →
      That H x u v (C x u v t) = x ^ H.edgeFinset.card + t)
    (hCuniq : ∀ x u v w t : ℝ, ((x, u, v, w) : ℝ × ℝ × ℝ × ℝ) ∈ S →
      ((x, u, v, t) : ℝ × ℝ × ℝ × ℝ) ∈ T →
      That H x u v w = x ^ H.edgeFinset.card + t → w = C x u v t) :
    ∀ᶠ ϑ in 𝓝[>] (0:ℝ),
      F1 H d ε (O.q11 ε ϑ) (O.q12 ε ϑ) (O.cpar ε ϑ) = 0 ∧
        F2 H d ε (O.q11 ε ϑ) (O.q12 ε ϑ) (O.cpar ε ϑ) = 0 := by
  classical
  have ha0 : O.q110 ε ∈ Set.Ioo (0:ℝ) 1 := O.q110_mem ε hε hne
  have hb0 : Z.zeta ε ∈ Set.Ioo (0:ℝ) 1 := Z.mem_Ioo ε hε
  have hbε : Z.zeta ε ≠ ε := Z.ne_self hd hε hne
  have hwin : 0 < O.hwin ε := O.hwin_pos ε hε hne
  have hPc := tendsto_krrsParams_c O hε hne
  have hPt := tendsto_krrsParams_theta O hε hne
  -- the surplus itself: positive and inside the KRR–S window
  have epos : ∀ᶠ ϑ in 𝓝[>] (0:ℝ), 0 < ϑ := eventually_mem_nhdsWithin
  have ewin : ∀ᶠ ϑ in 𝓝[>] (0:ℝ), ϑ < O.hwin ε :=
    Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hwin)
  -- interiority of the three block densities, and `c < 1`
  have e11 : ∀ᶠ ϑ in 𝓝[>] (0:ℝ), O.q11 ε ϑ ∈ Set.Ioo (0:ℝ) 1 :=
    (O.tendsto_q11 ε hε hne).eventually (isOpen_Ioo.mem_nhds ha0)
  have e12 : ∀ᶠ ϑ in 𝓝[>] (0:ℝ), O.q12 ε ϑ ∈ Set.Ioo (0:ℝ) 1 :=
    (O.tendsto_q12 ε hε hne).eventually (isOpen_Ioo.mem_nhds hb0)
  have e22 : ∀ᶠ ϑ in 𝓝[>] (0:ℝ), O.q22 ε ϑ ∈ Set.Ioo (0:ℝ) 1 :=
    (O.tendsto_q22 ε hε hne).eventually (isOpen_Ioo.mem_nhds hε)
  have ec1 : ∀ᶠ ϑ in 𝓝[>] (0:ℝ), O.cpar ε ϑ < 1 :=
    (O.tendsto_c ε hε hne).eventually (Iio_mem_nhds one_pos)
  -- the two chart windows and the analyticity of `C` at the moving point
  have eS : ∀ᶠ ϑ in 𝓝[>] (0:ℝ),
      ((ε, O.q11 ε ϑ, O.q12 ε ϑ, O.cpar ε ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ S :=
    hPc.eventually (hSopen.mem_nhds hSmem)
  have eT : ∀ᶠ ϑ in 𝓝[>] (0:ℝ),
      ((ε, O.q11 ε ϑ, O.q12 ε ϑ, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ T :=
    hPt.eventually (hTopen.mem_nhds hTmem)
  have eC : ∀ᶠ ϑ in 𝓝[>] (0:ℝ),
      AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => C w.1 w.2.1 w.2.2.1 w.2.2.2)
        ((ε, O.q11 ε ϑ, O.q12 ε ϑ, ϑ) : ℝ × ℝ × ℝ × ℝ) :=
    hPt.eventually hCana.eventually_analyticAt
  -- `∂_c𝒯̂ ≠ 0` near the base point (`eventually_partialC_That_ne_zero`)
  have eTc : ∀ᶠ ϑ in 𝓝[>] (0:ℝ),
      partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2)
        ((ε, O.q11 ε ϑ, O.q12 ε ϑ, O.cpar ε ϑ) : ℝ × ℝ × ℝ × ℝ) ≠ 0 :=
    hPc.eventually
      (eventually_partialC_That_ne_zero H hd hreg hm (O.q110 ε) hε.1 hb0.1.le hbε)
  filter_upwards [epos, ewin, e11, e12, e22, ec1, eS, eT, eC, eTc] with
    ϑ hϑ0 hϑw h11 h12 h22 hclt hSm hTm hCm hTcm
  have hmemR : ((ε, ϑ) : ℝ × ℝ) ∈ krrsRegion d O.hwin := ⟨hε, hne, hϑ0, hϑw⟩
  obtain ⟨W, hWe, hWt, hWae, hWmax, -⟩ := O.optimizer ((ε, ϑ) : ℝ × ℝ) hmemR
  obtain ⟨-, -, -, hcIcc⟩ := O.mem_Icc ((ε, ϑ) : ℝ × ℝ) hmemR
  exact F_eq_zero_of_maximizer H hreg hTopen hCcon hCuniq hCm hSm hTm hTcm h11 h12 h22
    hcIcc.1 hclt hϑ0 hWe hWt hWmax hWae

/-! ### Step B: the limit `ϑ ↓ 0` -/

/-- **`eq:krrs-boundary-stationarity`, first equation.**  Passing to the limit `ϑ ↓ 0` in the
stationarity of the KRR–S maximizers gives `F₁(ε, q₁₁⁰(ε), ζ_d(ε), 0) = 0`.

`F₁` is real-analytic, hence continuous, at the degenerate base point — there the
edge-density solve is `Q = ε ∈ (0,1)` (`Qmap_zero`) — so the composite
`ϑ ↦ F₁(ε, q₁₁, q₁₂, c)(ϑ)` tends to `F₁(ε, q₁₁⁰(ε), ζ_d(ε), 0)` along `𝓝[>] (0:ℝ)`; by
`eventually_F_eq_zero_of_krrsOptimizer` it is eventually `0`; and `𝓝[>] (0:ℝ)` is
nontrivial, so the two limits coincide.

This is the hypothesis `hF1` of `exists_stationary_family` (`KRRS/Family.lean`), and it is
the defining property of the appendix's degenerate first-pode density `q₁₁⁰(ε)`. -/
theorem F1_base_zero {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {Z : KRRSZeta d} (O : KRRSOptimizer H d Z) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0:ℝ) 1) (hne : ε ≠ rStar d)
    {S T : Set (ℝ × ℝ × ℝ × ℝ)} {C : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hSopen : IsOpen S) (hSmem : ((ε, O.q110 ε, Z.zeta ε, 0) : ℝ × ℝ × ℝ × ℝ) ∈ S)
    (hTopen : IsOpen T) (hTmem : ((ε, O.q110 ε, Z.zeta ε, 0) : ℝ × ℝ × ℝ × ℝ) ∈ T)
    (hCana : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => C w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((ε, O.q110 ε, Z.zeta ε, 0) : ℝ × ℝ × ℝ × ℝ))
    (hCcon : ∀ x u v t : ℝ, ((x, u, v, t) : ℝ × ℝ × ℝ × ℝ) ∈ T →
      That H x u v (C x u v t) = x ^ H.edgeFinset.card + t)
    (hCuniq : ∀ x u v w t : ℝ, ((x, u, v, w) : ℝ × ℝ × ℝ × ℝ) ∈ S →
      ((x, u, v, t) : ℝ × ℝ × ℝ × ℝ) ∈ T →
      That H x u v w = x ^ H.edgeFinset.card + t → w = C x u v t) :
    F1 H d ε (O.q110 ε) (Z.zeta ε) 0 = 0 := by
  have ha0 : O.q110 ε ∈ Set.Ioo (0:ℝ) 1 := O.q110_mem ε hε hne
  have hb0 : Z.zeta ε ∈ Set.Ioo (0:ℝ) 1 := Z.mem_Ioo ε hε
  have hev := eventually_F_eq_zero_of_krrsOptimizer H hd hreg hm O hε hne hSopen hSmem
    hTopen hTmem hCana hCcon hCuniq
  have hana : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => F1 H d w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((ε, O.q110 ε, Z.zeta ε, 0) : ℝ × ℝ × ℝ × ℝ) :=
    analyticAt_F1 H d (p := ((ε, O.q110 ε, Z.zeta ε, 0) : ℝ × ℝ × ℝ × ℝ)) (by norm_num)
      ha0.1 ha0.2 hb0.1 hb0.2 (by simpa using hε.1) (by simpa using hε.2)
  -- The composite is written with `∘` throughout: unifying `?g ∘ ?f` against an explicit
  -- lambda would force the elaborator to unfold `F1` down to the labelling sum.
  have h1 := Filter.Tendsto.comp hana.continuousAt (tendsto_krrsParams_c O hε hne)
  have h2 : Tendsto ((fun w : ℝ × ℝ × ℝ × ℝ => F1 H d w.1 w.2.1 w.2.2.1 w.2.2.2) ∘
      (fun ϑ : ℝ => ((ε, O.q11 ε ϑ, O.q12 ε ϑ, O.cpar ε ϑ) : ℝ × ℝ × ℝ × ℝ)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev] with ϑ hϑ
    simp only [Function.comp_apply]
    exact hϑ.1.symm
  exact tendsto_nhds_unique h1 h2

end UpperTailOptimizers
