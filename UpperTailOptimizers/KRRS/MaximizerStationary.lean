import UpperTailOptimizers.KRRS.SigmaLink
import UpperTailOptimizers.KRRS.CChart

/-!
# Stationarity of bipodal entropy maximizers

Paragraph 4 of Appendix A of `paper/bipodal_optimizer.tex` turns graphon maximality of a bipodal
graphon into the desingularized stationarity system `F₁ = F₂ = 0` for its parameters.  This
file is that step at a single positive surplus `ϑ`, for abstract parameters and an abstract
pode-size chart:

1. `bipodal_transfer` converts `e(W) = ε` into `E(θ) = ε` and `t(H,W) = ε^m + ϑ` into
   `T_H(θ) = ε^m + ϑ`;
2. `E(θ) = ε` together with `c ≠ 1` *solves* for the second-pode density,
   `q₂₂ = Q(ε,q₁₁,q₁₂,c)` `eq:krrs-edge-constraint` — the converse of `bipEdge_Qmap`;
3. substituting, `𝒯̂(ε,q₁₁,q₁₂,c) = ε^m + ϑ` (`That_eq_bipTd`);
4. the **uniqueness** clause of the pode-size chart (`exists_C_chart`,
   `eq:krrs-density-constraint`) pins `c = C(ε,q₁₁,q₁₂,ϑ)`;
5. `isLocalMax_reduced_entropy` (`KRRS/LocalMax.lean`) turns graphon maximality into local
   maximality of the reduced entropy `Σ(ε,·,·,ϑ)`, and
6. `F_eq_zero_of_isLocalMax` (`KRRS/SigmaLink.lean`) turns that into `F₁ = F₂ = 0`.

The strict positivity `0 < c` needed in step 6 comes from the strict surplus: a bipodal
graphon with a null first pode is constant (`tBip_zero`), so its `H`-density would be
`ε^m`, contradicting `ϑ > 0`.

It is used in `Bipodality/Optimal.lean`, where the chart is taken at the first-pode density of
the maximizer and a compactness argument makes the neighbourhoods uniform.

## Contents

* `F_eq_zero_of_maximizer` — stationarity of a bipodal maximizer at a fixed surplus.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Filter Topology

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

end UpperTailOptimizers
