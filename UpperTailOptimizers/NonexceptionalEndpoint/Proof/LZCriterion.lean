import UpperTailOptimizers.NonexceptionalEndpoint.Proof.Main

/-!
# The Lubetzky–Zhao criterion

`thm:lz-criterion` of `paper/paper.tex`: let `H` be `d`-regular with `d ≥ 2` and `0 < p < r < 1`.
If `(r^d, J_p(r))` lies on the convex minorant of `φ_{p,d} : x ↦ J_p(x^{1/d})`, the constant
graphon `W ≡ r` is the unique minimizer of `eq:graphon-variational-problem`; otherwise it is not a
minimizer.

The convex minorant is `lce 0 1 (phi p d)` (`LZBoundary/ConvexMinorant.lean`), and `W` is a
minimizer when `Feasible H r W` and `W.Ip p = phiVar H p r`.  A minimizer equal to `r` almost
everywhere is the constant graphon up to relabelling.

The first half does not use the axiom `lubetzkyZhao`: condition (M2) of Theorem 3.1
turns the minorant condition into `pc(r) ≤ p`, and `replica_symmetric_unique_global` (or
`replica_symmetric_unique_of_pStar_le` at `r = r_*`) gives the unique minimizer from
`generalized_holder`.  The second half uses `lubetzkyZhao`, which states that `Φ_H(p,r) = J_p(r)`
exactly when a supporting line touches `φ_{p,d}` at `r^d`.
-/

namespace UpperTailOptimizers

open MeasureTheory

/-- **`thm:lz-criterion`** (Lubetzky–Zhao criterion).  For a `d`-regular `H` with `d ≥ 2` and
`0 < p < r < 1`: if `lce 0 1 φ_{p,d} (r^d) = J_p(r)` then `W ≡ r` is a minimizer and every minimizer
equals `r` almost everywhere; otherwise `W ≡ r` is not a minimizer. -/
theorem lz_criterion {d : ℕ} (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) {p r : ℝ} (hp0 : 0 < p) (hpr : p < r) (hr1 : r < 1) :
    (lce 0 1 (phi p d) (r ^ d) = Jp p r →
      (∀ hr : r ∈ Set.Icc (0:ℝ) 1,
        Feasible H r (constGraphon r hr) ∧ (constGraphon r hr).Ip p = phiVar H p r) ∧
      ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
        ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = r) ∧
    (lce 0 1 (phi p d) (r ^ d) ≠ Jp p r →
      ∀ hr : r ∈ Set.Icc (0:ℝ) 1,
        ¬ (Feasible H r (constGraphon r hr) ∧ (constGraphon r hr).Ip p = phiVar H p r)) := by
  have hr0 : 0 < r := lt_trans hp0 hpr
  have hp1 : p < 1 := lt_trans hpr hr1
  have hrd : r ^ d ∈ Set.Ioo (0:ℝ) 1 := ⟨pow_pos hr0 d, pow_lt_one₀ hr0.le hr1 (by omega)⟩
  have hphi_eq : phi p d (r ^ d) = Jp p r := (Jp_eq_phi_pow hd hr0.le).symm
  -- lying on the convex minorant is the supporting-line condition
  have hsupp : (∃ a : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1, Jp p r + a * (x - r ^ d) ≤ phi p d x) ↔
      lce 0 1 (phi p d) (r ^ d) = Jp p r := by
    rw [← hphi_eq]
    exact exists_supportingLine_iff_lce_eq zero_lt_one (phi_continuousOn_Icc hd hp0 hp1) hrd
  refine ⟨fun hon => ?_, fun hoff hr => ?_⟩
  · have hpc : pcGlobal d r ≤ p := (lz_boundary_M2_global hd hr0 hr1 hp0 hp1).mp (hsupp.mpr hon)
    have hRS : phiVar H p r = Jp p r ∧
        (∀ hr' : r ∈ Set.Icc (0:ℝ) 1, (constGraphon r hr').Ip p = phiVar H p r) ∧
        (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
          ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = r) := by
      by_cases hrex : r = rStar d
      · subst hrex
        rw [pcGlobal_rStar hd] at hpc
        exact replica_symmetric_unique_of_pStar_le hd hr0 hr1 hpc hpr H hreg hm
      · exact replica_symmetric_unique_global hd H hreg hm hr0 hr1 hrex hpc hpr
    exact ⟨fun hr => ⟨feasible_constGraphon H hr, hRS.2.1 hr⟩, hRS.2.2⟩
  · rintro ⟨-, hIp⟩
    rw [Ip_constGraphon hr p] at hIp
    exact hoff (hsupp.mp ((lubetzkyZhao H hd hreg hm hp0 hpr hr1).mp hIp.symm))

end UpperTailOptimizers
