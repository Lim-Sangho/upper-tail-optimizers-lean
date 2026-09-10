import UpperTailOptimizers.SingularEndpoint.TerminalUnique

/-!
# Theorem 1.6 as a corollary of Theorem 7.1

`singular_endpoint_full` proves the family properties, optimality, uniqueness and
leading cost expansion. The introduction keeps the optimizer and convergence
conclusions. The additional boundary inequality is a separate theorem,
`singular_endpoint_symmetry_breaking`, in `StrictImprovement.lean`.
-/

namespace UpperTailOptimizers.SingularEndpoint

/-- **Theorem 1.6.** A direct projection of Theorem 7.1. -/
theorem singular_endpoint_optimizers {d : ℕ} (hd : 2 ≤ d)
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) (hv : 2 ≤ Fintype.card V) :
    ∃ (B : KKTFamily d) (δ : ℝ), SingularEndpointOptimizers H B δ := by
  obtain ⟨B, δ, h⟩ := singular_endpoint_full hd H hreg hcard hv
  exact ⟨B, δ, h.toSingularEndpointOptimizers⟩

end UpperTailOptimizers.SingularEndpoint
