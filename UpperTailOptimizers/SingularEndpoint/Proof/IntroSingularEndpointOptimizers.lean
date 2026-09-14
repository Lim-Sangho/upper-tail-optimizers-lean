import UpperTailOptimizers.SingularEndpoint.Proof.TerminalUnique

/-!
# Theorem 1.6 as a corollary of Theorem 5.1

`singular_endpoint_full` proves the family properties, the inequality `p_h < pc(r_h)`,
optimality, uniqueness, both expansions and the conclusions for every block. The introduction
keeps the family, boundary inequality, optimizer, convergence and expansion conclusions for the
canonical block, and drops the base values, the analyticity of `u_h` and `α_h`, and the
arbitrary-block clause.
-/

namespace UpperTailOptimizers.SingularEndpoint

universe u

/-- **Theorem 1.6.** A direct projection of Theorem 5.1: one family and one remainder constant
depending only on `d`, and for every `d`-regular graph a window on which the conclusions hold. -/
theorem singular_endpoint_optimizers {d : ℕ} (hd : 2 ≤ d) :
    ∃ (B : KKTFamily d) (C : ℝ), 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
        (∀ v, H.degree v = d) → 1 ≤ H.edgeFinset.card → 2 ≤ Fintype.card V →
        ∃ δ : ℝ, SingularEndpointOptimizers H B C δ := by
  obtain ⟨B, C, hC, hfull⟩ := singular_endpoint_full.{u} hd
  exact ⟨B, C, hC, fun H _ hreg hcard hv => by
    obtain ⟨δ, h⟩ := hfull H hreg hcard hv
    exact ⟨δ, h.toSingularEndpointOptimizers⟩⟩

end UpperTailOptimizers.SingularEndpoint
