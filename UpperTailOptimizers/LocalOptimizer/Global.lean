import UpperTailOptimizers.LocalOptimizer.Main

/-!
# Theorem 1.5 as a corollary of Theorem 6.1

`local_structure` in `LocalOptimizer/Main.lean` proves the global optimizer theorem,
including the positive analytic coefficient and the analytic bipodal family.
The introduction retains the coefficient, uniqueness and asymptotic conclusions.
-/

namespace UpperTailOptimizers

/-- **Theorem 1.5.** A direct projection of Theorem 6.1. -/
theorem main_bipodal_optimizer {d : ℕ} (hd : 2 ≤ d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1) (hr₀ex : r₀ ≠ rStar d) : NonexceptionalOptimizers H d r₀ :=
  (local_structure hd H hreg hm hr₀0 hr₀1 hr₀ex).toNonexceptionalOptimizers

end UpperTailOptimizers
