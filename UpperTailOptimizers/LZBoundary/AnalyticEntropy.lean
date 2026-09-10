import UpperTailOptimizers.LZBoundary.ContactMaps
import UpperTailOptimizers.Graphon.ScalarEntropy

/-!
# Real-analyticity of the scalar entropy

`analyticAt_shannonH` used to live in `Nondegeneracy/AnalyticTools.lean`, which sits high in
the import order (it reaches `LocalReduction/Main.lean`, hence `KRRS/Main.lean`).  Once Appendix A
was re-formalised, `KRRS/Reduced.lean` needed this lemma too, and importing `AnalyticTools`
from there closed an import cycle

  `KRRS/Reduced → Nondegeneracy/AnalyticTools → … → LocalReduction → KRRS/Main → … → KRRS/Reduced`.

So the lemma is recorded here instead, above both consumers: this file needs only
`LZBoundary/ContactMaps.lean` (for `analyticAt_log_comp`) and `Graphon/ScalarEntropy.lean`
(for `shannonH`), neither of which depends on the KRR–S development.
-/

namespace UpperTailOptimizers

open Real Filter Topology

/-- The Shannon entropy `H(x) = -x log x - (1-x) log(1-x)` is real-analytic on `(0,1)`. -/
theorem analyticAt_shannonH {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    AnalyticAt ℝ shannonH x := by
  have h1 : AnalyticAt ℝ (fun t : ℝ => t * Real.log t) x :=
    analyticAt_id.mul (analyticAt_log hx0)
  have h2 : AnalyticAt ℝ (fun t : ℝ => (1 - t) * Real.log (1 - t)) x := by
    have hg : AnalyticAt ℝ (fun t : ℝ => 1 - t) x := analyticAt_const.sub analyticAt_id
    exact hg.mul (analyticAt_log_comp hg (by linarith))
  have hE : AnalyticAt ℝ entIntegrand x := h1.add h2
  have hneg := hE.neg
  exact hneg.congr (by filter_upwards with t using rfl)

end UpperTailOptimizers
