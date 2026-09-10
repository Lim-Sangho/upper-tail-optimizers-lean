import UpperTailOptimizers.Graphon.ExternalInputs

/-!
# Cut metric and cut distance (Section 2)

This file records the cut-metric notions of Section 2 of `paper/bipodal_optimizer.tex`.

* `cutNorm`, `cutDist` — the cut norm and cut distance.

The file declares **no axiom**.  Two things that once lived here no longer do:

* Attainment of the infimum is the **theorem**
  `feasible_attains` in `Graphon/Attainment.lean`, derived from cut-compactness and the
  lower semicontinuity of `I_p`.
* The Chatterjee–Varadhan graphon LDP (`thm:graphon-large-deviations` of
  `paper/bipodal_optimizer.tex`) is outside the formalised scope. The unconstrained
  abstract-probability formulation described below is refutable; this is not a
  counterexample to the graphon LDP.
-/

namespace UpperTailOptimizers

open MeasureTheory Real
open scoped Classical

/-- The cut norm `‖U‖_□ = sup_{S,T} |∫_{S×T} U|` of an integrable kernel on
`[0,1]²` (Section 2). -/
noncomputable def cutNorm (U : ℝ → ℝ → ℝ) : ℝ :=
  sSup {v | ∃ S T : Set ℝ, MeasurableSet S ∧ MeasurableSet T ∧
    v = |∫ x in S, ∫ y in T, U x y ∂unitμ ∂unitμ|}

/-- The cut distance `δ_□(W,W') = inf_σ ‖W - (W')^σ‖_□`, the infimum over
relabellings `σ` of `[0,1]` (Section 2). -/
noncomputable def cutDist (W W' : Graphon) : ℝ :=
  sInf {v | ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
    v = cutNorm (fun x y => W.toFun x y - W'.toFun (σ x) (σ y))}

/-! ### The Chatterjee–Varadhan large deviation principle

Theorem 1.3 of `paper/bipodal_optimizer.tex` (the Chatterjee–Varadhan graphon LDP) is **not**
recorded here, and no result of the formalisation uses it.

It was previously carried as an axiom `chatterjeeVaradhan`, quantified over an abstract
normalised log-probability `logLaw : ℕ → (Graphon → Prop) → ℝ`.  That statement was
*refutable*: with `logLaw` an arbitrary function subject to no hypothesis tying it to the
law of `W_{G(n,p)}`, instantiating at the constant `logLaw n F = 1` and the (cut-closed)
set `F = fun _ => True` gives `1 ≤ -(1/2)·inf {I_p(W)} = 0`.  It has therefore been
removed.

Stating the LDP soundly requires a formal model of `G(n,p)` and of the empirical graphon
`W_{G_n}` — neither of which this development has, since every result formalised here is a
statement about the deterministic variational problem.  The random-graph corollaries of
Section 1 of the paper (the probability expansion and the conditional cut-convergence of
`W_{G_n}`) are consequently outside the formalised scope. -/

end UpperTailOptimizers
