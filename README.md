# Lean formalisation of *Bipodal optimizers in the upper-tail variational problem for regular subgraph densities*

This repository formalises the paper's deterministic graphon results in Lean 4 and Mathlib.
It covers the scalar boundary, optimizers near nonexceptional boundary points, and the
singular endpoint construction. It does not formalise the random graph model or the
probabilistic conclusions.

The reference is the paper included in this repository, [paper/paper.tex](paper/paper.tex).
The citations below use its compiled theorem, lemma and equation numbers and link to
the corresponding paper source. The detailed [numbered result index](FORMALISATION.md#numbered-result-index)
maps the paper's results to Lean entry points.

[FORMALISATION.md](FORMALISATION.md) explains the proofs, maps paper results to Lean
declarations, and records the exact assumptions and known differences.

## What is mainly formalised

This section maps the paper's main results to their Lean declarations and source files.
Each declaration name links to its own source line, including when several declarations
share a file.

| Paper result | Main Lean declarations<br>(namespace: `UpperTailOptimizers`) | Source files<br>(relative to `UpperTailOptimizers/`) |
|---|---|---|
| **[Theorem 1.5][thm:nonexceptional-optimizers]** — Nonexceptional optimizers; corollary of [Theorem 6.1][thm:local-optimizer-structure] | Introduction corollary: [main_bipodal_optimizer](UpperTailOptimizers/LocalOptimizer/Global.lean#L14) | [LocalOptimizer/Global.lean](UpperTailOptimizers/LocalOptimizer/Global.lean) |
| **[Theorem 1.6][thm:endpoint-optimizers]** — Singular endpoint optimizers; corollary of [Theorem 7.1][thm:endpoint-optimality] | Introduction corollary: [SingularEndpoint.singular_endpoint_optimizers](UpperTailOptimizers/SingularEndpoint/IntroSingularEndpointOptimizers.lean#L15) | [SingularEndpoint/IntroSingularEndpointOptimizers.lean](UpperTailOptimizers/SingularEndpoint/IntroSingularEndpointOptimizers.lean) |
| **[Theorem 2.1][thm:krrs-analytic-extension]** — Two-sided KRR–S extension, for regular graphs | Analytic parameter family: [krrs_rectangle](UpperTailOptimizers/KRRS/Main.lean#L50)<br>Bipodality and uniqueness: [kenyonRadinRenSadun](UpperTailOptimizers/KRRS/Main.lean#L96)<br>Two-sided analyticity: [kenyonRadinRenSadunStrip](UpperTailOptimizers/KRRS/Main.lean#L183)<br>Uniform block-size bound: [kenyonRadinRenSadunUniform](UpperTailOptimizers/KRRS/Main.lean#L284) | [KRRS/Main.lean](UpperTailOptimizers/KRRS/Main.lean) |
| **[Theorem 3.1][thm:scalar-lz-boundary]** — Scalar Lubetzky–Zhao boundary | Boundary arc construction: [scalar_lz_boundary_arcs](UpperTailOptimizers/LZBoundary/Existence.lean#L3137)<br>Boundary curve: [pcGlobal](UpperTailOptimizers/LZBoundary/Curve.lean#L140)<br>Second contact: [smGlobal](UpperTailOptimizers/LZBoundary/Curve.lean#L243)<br>Global boundary criterion: [lz_boundary_M2_global](UpperTailOptimizers/LZBoundary/Curve.lean#L167) | [LZBoundary/Existence.lean](UpperTailOptimizers/LZBoundary/Existence.lean), [LZBoundary/Curve.lean](UpperTailOptimizers/LZBoundary/Curve.lean) |
| **[Section 4][sec:local-reduction]** — Local reduction (Lemmas 4.1–4.4; Corollary 4.5) | Active constraint: [active_constraint](UpperTailOptimizers/LocalReduction/Main.lean#L274)<br>Uniform reduction: [reduction_core_uniform](UpperTailOptimizers/LocalReduction/Main.lean#L594)<br>Scalar minimization: [scalar_reduction](UpperTailOptimizers/LocalReduction/Main.lean#L728) | [LocalReduction/Main.lean](UpperTailOptimizers/LocalReduction/Main.lean) |
| **[Theorem 5.4][thm:positive-second-variation]** — Positive second variation | Full statement: [positive_second_variation](UpperTailOptimizers/Nondegeneracy/AnalyticExtension.lean#L291)<br>Analytic extension over `K`: [boundaryExcess_extension](UpperTailOptimizers/Nondegeneracy/AnalyticExtension.lean#L64)<br>Uniform Taylor bounds: [boundaryExcess_taylor](UpperTailOptimizers/Nondegeneracy/AnalyticExcess.lean#L742) | [Nondegeneracy/AnalyticExtension.lean](UpperTailOptimizers/Nondegeneracy/AnalyticExtension.lean), [Nondegeneracy/AnalyticExcess.lean](UpperTailOptimizers/Nondegeneracy/AnalyticExcess.lean) |
| **[Theorem 4.1][thm:nonexceptional-endpoint]** — Optimizers near nonexceptional endpoints (also gives Theorem 1.5) | Full local result: [local_structure](UpperTailOptimizers/LocalOptimizer/Main.lean#L329)<br>Part (d) with `0 < c < 1/2` on one window, same family: [bipodal_family_smallBlock](UpperTailOptimizers/LocalOptimizer/Analytic.lean#L635) | [LocalOptimizer/Main.lean](UpperTailOptimizers/LocalOptimizer/Main.lean), [LocalOptimizer/Analytic.lean](UpperTailOptimizers/LocalOptimizer/Analytic.lean) |
| **[Theorem 7.1][thm:endpoint-optimality]** — Singular endpoint optimizers (also gives Theorem 1.6) | Family, optimality and asymptotics: [SingularEndpoint.singular_endpoint_full](UpperTailOptimizers/SingularEndpoint/TerminalUnique.lean#L215) | [SingularEndpoint/TerminalUnique.lean](UpperTailOptimizers/SingularEndpoint/TerminalUnique.lean) |
| **[Theorem A.1][thm:krrs-bipodality]** — KRR–S bipodal entropy maximizer near zero surplus, for regular graphs; proved here, not assumed | Optimality of the analytic family: [KRRSFamily.isOptimal](UpperTailOptimizers/Bipodality/Optimal.lean#L131)<br>Exact bipodality of maximizers: [KRRSFamily.exists_bipodal](UpperTailOptimizers/Bipodality/BipodalUniform.lean#L301)<br>Euler–Lagrange equation: [QualDirs.el](UpperTailOptimizers/Bipodality/EulerLagrange.lean#L923)<br>Row balance: [QualDirs.ae_balFun_ge](UpperTailOptimizers/Bipodality/RowBalance.lean#L782)<br>Contraction estimate: [Graphon.rowDiff_le_contraction](UpperTailOptimizers/Bipodality/Contraction.lean#L645) | [Bipodality/Optimal.lean](UpperTailOptimizers/Bipodality/Optimal.lean), [Bipodality/BipodalUniform.lean](UpperTailOptimizers/Bipodality/BipodalUniform.lean), [Bipodality/](UpperTailOptimizers/Bipodality) |
| **[Theorem A.2][thm:krrs-cross-density]** — KRR–S cross density; proved here, not assumed | Packaged statement: [krrs_thm33](UpperTailOptimizers/KRRS/Inputs.lean#L77)<br>Existence and the selector: [exists_crit](UpperTailOptimizers/KRRS/PsiExists.lean#L150), [zetaFun](UpperTailOptimizers/KRRS/PsiExists.lean#L185)<br>Uniqueness of the critical point: [crit_unique](UpperTailOptimizers/KRRS/PsiUnique.lean#L227)<br>Maximality: [zetaFun_isMax](UpperTailOptimizers/KRRS/PsiExists.lean#L399)<br>Fixed point, involution and strict decrease: [zetaFun_rStar](UpperTailOptimizers/KRRS/PsiExists.lean#L200), [zetaFun_involutive](UpperTailOptimizers/KRRS/PsiExists.lean#L462), [zetaFun_strictAntiOn](UpperTailOptimizers/KRRS/PsiExists.lean#L475) | [KRRS/PsiExists.lean](UpperTailOptimizers/KRRS/PsiExists.lean), [KRRS/PsiUnique.lean](UpperTailOptimizers/KRRS/PsiUnique.lean), [KRRS/Inputs.lean](UpperTailOptimizers/KRRS/Inputs.lean) |
| **[Remark D.1][rmk:bipodal-parameter-expansions]** — Bipodal parameter asymptotics | Parameter expansions: [parameter_asymptotics](UpperTailOptimizers/LocalOptimizer/ParameterAsymptotics.lean#L479) | [LocalOptimizer/ParameterAsymptotics.lean](UpperTailOptimizers/LocalOptimizer/ParameterAsymptotics.lean) |

## What it rests on

The build uses six project axioms, in addition to Lean's foundational axioms
`propext`, `Classical.choice` and `Quot.sound`. The tables below state these assumptions
and show which ones each main theorem uses.

| Axiom | Paper reference | Assumed content | File |
|---|---|---|---|
| `generalized_holder` | [Eq. (4)][eq:generalized-holder] | For a finite `d`-regular graph with `m ≥ 1` edges and `d ≥ 2`, `t(H,W) ≤ (∫W^d)^{m/d}`. | [Graphon/ExternalInputs.lean](UpperTailOptimizers/Graphon/ExternalInputs.lean) |
| `lubetzkyZhao` | [Theorem 1.4][thm:lz-criterion] | Under the same graph hypotheses and `0 < p < r < 1`, `Φ_H(p,r) = J_p(r)` exactly when an affine function supports `x ↦ J_p(x^{1/d})` at `r^d`. This axiom does not include uniqueness. | [Graphon/ExternalInputs.lean](UpperTailOptimizers/Graphon/ExternalInputs.lean) |
| `cut_seqCompact` | Background in [Section 2.1][sec:graphons] | Every graphon sequence has a subsequence converging in `cutDist`. | [Graphon/CutContinuity.lean](UpperTailOptimizers/Graphon/CutContinuity.lean) |
| `edgeDensity_cutContinuous` | Background in [Section 2.1][sec:graphons] | Edge density is continuous under sequential cut convergence. | [Graphon/CutContinuity.lean](UpperTailOptimizers/Graphon/CutContinuity.lean) |
| `tDensity_cutContinuous` | Background in [Section 2.1][sec:graphons] | Every finite simple graph's homomorphism density is continuous under sequential cut convergence. | [Graphon/CutContinuity.lean](UpperTailOptimizers/Graphon/CutContinuity.lean) |
| `Ip_cut_lowerSemicontinuous` | Background in [Section 2.1][sec:graphons] | For `0 < p < 1`, an eventual upper bound on the costs along a cut-convergent sequence also bounds the limit's cost. | [Graphon/CutContinuity.lean](UpperTailOptimizers/Graphon/CutContinuity.lean) |

[Theorem A.1][thm:krrs-bipodality] (KRR–S Theorem 1.1) is not assumed: for `d`-regular graphs
and near zero surplus, the range the paper uses, it is proved in
[Bipodality/](UpperTailOptimizers/Bipodality) from `generalized_holder` and the four cut
axioms; see [FORMALISATION.md §6](FORMALISATION.md#6-what-it-rests-on).
The six declarations are not an independent basis: edge-density continuity follows
from homomorphism-density continuity applied to `K₂`, although both are currently axioms.

The main theorem dependencies are:

| Lean declaration | Project axioms |
|---|---|
| `scalar_lz_boundary_arcs` | None |
| `SingularEndpoint.singular_endpoint_full` | `generalized_holder` |
| `SingularEndpoint.singular_endpoint_optimizers` | `generalized_holder` |
| `SingularEndpoint.singular_endpoint_symmetry_breaking` | `lubetzkyZhao` |
| `krrs_rectangle`, `KRRSFamily.isOptimal` | `generalized_holder` and the four cut axioms |
| `analyticAt_AHGlobal_and_pos` | `generalized_holder` and the four cut axioms |
| `local_structure`, `main_bipodal_optimizer` | All six |

“None” means no project axioms; Lean's foundational axioms still appear in these proofs.
The Chatterjee–Varadhan large deviation principle is neither assumed nor formalised.

## Build and check

This section explains how to build the project with its pinned dependencies and
inspect the axioms used by its theorems.

The repository pins Lean to `leanprover/lean4:v4.33.1` and Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`).
With `~/.elan/bin` on `PATH`, run from the repository root:

```sh
lake exe cache get
lake build
rg -n '^axiom ' UpperTailOptimizers
```

The cache command downloads compiled Mathlib files. Keep `lake-manifest.json` unchanged
when reproducing this build: `lake update` may change dependency revisions.

After building, inspect theorem dependencies without creating a file:

```sh
lake env lean --stdin <<'EOF'
import UpperTailOptimizers
#print axioms UpperTailOptimizers.scalar_lz_boundary_arcs
#print axioms UpperTailOptimizers.SingularEndpoint.singular_endpoint_full
#print axioms UpperTailOptimizers.SingularEndpoint.singular_endpoint_optimizers
#print axioms UpperTailOptimizers.krrs_rectangle
#print axioms UpperTailOptimizers.KRRSFamily.isOptimal
#print axioms UpperTailOptimizers.analyticAt_AHGlobal_and_pos
#print axioms UpperTailOptimizers.local_structure
#print axioms UpperTailOptimizers.main_bipodal_optimizer
EOF
```

The project axioms should match the table above. A `sorryAx` dependency would indicate
a proof placeholder. This command checks the named declarations, not every declaration
in the repository.

Most names use the namespace `UpperTailOptimizers`. Singular endpoint names use
`UpperTailOptimizers.SingularEndpoint`; results attached to a family use
`UpperTailOptimizers.SingularEndpoint.KKTFamily`. For example:

```lean
#print axioms UpperTailOptimizers.SingularEndpoint.KKTFamily.distribution_unique
```

The 2026-09-13 build passed without warnings (8918 jobs). A separate traversal of
4880 compiled project declarations found only the six project axioms and the three
foundational axioms, with no `sorryAx`. See the
[verification scope](FORMALISATION.md#verification-scope) for what was checked and its limits.
The repository contains 212 Lean source files, including the root import module;
111 are under `SingularEndpoint/` and 27 under `Bipodality/`.

## Reading order

The following route starts with the definitions and assumptions, then connects the
paper's results to the Lean proofs.

1. Read the [definition conventions](FORMALISATION.md#definitions-and-domains) and the
   [assumptions](FORMALISATION.md#6-what-it-rests-on).
2. Use the [paper-to-Lean map](FORMALISATION.md#4-paper--lean) to find a theorem. Read its
   statement together with the [known differences](FORMALISATION.md#7-deviations-from-the-paper).
3. Read [the proof overview](FORMALISATION.md#1-the-dependency-layers), then follow the
   imports in the relevant Lean file.

<!-- Paper reference targets; display numbers come from the compiled manuscript. -->
[thm:nonexceptional-optimizers]: paper/sections/intro.tex#L238
[thm:endpoint-optimizers]: paper/sections/intro.tex#L287
[thm:krrs-analytic-extension]: paper/sections/preliminaries.tex#L181
[thm:scalar-lz-boundary]: paper/sections/lz_boundary.tex#L21
[sec:local-reduction]: paper/sections/local_reduction.tex#L1
[thm:positive-second-variation]: paper/sections/nondegeneracy.tex#L552
[thm:local-optimizer-structure]: paper/sections/local_optimizer.tex#L12
[thm:nonexceptional-endpoint]: paper/sections/nonexceptional.tex#L22
[thm:endpoint-optimality]: paper/sections/singular_endpoint.tex#L34
[rmk:bipodal-parameter-expansions]: paper/sections/appendix_local_optimizer.tex#L5
[eq:generalized-holder]: paper/sections/preliminaries.tex#L79
[thm:lz-criterion]: paper/sections/intro.tex#L228
[sec:graphons]: paper/sections/preliminaries.tex#L8
[thm:krrs-cross-density]: paper/sections/appendix_preliminaries.tex#L50
[thm:krrs-bipodality]: paper/sections/appendix_preliminaries.tex#L11
[lem:stationary-rank-one-bipodality]: paper/sections/singular_endpoint.tex#L151
[lem:rank-one-kkt-family]: paper/sections/singular_endpoint.tex#L270
[lem:rank-one-parameter-expansions]: paper/sections/singular_endpoint.tex#L508
[lem:constant-graphon-comparison]: paper/sections/singular_endpoint.tex#L561
[eq:graphon-stationarity]: paper/sections/singular_endpoint.tex#L94
[eq:block-stationarity]: paper/sections/singular_endpoint.tex#L122
