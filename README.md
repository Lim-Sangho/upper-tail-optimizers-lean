# Lean formalization of *Bipodal optimizers in the upper-tail variational problem for regular subgraph densities*

This repository formalizes the deterministic graphon results of the
[paper](paper/paper.tex) in Lean 4 and Mathlib: the Lubetzky–Zhao boundary,
bipodal optimizers near nonexceptional boundary points, and optimizers near the
singular endpoint. The random graph model and probabilistic conclusions are outside
its scope.

## Main results

Each row identifies the main Lean declaration for a result in the paper. Paper
citations and Lean declarations link directly to their source lines. Declaration
names are relative to the namespace `UpperTailOptimizers`.

| Paper result | Lean declaration |
|---|---|
| [Theorem 1.5][thm:nonexceptional-optimizers] — Nonexceptional optimizers; corollary of [Theorem 4.1][thm:nonexceptional-endpoint] | Introduction corollary: [nonexceptional_optimizers](UpperTailOptimizers/NonexceptionalEndpoint/Proof/Global.lean#L133) |
| [Theorem 1.6][thm:endpoint-optimizers] — Singular endpoint optimizers; corollary of [Theorem 5.1][thm:singular-endpoint] | Introduction corollary: [SingularEndpoint.singular_endpoint_optimizers](UpperTailOptimizers/SingularEndpoint/Proof/IntroSingularEndpointOptimizers.lean#L19) |
| [Theorem 2.1][thm:krrs-analytic-extension] — Two-sided analytic extension of the KRR–S family | Analytic extension: [krrs_analytic_extension](UpperTailOptimizers/Preliminaries/KRRSAnalyticExtension/Extension.lean#L105) |
| [Theorem 3.1][thm:lz-boundary] — Lubetzky–Zhao boundary | Boundary and contact geometry: [lz_boundary](UpperTailOptimizers/LZBoundary/PaperForm.lean#L472) |
| [Theorem 4.1][thm:nonexceptional-endpoint] — Nonexceptional optimizer structure | Uniqueness, analyticity and asymptotics: [nonexceptional_endpoint](UpperTailOptimizers/NonexceptionalEndpoint/Proof/Global.lean#L42) |
| [Theorem 5.1][thm:singular-endpoint] — Singular endpoint optimizer structure | Family, uniqueness and both expansions: [SingularEndpoint.singular_endpoint_full](UpperTailOptimizers/SingularEndpoint/Proof/TerminalUnique.lean#L268) |
| [Theorem A.1][thm:krrs-bipodality] — KRR–S bipodal entropy maximizers | Bipodality and parameter family: [krrs_bipodality](UpperTailOptimizers/Preliminaries/KRRSAnalyticExtension/Bipodality.lean#L120) |
| [Theorem A.2][thm:krrs-cross-density] — KRR–S cross density | Cross-density selector: [krrs_cross_density](UpperTailOptimizers/Preliminaries/KRRSAnalyticExtension/PsiFill.lean#L286) |
| [Remark C.1][rmk:bipodal-parameter-expansions] — Bipodal parameter asymptotics | Parameter expansions: [bipodal_parameter_expansions](UpperTailOptimizers/NonexceptionalEndpoint/Proof/ParameterExpansions.lean#L56) |

## Assumptions

The proofs use six axioms, together with Lean's foundational axioms
`propext`, `Classical.choice` and `Quot.sound`.

| Axiom | Assumed result |
|---|---|
| `generalized_holder` | Generalized Hölder inequality for densities of regular graphs |
| `lubetzkyZhao` | Supporting-line criterion for when the constant graphon attains the minimum |
| `cut_seqCompact` | Sequential compactness in cut distance |
| `edgeDensity_cutContinuous` | Continuity of edge density under cut convergence |
| `tDensity_cutContinuous` | Continuity of homomorphism densities under cut convergence |
| `Ip_cut_lowerSemicontinuous` | Lower semicontinuity of relative entropy under cut convergence |

The $d$-regular restriction of KRR–S results is proved within the project.
Some proofs use different arguments from the paper.

## Build

The project pins Lean to `v4.33.1` and Mathlib to commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). With `~/.elan/bin`
on `PATH`, run these commands from the repository root:

```sh
lake exe cache get
lake build
```

The first command downloads compiled Mathlib files. Keep `lake-manifest.json`
unchanged to reproduce the pinned dependencies.

After building, inspect a theorem's assumptions with `#print axioms`:

```sh
lake env lean --stdin <<'EOF'
import UpperTailOptimizers
#print axioms UpperTailOptimizers.nonexceptional_optimizers
#print axioms UpperTailOptimizers.SingularEndpoint.singular_endpoint_optimizers
EOF
```

The output lists the theorem's project and foundational axioms; `sorryAx` would
indicate an unproved placeholder.

For definitions, the proof overview, detailed theorem correspondence and exact
assumptions, read [FORMALIZATION.md](FORMALIZATION.md).

<!-- Paper citations link to the corresponding source labels. -->
[thm:nonexceptional-optimizers]: paper/sections/intro.tex#L256
[thm:nonexceptional-endpoint]: paper/sections/nonexceptional.tex#L23
[thm:endpoint-optimizers]: paper/sections/intro.tex#L310
[thm:singular-endpoint]: paper/sections/singular.tex#L37
[thm:krrs-analytic-extension]: paper/sections/preliminaries.tex#L166
[thm:lz-boundary]: paper/sections/lz_boundary.tex#L21
[thm:krrs-bipodality]: paper/sections/appendix_preliminaries.tex#L12
[thm:krrs-cross-density]: paper/sections/appendix_preliminaries.tex#L46
[rmk:bipodal-parameter-expansions]: paper/sections/appendix_nonexceptional_endpoint.tex#L181
