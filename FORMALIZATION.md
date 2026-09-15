# Formalization guide

This guide connects the definitions, proofs and numbered results of the
[paper](paper/paper.tex) to their Lean declarations. It covers the deterministic
graphon theory. The random graph model, large deviation principle and probabilistic
consequences are outside the formalization.

## Definitions and notation

The variational problem fixes a finite simple `d`-regular graph `H`, with `d ≥ 2`
and `m = |E(H)| ≥ 1`. It minimizes the relative entropy `I_p(W)` subject to
`t(H,W) ≥ r^m`. The usual parameter range is `0 < p < r < 1`.

| Paper notation or concept | Lean representation |
|---|---|
| A graphon on `[0,1]²` | `Graphon` is a symmetric measurable kernel on `ℝ²` with values in `[0,1]`; integration uses `unitμ` on `[0,1]` and `gμ` on its square. `UnitGraphon` uses the paper's domain directly. The conversions in [UnitGraphon.lean](UpperTailOptimizers/Preliminaries/Graphons/UnitGraphon.lean) preserve densities and entropy. |
| `e(W)` and `t(H,W)` | `Graphon.edgeDensity` and `Graphon.tDensity`. Homomorphism density integrates one kernel value per unordered edge of `H`. |
| `J_p`, `I_p` and `s(W)` | `Jp`, `Graphon.Ip` and `Graphon.entropy`. Only `s(W)` includes the factor `1/2`, giving the coefficient `−2` in [Eq. (7)][eq:relative-entropy-identity]. |
| `Φ_H(p,r)` | `phiVar H p r`, the infimum over `Feasible H r W`. `phiVar_isGLB` proves that it is the infimum of a nonempty, bounded-below set for `0 < p < 1` and `r ∈ [0,1]`. |
| `S_H(ε,τ)` and `I_{p,r}(ε)` | `entropyEnvelope` and `reducedObjective`, valued in `EReal`. Empty constraint sets give `−∞` and `+∞`, respectively. Their `Real` variants agree on nonempty slices. |
| Bipodality and relabeling | `IsBipodal` means a.e. agreement with a three-value kernel on two measurable blocks. `IsRelabelling` is measure preserving and has an a.e. inverse. Optimizer uniqueness is stated up to such relabelings. |
| Cut distance and the graphon space | `cutDist` is a pseudometric; `GraphonSpace` is its metric quotient. A.e. equality after relabeling implies equality in this quotient. |
| `pc(r)`, `sm(r)`, `A_H(r)` and `λ(p,r)` | `pcGlobal`, `smGlobal`, `AHGlobal` and `lambdaGlobal`: the boundary curve, second contact density, second-variation coefficient and log-odds displacement. |
| The convex minorant and its contacts | `lce` is the lower convex envelope. `uMinus`, `uPlus`, `contactXa` and `contactXb` name the zeros and contacts used in the Lubetzky–Zhao boundary theorem. |
| `ζ_d(ε)` and `ψ_d(ε,z)` | `zetaFun` is the cross-density selector. `psiFill` fills the removable singularity of the scalar quotient at `z = ε` with its continuous value. |
| The rank-one family | `KKTFamily d` contains the analytic parameters, base values, symmetries and KKT equations. It depends on `d`; the graph enters the optimality statement. |

The **exceptional density** is `r_* = (d−1)/d`. The **singular endpoint** is the
boundary point `(pc(r_*), r_*)`, where the two contacts merge. At other boundary
points, `λ(p,r)` measures displacement into the symmetry-breaking region `p < pc(r)`.
The singular endpoint family instead uses `h`, half the difference between the two
values of its rank-one factor.

## Proof overview

The nonexceptional and singular endpoint optimizer theorems use different local
arguments. Away from the exceptional density, the proof reduces the problem to a
scalar minimum. At the singular endpoint, it constructs a rank-one family and
compares its cost with arbitrary competitors.
The [Graphon directory](UpperTailOptimizers/Preliminaries/Graphons/) supplies their common definitions,
cut convergence, relabeling results and attainment of the variational minimum.

### Nonexceptional boundary points

The [Lubetzky–Zhao boundary analysis](UpperTailOptimizers/LZBoundary/) constructs the two
contact densities and the common supporting line. The gap above this line controls
how much an optimizer can depart from the constant graphon near the boundary.

The [KRR–S construction](UpperTailOptimizers/Preliminaries/KRRSAnalyticExtension/) supplies an analytic family of
bipodal parameters at fixed edge and subgraph densities. The
[bipodality proof](UpperTailOptimizers/Preliminaries/KRRSBipodality/) identifies this family with the
entropy maximizers. It derives stationarity and row balance, then uses a contraction
estimate to force two classes of identical rows. Together these give
[Theorem 2.1][thm:krrs-analytic-extension]. The family uses coordinates `(ε,ϑ)`, where
`ϑ = τ − ε^m`; the paper writes the corresponding maximizer as `B_{ε,τ}`.

The [local reduction](UpperTailOptimizers/NonexceptionalEndpoint/LocalReduction/) shows that an upper-tail
optimizer has `t(H,W) = r^m` and lies in this fixed-density regime. Thus its only
remaining choice is the edge density `ε`, or equivalently the deficit `δ = r − ε`.
[Corollary 4.6][cor:scalar-reduction] identifies the graphon optimizers with the scalar minimizers.

The [second-variation estimates](UpperTailOptimizers/NonexceptionalEndpoint/QuadraticGrowth/) show that the
boundary cost has a positive quadratic term. Writing
`G_r(δ) = I_{pc(r),r}(r−δ) − J_{pc(r)}(r)`, the exact identity

`I_{p,r}(r−δ) − J_p(r) = G_r(δ) − λ(p,r)δ`

turns the problem into minimization of a scalar function with positive curvature.
This gives a unique minimizer and the edge-density and cost expansions. The
[local optimizer results](UpperTailOptimizers/NonexceptionalEndpoint/Proof/) then recover analytic
block parameters, with a smaller block whose size tends to zero.
[Theorem 4.1][thm:nonexceptional-endpoint] assembles these conclusions on one open neighborhood;
[Theorem 1.5][thm:nonexceptional-optimizers] follows from it. [Remark C.1][rmk:bipodal-parameter-expansions]
refines the individual block parameters.

### The singular endpoint

At the singular endpoint, the two contacts coincide, so a separate construction is
needed. The [SingularEndpoint directory](UpperTailOptimizers/SingularEndpoint/) has one subdirectory for each
subsection of Section 5. The [rank-one stationary family](UpperTailOptimizers/SingularEndpoint/RankOneStationaryFamily/)
constructs `W_h = f_h ⊗ f_h`, where `f_h` takes the values `u_h − h` and `u_h + h`.
The implicit function theorem produces an analytic family satisfying the KKT
stationarity equations. In the [constant-graphon comparison](UpperTailOptimizers/SingularEndpoint/ConstantGraphonComparison/),
analyticity and symmetry under `h ↦ −h` give

`e(W_h) − r_h = −(d−1)h² + O_d(h⁴)`,

`I_{p_h}(W_h) − J_{p_h}(r_h) = −d³h⁴/3 + O_d(h⁶)`.

The second expansion gives strict improvement over the constant graphon. The
Lubetzky–Zhao criterion then places `(p_h,r_h)` in the symmetry-breaking region.
To prove global optimality, the [localization](UpperTailOptimizers/SingularEndpoint/LocalizationRankOne/) step localizes a
feasible competitor of no greater cost and constructs its decomposition `W = f ⊗ f + E`.
The [auxiliary Lagrangian](UpperTailOptimizers/SingularEndpoint/AuxiliaryLagrangian/) and
[arbitrary-graphon comparison](UpperTailOptimizers/SingularEndpoint/GraphonComparison/) bound the cost contributions of the
factor and residual. Equality forces the candidate's two-valued factor, giving
uniqueness up to relabeling.

In the [proof of the theorem](UpperTailOptimizers/SingularEndpoint/Proof/), [Theorem 5.1][thm:singular-endpoint] chooses the
family and remainder constant depending only on `d`, and an optimality window for each graph `H`. Its conclusions hold for every
block of measure `α_h`. [Theorem 1.6][thm:endpoint-optimizers] is obtained by projecting to the
introduction's conclusions, including both expansions.

## Paper-to-Lean correspondence

Each row links a paper result to the declaration that states it. The tables follow
the paper's order and include the introduction corollaries. Selected supporting
results explain how the main declarations are assembled.

Paper citations use the compiled numbers and link to the corresponding LaTeX source.
Lean links point to declaration lines. Names are relative to `UpperTailOptimizers`;
namespaces of Lean structures, such as `Graphon.` or `KRRSFamily.`, are written explicitly.

### Introduction and analytic extension

The introduction states the optimizer results as consequences of the detailed
body theorems. The KRR–S extension provides the fixed-density family used in the
nonexceptional proof.

| Paper result | Lean declaration |
|---|---|
| [Theorem 1.3][thm:graphon-large-deviations] — Graphon large deviations | Outside the formalization |
| [Theorem 1.4][thm:lz-criterion] — Lubetzky–Zhao criterion | Criterion and uniqueness: [lz_criterion](UpperTailOptimizers/NonexceptionalEndpoint/Proof/LZCriterion.lean#L29) |
| [Theorem 1.5][thm:nonexceptional-optimizers] — Nonexceptional optimizers | Corollary of Theorem 4.1: [nonexceptional_optimizers](UpperTailOptimizers/NonexceptionalEndpoint/Proof/Global.lean#L133) |
| [Theorem 1.6][thm:endpoint-optimizers] — Singular endpoint optimizers | Corollary of Theorem 5.1: [singular_endpoint_optimizers](UpperTailOptimizers/SingularEndpoint/Proof/IntroSingularEndpointOptimizers.lean#L19) |
| [Theorem 2.1][thm:krrs-analytic-extension] — Two-sided KRR–S extension | Analytic parameter maps: [krrs_analytic_extension](UpperTailOptimizers/Preliminaries/KRRSAnalyticExtension/Extension.lean#L105) |

Theorems 1.1–1.2 are informal statements. Their deterministic content is represented
by Theorems 1.4–1.6. The KRR–S parameter family used by later proofs is
[krrs_rectangle](UpperTailOptimizers/Preliminaries/KRRSAnalyticExtension/Main.lean#L53); its optimality is [KRRSFamily.isOptimal](UpperTailOptimizers/Preliminaries/KRRSBipodality/Optimal.lean#L131).

### Lubetzky–Zhao boundary

These results construct the boundary and describe its contact geometry. The global
statements are derived from boundary arcs, which provide the local analytic data.

| Paper result | Lean declaration |
|---|---|
| [Theorem 3.1][thm:lz-boundary] — Lubetzky–Zhao boundary | Boundary and contacts: [lz_boundary](UpperTailOptimizers/LZBoundary/PaperForm.lean#L472) |
| [Lemma 3.2][lem:convexity-defect] — Convexity defect | Curvature and its zeros: [convexity_defect_zeros](UpperTailOptimizers/LZBoundary/PaperForm.lean#L96) |
| [Lemma 3.3][lem:contact-points] — Contact points | Contact functions: [contact_points](UpperTailOptimizers/LZBoundary/PaperForm.lean#L246) |
| [Lemma 3.4][lem:contact-point-limits] — Contact-point limits | Limiting values: [contact_point_limits](UpperTailOptimizers/LZBoundary/PaperForm.lean#L356) |

The local data are constructed by [lz_boundary_arcs](UpperTailOptimizers/LZBoundary/Existence.lean#L3137) and stored in
`LZBoundaryArc`. For individual clauses of Theorem 3.1, [lz_boundary_M2_lce](UpperTailOptimizers/LZBoundary/PaperForm.lean#L390)
provides the convex-minorant criterion and [lz_boundary_quadSep](UpperTailOptimizers/LZBoundary/PaperForm.lean#L426) provides uniform
quadratic separation.

### Nonexceptional optimizers

The local reduction identifies the scalar problem, and the quadratic estimates give
its positive curvature. Theorem 4.1 combines these ingredients with the analytic
family to prove uniqueness and asymptotics on one neighborhood.

| Paper result | Lean declaration |
|---|---|
| [Theorem 4.1][thm:nonexceptional-endpoint] — Optimizer structure | Uniqueness, analyticity and asymptotics: [nonexceptional_endpoint](UpperTailOptimizers/NonexceptionalEndpoint/Proof/Global.lean#L42) |
| [Lemma 4.2][lem:active-constraint] — Active density constraint | Equality `t(H,W) = r^m`: [active_constraint](UpperTailOptimizers/NonexceptionalEndpoint/LocalReduction/Main.lean#L275) |
| [Lemma 4.3][lem:edge-density-deficit] — Strict edge-density deficit | Inequality `e(W) < r`: [edge_density_deficit](UpperTailOptimizers/NonexceptionalEndpoint/LocalReduction/Global.lean#L99) |
| [Lemma 4.4][lem:boundary-convergence] — Boundary convergence | Cut and edge-density convergence: [boundary_convergence](UpperTailOptimizers/NonexceptionalEndpoint/LocalReduction/Global.lean#L113) |
| [Lemma 4.5][lem:fixed-density-bipodality] — Localization and bipodality | Fixed-density optimizers: [fixed_density_bipodality](UpperTailOptimizers/NonexceptionalEndpoint/LocalReduction/Global.lean#L617) |
| [Corollary 4.6][cor:scalar-reduction] — One-dimensional reduction | Bijection of minimizers: [one_dimensional_reduction](UpperTailOptimizers/NonexceptionalEndpoint/LocalReduction/Global.lean#L326) |
| [Lemma 4.7][lem:scalar-quadratic-bound] — Scalar quadratic lower bound | Uniform lower bound: [scalar_quadratic_bound_Icc](UpperTailOptimizers/NonexceptionalEndpoint/QuadraticGrowth/Global.lean#L251) |
| [Corollary 4.8][prop:graphon-quadratic-bound] — Graphon quadratic lower bound | Bound with the constants of Lemma 4.7: [graphon_quadratic_bound_Icc](UpperTailOptimizers/NonexceptionalEndpoint/QuadraticGrowth/Global.lean#L290) |
| [Lemma 4.9][lem:bipodal-quadratic-bound] — Bipodal quadratic upper bound | Bipodal competitor: [bipodal_quadratic_bound](UpperTailOptimizers/NonexceptionalEndpoint/QuadraticGrowth/Global.lean#L313) |
| [Theorem 4.10][thm:positive-second-variation] — Positive second variation | Analytic extension and Taylor bounds: [positive_second_variation_interval](UpperTailOptimizers/NonexceptionalEndpoint/QuadraticGrowth/Global.lean#L344) |

[uniform_scalar_reduction](UpperTailOptimizers/NonexceptionalEndpoint/LocalReduction/Global.lean#L530) combines localization with scalar minimization.
[local_structure](UpperTailOptimizers/NonexceptionalEndpoint/Proof/Main.lean#L354) collects the optimizer conclusions as a structure;
`nonexceptional_endpoint` states them on one common open neighborhood.
The coefficient identity `A_H(r) = ∂²_δG(r,0)` is
[dDelta_dDelta_eq_AHGlobal](UpperTailOptimizers/NonexceptionalEndpoint/Proof/Coefficient.lean#L40), and [analyticAt_AHGlobal_and_pos](UpperTailOptimizers/NonexceptionalEndpoint/Proof/Main.lean#L211) proves its
analyticity and positivity.

### Singular endpoint optimizers

The family and comparison lemmas culminate in Theorem 5.1. In the uniform statements,
constants depending on `d` or `(d,m)` are chosen before the graph, as in the paper.

| Paper result | Lean declaration |
|---|---|
| [Theorem 5.1][thm:singular-endpoint] — Optimizer structure | Family, optimality, uniqueness and expansions: [singular_endpoint_full](UpperTailOptimizers/SingularEndpoint/Proof/TerminalUnique.lean#L266) |
| [Lemma 5.2][lem:stationary-rank-one-bipodality] — Stationary rank-one bipodality | Bipodality from stationarity: [stationary_rank_one_bipodality](UpperTailOptimizers/SingularEndpoint/RankOneStationaryFamily/StationaryBipodality.lean#L95) |
| [Lemma 5.3][lem:rank-one-kkt-family] — Analytic KKT family | Stationarity and local exhaustiveness: [rank_one_kkt_family](UpperTailOptimizers/SingularEndpoint/RankOneStationaryFamily/RankOneKKTFamily.lean#L998) |
| [Remark 5.4][rmk:rank-one-family-universality] — Dependence on `d` | Family structure: [KKTFamily](UpperTailOptimizers/SingularEndpoint/RankOneStationaryFamily/Family.lean#L124) |
| [Lemma 5.5][lem:rank-one-parameter-expansions] — Parameter expansions | All four expansions: [rank_one_parameter_expansions](UpperTailOptimizers/SingularEndpoint/ConstantGraphonComparison/ParameterRemainders.lean#L196) |
| [Lemma 5.6][lem:constant-graphon-comparison] — Constant-graphon comparison | Both expansions, strict improvement and boundary placement: [constant_graphon_comparison_full](UpperTailOptimizers/SingularEndpoint/ConstantGraphonComparison/ConstantComparison.lean#L32) |
| [Lemma 5.7][lem:localization-rank-one] — Localization and rank-one reduction | Decomposition and bounds: [localization_rank_one_reduction](UpperTailOptimizers/SingularEndpoint/LocalizationRankOne/LocalizationRankOne.lean#L118) |
| [Lemma 5.8][lem:continuation-kernel-bounds] — Continuation and kernel bounds | All six estimates: [continuation_kernel_bounds](UpperTailOptimizers/SingularEndpoint/AuxiliaryLagrangian/ContinuationKernelBounds.lean#L201) |
| [Lemma 5.9][lem:first-variation-bound] — First-variation lower bound | Central and tail estimates: [first_variation_bound](UpperTailOptimizers/SingularEndpoint/AuxiliaryLagrangian/FirstVariationCentralKernel.lean#L74) |
| [Lemma 5.10][lem:central-kernel-bound] — Central kernel bound | Bound uniform in the radius: [central_kernel_bound](UpperTailOptimizers/SingularEndpoint/AuxiliaryLagrangian/FirstVariationCentralKernel.lean#L162) |
| [Lemma 5.11][lem:auxiliary-lagrangian-bound] — Auxiliary Lagrangian bound | Uniform comparison for the factor: [auxiliary_lagrangian_bound_uniform](UpperTailOptimizers/SingularEndpoint/GraphonComparison/PaperForms.lean#L136) |
| [Lemma 5.12][lem:graphon-lagrangian-bound] — Full-graphon Lagrangian bound | Uniform graphon comparison: [graphon_lagrangian_bound_uniform](UpperTailOptimizers/SingularEndpoint/GraphonComparison/PaperForms.lean#L221) |

The family is constructed by [exists_kktFamily](UpperTailOptimizers/SingularEndpoint/RankOneStationaryFamily/FamilyBuild.lean#L40).
[constant_graphon_comparison](UpperTailOptimizers/SingularEndpoint/ConstantGraphonComparison/CostRemainder.lean#L127) gives the scalar expansions, while
[singular_endpoint_symmetry_breaking](UpperTailOptimizers/SingularEndpoint/ConstantGraphonComparison/StrictImprovement.lean#L134) uses the Lubetzky–Zhao
criterion to show `p_h < pc(r_h)`.
[anyBlock_of_singularEndpointOptimizers](UpperTailOptimizers/SingularEndpoint/Proof/TerminalUnique.lean#L176) transfers the optimizer
conclusions from the canonical block to any block of the prescribed measure.

### Appendices

The appendices supply the KRR–S results, scalar geometry and parameter calculations
used in the body. Appendix D supports the singular endpoint family and expansions
listed in the preceding table.

| Paper result | Lean declaration |
|---|---|
| [Theorem A.1][thm:krrs-bipodality] — Bipodal entropy maximizers | Optimizers and analytic parameters: [krrs_bipodality](UpperTailOptimizers/Preliminaries/KRRSAnalyticExtension/Bipodality.lean#L120) |
| [Theorem A.2][thm:krrs-cross-density] — Cross-density selector | Scalar selector properties: [krrs_cross_density](UpperTailOptimizers/Preliminaries/KRRSAnalyticExtension/PsiFill.lean#L286) |
| [Lemma B.1][lem:two-point-convex-minorant] — Two-point convex minorant | Attained representation: [lce_isLeast_twoPoint](UpperTailOptimizers/LZBoundary/ConvexMinorant.lean#L1056) |
| [Remark C.1][rmk:bipodal-parameter-expansions] — Parameter asymptotics | Expansions with `ζ_d(r)`: [bipodal_parameter_expansions](UpperTailOptimizers/NonexceptionalEndpoint/Proof/ParameterExpansions.lean#L56) |

For Remark C.1, the identities [zetaFun_eq_smGlobal](UpperTailOptimizers/NonexceptionalEndpoint/Proof/CrossDensity.lean#L42) and [zetaFun_two](UpperTailOptimizers/NonexceptionalEndpoint/Proof/CrossDensity.lean#L92) identify
the cross density, and [bipodal_block_size_two](UpperTailOptimizers/NonexceptionalEndpoint/Proof/ParameterExpansions.lean#L148) gives the block-size expansion
for `d = 2`. The general parameter theorem includes [Eq. (103)][eq:optimizer-block-size] and
[Eq. (104)][eq:optimizer-block-density] with bounds uniform on a smaller neighborhood.

## Axioms and dependencies

The statements below specify the six external results assumed as axioms.
Lean's foundational axioms are `propext`, `Classical.choice` and `Quot.sound`,
and are excluded in the following table.

| Axiom | Exact assumed content |
|---|---|
| [generalized_holder](UpperTailOptimizers/Preliminaries/Graphons/ExternalInputs.lean#L70) | For every finite `d`-regular graph with `d ≥ 2`, `m ≥ 1` and every graphon `W`, `t(H,W) ≤ (∫W^d)^{m/d}`, as in [Eq. (5)][eq:generalized-holder]. |
| [lubetzkyZhao](UpperTailOptimizers/Preliminaries/Graphons/ExternalInputs.lean#L122) | Under the same graph hypotheses and `0 < p < r < 1`, `Φ_H(p,r) = J_p(r)` iff an affine function supports `x ↦ J_p(x^{1/d})` at `r^d` on `[0,1]`. This is the variational-value criterion underlying [Theorem 1.4][thm:lz-criterion]. |
| [cut_seqCompact](UpperTailOptimizers/Preliminaries/Graphons/CutContinuity.lean#L98) | Every graphon sequence has a subsequence converging in cut distance to a graphon. |
| [edgeDensity_cutContinuous](UpperTailOptimizers/Preliminaries/Graphons/CutContinuity.lean#L103) | If a graphon sequence converges in cut distance, its edge densities converge to the limit's edge density. |
| [tDensity_cutContinuous](UpperTailOptimizers/Preliminaries/Graphons/CutContinuity.lean#L108) | Under the same convergence, `t(H,W_n) → t(H,W)` for every finite simple graph `H`. |
| [Ip_cut_lowerSemicontinuous](UpperTailOptimizers/Preliminaries/Graphons/CutContinuity.lean#L117) | For `0 < p < 1`, if `W_n → W` in cut distance and eventually `I_p(W_n) ≤ C`, then `I_p(W) ≤ C`. |

### Dependencies of the main results

The table shows which external assumptions each main result uses. Its rows match
the results and order in the README's main-results table. Each row refers to the
main Lean declaration for that result, including dependencies inherited through
other theorems.

**Hölder** is `generalized_holder`, and **LZ** is `lubetzkyZhao`.
**Cut axioms** groups the last four assumptions about convergence in cut distance in the above table.
A check mark means the proof uses the assumption; a dash means it does not.
For **Cut axioms**, these mean all four or none. Lean's foundational axioms are omitted.

| Paper result | Hölder | LZ | Cut axioms |
|---|:---:|:---:|:---:|
| [Theorem 1.5][thm:nonexceptional-optimizers] — Nonexceptional optimizers | ✓ | ✓ | ✓ |
| [Theorem 1.6][thm:endpoint-optimizers] — Singular endpoint optimizers | ✓ | ✓ | — |
| [Theorem 2.1][thm:krrs-analytic-extension] — KRR–S analytic extension | ✓ | — | ✓ |
| [Theorem 3.1][thm:lz-boundary] — Lubetzky–Zhao boundary | — | — | — |
| [Theorem 4.1][thm:nonexceptional-endpoint] — Nonexceptional optimizer structure | ✓ | ✓ | ✓ |
| [Theorem 5.1][thm:singular-endpoint] — Singular endpoint optimizer structure | ✓ | ✓ | — |
| [Theorem A.1][thm:krrs-bipodality] — KRR–S bipodality | ✓ | — | ✓ |
| [Theorem A.2][thm:krrs-cross-density] — KRR–S cross density | — | — | — |
| [Remark C.1][rmk:bipodal-parameter-expansions] — Parameter asymptotics | ✓ | ✓ | ✓ |

To check a declaration's assumptions, use `#print axioms` after importing
`UpperTailOptimizers`.

## Differences in proof methods

Some Lean proofs use different arguments from those in the paper.
The differences are explained below for each result.

- **KRR–S results ([Theorem A.1][thm:krrs-bipodality] and [Theorem A.2][thm:krrs-cross-density]).** Lean
  constructs the stationary family and proves its optimality directly. The paper
  invokes the external bipodality theorem and identifies its optimizers with the
  analytic family in [Eq. (95)][eq:krrs-map-agreement]. The Lean cross-density proof shows
  that every critical point is a strict local maximum, which yields uniqueness.
  The separate [bipodality proof](paper/sections/krrs_bipodality.tex) describes the
  argument used by Lean and is not included in the compiled paper.
- **Rank-one factor ([Lemma 5.7][lem:localization-rank-one]).** The paper constructs the factor
  variationally. Lean obtains it as a fixed point of a contraction in `L⁴`, then
  proves the localization bounds.
- **Comparison estimates ([Lemma 5.9][lem:first-variation-bound]–[Lemma 5.12][lem:graphon-lagrangian-bound]).**
  The final Lean optimality proof first uses one closed neighborhood and a linear
  moment correction, then converts the comparison to the graph constraint. Separate
  declarations give the paper's open neighborhoods and nonlinear Lagrangian bounds.

<!-- Paper citations link to the corresponding source labels. -->
[eq:relative-entropy-identity]: paper/sections/preliminaries.tex#L96
[thm:krrs-analytic-extension]: paper/sections/preliminaries.tex#L166
[cor:scalar-reduction]: paper/sections/nonexceptional_local_reduction.tex#L189
[thm:nonexceptional-endpoint]: paper/sections/nonexceptional.tex#L23
[thm:nonexceptional-optimizers]: paper/sections/intro.tex#L256
[rmk:bipodal-parameter-expansions]: paper/sections/appendix_nonexceptional_endpoint.tex#L181
[thm:singular-endpoint]: paper/sections/singular.tex#L37
[thm:endpoint-optimizers]: paper/sections/intro.tex#L310
[thm:graphon-large-deviations]: paper/sections/intro.tex#L223
[thm:lz-criterion]: paper/sections/intro.tex#L245
[thm:lz-boundary]: paper/sections/lz_boundary.tex#L21
[lem:convexity-defect]: paper/sections/lz_boundary.tex#L65
[lem:contact-points]: paper/sections/lz_boundary.tex#L95
[lem:contact-point-limits]: paper/sections/lz_boundary.tex#L113
[lem:active-constraint]: paper/sections/nonexceptional_local_reduction.tex#L12
[lem:edge-density-deficit]: paper/sections/nonexceptional_local_reduction.tex#L54
[lem:boundary-convergence]: paper/sections/nonexceptional_local_reduction.tex#L75
[lem:fixed-density-bipodality]: paper/sections/nonexceptional_local_reduction.tex#L128
[lem:scalar-quadratic-bound]: paper/sections/nonexceptional_quadratic_growth.tex#L64
[prop:graphon-quadratic-bound]: paper/sections/nonexceptional_quadratic_growth.tex#L122
[lem:bipodal-quadratic-bound]: paper/sections/nonexceptional_quadratic_growth.tex#L151
[thm:positive-second-variation]: paper/sections/nonexceptional_quadratic_growth.tex#L247
[lem:stationary-rank-one-bipodality]: paper/sections/singular_stationary_family.tex#L85
[lem:rank-one-kkt-family]: paper/sections/singular_stationary_family.tex#L204
[rmk:rank-one-family-universality]: paper/sections/singular_stationary_family.tex#L413
[lem:rank-one-parameter-expansions]: paper/sections/singular_constant_comparison.tex#L31
[lem:constant-graphon-comparison]: paper/sections/singular_constant_comparison.tex#L84
[lem:localization-rank-one]: paper/sections/singular_localization.tex#L82
[lem:continuation-kernel-bounds]: paper/sections/singular_auxiliary_lagrangian.tex#L133
[lem:first-variation-bound]: paper/sections/singular_auxiliary_lagrangian.tex#L320
[lem:central-kernel-bound]: paper/sections/singular_auxiliary_lagrangian.tex#L417
[lem:auxiliary-lagrangian-bound]: paper/sections/singular_auxiliary_lagrangian.tex#L627
[lem:graphon-lagrangian-bound]: paper/sections/singular_graphon_comparison.tex#L14
[thm:krrs-bipodality]: paper/sections/appendix_preliminaries.tex#L12
[thm:krrs-cross-density]: paper/sections/appendix_preliminaries.tex#L46
[lem:two-point-convex-minorant]: paper/sections/appendix_lz_boundary.tex#L14
[eq:optimizer-block-size]: paper/sections/appendix_nonexceptional_endpoint.tex#L215
[eq:optimizer-block-density]: paper/sections/appendix_nonexceptional_endpoint.tex#L221
[eq:generalized-holder]: paper/sections/preliminaries.tex#L76
[sec:graphons]: paper/sections/preliminaries.tex#L13
[eq:krrs-map-agreement]: paper/sections/appendix_preliminaries.tex#L612
