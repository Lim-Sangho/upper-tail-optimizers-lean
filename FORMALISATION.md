# How the paper is formalised

This guide explains how the Lean development relates to the paper in this repository,
[paper/paper.tex](paper/paper.tex), whose sections are in [paper/sections/](paper/sections/).
[README.md](README.md) gives the main results and build instructions.

| Guide section | Contents |
|---|---|
| 1–3 | Proof structure |
| 4 | Definitions and the paper-to-Lean map |
| 5 | Module map |
| 6 | Assumptions, theorem dependencies and verification scope |
| 7 | Differences from the paper |
| 8 | Results outside this repository |

Paper citations use the numbers in the compiled manuscript: for example,
[Theorem 1.5][thm:nonexceptional-optimizers], [Lemma 4.1][lem:active-constraint] and [Remark D.1][rmk:bipodal-parameter-expansions].
Click a numbered citation to open the corresponding paper source. Start with the
[numbered result index](#numbered-result-index) for an overview; the detailed tables
below it separate individual clauses and supporting calculations.

References written as §1–§8 point to sections of this guide. References written as
“Section”, “Theorem”, “Lemma” or “Eq.” point to the paper.
A table entry identifies the relevant Lean result, with its scope qualified in §7.

The numbers were checked against LaTeX output from the bundled `paper/paper.tex`.
When the manuscript changes, rebuild it and refresh the displayed numbers from
`paper.aux`. The Markdown reference definitions retain the paper labels for this
purpose; the rendered citations show only the result type and number.

## 1. The dependency layers

The nonexceptional argument starts with the scalar boundary, reduces the graphon problem
to one variable, and then studies the resulting minimum. The singular endpoint argument constructs
a separate rank-one family and compares it with arbitrary graphons.

| Layer | Purpose | Main files |
|---|---|---|
| Scalar analysis | Relative entropy, convex minorants and common tangent points | `LZBoundary/` |
| Boundary curves | Construct `pc` and the second contact point, first on arcs and then globally | `LZBoundary/Existence.lean`, `LZBoundary/Curve.lean` |
| Graphon foundations | Define densities, entropy, cut convergence and attainment | `Graphon/`, `Graphon/ExternalInputs.lean` |
| KRR–S extension | Extend fixed-density optimizer parameters through zero surplus | `KRRS/` |
| Local reduction | Reduce upper-tail minimization to edge density | `LocalReduction/Main.lean` |
| Second variation | Prove quadratic bounds and analytic expansions | `Nondegeneracy/` |
| Local optimizer structure | Prove uniqueness, analyticity and asymptotics near the boundary | `LocalOptimizer/` |
| Singular endpoint | Construct the family and prove optimality and uniqueness | `SingularEndpoint/` |

The project axioms enter at the graphon and KRR–S layers. Scalar boundary construction
uses no project axioms. The exact dependencies are listed in §6.

## 2. Sections 2–6 and Appendix A

### Scalar boundary

`LZBoundary/Jp.lean` defines relative entropy `Jp`.
The `Phi*` files study `φ_{p,d}(x) = J_p(x^{1/d})` and its convexity defect.
Much of the calculation uses `u = x^{1/d}`; `ContactBridge.lean` connects the two coordinates.

`LZBoundary/ConvexMinorant.lean` proves that the lower convex envelope at a point is an
attained minimum over two-point convex combinations.
The contact analysis then constructs the two points joined by a common supporting line
and proves their analytic dependence and limits at the ends of the contact curves.

`scalar_lz_boundary_arcs` collects the boundary properties in `LZBoundaryArc`.
`LZBoundary/Curve.lean` defines `pcGlobal` and `smGlobal`, identifies them with each arc's
functions, and proves continuity at the exceptional density. It also proves the global
supporting-line criterion, including the exceptional point.

### Graphons and the KRR–S extension

A graphon is a concrete measurable kernel. Integrals use Lebesgue measure restricted to
`[0,1]`; equality of optimizers is almost everywhere. The definition conventions are in §4.

The generalized Hölder inequality and the Lubetzky–Zhao criterion are external inputs.
Four further axioms describe sequential cut compactness, continuity and lower
semicontinuity. From these, `feasible_attains` proves that the upper-tail infimum is attained.

`KRRS/Inputs.lean` assumes the positive-surplus optimizer and cross-density properties
used from Kenyon–Radin–Ren–Sadun. The rest of `KRRS/` proves the two-sided analytic
extension in [Theorem 2.1][thm:krrs-analytic-extension], for regular graphs:

1. Express a bipodal graphon by its three densities and first-block measure.
2. Solve the edge constraint and then the subgraph-density constraint locally.
3. Factor the vanishing block-size terms out of the stationarity equations.
4. Prove that the resulting Jacobian is invertible and apply the analytic implicit
   function theorem.
5. Identify the new family with the assumed optimizer on a positive-surplus open set.
   The identity theorem extends that agreement across the connected rectangle.

`krrs_rectangle` gives the common parameter family. The public declarations
`kenyonRadinRenSadun`, `kenyonRadinRenSadunAnalytic`,
`kenyonRadinRenSadunStrip` and `kenyonRadinRenSadunUniform` expose different parts of it.
In particular, `Strip` states analyticity throughout the two-sided strip, while
`Uniform` includes the uniform linear block-size bound and states analyticity at the
boundary slice.

Both the current paper and Lean choose a neighbourhood of one fixed density.
Uniform estimates over a compact set are obtained later, in `LocalReduction/Main.lean`.

### Local reduction

`active_constraint` proves that an optimizer satisfies `t(H,W) = r^m`.
On the symmetry-breaking side, `edgeDensity_lt_broken` gives `e(W) < r`.
Boundary uniqueness and cut compactness then force optimizers to approach the constant
boundary graphon.

This localization places every optimizer in the KRR–S regime. At a fixed edge density,
minimizing relative entropy is equivalent to maximizing Shannon entropy.
`reduction_core_uniform` proves this reduction with one choice of constants over a
compact boundary subarc. Its consequences are the scalar minimization formula,
bipodality of every optimizer, and existence of a bipodal optimizer.

### Second variation

At a boundary point, the reduced excess cost is
`G_r(δ) = 𝓕_{pc(r),r}(r−δ) − J_{pc(r)}(r)`.

The lower bound uses the scalar supporting-line gap and generalized Hölder.
An explicit bipodal competitor gives the upper bound. Together they yield
`Cδ² ≤ G_r(δ) ≤ C'δ²`, without using the KRR–S axioms.

The KRR–S extension then gives a local analytic function `Gc(r,δ)` on both sides of
`δ = 0`, agreeing with `G_r(δ)` for positive `δ`.
`boundaryExcess_chart` proves its derivative identities and curvature bound;
`boundaryExcess_chart_full` also returns the bipodal parameters.
`boundaryExcess_taylor` gives a positive lower bound for `A_H` and the cubic Taylor
remainder uniformly on a compact set.

These are local analytic charts plus uniform estimates. Lean does not combine the
charts into the single analytic function on a neighbourhood of `K × {0}` stated in
[Theorem 5.4][thm:positive-second-variation]; see §7.

### Local optimizer structure

The identity
`𝓕_{p,r}(r−δ) − J_p(r) = G_r(δ) − λ(p,r)δ`
reduces the problem to a tilted scalar function.

On the replica-symmetric side, a supporting line and its equality cases force the
optimizer to be constant. On the symmetry-breaking side, positive curvature gives a
unique critical point `Δ(p,r)`. It determines the edge density and the optimal value:

```text
e(W)     = r − λ/A_H + O(λ²)
Φ_H(p,r) = J_p(r) − λ²/(2A_H) + O(λ³).
```

`local_structure_on_arc` combines parts (a)–(c) on a common window for a chosen boundary arc.
`bipodal_family` applies the implicit function theorem on the same chart used for
uniqueness, so the analytic critical point is the minimizer already constructed.
`symmetry_breaking_analytic` states analyticity of the six functions in part (d).

The block parameters are initially functions of `(ε,ϑ)`. Their dependence on `(p,r)`
is stated explicitly by composition with
`ε = r−Δ(p,r)` and `ϑ = r^m−ε^m`.
`bipodal_family` also proves `|c| ≤ LΔ` and `Δ ≤ Cλ`.
These bounds imply the block-size limit in the paper, but the public statement does
not explicitly assert that limit or `0 < c < 1/2`; see §7.

`parameter_asymptotics` proves the first-order block-size and density expansions
from Appendix D, with uniform quadratic error bounds where the paper states them.

### Theorem 6.1 and its introduction corollary

`LocalOptimizer/Main.lean` collects the result in `local_structure`, using
`pcGlobal`, `AHGlobal` and `lambdaGlobal` with no chosen boundary arc in its statement.
It proves `LocalOptimizerStructure H d r₀`, whose fields are:

- `coefficient`: positivity and analyticity of `AHGlobal` at every nonexceptional density;
- `window`: replica symmetry, bipodal uniqueness and uniform asymptotic bounds;
- `analyticFamily`: the analytic bipodal family, its boundary values and quantitative
  block-parameter bounds. Its window and the optimizer window can be intersected.

`AHGlobal` is defined by the limit of `2G_r(δ)/δ²`.
`AH_eq_AHGlobal` identifies it with each arc's coefficient, and
`analyticAt_AHGlobal_and_pos` supplies the coefficient field.

[Theorem 1.5][thm:nonexceptional-optimizers] is the direct corollary
[main_bipodal_optimizer](UpperTailOptimizers/LocalOptimizer/Global.lean#L14).
Its proof is `(local_structure ...).toNonexceptionalOptimizers`, retaining the
`coefficient` and `window` fields. It needs no additional coordinate conversion or
analyticity proof, so it is not listed as an independent result in the tables.

## 3. Section 7 — the singular endpoint

The **singular endpoint** is the boundary point `P_* = (p_*, r_*)` where the two
Lubetzky–Zhao contacts coalesce. Its density `r_* = (d−1)/d` is the **exceptional
density**, where the nonexceptional argument does not apply. The directory `SingularEndpoint/`
and namespace `UpperTailOptimizers.SingularEndpoint` refer specifically to this singular endpoint.
The singular endpoint construction instead starts with a rank-one bipodal graphon
`W_h = f_h ⊗ f_h`, where `f_h` takes the two values `u_h−h` and `u_h+h`.

### Family construction and cost gap

`FamilySystem.lean` rewrites the three scalar KKT equations in a form that remains
analytic at `h = 0`. The implicit function theorem gives the local family.
Symmetry and the block-balance equation determine its parity properties and block weight.
`exists_kktFamily` collects these results in an inhabited `KKTFamily` structure.

The expansion files compute the leading coefficients of the parameters and the cost gap.
`tendsto_cost_gap` proves
`(I_{p_h}(W_h) − J_{p_h}(r_h))/h⁴ → −d³/3`.
Consequently, `singular_endpoint_strict_improvement` gives a strict improvement over the constant
graphon for small positive `h`. `SingularEndpoint/ParityOrder.lean` then upgrades the remainders
to the paper's: every family parameter is analytic in `h` with a definite parity, so its Taylor
expansion proceeds in steps of two and the first omitted term is two orders down.
`rank_one_parameter_expansions` and `constant_graphon_comparison` are the results.

### Localization and comparison

The optimality proof has four parts:

1. **Localize a competitor.** The cost and density constraints force a competing graphon
   close to the constant graphon `W ≡ r_*` in `L⁴`.
2. **Construct a rank-one factor.** Write `W = f ⊗ f + E`, with the orthogonality and
   moment estimates needed for comparison.
3. **Compare distributions.** Estimate the auxiliary entropy functional for the
   distribution of `f`, using the first-variation gap and kernel interpolation.
4. **Control the residual.** Combine estimates on the central square, mixed rectangles
   and tail square to control `E`. Equality forces the two-atom family distribution
   and a vanishing residual.

For the second part, the paper uses a variational construction. Lean uses a normalized
contraction map on a complete subset of `L⁴`.
`localization_rankOne` assumes `L⁴` closeness directly; `singular_endpoint_localization` derives
it from the paper's cost and feasibility hypotheses and collects the required estimates.

`CdfTransport.lean` and `BipodalTransport.lean` construct the relabelling from an arbitrary
measurable block to the canonical interval, together with the quantile map that inverts it
almost everywhere in both directions. This completes uniqueness up to relabelling.

### Theorem 7.1 and its introduction corollary

`singular_endpoint_full` constructs one family `B` and a positive window `δ`, and proves
`SingularEndpointStructure H B δ`. Its fields collect the analytic parameter curve,
parameter and block limits, rank-one bipodality, nonconstancy, the exact density
constraint, optimality, uniqueness and uniform convergence. The `base_values` and
`cost_gap` fields add the values at `h = 0` and the cost expansion
`I_{p_h}(W_h) − J_{p_h}(r_h) = −d³h⁴/3 + O(h⁶)`, with the paper's remainder.

[Theorem 1.6][thm:endpoint-optimizers] is the direct corollary
[singular_endpoint_optimizers](UpperTailOptimizers/SingularEndpoint/IntroSingularEndpointOptimizers.lean#L15).
It calls `singular_endpoint_full` and keeps `toSingularEndpointOptimizers`, dropping
only `base_values` and `cost_gap`. It constructs no additional family and needs no
additional axioms. The elementary family lemmas live in `FamilyContinuity.lean`.

The additional inequality `p_h < pc(r_h)` is proved separately by
`singular_endpoint_symmetry_breaking` in `StrictImprovement.lean`. It is used by the
concrete graph examples, but is not a clause of either public theorem [D1].

## 4. Paper → Lean

### Numbered result index

This index lists the principal numbered results. Click a paper number to open its
statement, or a Lean name to open its declaration. Lean names omit the common
`UpperTailOptimizers.` prefix. The scope column records qualifications that matter
when comparing the statements; §7 gives the details. Theorems 1.5 and 1.6 are
direct corollaries of Theorems 6.1 and 7.1, so they have no separate rows.

| Paper result | Lean entry points | Scope or role |
|---|---|---|
| **[Theorem 1.3][thm:graphon-large-deviations]** — Graphon large deviations | — | Not formalised; probabilistic layer |
| **[Theorem 1.4][thm:lz-criterion]** — Lubetzky–Zhao criterion | Assumed criterion: [lubetzkyZhao](UpperTailOptimizers/Graphon/ExternalInputs.lean#L122) | Criterion assumed; uniqueness proved separately |
| **[Theorem 2.1][thm:krrs-analytic-extension]** — Two-sided KRR–S extension | Analytic parameter family: [krrs_rectangle](UpperTailOptimizers/KRRS/Main.lean#L111)<br>Uniform block-size bound: [kenyonRadinRenSadunUniform](UpperTailOptimizers/KRRS/Main.lean#L791) | Regular graphs; conclusions split across public forms |
| **[Theorem 3.1][thm:scalar-lz-boundary]** — Scalar Lubetzky–Zhao boundary | Boundary arc construction: [scalar_lz_boundary_arcs](UpperTailOptimizers/LZBoundary/Existence.lean#L3137)<br>Global boundary criterion: [lz_boundary_M2_global](UpperTailOptimizers/LZBoundary/Curve.lean#L167) | Arc construction and global criterion |
| **[Lemma 3.2][lem:convexity-defect]** — Convexity defect | Convexity classification: [convexity_defect](UpperTailOptimizers/LZBoundary/PhiDeriv.lean#L782) | Convexity and curvature threshold |
| **[Lemma 3.3][lem:contact-points]** — Contact points | Contact existence and uniqueness: [lz_boundary_contacts](UpperTailOptimizers/LZBoundary/Existence.lean#L719) | Existence and uniqueness of the contacts |
| **[Lemma 3.4][lem:contact-point-limits]** — Contact-point limits | Contact-point limits: [lz_boundary_endpoint_limits](UpperTailOptimizers/LZBoundary/Existence.lean#L823) | Limits at the ends of the contact curves |
| **[Lemma 4.1][lem:active-constraint]** — Active constraint | Active constraint: [active_constraint](UpperTailOptimizers/LocalReduction/Main.lean#L274) | Equality in the density constraint |
| **[Lemma 4.2][lem:edge-density-deficit]** — Strict edge-density deficit | Edge-density deficit: [edgeDensity_lt_broken](UpperTailOptimizers/LocalReduction/Main.lean#L93) | Edge density below the target |
| **[Lemma 4.3][lem:boundary-convergence]** — Boundary convergence | Cut convergence: [cutDist_tendsto_boundary](UpperTailOptimizers/LocalReduction/Main.lean#L242)<br>Edge-density convergence: [edgeDensity_tendsto_boundary](UpperTailOptimizers/LocalReduction/Main.lean#L219) | Cut and edge-density convergence |
| **[Lemma 4.4][lem:fixed-density-bipodality]** — Uniform localization and bipodality | Uniform reduction: [reduction_core_uniform](UpperTailOptimizers/LocalReduction/Main.lean#L594) | Localization and fixed-density optimizer |
| **[Corollary 4.5][cor:scalar-reduction]** — One-dimensional reduction | Scalar minimization: [scalar_reduction](UpperTailOptimizers/LocalReduction/Main.lean#L728)<br>Optimizer bipodality: [optimizer_bipodal](UpperTailOptimizers/LocalReduction/Main.lean#L752) | Scalar minimization and optimizer structure |
| **[Lemma 5.1][lem:scalar-quadratic-bound]** — Scalar quadratic lower bound | Scalar lower bound: [expectation_quadratic_lower](UpperTailOptimizers/Nondegeneracy/ScalarLower.lean#L34) | Scalar lower bound |
| **[Proposition 5.2][prop:graphon-quadratic-bound]** — Graphon quadratic lower bound | Graphon lower bound: [quadratic_lower_graphon](UpperTailOptimizers/Nondegeneracy/GraphonLower.lean#L29) | Lower bound for arbitrary graphons |
| **[Lemma 5.3][lem:bipodal-quadratic-bound]** — Bipodal quadratic upper bound | Bipodal upper bound: [quadratic_upper](UpperTailOptimizers/Nondegeneracy/QuadraticUpper.lean#L54) | Upper bound from a bipodal competitor |
| **[Theorem 5.4][thm:positive-second-variation]** — Positive second variation | Local analytic extension: [boundaryExcess_chart](UpperTailOptimizers/Nondegeneracy/AnalyticExcess.lean#L631)<br>Uniform Taylor bounds: [boundaryExcess_taylor](UpperTailOptimizers/Nondegeneracy/AnalyticExcess.lean#L741) | Local charts and uniform Taylor bounds; see §7 |
| **[Theorem 6.1][thm:local-optimizer-structure]** — Local optimizer structure (includes Theorem 1.5) | Full local result: [local_structure](UpperTailOptimizers/LocalOptimizer/Main.lean#L310) | Global coefficient, optimizer window and analytic family; see §7 |
| **[Theorem 7.1][thm:endpoint-optimality]** — Singular endpoint optimizers (includes Theorem 1.6) | Family, optimality and asymptotics: [SingularEndpoint.singular_endpoint_full](UpperTailOptimizers/SingularEndpoint/TerminalUnique.lean#L215) | Continuation estimates not collected [D8] |
| **[Lemma 7.2][lem:stationary-rank-one-bipodality]** — Stationary rank-one bipodality | Two-valued factor: [SingularEndpoint.exists_two_values](UpperTailOptimizers/SingularEndpoint/EssRange.lean#L105) | Starts from the scalar KKT equation [D9] |
| **[Lemma 7.3][lem:rank-one-kkt-family]** — Analytic rank-one KKT family | KKT family construction: [SingularEndpoint.exists_kktFamily](UpperTailOptimizers/SingularEndpoint/FamilyBuild.lean#L42) | Family construction; scalar exhaustiveness [D2], [D9] |
| **[Lemma 7.4][lem:rank-one-parameter-expansions]** — Rank-one parameter expansions | All four expansions: [SingularEndpoint.rank_one_parameter_expansions](UpperTailOptimizers/SingularEndpoint/ParameterRemainders.lean#L196) | Further entries below |
| **[Lemma 7.5][lem:constant-graphon-comparison]** — Comparison with the constant graphon | Cost gap: [SingularEndpoint.constant_graphon_comparison](UpperTailOptimizers/SingularEndpoint/CostRemainder.lean#L124)<br>Strict cost improvement: [SingularEndpoint.singular_endpoint_strict_improvement](UpperTailOptimizers/SingularEndpoint/StrictImprovement.lean#L91) | Cost gap, its remainder and its sign |
| **[Lemma 7.6][lem:localization-rank-one]** — Localization and rank-one reduction | Competitor localization: [SingularEndpoint.singular_endpoint_localization](UpperTailOptimizers/SingularEndpoint/LocalizationMain.lean#L131) | Localization from cost and feasibility [D3] |
| **[Lemma 7.7][lem:continuation-kernel-bounds]** — Continuation and kernel bounds | Continuity modulus: [SingularEndpoint.exists_JpTilde_modulus](UpperTailOptimizers/SingularEndpoint/JpTilde.lean#L402)<br>Uniform entropy bound: [SingularEndpoint.KKTFamily.exists_abs_JpTildeH_le](UpperTailOptimizers/SingularEndpoint/DistributionQuant.lean#L1173) | Separate continuity and boundedness estimates [D10] |
| **[Lemma 7.8][lem:first-variation-bound]** — First-variation lower bound | Central lower bound: [SingularEndpoint.KKTFamily.exists_firstVariation_lower](UpperTailOptimizers/SingularEndpoint/FirstVariationBound.lean#L453)<br>Tail lower bound: [SingularEndpoint.KKTFamily.exists_firstVariation_upperGap](UpperTailOptimizers/SingularEndpoint/PsiTilde.lean#L363) | Central and tail bounds |
| **[Lemma 7.9][lem:central-kernel-bound]** — Central kernel bound | Central integral bound: [SingularEndpoint.KKTFamily.centralQuad_lower](UpperTailOptimizers/SingularEndpoint/DistributionQuant.lean#L1037) | Central integral bound; interpolation estimates [D6] |
| **[Lemma 7.10][lem:auxiliary-lagrangian-bound]** — Auxiliary Lagrangian bound | Distribution comparison: [SingularEndpoint.KKTFamily.exists_distributionGap_refined_window_forall](UpperTailOptimizers/SingularEndpoint/DistributionFinal.lean#L94) | Linear moment formulation [D4], [D5] |
| **[Lemma 7.11][lem:graphon-lagrangian-bound]** — Full-graphon Lagrangian bound | Graphon comparison: [SingularEndpoint.exists_comparison_master](UpperTailOptimizers/SingularEndpoint/GraphonComparisonMaster.lean#L497)<br>Graph-constraint comparison: [SingularEndpoint.exists_singular_endpoint_comparison_graph](UpperTailOptimizers/SingularEndpoint/GraphonComparisonMaster.lean#L898) | Comparison and graph-constraint conversion [D4], [D5] |
| **[Theorem A.1][thm:krrs-bipodality]** — KRR–S bipodal entropy maximizer | Assumed bipodality: [krrs_thm11](UpperTailOptimizers/KRRS/Inputs.lean#L220) | External input: KRR–S Theorem 1.1 |
| **[Theorem A.2][thm:krrs-cross-density]** — KRR–S cross-density selector | Assumed cross-density properties: [krrs_thm33](UpperTailOptimizers/KRRS/Inputs.lean#L88) | External input: KRR–S Theorem 3.3 and maximizer characterization |
| **[Lemma B.1][lem:two-point-convex-minorant]** — Two-point convex minorant | Two-point representation: [lce_isLeast_twoPoint](UpperTailOptimizers/LZBoundary/ConvexMinorant.lean#L1056) | Attained two-point representation |
| **[Remark D.1][rmk:bipodal-parameter-expansions]** — Bipodal parameter asymptotics | Parameter expansions: [parameter_asymptotics](UpperTailOptimizers/LocalOptimizer/ParameterAsymptotics.lean#L479) | Uniform first-order block parameter expansions |

The following tables give the definitions, individual theorem clauses and supporting
calculations. The paper's informal Theorems 1.1–1.2 are represented here by its precise
statements, [Theorem 1.4][thm:lz-criterion]–[Theorem 1.6][thm:endpoint-optimizers].


### Definitions and domains

| Lean objects | Mathematical meaning | Representation and domain qualifications |
|---|---|---|
| `Graphon`, `unitμ`, `gμ` (`Graphon/Basic.lean`) | A symmetric measurable kernel with values in `[0,1]`, integrated over the unit interval or its square. | The kernel is a total function on `ℝ²`, with pointwise symmetry and bounds. Optimizer equalities are a.e.; there is no quotient type. |
| `Graphon.tDensity` (`Graphon/Basic.lean`) | The product of one kernel value per unordered edge, integrated over all vertex coordinates. | `H` is a finite simple graph. An empty edge product is 1, so the main theorems explicitly require a nonempty graph. |
| `Jp`, `Graphon.Ip`, `Graphon.entropy` (`LZBoundary/Jp.lean`, `Graphon/Basic.lean`) | Relative entropy `J_p`, its graphon integral, and Shannon entropy with the factor `1/2`. | `Ip` has no factor `1/2`; `Ip_eq_entropy` therefore has coefficient `−2` on the entropy. |
| `Feasible`, `phiVar` (`Graphon/ExternalInputs.lean`) | The inequality `r^m ≤ t(H,W)` and the infimum of `I_p` over all feasible graphons. | `phiVar` uses real-valued `sInf`; intended uses require a nonempty feasible set and a lower bound. |
| `entropyEnvelope`, `reducedObjective` (`LocalReduction/Main.lean`) | The entropy supremum at the equalities `e(W)=ε`, `t(H,W)=τ`, then the scalar entropy identity. | The empty constraint set has Mathlib's real `sSup` value 0, rather than the paper's `−∞`. The KRR–S family supplies witnesses on the relevant strip. |
| `IsBipodal` (`Graphon/Bipodal.lean`) | A.e. agreement with a three-value kernel on a measurable two-block partition. | The block is a measurable subset of `ℝ`; only its intersection with `[0,1]` matters. Degenerate blocks and constant graphons are allowed. Nonconstancy is a separate theorem clause. |
| `cutDist` (`Graphon/CutMetric.lean`) | An infimum of cut norms over relabellings, as in the paper. | Metric and quotient equivalences are not proved. |
| `pcGlobal`, `AHGlobal`, `lambdaGlobal` (`LZBoundary/Curve.lean`, `LocalOptimizer/Main.lean`) | The scalar boundary, the chart-independent second-variation coefficient, and the difference of log odds. | `AHGlobal` is defined by `limUnder`; positivity and analyticity away from `r_*` are included in `local_structure`. |
| [NonexceptionalOptimizers](UpperTailOptimizers/LocalOptimizer/Main.lean#L232), [LocalOptimizerStructure](UpperTailOptimizers/LocalOptimizer/Main.lean#L262) | Proposition structures for the global optimizer conclusions. The latter adds the analytic family to the former's coefficient and optimizer-window fields. | `local_structure` proves the larger structure; Theorem 1.5 projects its parent. |
| [SingularEndpointOptimizers](UpperTailOptimizers/SingularEndpoint/TerminalUnique.lean#L115), [SingularEndpointStructure](UpperTailOptimizers/SingularEndpoint/TerminalUnique.lean#L203) | Proposition structures for one family and one positive optimality window. The latter adds base values and the leading cost gap. | `singular_endpoint_full` constructs a family satisfying the larger structure; Theorem 1.6 projects its parent. |
| `KKTFamily` (`SingularEndpoint/Family.lean`) | An analytic family with base values, symmetry, interiority, three scalar KKT equations and block balance. | `exists_kktFamily` supplies a witness. First-variation stationarity and its equivalence to these scalar conditions are not formalised [D9]. |

### Namespaces and file paths

Most declarations below use `UpperTailOptimizers.<name>`.
Singular endpoint declarations use `UpperTailOptimizers.SingularEndpoint.<name>`; names marked † use
`UpperTailOptimizers.SingularEndpoint.KKTFamily.<name>`. Names beginning with `FactorDecomp.`
refer to declarations inside `UpperTailOptimizers.SingularEndpoint.FactorDecomp`.
The examples in `LocalOptimizer/Instances.lean` use `UpperTailOptimizers.LocalOptimizer.Instances.<name>`.

Each declaration name in the result tables links to its own source line. The File
column lists the containing modules, with paths relative to `UpperTailOptimizers/`.
These tables list the main declarations and selected supporting results. They are not
an inventory of every equation in the paper.

### Sections 1–3 and scalar geometry

| Paper result or definition | Lean declarations | File and scope |
|---|---|---|
| **[Theorem 1.3][thm:graphon-large-deviations]** — Graphon large deviations and the probabilistic conclusions | — | Outside the formalisation |
| **[Theorem 1.4][thm:lz-criterion]** — Lubetzky–Zhao criterion | [lubetzkyZhao](UpperTailOptimizers/Graphon/ExternalInputs.lean#L122) | [Graphon/ExternalInputs.lean](UpperTailOptimizers/Graphon/ExternalInputs.lean); the criterion is assumed, without uniqueness |
| Applications to `K₃` and `K₄` | [K3_has_nonconstant_optimizer](UpperTailOptimizers/LocalOptimizer/Instances.lean#L77), [K4_has_nonconstant_optimizer](UpperTailOptimizers/LocalOptimizer/Instances.lean#L106), [K3_main_bipodal_optimizer](UpperTailOptimizers/LocalOptimizer/Instances.lean#L137) | [LocalOptimizer/Instances.lean](UpperTailOptimizers/LocalOptimizer/Instances.lean) |
| [Eq. (5)][eq:relative-entropy-identity] | [Graphon.Ip_eq_entropy](UpperTailOptimizers/Graphon/Basic.lean#L264) | [Graphon/Basic.lean](UpperTailOptimizers/Graphon/Basic.lean) |
| [Eq. (4)][eq:generalized-holder] | [generalized_holder](UpperTailOptimizers/Graphon/ExternalInputs.lean#L70), [holder_moment](UpperTailOptimizers/Graphon/ExternalInputs.lean#L77) | [Graphon/ExternalInputs.lean](UpperTailOptimizers/Graphon/ExternalInputs.lean); the first is an axiom, the second a consequence |
| Identity `e(W) = t(K₂,W)` | [tDensity_top_two](UpperTailOptimizers/Graphon/HomDensity.lean#L228) | [Graphon/HomDensity.lean](UpperTailOptimizers/Graphon/HomDensity.lean) |
| **[Lemma B.1][lem:two-point-convex-minorant]** — Two-point convex minorant (Appendix B) | [twoPointVals](UpperTailOptimizers/LZBoundary/ConvexMinorant.lean#L37), [lce_isLeast_twoPoint](UpperTailOptimizers/LZBoundary/ConvexMinorant.lean#L1056), [lce_eq_sInf_twoPoint](UpperTailOptimizers/LZBoundary/ConvexMinorant.lean#L1088) | [LZBoundary/ConvexMinorant.lean](UpperTailOptimizers/LZBoundary/ConvexMinorant.lean) |
| **[Lemma 3.2][lem:convexity-defect]** — Convexity defect | [convexity_defect](UpperTailOptimizers/LZBoundary/PhiDeriv.lean#L782), [convexOn_phi_of_pStar_le](UpperTailOptimizers/LZBoundary/PhiDeriv.lean#L591), [strictConvexOn_phi_of_pStar_le](UpperTailOptimizers/LZBoundary/PhiAsymptotics.lean#L449) | [LZBoundary/PhiDeriv.lean](UpperTailOptimizers/LZBoundary/PhiDeriv.lean); the zeros are given existentially |
| **[Lemma 3.3][lem:contact-points]** — Contact points | [lz_boundary_contacts](UpperTailOptimizers/LZBoundary/Existence.lean#L719) | [LZBoundary/Existence.lean](UpperTailOptimizers/LZBoundary/Existence.lean) |
| **[Lemma 3.4][lem:contact-point-limits]** — Contact-point limits | [lz_boundary_endpoint_limits](UpperTailOptimizers/LZBoundary/Existence.lean#L823) | [LZBoundary/Existence.lean](UpperTailOptimizers/LZBoundary/Existence.lean) |
| Analytic contact functions | [exists_globalContacts](UpperTailOptimizers/LZBoundary/Existence.lean#L1213) | [LZBoundary/Existence.lean](UpperTailOptimizers/LZBoundary/Existence.lean) |
| **[Theorem 3.1][thm:scalar-lz-boundary]** — Scalar Lubetzky–Zhao boundary, arc formulation | [scalar_lz_boundary_arcs](UpperTailOptimizers/LZBoundary/Existence.lean#L3137), [LZBoundaryArc](UpperTailOptimizers/LZBoundary/Arc.lean#L68) | [LZBoundary/Existence.lean](UpperTailOptimizers/LZBoundary/Existence.lean), [LZBoundary/Arc.lean](UpperTailOptimizers/LZBoundary/Arc.lean) |
| Global boundary functions and agreement with the arcs | [pcGlobal](UpperTailOptimizers/LZBoundary/Curve.lean#L140), [smGlobal](UpperTailOptimizers/LZBoundary/Curve.lean#L243), [pcGlobal_eq_pc](UpperTailOptimizers/LZBoundary/Curve.lean#L146) | [LZBoundary/Curve.lean](UpperTailOptimizers/LZBoundary/Curve.lean) |
| Boundary values at the exceptional density | [pcGlobal_rStar](UpperTailOptimizers/LZBoundary/Curve.lean#L155), [smGlobal_rStar](UpperTailOptimizers/LZBoundary/Curve.lean#L323), [contactSet_pStar_rStar](UpperTailOptimizers/LZBoundary/Curve.lean#L256) | [LZBoundary/Curve.lean](UpperTailOptimizers/LZBoundary/Curve.lean) |
| Continuity and analyticity of the boundary functions | [continuousOn_pcGlobal](UpperTailOptimizers/LZBoundary/Curve.lean#L398), [analyticAt_pcGlobal](UpperTailOptimizers/LZBoundary/Curve.lean#L390), [continuousOn_smGlobal](UpperTailOptimizers/LZBoundary/Curve.lean#L702), [analyticAt_smGlobal](UpperTailOptimizers/LZBoundary/Curve.lean#L694) | [LZBoundary/Curve.lean](UpperTailOptimizers/LZBoundary/Curve.lean); analyticity is away from `r_*` |
| Condition (M2), including the exceptional point | [lz_boundary_M2_global](UpperTailOptimizers/LZBoundary/Curve.lean#L167) | [LZBoundary/Curve.lean](UpperTailOptimizers/LZBoundary/Curve.lean) |
| Supporting-line contact set and uniqueness of arc data | [LZBoundaryArc.contactSet_eq](UpperTailOptimizers/LZBoundary/Curve.lean#L207), [LZBoundaryArc.pc_unique](UpperTailOptimizers/LZBoundary/Curve.lean#L56), [LZBoundaryArc.sm_unique](UpperTailOptimizers/LZBoundary/Curve.lean#L66) | [LZBoundary/Curve.lean](UpperTailOptimizers/LZBoundary/Curve.lean) |
| Boundary optimizer uniqueness, used in the local reduction | [boundary_uniqueness](UpperTailOptimizers/LZBoundary/Uniqueness.lean#L40) | [LZBoundary/Uniqueness.lean](UpperTailOptimizers/LZBoundary/Uniqueness.lean) |
| Supporting line and no flat tie above `p_*`, where `φ_{p,d}` is strictly convex | [supportingLine_strict_of_pStar_le](UpperTailOptimizers/LZBoundary/Existence.lean#L3088), [orientation_of_pStar_le](UpperTailOptimizers/LZBoundary/Existence.lean#L3108), [noFlatTie_of_pStar_le](UpperTailOptimizers/LZBoundary/Existence.lean#L3119) | [LZBoundary/Existence.lean](UpperTailOptimizers/LZBoundary/Existence.lean) |
| Regular-graph counting identities | [regular_handshake](UpperTailOptimizers/Graphon/RegularGraph.lean#L32), [degree_le_card_edges](UpperTailOptimizers/Graphon/RegularGraph.lean#L41), [two_le_card_edgeFinset](UpperTailOptimizers/Graphon/RegularGraph.lean#L57), [nonempty_of_edge](UpperTailOptimizers/Graphon/RegularGraph.lean#L25) | [Graphon/RegularGraph.lean](UpperTailOptimizers/Graphon/RegularGraph.lean) |

The field-to-(M1)–(M5) correspondence is explained in `LZBoundary/Arc.lean`.
The additional `noFlatTie` field is proved during arc construction and used for
replica-symmetric uniqueness below `p_*`; above `p_*` the same conclusion follows from strict
convexity of `φ_{p,d}` on `[0,1]`, through `noFlatTie_of_pStar_le`.

### Section 4 — local reduction

| Paper result | Lean declarations | File |
|---|---|---|
| **[Lemma 4.1][lem:active-constraint]** — Active constraint | [active_constraint](UpperTailOptimizers/LocalReduction/Main.lean#L274) | [LocalReduction/Main.lean](UpperTailOptimizers/LocalReduction/Main.lean) |
| **[Lemma 4.2][lem:edge-density-deficit]** — Strict edge-density deficit | [edgeDensity_lt_of_no_support](UpperTailOptimizers/LocalReduction/Main.lean#L66), [edgeDensity_lt_broken](UpperTailOptimizers/LocalReduction/Main.lean#L93) | [LocalReduction/Main.lean](UpperTailOptimizers/LocalReduction/Main.lean) |
| **[Lemma 4.3][lem:boundary-convergence]** — Boundary convergence | [edgeDensity_tendsto_boundary](UpperTailOptimizers/LocalReduction/Main.lean#L219), [cutDist_tendsto_boundary](UpperTailOptimizers/LocalReduction/Main.lean#L242) | [LocalReduction/Main.lean](UpperTailOptimizers/LocalReduction/Main.lean) |
| Fixed-density entropy and reduced objective, [Eq. (9)][eq:fixed-density-entropy], [Eq. (10)][eq:reduced-objective] | [entropyEnvelope](UpperTailOptimizers/LocalReduction/Main.lean#L420), [reducedObjective](UpperTailOptimizers/LocalReduction/Main.lean#L427) | [LocalReduction/Main.lean](UpperTailOptimizers/LocalReduction/Main.lean) |
| **[Lemma 4.4][lem:fixed-density-bipodality]** — Uniform localization and bipodality: localization and a uniform optimizer strip | [uniform_localization](UpperTailOptimizers/LocalReduction/Main.lean#L354), [krrs_strip](UpperTailOptimizers/LocalReduction/Main.lean#L475) | [LocalReduction/Main.lean](UpperTailOptimizers/LocalReduction/Main.lean) |
| **[Lemma 4.4][lem:fixed-density-bipodality]** — Uniform localization and bipodality, including [Eq. (11)][eq:reduced-objective-attainment] | [reduction_core_uniform](UpperTailOptimizers/LocalReduction/Main.lean#L594) | [LocalReduction/Main.lean](UpperTailOptimizers/LocalReduction/Main.lean) |
| **[Corollary 4.5][cor:scalar-reduction]** — One-dimensional reduction, including [Eq. (13)][eq:edge-density-minimization] | [scalar_reduction](UpperTailOptimizers/LocalReduction/Main.lean#L728), [optimizer_bipodal](UpperTailOptimizers/LocalReduction/Main.lean#L752), [exists_bipodal_optimizer](UpperTailOptimizers/LocalReduction/Main.lean#L772) | [LocalReduction/Main.lean](UpperTailOptimizers/LocalReduction/Main.lean) |
| Attainment used in the reduction | [feasible_attains](UpperTailOptimizers/Graphon/Attainment.lean#L36) | [Graphon/Attainment.lean](UpperTailOptimizers/Graphon/Attainment.lean) |

`reduction_core_uniform` preserves the paper's order of quantifiers: one upper radius,
then any smaller positive radius, then a parameter window valid for every density in
the compact subarc.

### Section 5 — positive second variation

| Paper result or calculation | Lean declarations | File and scope |
|---|---|---|
| [Eq. (6)][eq:contact-quadratic-separation], expressed in the `u` coordinate | [quadSep_dist](UpperTailOptimizers/Nondegeneracy/ArcBounds.lean#L91), [arc_uniform_bounds](UpperTailOptimizers/Nondegeneracy/ArcBounds.lean#L44) | [Nondegeneracy/ArcBounds.lean](UpperTailOptimizers/Nondegeneracy/ArcBounds.lean) |
| **[Lemma 5.1][lem:scalar-quadratic-bound]** — Scalar quadratic lower bound | [expectation_quadratic_lower](UpperTailOptimizers/Nondegeneracy/ScalarLower.lean#L34) | [Nondegeneracy/ScalarLower.lean](UpperTailOptimizers/Nondegeneracy/ScalarLower.lean) |
| **[Proposition 5.2][prop:graphon-quadratic-bound]** — Graphon quadratic lower bound | [quadratic_lower_graphon](UpperTailOptimizers/Nondegeneracy/GraphonLower.lean#L29) | [Nondegeneracy/GraphonLower.lean](UpperTailOptimizers/Nondegeneracy/GraphonLower.lean) |
| Bipodal homomorphism-density polynomial and expansion | [tBip_eq_tDensity](UpperTailOptimizers/Nondegeneracy/TDensityExpansion.lean#L204), [tBip_expansion](UpperTailOptimizers/Nondegeneracy/TDensityExpansion.lean#L241), [tBipRem_le](UpperTailOptimizers/Nondegeneracy/TDensityExpansion.lean#L327) | [Nondegeneracy/TDensityExpansion.lean](UpperTailOptimizers/Nondegeneracy/TDensityExpansion.lean) |
| **[Lemma 5.3][lem:bipodal-quadratic-bound]** — Bipodal quadratic upper bound | [quadratic_upper](UpperTailOptimizers/Nondegeneracy/QuadraticUpper.lean#L54) | [Nondegeneracy/QuadraticUpper.lean](UpperTailOptimizers/Nondegeneracy/QuadraticUpper.lean) |
| Quadratic bounds for the boundary excess | [boundaryExcess_quadratic](UpperTailOptimizers/Nondegeneracy/BoundaryExcess.lean#L62), [boundaryExcess_pos](UpperTailOptimizers/Nondegeneracy/BoundaryExcess.lean#L107) | [Nondegeneracy/BoundaryExcess.lean](UpperTailOptimizers/Nondegeneracy/BoundaryExcess.lean) |
| **[Theorem 5.4][thm:positive-second-variation]** — Positive second variation: local extension, derivative identities and curvature bound | [boundaryExcess_chart](UpperTailOptimizers/Nondegeneracy/AnalyticExcess.lean#L631), [boundaryExcess_chart_full](UpperTailOptimizers/Nondegeneracy/AnalyticExcess.lean#L80) | [Nondegeneracy/AnalyticExcess.lean](UpperTailOptimizers/Nondegeneracy/AnalyticExcess.lean); local around one density, not a single extension over all of `K` |
| **[Theorem 5.4][thm:positive-second-variation]** — Positive second variation: uniform Taylor remainder and positive coefficient | [AH](UpperTailOptimizers/Nondegeneracy/AnalyticExcess.lean#L53), [boundaryExcess_taylor](UpperTailOptimizers/Nondegeneracy/AnalyticExcess.lean#L741) | [Nondegeneracy/AnalyticExcess.lean](UpperTailOptimizers/Nondegeneracy/AnalyticExcess.lean); uniform over compact `K` |
| Bounds on the block parameters near the boundary | [krrs_parameter_lipschitz](UpperTailOptimizers/Nondegeneracy/AnalyticExcess.lean#L662) | [Nondegeneracy/AnalyticExcess.lean](UpperTailOptimizers/Nondegeneracy/AnalyticExcess.lean) |
| Partial derivative in the deficit variable | [dDelta](UpperTailOptimizers/Nondegeneracy/AnalyticTools.lean#L50) | [Nondegeneracy/AnalyticTools.lean](UpperTailOptimizers/Nondegeneracy/AnalyticTools.lean) |

The equality `boundaryExcess = Gc` is stated only for positive deficit.
The derivative identities at zero concern the analytic extension `Gc`, not an
unqualified evaluation of the entropy envelope outside its feasible domain.

### Section 6 and Appendix D — optimizer structure and parameters

| Paper result or calculation | Lean declarations | File and scope |
|---|---|---|
| Log-odds displacement and deficit rate | [lambdaDisp](UpperTailOptimizers/LocalOptimizer/Basic.lean#L52), [lambdaDisp_pos](UpperTailOptimizers/LocalOptimizer/Basic.lean#L60), [lambdaDisp_nonpos](UpperTailOptimizers/LocalOptimizer/Basic.lean#L68), [Dd](UpperTailOptimizers/LocalOptimizer/Basic.lean#L84), [Dd_pos](UpperTailOptimizers/LocalOptimizer/Basic.lean#L96) | [LocalOptimizer/Basic.lean](UpperTailOptimizers/LocalOptimizer/Basic.lean) |
| Shift to the tilted boundary excess | [reducedObjective_sub_Jp_eq_boundaryExcess](UpperTailOptimizers/LocalOptimizer/Basic.lean#L129) | [LocalOptimizer/Basic.lean](UpperTailOptimizers/LocalOptimizer/Basic.lean) |
| **[Theorem 6.1(a)][thm:local-optimizer-structure]** — Local optimizer structure | [replica_symmetric_unique](UpperTailOptimizers/LocalOptimizer/ReplicaSymmetric.lean#L163), in global coordinates [replica_symmetric_unique_global](UpperTailOptimizers/LocalOptimizer/Main.lean#L149) | [LocalOptimizer/ReplicaSymmetric.lean](UpperTailOptimizers/LocalOptimizer/ReplicaSymmetric.lean); the full range `pc(r) ≤ p < r` |
| Unique minimizer of the tilted scalar function | [tilted_critical_point](UpperTailOptimizers/LocalOptimizer/ScalarCritical.lean#L70) | [LocalOptimizer/ScalarCritical.lean](UpperTailOptimizers/LocalOptimizer/ScalarCritical.lean) |
| **[Theorem 6.1(b)–(c)][thm:local-optimizer-structure]** — Symmetry breaking and the expansions in [Eq. (28)][eq:optimizer-edge-expansion] and [Eq. (29)][eq:optimal-value-expansion] | [symmetry_breaking_core](UpperTailOptimizers/LocalOptimizer/SymmetryBreaking.lean#L186), [symmetry_breaking_side](UpperTailOptimizers/LocalOptimizer/SymmetryBreaking.lean#L470) | [LocalOptimizer/SymmetryBreaking.lean](UpperTailOptimizers/LocalOptimizer/SymmetryBreaking.lean) |
| **[Theorem 6.1][thm:local-optimizer-structure]** — Assembled global result | [local_structure](UpperTailOptimizers/LocalOptimizer/Main.lean#L310), [LocalOptimizerStructure](UpperTailOptimizers/LocalOptimizer/Main.lean#L262) | [LocalOptimizer/Main.lean](UpperTailOptimizers/LocalOptimizer/Main.lean); Theorem 1.5 is a projection |
| **[Theorem 6.1(a)–(c)][thm:local-optimizer-structure]** — Optimizer structure on a common parameter window | [local_structure_on_arc](UpperTailOptimizers/LocalOptimizer/Main.lean#L73), [arc_gap_bounds](UpperTailOptimizers/LocalOptimizer/Main.lean#L32) | [LocalOptimizer/Main.lean](UpperTailOptimizers/LocalOptimizer/Main.lean) |
| Analytic critical point | [analytic_critical_family_of_chart](UpperTailOptimizers/LocalOptimizer/Analytic.lean#L98), [exists_analytic_critical_family](UpperTailOptimizers/LocalOptimizer/Analytic.lean#L182) | [LocalOptimizer/Analytic.lean](UpperTailOptimizers/LocalOptimizer/Analytic.lean) |
| **[Theorem 6.1(d)][thm:local-optimizer-structure]** — Local optimizer structure: analyticity of the value, edge density and four block parameters | [symmetry_breaking_analytic](UpperTailOptimizers/LocalOptimizer/Analytic.lean#L583), [bipodal_family](UpperTailOptimizers/LocalOptimizer/Analytic.lean#L243) | [LocalOptimizer/Analytic.lean](UpperTailOptimizers/LocalOptimizer/Analytic.lean); the strict smaller-block convention and block-size limit are not explicit conclusions |
| Constraint linearizations and their elimination | [krrs_edge_linearization](UpperTailOptimizers/LocalOptimizer/ParameterAsymptotics.lean#L84), [krrs_H_linearization](UpperTailOptimizers/LocalOptimizer/ParameterAsymptotics.lean#L137), [krrs_eliminate](UpperTailOptimizers/LocalOptimizer/ParameterAsymptotics.lean#L253), [exists_Dd_floor](UpperTailOptimizers/LocalOptimizer/ParameterAsymptotics.lean#L328) | [LocalOptimizer/ParameterAsymptotics.lean](UpperTailOptimizers/LocalOptimizer/ParameterAsymptotics.lean) |
| **[Remark D.1][rmk:bipodal-parameter-expansions]** — Bipodal parameter asymptotics, [Eq. (104)][eq:optimizer-block-size], [Eq. (105)][eq:optimizer-block-density] | [parameter_asymptotics](UpperTailOptimizers/LocalOptimizer/ParameterAsymptotics.lean#L479) | [LocalOptimizer/ParameterAsymptotics.lean](UpperTailOptimizers/LocalOptimizer/ParameterAsymptotics.lean) |
| Global coefficient and displacement | [AHGlobal](UpperTailOptimizers/LocalOptimizer/Main.lean#L169), [AH_eq_AHGlobal](UpperTailOptimizers/LocalOptimizer/Main.lean#L177), [lambdaGlobal](UpperTailOptimizers/LocalOptimizer/Main.lean#L184), [lambdaDisp_eq_lambdaGlobal](UpperTailOptimizers/LocalOptimizer/Main.lean#L187) | [LocalOptimizer/Main.lean](UpperTailOptimizers/LocalOptimizer/Main.lean) |

### Appendix A — the KRR–S analytic extension

All graph-dependent results here require regularity. [Theorem A.1][thm:krrs-bipodality] and
[Theorem A.2][thm:krrs-cross-density] restate KRR–S Theorems 1.1 and 3.3, respectively.
The Lean names `krrs_thm11` and `krrs_thm33` retain the external source's numbering.
The two input axioms and their interpretation are explained in §6.

| Paper result or proof step | Lean declarations | File |
|---|---|---|
| **[Theorem A.2][thm:krrs-cross-density]** — KRR–S cross-density selector and the following maximizer characterization | [KRRSZeta](UpperTailOptimizers/KRRS/Inputs.lean#L69), [krrs_thm33](UpperTailOptimizers/KRRS/Inputs.lean#L88) | [KRRS/Inputs.lean](UpperTailOptimizers/KRRS/Inputs.lean) |
| **[Theorem A.1][thm:krrs-bipodality]** — KRR–S bipodal entropy maximizer | [KRRSOptimizer](UpperTailOptimizers/KRRS/Inputs.lean#L158), [krrs_thm11](UpperTailOptimizers/KRRS/Inputs.lean#L220) | [KRRS/Inputs.lean](UpperTailOptimizers/KRRS/Inputs.lean) |
| [Eq. (94)][eq:krrs-uniform-domain] | [exists_uniform_strip](UpperTailOptimizers/KRRS/Inputs.lean#L238) | [KRRS/Inputs.lean](UpperTailOptimizers/KRRS/Inputs.lean) |
| Bipodal parameters, densities and entropy | [Theta](UpperTailOptimizers/KRRS/Chart.lean#L54), [bipEdge](UpperTailOptimizers/KRRS/Chart.lean#L57), [bipTd](UpperTailOptimizers/KRRS/Chart.lean#L62), [bipEnt](UpperTailOptimizers/KRRS/Chart.lean#L66), [bipG](UpperTailOptimizers/KRRS/Chart.lean#L128), [bipodal_transfer](UpperTailOptimizers/KRRS/Chart.lean#L223) | [KRRS/Chart.lean](UpperTailOptimizers/KRRS/Chart.lean) |
| Entropy and moment remainders; edge constraint | [Nfun](UpperTailOptimizers/KRRS/Reduced.lean#L91), [Dfun](UpperTailOptimizers/KRRS/Reduced.lean#L94), [psiD](UpperTailOptimizers/KRRS/Reduced.lean#L98), [Qmap](UpperTailOptimizers/KRRS/Reduced.lean#L265), [That](UpperTailOptimizers/KRRS/Reduced.lean#L312), [Shat](UpperTailOptimizers/KRRS/Reduced.lean#L316) | [KRRS/Reduced.lean](UpperTailOptimizers/KRRS/Reduced.lean) |
| [Eq. (66)][eq:krrs-scalar-nondegeneracy] | [Wr](UpperTailOptimizers/KRRS/PsiNondeg.lean#L201), [dWr](UpperTailOptimizers/KRRS/PsiNondeg.lean#L204), [krrs_scalar_nondegenerate](UpperTailOptimizers/KRRS/PsiNondeg.lean#L239) | [KRRS/PsiNondeg.lean](UpperTailOptimizers/KRRS/PsiNondeg.lean) |
| Entropy derivatives, including [Eq. (75)][eq:krrs-entropy-derivative] | [hasDerivAt_Shat_a](UpperTailOptimizers/KRRS/SCalc.lean#L71), [hasDerivAt_Shat_b](UpperTailOptimizers/KRRS/SCalc.lean#L96), [hasDerivAt_Shat_c_zero](UpperTailOptimizers/KRRS/SCalc.lean#L124) | [KRRS/SCalc.lean](UpperTailOptimizers/KRRS/SCalc.lean) |
| Density expansion and derivatives | [tBip_factored](UpperTailOptimizers/KRRS/TCalc.lean#L89), [Afun_pos](UpperTailOptimizers/KRRS/TCalc.lean#L110), [hasDerivAt_That_c_zero](UpperTailOptimizers/KRRS/TCalc.lean#L126), [Rda_zero_indep_a](UpperTailOptimizers/KRRS/TCalcAB.lean#L241), [Rdb](UpperTailOptimizers/KRRS/TCalcAB.lean#L265) | [KRRS/TCalc.lean](UpperTailOptimizers/KRRS/TCalc.lean), [KRRS/TCalcAB.lean](UpperTailOptimizers/KRRS/TCalcAB.lean) |
| [Eq. (72)][eq:krrs-density-constraint] | [exists_C_chart](UpperTailOptimizers/KRRS/CChart.lean#L242) | [KRRS/CChart.lean](UpperTailOptimizers/KRRS/CChart.lean) |
| Desingularized stationarity and its Jacobian | [F1](UpperTailOptimizers/KRRS/Stationarity.lean#L130), [F2](UpperTailOptimizers/KRRS/Stationarity.lean#L142), [F_jacobian_nondegenerate](UpperTailOptimizers/KRRS/Stationarity.lean#L327) | [KRRS/Stationarity.lean](UpperTailOptimizers/KRRS/Stationarity.lean) |
| From entropy maximality to stationarity | [isLocalMax_reduced_entropy](UpperTailOptimizers/KRRS/LocalMax.lean#L82), [F_eq_zero_of_isLocalMax](UpperTailOptimizers/KRRS/SigmaLink.lean#L283) | [KRRS/LocalMax.lean](UpperTailOptimizers/KRRS/LocalMax.lean), [KRRS/SigmaLink.lean](UpperTailOptimizers/KRRS/SigmaLink.lean) |
| [Eq. (85)][eq:krrs-boundary-stationarity] | [F_eq_zero_of_maximizer](UpperTailOptimizers/KRRS/BaseZero.lean#L110), [F1_base_zero](UpperTailOptimizers/KRRS/BaseZero.lean#L280) | [KRRS/BaseZero.lean](UpperTailOptimizers/KRRS/BaseZero.lean) |
| [Eq. (89)][eq:krrs-stationary-densities] | [exists_stationary_family](UpperTailOptimizers/KRRS/Family.lean#L392) | [KRRS/Family.lean](UpperTailOptimizers/KRRS/Family.lean) |
| [Eq. (96)][eq:krrs-map-agreement] and the two-sided extension | [krrs_rectangle](UpperTailOptimizers/KRRS/Main.lean#L111) | [KRRS/Main.lean](UpperTailOptimizers/KRRS/Main.lean) |
| **[Theorem 2.1][thm:krrs-analytic-extension]** — Two-sided KRR–S extension: optimizer uniqueness and analytic parameters | [kenyonRadinRenSadun](UpperTailOptimizers/KRRS/Main.lean#L600), [kenyonRadinRenSadunAnalytic](UpperTailOptimizers/KRRS/Main.lean#L636) | [KRRS/Main.lean](UpperTailOptimizers/KRRS/Main.lean) |
| Analyticity on the full two-sided strip | [kenyonRadinRenSadunStrip](UpperTailOptimizers/KRRS/Main.lean#L689) | [KRRS/Main.lean](UpperTailOptimizers/KRRS/Main.lean) |
| Uniform `c(ε,ϑ) = O(ϑ)` | [kenyonRadinRenSadunUniform](UpperTailOptimizers/KRRS/Main.lean#L791), [exists_uniform_linear_bound](UpperTailOptimizers/KRRS/Main.lean#L726) | [KRRS/Main.lean](UpperTailOptimizers/KRRS/Main.lean) |
| Analyticity of the cross-density selector | [zeta_analytic](UpperTailOptimizers/KRRS/Main.lean#L865) | [KRRS/Main.lean](UpperTailOptimizers/KRRS/Main.lean) |

The public forms separate conclusions that the paper collects in one statement.
In particular, `Strip` does not state optimizer maximality, and `Uniform` states
analyticity at `(ε,0)`, not on the full strip. Both are derived from `krrs_rectangle`.
The explicit block-size derivative in [Eq. (97)][eq:krrs-block-size-derivative] is not exported
as a corresponding theorem; the uniform linear bound is proved directly from analyticity.

### Section 7 and Appendix E — the singular endpoint

The files in the following tables are under `UpperTailOptimizers/SingularEndpoint/`.
The differences [D1]–[D10] are explained in §7.

#### Family and singular endpoint statements

| Paper result or calculation | Lean declarations | File |
|---|---|---|
| The singular endpoint values forced by triple contact | [triple_contact_forced](UpperTailOptimizers/SingularEndpoint/Forced.lean#L171) | [Forced.lean](UpperTailOptimizers/SingularEndpoint/Forced.lean) |
| Scalar KKT root count | [four_zeros_absurd](UpperTailOptimizers/SingularEndpoint/Bipodality.lean#L186), [three_values_absurd](UpperTailOptimizers/SingularEndpoint/Bipodality.lean#L213) | [Bipodality.lean](UpperTailOptimizers/SingularEndpoint/Bipodality.lean) |
| **[Lemma 7.2][lem:stationary-rank-one-bipodality]** — Stationary rank-one bipodality, from the scalar a.e. KKT equation [D9] | [not_three_values](UpperTailOptimizers/SingularEndpoint/TwoValued.lean#L70), [exists_two_values](UpperTailOptimizers/SingularEndpoint/EssRange.lean#L105) | [TwoValued.lean](UpperTailOptimizers/SingularEndpoint/TwoValued.lean), [EssRange.lean](UpperTailOptimizers/SingularEndpoint/EssRange.lean) |
| Rank-one homomorphism density | [tBip_rankOne](UpperTailOptimizers/SingularEndpoint/RankOne.lean#L143), [tDensity_rankOne_two_block](UpperTailOptimizers/SingularEndpoint/RankOne.lean#L177), [prod_edges_eq_prod_pow_degree](UpperTailOptimizers/SingularEndpoint/RankOne.lean#L58) | [RankOne.lean](UpperTailOptimizers/SingularEndpoint/RankOne.lean) |
| **[Lemma 7.3][lem:rank-one-kkt-family]** — Analytic rank-one KKT family: scalar construction and symmetry | [exists_scalar_family](UpperTailOptimizers/SingularEndpoint/FamilyExists.lean#L55), [exists_scalar_family_density](UpperTailOptimizers/SingularEndpoint/FamilySymm.lean#L278) | [FamilyExists.lean](UpperTailOptimizers/SingularEndpoint/FamilyExists.lean), [FamilySymm.lean](UpperTailOptimizers/SingularEndpoint/FamilySymm.lean) |
| Local exhaustiveness in scalar coordinates [D2] | [exists_scalar_family_locally_unique](UpperTailOptimizers/SingularEndpoint/FamilyUnique.lean#L125) | [FamilyUnique.lean](UpperTailOptimizers/SingularEndpoint/FamilyUnique.lean) |
| [Eq. (35)][eq:three-value-kkt], after desingularization | [Esys1](UpperTailOptimizers/SingularEndpoint/FamilySystem.lean#L61), [Esys2](UpperTailOptimizers/SingularEndpoint/FamilySystem.lean#L72), [Esys3](UpperTailOptimizers/SingularEndpoint/FamilySystem.lean#L86), [lell_three_eq_iff](UpperTailOptimizers/SingularEndpoint/FamilySystem.lean#L141) | [FamilySystem.lean](UpperTailOptimizers/SingularEndpoint/FamilySystem.lean) |
| [Eq. (115)][eq:block-proportion-balance] and the block-weight formula | [rowBalance_solution](UpperTailOptimizers/SingularEndpoint/RowSign.lean#L355), [exists_family_with_block_weight](UpperTailOptimizers/SingularEndpoint/Alpha.lean#L328) | [RowSign.lean](UpperTailOptimizers/SingularEndpoint/RowSign.lean), [Alpha.lean](UpperTailOptimizers/SingularEndpoint/Alpha.lean) |
| Family structure and its existence | [KKTFamily](UpperTailOptimizers/SingularEndpoint/Family.lean#L114), [exists_kktFamily](UpperTailOptimizers/SingularEndpoint/FamilyBuild.lean#L42), [kktFamily](UpperTailOptimizers/SingularEndpoint/FamilyBuild.lean#L80) | [Family.lean](UpperTailOptimizers/SingularEndpoint/Family.lean), [FamilyBuild.lean](UpperTailOptimizers/SingularEndpoint/FamilyBuild.lean) |
| **[Lemma 7.4][lem:rank-one-parameter-expansions]** — Rank-one parameter expansions: coefficients for `u_h, γ_h, ℓ_h` | [Ucoeff_eq](UpperTailOptimizers/SingularEndpoint/Expansions.lean#L465), [Gcoeff_eq](UpperTailOptimizers/SingularEndpoint/Expansions.lean#L422), [Lcoeff_eq](UpperTailOptimizers/SingularEndpoint/Expansions.lean#L445) | [Expansions.lean](UpperTailOptimizers/SingularEndpoint/Expansions.lean) |
| Block-weight coefficient | [tendsto_alph_slope](UpperTailOptimizers/SingularEndpoint/Order5.lean#L224) | [Order5.lean](UpperTailOptimizers/SingularEndpoint/Order5.lean) |
| Coefficients for `q_h, r_h, μ_h` | [tendsto_qVal_coeff](UpperTailOptimizers/SingularEndpoint/EdgeGap.lean#L128), [tendsto_rVal_coeff](UpperTailOptimizers/SingularEndpoint/EdgeGap.lean#L183), [tendsto_muVal_coeff](UpperTailOptimizers/SingularEndpoint/MuExpansion.lean#L228) | [EdgeGap.lean](UpperTailOptimizers/SingularEndpoint/EdgeGap.lean), [MuExpansion.lean](UpperTailOptimizers/SingularEndpoint/MuExpansion.lean) |
| The `O` remainders of [Lemma 7.4][lem:rank-one-parameter-expansions], from analyticity and parity | [rank_one_parameter_expansions](UpperTailOptimizers/SingularEndpoint/ParameterRemainders.lean#L196), [exists_pow_bound_of_reflect](UpperTailOptimizers/SingularEndpoint/ParityOrder.lean#L178) | [ParameterRemainders.lean](UpperTailOptimizers/SingularEndpoint/ParameterRemainders.lean), [ParityOrder.lean](UpperTailOptimizers/SingularEndpoint/ParityOrder.lean) |
| **[Lemma 7.5][lem:constant-graphon-comparison]** — Comparison with the constant graphon and the cost clause of [Theorem 7.1][thm:endpoint-optimality] | [tendsto_cost_gap](UpperTailOptimizers/SingularEndpoint/StrictImprovement.lean#L55), [constant_graphon_comparison](UpperTailOptimizers/SingularEndpoint/CostRemainder.lean#L124), [singular_endpoint_strict_improvement](UpperTailOptimizers/SingularEndpoint/StrictImprovement.lean#L91) | [StrictImprovement.lean](UpperTailOptimizers/SingularEndpoint/StrictImprovement.lean), [CostRemainder.lean](UpperTailOptimizers/SingularEndpoint/CostRemainder.lean) |
| **[Theorem 7.1][thm:endpoint-optimality]** — Nonconstancy of the singular endpoint graphon | [graphon_not_ae_const](UpperTailOptimizers/SingularEndpoint/Terminal.lean#L117)† | [Terminal.lean](UpperTailOptimizers/SingularEndpoint/Terminal.lean) |
| **[Theorem 7.1][thm:endpoint-optimality]** — Assembled family, optimality, uniqueness and cost expansion, for every candidate block | [exists_singular_endpoint_full](UpperTailOptimizers/SingularEndpoint/TerminalUnique.lean#L95), [singular_endpoint_full](UpperTailOptimizers/SingularEndpoint/TerminalUnique.lean#L215) | [TerminalUnique.lean](UpperTailOptimizers/SingularEndpoint/TerminalUnique.lean) |
| Placement below the boundary [D1] | [singular_endpoint_symmetry_breaking](UpperTailOptimizers/SingularEndpoint/StrictImprovement.lean#L131) | [StrictImprovement.lean](UpperTailOptimizers/SingularEndpoint/StrictImprovement.lean); additional Lubetzky–Zhao consequence |

#### Localization

| Paper result or calculation | Lean declarations | File |
|---|---|---|
| Singular endpoint supporting gap and quartic lower bound | [Gam_nonneg](UpperTailOptimizers/SingularEndpoint/Gap.lean#L188), [Gam_eq_zero_iff](UpperTailOptimizers/SingularEndpoint/Gap.lean#L195), [exists_gam_quartic_lower](UpperTailOptimizers/SingularEndpoint/Quartic.lean#L157) | [Gap.lean](UpperTailOptimizers/SingularEndpoint/Gap.lean), [Quartic.lean](UpperTailOptimizers/SingularEndpoint/Quartic.lean) |
| [Eq. (47)][eq:graphon-cost-decomposition] | [Ip_sub_Ip_eq](UpperTailOptimizers/SingularEndpoint/Localization.lean#L101), [localization_basic](UpperTailOptimizers/SingularEndpoint/Localization.lean#L131) | [Localization.lean](UpperTailOptimizers/SingularEndpoint/Localization.lean) |
| Rank-one decomposition and orthogonality | [FactorDecomp](UpperTailOptimizers/SingularEndpoint/Factor.lean#L87), [FactorDecomp.factor_eq](UpperTailOptimizers/SingularEndpoint/Factor.lean#L180), [FactorDecomp.rankOne_moment](UpperTailOptimizers/SingularEndpoint/Factor.lean#L205) | [Factor.lean](UpperTailOptimizers/SingularEndpoint/Factor.lean) |
| Construction under an `L⁴` closeness hypothesis [D3] | [localization_rankOne](UpperTailOptimizers/SingularEndpoint/FactorMain.lean#L568), [factorMain_unique](UpperTailOptimizers/SingularEndpoint/FactorMain.lean#L768) | [FactorMain.lean](UpperTailOptimizers/SingularEndpoint/FactorMain.lean) |
| Contraction and fixed point | [contractionMap_contraction](UpperTailOptimizers/SingularEndpoint/FactorContraction.lean#L726), [lpBridgeSet_exists_fixedPoint](UpperTailOptimizers/SingularEndpoint/FactorLpBridge.lean#L347), [exists_factor_solution](UpperTailOptimizers/SingularEndpoint/FactorFix.lean#L430) | [FactorContraction.lean](UpperTailOptimizers/SingularEndpoint/FactorContraction.lean), [FactorLpBridge.lean](UpperTailOptimizers/SingularEndpoint/FactorLpBridge.lean), [FactorFix.lean](UpperTailOptimizers/SingularEndpoint/FactorFix.lean) |
| Moment stability in [Eq. (51)][eq:moment-and-cost-gap-bounds] | [FactorDecomp.holder_stability](UpperTailOptimizers/SingularEndpoint/FactorStability.lean#L503), [exists_holder_stability](UpperTailOptimizers/SingularEndpoint/FactorStability.lean#L581) | [FactorStability.lean](UpperTailOptimizers/SingularEndpoint/FactorStability.lean) |
| Homomorphism-density error in [Eq. (50)][eq:rank-one-reduction-bounds] | [FactorDecomp.abs_tDensity_sub_qVal_pow_le](UpperTailOptimizers/SingularEndpoint/FactorHDensity.lean#L1066) | [FactorHDensity.lean](UpperTailOptimizers/SingularEndpoint/FactorHDensity.lean) |
| [Eq. (48)][eq:graphon-quartic-localization] | [family_localization](UpperTailOptimizers/SingularEndpoint/FamilyLocalization.lean#L90), [family_localization_sq](UpperTailOptimizers/SingularEndpoint/FamilyLocalization.lean#L208) | [FamilyLocalization.lean](UpperTailOptimizers/SingularEndpoint/FamilyLocalization.lean) |
| Sharp moment and Hölder-deficit bounds | [family_ld_sharp](UpperTailOptimizers/SingularEndpoint/LdSharp.lean#L211), [family_holder_deficit](UpperTailOptimizers/SingularEndpoint/LdSharp.lean#L292) | [LdSharp.lean](UpperTailOptimizers/SingularEndpoint/LdSharp.lean) |
| [Eq. (54)][eq:factor-tail-mass] | [family_factor_tail_mass](UpperTailOptimizers/SingularEndpoint/FactorTail.lean#L266) | [FactorTail.lean](UpperTailOptimizers/SingularEndpoint/FactorTail.lean) |
| **[Lemma 7.6][lem:localization-rank-one]** — Localization and rank-one reduction, from cost and feasibility [D3] | [singular_endpoint_localization](UpperTailOptimizers/SingularEndpoint/LocalizationMain.lean#L131) | [LocalizationMain.lean](UpperTailOptimizers/SingularEndpoint/LocalizationMain.lean) |

#### Auxiliary Lagrangian and arbitrary-graphon comparison

| Paper result or proof step | Lean declarations | File |
|---|---|---|
| [Eq. (52)][eq:entropy-continuation] | [JpTilde](UpperTailOptimizers/SingularEndpoint/JpTilde.lean#L79), [JpTilde_of_le_one](UpperTailOptimizers/SingularEndpoint/JpTilde.lean#L85), [GamTilde](UpperTailOptimizers/SingularEndpoint/Continuation.lean#L57), [JpTildeH](UpperTailOptimizers/SingularEndpoint/PsiTilde.lean#L72)† | [JpTilde.lean](UpperTailOptimizers/SingularEndpoint/JpTilde.lean), [Continuation.lean](UpperTailOptimizers/SingularEndpoint/Continuation.lean), [PsiTilde.lean](UpperTailOptimizers/SingularEndpoint/PsiTilde.lean) |
| Continuity estimates used in [Lemma 7.7][lem:continuation-kernel-bounds] | [exists_JpTilde_modulus](UpperTailOptimizers/SingularEndpoint/JpTilde.lean#L402), [exists_abs_JpTildeH_le](UpperTailOptimizers/SingularEndpoint/DistributionQuant.lean#L1173)† | [JpTilde.lean](UpperTailOptimizers/SingularEndpoint/JpTilde.lean), [DistributionQuant.lean](UpperTailOptimizers/SingularEndpoint/DistributionQuant.lean) |
| [Eq. (55)][eq:first-variation]: auxiliary scalar function and contacts | [Psi](UpperTailOptimizers/SingularEndpoint/FirstVariation.lean#L94)†, [etaVal](UpperTailOptimizers/SingularEndpoint/FirstVariation.lean#L74)†, [kappaVal](UpperTailOptimizers/SingularEndpoint/FirstVariation.lean#L88)†, [Psi_sVal](UpperTailOptimizers/SingularEndpoint/FirstVariation.lean#L112)†, [Psi_tVal](UpperTailOptimizers/SingularEndpoint/FirstVariation.lean#L134)† | [FirstVariation.lean](UpperTailOptimizers/SingularEndpoint/FirstVariation.lean) |
| **[Lemma 7.8][lem:first-variation-bound]** — First-variation lower bound: central and tail bounds | [exists_firstVariation_lower](UpperTailOptimizers/SingularEndpoint/FirstVariationBound.lean#L453)†, [exists_firstVariation_upperGap](UpperTailOptimizers/SingularEndpoint/PsiTilde.lean#L363)† | [FirstVariationBound.lean](UpperTailOptimizers/SingularEndpoint/FirstVariationBound.lean), [PsiTilde.lean](UpperTailOptimizers/SingularEndpoint/PsiTilde.lean) |
| Interpolation used to prove [Lemma 7.9][lem:central-kernel-bound] | [exists_powResid_bound](UpperTailOptimizers/SingularEndpoint/PowInterp.lean#L387), [kernel_decomposition](UpperTailOptimizers/SingularEndpoint/KernelInterp.lean#L576)† | [PowInterp.lean](UpperTailOptimizers/SingularEndpoint/PowInterp.lean), [KernelInterp.lean](UpperTailOptimizers/SingularEndpoint/KernelInterp.lean) |
| Limiting kernel coefficient and its error [D6] | [powDopOf_powDopOf_kernel_zero](UpperTailOptimizers/SingularEndpoint/KernelTheta.lean#L430)†, [exists_kernelTheta_bound](UpperTailOptimizers/SingularEndpoint/KernelError.lean#L1655)†, [exists_kernelTheta_error](UpperTailOptimizers/SingularEndpoint/KernelError.lean#L909)† | [KernelTheta.lean](UpperTailOptimizers/SingularEndpoint/KernelTheta.lean), [KernelError.lean](UpperTailOptimizers/SingularEndpoint/KernelError.lean) |
| Distribution of the factor and tail interpolation | [distributionMeasure](UpperTailOptimizers/SingularEndpoint/DistributionMeasure.lean#L238)†, [exists_tail_interpolation](UpperTailOptimizers/SingularEndpoint/DistributionMeasure.lean#L355)† | [DistributionMeasure.lean](UpperTailOptimizers/SingularEndpoint/DistributionMeasure.lean) |
| First-variation decomposition of the distribution cost | [distributionJ_sub_eq](UpperTailOptimizers/SingularEndpoint/DistributionGap.lean#L239)†, [sigmaQuad_eq](UpperTailOptimizers/SingularEndpoint/DistributionGap.lean#L220)† | [DistributionGap.lean](UpperTailOptimizers/SingularEndpoint/DistributionGap.lean) |
| Central integral estimate in [Lemma 7.9][lem:central-kernel-bound], and mixed/tail estimates | [centralQuad_lower](UpperTailOptimizers/SingularEndpoint/DistributionQuant.lean#L1037)†, [exists_abs_mixedQuad_le](UpperTailOptimizers/SingularEndpoint/DistributionQuant.lean#L1142)†, [exists_abs_tailQuad_le](UpperTailOptimizers/SingularEndpoint/DistributionQuant.lean#L1218)† | [DistributionQuant.lean](UpperTailOptimizers/SingularEndpoint/DistributionQuant.lean) |
| **[Lemma 7.10][lem:auxiliary-lagrangian-bound]** — Auxiliary Lagrangian bound, with the linear moment term [D4], [D5] | [exists_distributionGap_refined_window_forall](UpperTailOptimizers/SingularEndpoint/DistributionFinal.lean#L94)†, [exists_distributionGap_window](UpperTailOptimizers/SingularEndpoint/DistributionFinal.lean#L126)† | [DistributionFinal.lean](UpperTailOptimizers/SingularEndpoint/DistributionFinal.lean) |
| Additional distribution uniqueness result | [distribution_unique](UpperTailOptimizers/SingularEndpoint/DistributionUnique.lean#L210)†, [distributionMeasure_isMinimizer](UpperTailOptimizers/SingularEndpoint/DistributionUnique.lean#L274)† | [DistributionUnique.lean](UpperTailOptimizers/SingularEndpoint/DistributionUnique.lean); not a clause of the paper's auxiliary-bound lemma |
| Distribution-to-graphon comparison | [comparisonDistribution](UpperTailOptimizers/SingularEndpoint/GraphonComparison.lean#L92), [comparison_splitting](UpperTailOptimizers/SingularEndpoint/GraphonComparison.lean#L312), [exists_comparison_gap](UpperTailOptimizers/SingularEndpoint/GraphonComparison.lean#L348) | [GraphonComparison.lean](UpperTailOptimizers/SingularEndpoint/GraphonComparison.lean) |
| Central entropy and KKT terms [D7] | [comparisonMain_central_convexGap](UpperTailOptimizers/SingularEndpoint/GraphonComparisonMain.lean#L415), [comparisonMain_abs_kkt_error_le](UpperTailOptimizers/SingularEndpoint/GraphonComparisonMain.lean#L1071) | [GraphonComparisonMain.lean](UpperTailOptimizers/SingularEndpoint/GraphonComparisonMain.lean) |
| Residual estimates [D8] | [comparisonMain_exists_residual_bound](UpperTailOptimizers/SingularEndpoint/GraphonComparisonMain.lean#L2006), [comparisonMain_exists_splitting_gap](UpperTailOptimizers/SingularEndpoint/GraphonComparisonMain.lean#L2318) | [GraphonComparisonMain.lean](UpperTailOptimizers/SingularEndpoint/GraphonComparisonMain.lean) |
| Mixed rectangles and tail square | [rowJensen_exists_mixed](UpperTailOptimizers/SingularEndpoint/RowJensen.lean#L642), [rowJensen_exists_tailSq](UpperTailOptimizers/SingularEndpoint/RowJensen.lean#L771) | [RowJensen.lean](UpperTailOptimizers/SingularEndpoint/RowJensen.lean) |
| **[Lemma 7.11][lem:graphon-lagrangian-bound]** — Full-graphon Lagrangian bound, with the qualifications [D4], [D5] | [exists_comparison_master](UpperTailOptimizers/SingularEndpoint/GraphonComparisonMaster.lean#L497), [exists_singular_endpoint_comparison_graph](UpperTailOptimizers/SingularEndpoint/GraphonComparisonMaster.lean#L898) | [GraphonComparisonMaster.lean](UpperTailOptimizers/SingularEndpoint/GraphonComparisonMaster.lean) |
| From the linear moment term to the graph constraint | [muVal_tDensity_le_etaVal](UpperTailOptimizers/SingularEndpoint/LagrangeBridge.lean#L182), [etaVal_eq_muVal](UpperTailOptimizers/SingularEndpoint/LagrangeBridge.lean#L125)† | [LagrangeBridge.lean](UpperTailOptimizers/SingularEndpoint/LagrangeBridge.lean) |
| Final optimality and rigidity | [terminal_optimality_of_master](UpperTailOptimizers/SingularEndpoint/Terminal.lean#L163), [exists_singular_endpoint_rigidity](UpperTailOptimizers/SingularEndpoint/SingularEndpointOptimality.lean#L184), [exists_singular_endpoint_optimality](UpperTailOptimizers/SingularEndpoint/SingularEndpointOptimality.lean#L395) | [Terminal.lean](UpperTailOptimizers/SingularEndpoint/Terminal.lean), [SingularEndpointOptimality.lean](UpperTailOptimizers/SingularEndpoint/SingularEndpointOptimality.lean) |
| Equality implies a two-valued factor | [FactorDecomp.ae_eq_rankOne_of_residSq_zero](UpperTailOptimizers/SingularEndpoint/TerminalTwoValued.lean#L53), [ae_twoValued_of_R_zero](UpperTailOptimizers/SingularEndpoint/TerminalTwoValued.lean#L78), [measure_eq_alph_of_qVal_eq](UpperTailOptimizers/SingularEndpoint/TerminalTwoValued.lean#L167) | [TerminalTwoValued.lean](UpperTailOptimizers/SingularEndpoint/TerminalTwoValued.lean) |
| Relabelling to any block of the right measure | [measurePreserving_relabel](UpperTailOptimizers/SingularEndpoint/CdfTransport.lean#L539), [exists_relabel_eq_bipodalGraphon](UpperTailOptimizers/SingularEndpoint/BipodalTransport.lean#L61), [anyBlock_of_singularEndpointOptimizers](UpperTailOptimizers/SingularEndpoint/TerminalUnique.lean#L150) | [CdfTransport.lean](UpperTailOptimizers/SingularEndpoint/CdfTransport.lean), [BipodalTransport.lean](UpperTailOptimizers/SingularEndpoint/BipodalTransport.lean) |
| Uniqueness | [exists_singular_endpoint_uniqueness](UpperTailOptimizers/SingularEndpoint/TerminalUnique.lean#L61) | [TerminalUnique.lean](UpperTailOptimizers/SingularEndpoint/TerminalUnique.lean) |

The general graphon and block first-variation definitions are absent; the scalar
function `Psi` in this table does not supply those definitions. See [D9].

## 5. Module map

The repository contains 168 Lean files, including the root import module.
All are reachable from `UpperTailOptimizers.lean`.

| Directory | Files | Contents |
|---|---|---|
| `LZBoundary/` | 16 | Relative entropy, convex minorants, contact geometry, analytic implicit/inverse function tools, and the boundary curve |
| `Graphon/` | 12 | Graphons, densities, entropy, cut convergence, attainment, bipodal kernels, the external inputs and graph-counting helpers |
| `KRRS/` | 14 | The two external KRR–S inputs and the proof of their analytic extension |
| `Nondegeneracy/` | 10 | Quadratic estimates, the boundary excess and its analytic coefficient |
| `LocalOptimizer/` | 9 | Optimizer uniqueness, analytic dependence, asymptotics, global statements and the worked instances |
| `SingularEndpoint/` | 105 | The singular endpoint family, localization, comparison, optimality and uniqueness |
| `LocalReduction/` | 1 | Reduction of the upper-tail problem to the edge density |

Import coverage shows that the build checks every source module. It does not establish
that every declaration is needed: public results may have no internal callers, and
simp lemmas can be used without appearing by name in a proof.

## 6. What it rests on

The eight project axioms are listed in [the README](README.md#what-it-rests-on).
This section explains their scope and the dependencies reported by Lean.

### Generalized Hölder and the Lubetzky–Zhao criterion

`generalized_holder` assumes [Eq. (4)][eq:generalized-holder].
`lubetzkyZhao` assumes the deterministic criterion in [Theorem 1.4][thm:lz-criterion], expressed
as the existence of a supporting affine function at `r^d`.
Both require a finite `d`-regular graph with `d ≥ 2` and at least one edge.
The criterion also requires `0 < p < r < 1`.

The criterion axiom does not include uniqueness. The boundary and replica-symmetric
uniqueness results are proved from Hölder, scalar contact geometry and strict convexity.
The explicit nonempty-edge hypothesis matters because regularity alone is vacuous
on an empty vertex type.

### Cut compactness, continuity and lower semicontinuity

The four axioms in `Graphon/CutContinuity.lean` represent graph-limit background used
in the paper's preliminaries. All are phrased for sequences through `CutTendsto`.
No topology or metric-space structure on a graphon quotient is constructed.

These declarations are not independent:
`edgeDensity_cutContinuous` follows from `tDensity_cutContinuous` applied to the
complete graph on `Fin 2`, using `tDensity_top_two`. Its separate declaration remains
part of the current dependency inventory.

`feasible_attains` proves attainment of the upper-tail infimum from sequential
compactness, homomorphism-density continuity and lower semicontinuity of the cost.
The Chatterjee–Varadhan large deviation principle is not an axiom here.

### The two KRR–S inputs

The axioms in `KRRS/Inputs.lean` return `Nonempty` structures.
Every field of those structures is part of the assumption.

**`krrs_thm33`** supplies `KRRSZeta d` for `d ≥ 2`.
Its selector has values in `(0,1)`, is strictly decreasing and involutive, and fixes
`(d−1)/d`. It also maximizes the scalar quotient among off-diagonal competitors.
This maximality uses the characterization following [Theorem A.2][thm:krrs-cross-density],
not just the quoted theorem statement.

The maximality field excludes a competitor `z = ε`. Lean evaluates the displayed
quotient there as `0/0 = 0`, so including the diagonal would change the intended
statement. The structure does not assume the source's nonvanishing derivative or
uniqueness of the maximizer.

**`krrs_thm11`** supplies `KRRSOptimizer H d Z` for a regular graph with `d ≥ 2`
and at least two edges. Its fields assume a positive-surplus region, analytic bipodal
parameters, existence and entropy maximality at fixed edge and subgraph densities,
uniqueness up to a relabelling — measure-preserving with a measure-preserving inverse that
undoes it almost everywhere in both directions — and four one-sided boundary limits.
The source's block-size `O(ϑ)` bound is weakened to convergence to zero in this input.

**Openness is an explicit additional interpretation.**
`KRRSOptimizer.region_open` assumes that the positive-surplus region is open.
The paper reads the source's analyticity assertion as including this property.
In Lean, it does not follow from the pointwise positivity of the surplus threshold
or from the structure's `AnalyticAt` field. The proof of `exists_uniform_strip`
uses this openness.

The input structures are therefore adapted statements, not literal transcriptions
of the cited theorems. The local uniform surplus window, two-sided continuation,
interiority needed for the construction and uniform `c = O(ϑ)` bound are derived
inside the repository. Fixed-density entropy attainment is assumed in this input;
upper-tail cost attainment is proved separately.

### Verified axiom footprints

A footprint lists the axioms used transitively by a declaration.
Here **GH** is `generalized_holder`, **LZ** is `lubetzkyZhao`,
**KRRS₂** is `krrs_thm11` and `krrs_thm33`, and **CUT₄** denotes the four cut axioms.
**CUT₃** omits `edgeDensity_cutContinuous`.
“None” means no project axioms; the proofs may still use
`propext`, `Classical.choice` and `Quot.sound`.

| Declarations | Project axioms |
|---|---|
| `scalar_lz_boundary_arcs`, `lz_boundary_contacts`, `lz_boundary_endpoint_limits` | None |
| Declarations in `LZBoundary/Curve.lean` | None |
| `lce_isLeast_twoPoint`, `Graphon.Ip_eq_entropy`, `tDensity_top_two` | None |
| `active_constraint`, `expectation_quadratic_lower`, `quadratic_upper` | None |
| `tilted_critical_point`, `analytic_implicit`, `analytic_inverse`, `AH_eq_AHGlobal` | None |
| `krrs_parameter_lipschitz`, `arc_gap_bounds`, `exists_Dd_floor`, `krrs_edge_linearization`, `krrs_H_linearization`, `krrs_eliminate` | None |
| `holder_moment`, `boundary_uniqueness`, `quadratic_lower_graphon` | GH |
| `boundaryExcess_quadratic`, `boundaryExcess_pos`, `replica_symmetric_unique` | GH |
| `edgeDensity_lt_broken` | LZ |
| `feasible_attains` | CUT₃ |
| `cutDist_tendsto_boundary` | GH + CUT₃ |
| `edgeDensity_tendsto_boundary` | GH + CUT₄ |
| `uniform_localization` | GH + LZ + CUT₄ |
| `krrs_rectangle`, the four public `kenyonRadinRenSadun…` forms, `zeta_analytic`, `krrs_strip` | KRRS₂ |
| `boundaryExcess_taylor`, `boundaryExcess_chart`, `boundaryExcess_chart_full`, `exists_analytic_critical_family` | GH + KRRS₂ |
| `analyticAt_AHGlobal_and_pos` | GH + KRRS₂ |
| `reduction_core_uniform`, `scalar_reduction`, `optimizer_bipodal`, `exists_bipodal_optimizer` | All eight |
| `symmetry_breaking_core`, `symmetry_breaking_side`, `symmetry_breaking_analytic`, `bipodal_family` | All eight |
| `parameter_asymptotics`, `local_structure_on_arc`, `local_structure`, `main_bipodal_optimizer` | All eight |
| Singular endpoint family existence, strict improvement, factor construction, distribution comparison and residual estimates | None |
| `SingularEndpoint.singular_endpoint_localization`, `SingularEndpoint.exists_singular_endpoint_full`, `SingularEndpoint.singular_endpoint_full` | GH |
| `SingularEndpoint.singular_endpoint_symmetry_breaking` | LZ |
| `SingularEndpoint.singular_endpoint_optimizers` | GH |

The singular endpoint development uses neither cut axioms nor KRR–S inputs.
Generalized Hölder enters its localization argument; Lubetzky–Zhao enters the proof
that the family lies below the boundary.

### Verification scope

On 2026-09-10, the project built without errors or warnings (8877 jobs), using the
pinned Lean and Mathlib versions. A dependency traversal of 3931 compiled project
declarations found only the eight project axioms and the three foundational axioms,
with no `sorryAx`. Exact footprints were checked for the capstone declarations
`scalar_lz_boundary_arcs`, `local_structure_on_arc`, `local_structure`,
`main_bipodal_optimizer`, `analyticAt_AHGlobal_and_pos`, `singular_endpoint_full`,
`singular_endpoint_optimizers` and `singular_endpoint_symmetry_breaking`, and for
`replica_symmetric_unique`, `replica_symmetric_unique_global` and `arcMaps_noFlatTie`,
which use no project axiom other than `generalized_holder`.
The compiled proof terms also confirm that each introduction corollary directly
uses its corresponding body theorem and the conclusion-structure projection.

The documentation review used the paper sources in this repository. It compared the
definitions and principal theorem statements, including graph hypotheses, parameter
windows, entropy normalization, relabelling, analytic domains and remainder orders.
It also checked the declaration names, file references and local Markdown links used
in the documentation.

These checks establish build validity and the reported dependency and statement
information. They are not a line-by-line review of every proof or an independent
verification of the external literature. Kernel checking proves derivability from
the assumptions; it does not prove those assumptions consistent or equivalent to
every convention used in the literature. The differences in §7 remain part of the
formalisation's scope.

The [README commands](README.md#build-and-check) inspect selected theorem dependencies
directly from standard input.

### What is not assumed

Several substantial steps are theorems in this repository:

- The scalar boundary, including its global extension.
- The KRR–S two-sided continuation and uniform block-size bound.
- Attainment of the upper-tail infimum and the boundary uniqueness result.
- The lower convex envelope and the analytic implicit/inverse function tools used here.
- The relabelling transport, and its quantile inverse, used in singular endpoint uniqueness.
- Existence of the boundary arcs and singular endpoint families.

The worked `K₃` and `K₄` examples show that the main graph hypotheses have instances.
These existence results use the assumptions reported for their proofs.

## 7. Deviations from the paper

This section distinguishes restrictions in the formal statements from changes in
representation or proof. The reference is the bundled paper, including its current
four-part local structure theorem and singular endpoint comparison lemmas.

### Graphons, domains and relabelling

`Graphon` is a total, pointwise symmetric measurable function on `ℝ²` with values in
`[0,1]`. Integration restricts it to the unit square, and optimizer equalities are
almost everywhere. `IsBipodal` allows zero-measure blocks and coincident densities;
nonconstancy is stated separately.

The graph-dependent main theorems require at least one edge. Singular endpoint theorems also
state a lower bound on the vertex count. These hypotheses exclude the empty vertex
type, on which a degree condition alone would be vacuous.

Uniqueness is expressed through `IsRelabelling` (`Graphon/Basic.lean`): for every optimizer
`W` there are measure-preserving `σ` and `τ` with `W(x,y) = W_*(σx,σy)` almost everywhere and
with `τ ∘ σ` and `σ ∘ τ` the identity almost everywhere. This is the paper's class of
measure-preserving a.e. bijections of `[0,1]`. `cutDist` ranges over the same class, so the
four cut inputs are stated against it. No graphon quotient or metric-space instance is
constructed.

`phiVar` and `entropyEnvelope` use real-valued infima and suprema.
In particular, an empty fixed-density constraint set gives `entropyEnvelope = 0`,
where the paper uses `−∞`. Relevant theorems supply feasible witnesses and bounds.
The coefficients `AH` and `AHGlobal` are defined by limits and used on domains where
those limits are proved to exist.

### Nonexceptional results

**Regular graphs.** The KRR–S extension is proved for `d`-regular graphs.
[Theorem 2.1][thm:krrs-analytic-extension] states it for `d`-starlike graphs. All subsequent graph-dependent main
results use the regular case.

**One local analytic extension versus an extension over a compact set.**
[Theorem 5.4][thm:positive-second-variation] states a single analytic `G` on a neighbourhood of
`K × {0}`, with a uniform curvature estimate.
`boundaryExcess_chart` and `boundaryExcess_chart_full` construct `Gc` near a fixed
density. `boundaryExcess_taylor` proves the uniform Taylor estimate and positivity on
compact `K`, but does not return a single extension or its uniform curvature bound
over all of `K`. That combined statement remains unformalised.

**[Theorem 6.1(d)][thm:local-optimizer-structure].**
The `analyticFamily` field of `local_structure` collects `bipodal_family` in global
coordinates, including its quantitative block-size bounds. The supporting theorem
`symmetry_breaking_analytic` states analyticity of the six functions after composing
the fixed-density parameters with `(p,r) ↦ (r−Δ, r^m−(r−Δ)^m)`.
It exhibits a concrete bipodal optimizer and states the common edge density of every
optimizer. The construction also gives boundary values and
`|c| ≤ LΔ ≤ LCλ`. `exists_blockSize_pos_tendsto` turns these into the paper's part (d):
`0 < c(p,r)` on the whole window, `c(p,r) → 0` as `p ↑ pc(r)`, and hence `c(p,r) < 1/2`.
The `< 1/2` clause is stated on a left neighbourhood of `pc(r)` for each `r`, not on one
window uniform in `r`.

**Separate KRR–S conclusions.** The paper and Lean both start near a fixed density;
this local choice is not a difference in scope.
Lean separates optimizer uniqueness, strip analyticity and the uniform linear bound
into several public declarations. No one of those shortened statements should be
read as containing all the others. The explicit positive block-size derivative in
Appendix A is not exported as a matching theorem.

**Global coefficient.** `local_structure` includes the positivity and analyticity
of `A_H`, and `main_bipodal_optimizer` inherits them directly. The definition of
`AHGlobal` uses the limit of `2G_r(δ)/δ²`, so its well-definedness does not require
the paper's analytic-chart patching argument.

**Scalar coordinates and proof methods.** The scalar contact calculation mainly uses
`u = x^{1/d}`; the two zeros of the convexity defect are existential values rather
than named functions. The scalar lower bound and bipodal upper construction use
quantitative estimates. The critical-point existence proof uses the intermediate
value theorem, with the implicit function theorem used for analytic dependence.

### The singular endpoint

**[D1] Placement below the boundary.**
`singular_endpoint_symmetry_breaking` proves `p_h < pc(r_h)` using the
Lubetzky–Zhao axiom. This is an additional consequence, kept separate from
`singular_endpoint_full` and `singular_endpoint_optimizers`, in agreement with the
paper's theorem statements. The concrete graph examples invoke it explicitly.

**[D2] Local exhaustiveness.**
`exists_scalar_family_locally_unique` gives uniqueness of nearby scalar triples
`(u,ℓ,γ)` solving the three KKT equations at nonzero half-gap `h`.
The local exhaustiveness clause of [Lemma 7.3][lem:rank-one-kkt-family] is stated for stationary
graphons. The passage from that graphon statement to the scalar hypotheses is not
included; see [D9].

**[D3] Rank-one construction.**
The paper's [Lemma 7.6][lem:localization-rank-one] begins with feasibility and a cost comparison.
`localization_rankOne` instead assumes `L⁴` closeness directly and constructs the
factor by contraction. `singular_endpoint_localization` derives that closeness from the
paper's hypotheses and collects the localization, moment, orthogonality and residual
bounds. The separate `factorMain_unique` proves uniqueness among normalized factor
solutions under a smaller closeness threshold; this is an additional Lean result.

**[D4] Choice of localization radius.**
`exists_comparison_master` and `exists_distributionGap_window` produce one
positive radius. [Lemma 7.10][lem:auxiliary-lagrangian-bound] and [Lemma 7.11][lem:graphon-lagrangian-bound] allow every sufficiently
small positive radius, with constants depending on it.
Several intermediate results do preserve that latter order, including
`exists_distributionGap_refined_window_forall`,
`exists_distribution_window_forall` and
`comparisonMain_exists_multiplier_bound_forall`.

**[D5] Linear moment term.**
The distribution and comparison estimates first subtract
`η_h Δ_h(ν)`, where `Δ_h(ν) = ∫x^d dν − q_h`.
The paper's auxiliary Lagrangian in [Eq. (59)][eq:auxiliary-lagrangian-bound] subtracts `μ_h{(∫x^d dν)^v−q_h^v}`,
and its graphon version in [Eq. (60)][eq:graphon-lagrangian-bound] subtracts `μ_h{t(H,W)−r_h^m}`.
Lean performs the conversion later, using `muVal_tDensity_le_etaVal` and
`exists_singular_endpoint_comparison_graph`. The final optimality theorem therefore uses
the graph constraint, while the intermediate formulas differ.

**[D6] Kernel interpolation estimates.**
`exists_kernelTheta_bound` chooses its own radius.
`exists_kernelTheta_error` states an epsilon estimate by choosing a sufficiently
small neighbourhood. The paper presents these estimates inside the proof of
[Lemma 7.9][lem:central-kernel-bound], with a radius-dependent error tending to zero.
Lean does not collect them in exactly that form.

**[D7] Central KKT estimate.**
Both `comparisonMain_abs_kkt_error_le` and the current proof of
[Lemma 7.11][lem:graphon-lagrangian-bound] use the residual norm restricted to the central square.
The intermediate constants are organized differently.

**[D8] A separate residual estimate.**
`comparisonMain_exists_residual_bound` proves, for any prescribed `θ > 0`,
a lower bound on the entropy difference of the form
`‖E‖₂² − θA − C·tailMass`, for every supplied `FactorDecomp` in its parameter window.
`comparisonMain_exists_splitting_gap` combines it with the distribution cost.
This is an additional intermediate formulation. The proof of [Lemma 7.11][lem:graphon-lagrangian-bound] combines
central, mixed and tail estimates within the full-graphon comparison.

**[D9] Variational stationarity.**
The general definitions [Eq. (32)][eq:graphon-stationarity] and [Eq. (33)][eq:block-stationarity],
and their reduction to the scalar equations, are not formalised.
The singular endpoint development starts with
`Fkkt d p γ z = J_p'(z) − γz^{d−1}`.
It uses either an a.e. equation at `z = f(x)f(y)`, or the three scalar family
equations together with block balance.
The scalar first-variation function `Psi` and the finite-dimensional derivative
calculations in `KRRS/` do not replace the missing general variational definitions.

**[D10] Continuation estimates.**
[Lemma 7.7][lem:continuation-kernel-bounds] collects Hölder-`1/2` estimates, uniform bounds
and `O(h²)` convergence for both the continued entropy and its kernel.
Lean instead provides a logarithmic modulus
`C t(1 + max(0,log(1/t)))` for `JpTilde` at the singular endpoint, and separate bounds for
the family-dependent continuation. The corresponding six estimates are not collected
in a theorem matching the paper's lemma.

## 8. What is not formalised

The random graph model, its large deviation principle and the probabilistic
consequences of the introduction are outside this repository.
The graphon quotient metric theorem is also absent.
The cross-density maximizer characterization enters as an input field rather than
as a proved theorem.

Other missing clauses within the deterministic development are recorded in §7:
the broader KRR–S graph class, the single
analytic extension over a compact set, the explicit smaller-block and limit clauses,
and general variational stationarity.

`analyticAt_AHGlobal_and_pos` excludes `r_*`; it does not settle positivity or the limiting behavior
of that coefficient at the exceptional density. The singular endpoint optimizer construction
is a separate result. The general theorems accept finite regular graphs; the worked
instances in `LocalOptimizer/Instances.lean` are `K₃` and `K₄`, without a separate cycle-family example.

The paper's [Section 8][sec:lean-formalization] says that the repository contains a separate
`p ↓ 0` triangle-boundary development with its own assumption. That description does not apply to this standalone repository:
no such additional development or axiom is included here.

<!-- Paper reference targets; display numbers come from the compiled manuscript. -->
[thm:nonexceptional-optimizers]: paper/sections/intro.tex#L238
[lem:active-constraint]: paper/sections/local_reduction.tex#L13
[rmk:bipodal-parameter-expansions]: paper/sections/appendix_local_optimizer.tex#L5
[thm:krrs-analytic-extension]: paper/sections/preliminaries.tex#L181
[thm:positive-second-variation]: paper/sections/nondegeneracy.tex#L552
[thm:endpoint-optimality]: paper/sections/singular_endpoint.tex#L34
[thm:graphon-large-deviations]: paper/sections/intro.tex#L204
[thm:lz-criterion]: paper/sections/intro.tex#L228
[thm:endpoint-optimizers]: paper/sections/intro.tex#L287
[thm:scalar-lz-boundary]: paper/sections/lz_boundary.tex#L21
[lem:convexity-defect]: paper/sections/lz_boundary.tex#L65
[lem:contact-points]: paper/sections/lz_boundary.tex#L95
[lem:contact-point-limits]: paper/sections/lz_boundary.tex#L113
[lem:edge-density-deficit]: paper/sections/local_reduction.tex#L56
[lem:boundary-convergence]: paper/sections/local_reduction.tex#L82
[lem:fixed-density-bipodality]: paper/sections/local_reduction.tex#L138
[cor:scalar-reduction]: paper/sections/local_reduction.tex#L253
[lem:scalar-quadratic-bound]: paper/sections/nondegeneracy.tex#L84
[prop:graphon-quadratic-bound]: paper/sections/nondegeneracy.tex#L207
[lem:bipodal-quadratic-bound]: paper/sections/nondegeneracy.tex#L236
[thm:local-optimizer-structure]: paper/sections/local_optimizer.tex#L12
[lem:stationary-rank-one-bipodality]: paper/sections/singular_endpoint.tex#L151
[lem:rank-one-kkt-family]: paper/sections/singular_endpoint.tex#L270
[lem:rank-one-parameter-expansions]: paper/sections/singular_endpoint.tex#L508
[lem:constant-graphon-comparison]: paper/sections/singular_endpoint.tex#L561
[lem:localization-rank-one]: paper/sections/singular_endpoint.tex#L755
[lem:continuation-kernel-bounds]: paper/sections/singular_endpoint.tex#L1158
[lem:first-variation-bound]: paper/sections/singular_endpoint.tex#L1345
[lem:central-kernel-bound]: paper/sections/singular_endpoint.tex#L1442
[lem:auxiliary-lagrangian-bound]: paper/sections/singular_endpoint.tex#L1652
[lem:graphon-lagrangian-bound]: paper/sections/singular_endpoint.tex#L1775
[thm:krrs-bipodality]: paper/sections/appendix_preliminaries.tex#L11
[thm:krrs-cross-density]: paper/sections/appendix_preliminaries.tex#L50
[lem:two-point-convex-minorant]: paper/sections/appendix_lz_boundary.tex#L14
[eq:relative-entropy-identity]: paper/sections/preliminaries.tex#L101
[eq:generalized-holder]: paper/sections/preliminaries.tex#L79
[eq:fixed-density-entropy]: paper/sections/local_reduction.tex#L103
[eq:reduced-objective]: paper/sections/local_reduction.tex#L112
[eq:reduced-objective-attainment]: paper/sections/local_reduction.tex#L151
[eq:edge-density-minimization]: paper/sections/local_reduction.tex#L259
[eq:contact-quadratic-separation]: paper/sections/lz_boundary.tex#L36
[eq:optimizer-edge-expansion]: paper/sections/local_optimizer.tex#L26
[eq:optimal-value-expansion]: paper/sections/local_optimizer.tex#L30
[eq:optimizer-block-size]: paper/sections/appendix_local_optimizer.tex#L37
[eq:optimizer-block-density]: paper/sections/appendix_local_optimizer.tex#L43
[eq:krrs-uniform-domain]: paper/sections/appendix_preliminaries.tex#L556
[eq:krrs-scalar-nondegeneracy]: paper/sections/appendix_preliminaries.tex#L102
[eq:krrs-entropy-derivative]: paper/sections/appendix_preliminaries.tex#L257
[eq:krrs-density-constraint]: paper/sections/appendix_preliminaries.tex#L222
[eq:krrs-boundary-stationarity]: paper/sections/appendix_preliminaries.tex#L447
[eq:krrs-stationary-densities]: paper/sections/appendix_preliminaries.tex#L479
[eq:krrs-map-agreement]: paper/sections/appendix_preliminaries.tex#L611
[eq:krrs-block-size-derivative]: paper/sections/appendix_preliminaries.tex#L641
[eq:three-value-kkt]: paper/sections/singular_endpoint.tex#L382
[eq:block-proportion-balance]: paper/sections/appendix_singular_endpoint.tex#L257
[eq:graphon-cost-decomposition]: paper/sections/singular_endpoint.tex#L727
[eq:moment-and-cost-gap-bounds]: paper/sections/singular_endpoint.tex#L832
[eq:rank-one-reduction-bounds]: paper/sections/singular_endpoint.tex#L777
[eq:graphon-quartic-localization]: paper/sections/singular_endpoint.tex#L759
[eq:factor-tail-mass]: paper/sections/singular_endpoint.tex#L1267
[eq:entropy-continuation]: paper/sections/singular_endpoint.tex#L1134
[eq:first-variation]: paper/sections/singular_endpoint.tex#L1291
[eq:auxiliary-lagrangian-bound]: paper/sections/singular_endpoint.tex#L1659
[eq:graphon-lagrangian-bound]: paper/sections/singular_endpoint.tex#L1782
[eq:graphon-stationarity]: paper/sections/singular_endpoint.tex#L94
[eq:block-stationarity]: paper/sections/singular_endpoint.tex#L122
[sec:lean-formalization]: paper/sections/lean.tex#L1
