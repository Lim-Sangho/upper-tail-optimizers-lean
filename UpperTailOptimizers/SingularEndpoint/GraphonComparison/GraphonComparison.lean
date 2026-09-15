import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.GamRVal
import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.DistributionFinal
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.FactorTail

/-!
# The calibration interface of `lem:graphon-lagrangian-bound` (Section 5, `paper/sections/singular_graphon_comparison.tex`)

`lem:graphon-lagrangian-bound` is where the two halves of Section 5
meet.  The **law layer** (`SingularEndpoint/Distribution*.lean`) speaks of a probability measure `ν` on
the law interval `[0,2]`; the **Factor layer** (`SingularEndpoint/Factor*.lean`) speaks of a
function `f` on `[0,1]` with `W = f ⊗ f + E`.  The lemma joins them through the phrase "let
`ν` be the distribution of the values of `f`", i.e. `ν = f_#λ` (`sec:auxiliary-lagrangian`).
This file builds that join and carries it as far as the law part of the master estimate.

## Paper results realised

* the phrase "let `ν` be the distribution of the values of `f`" of
  `lem:graphon-lagrangian-bound` — `comparisonDistribution` and the transport lemmas below;
* the exact decomposition at the start of the proof of **`lem:graphon-lagrangian-bound`**: the
  identity `𝒥_h(ν_h) = I_{p_h}(W_h)` (`comparison_distributionJ_distributionMeasure`) and the
  splitting of the cost difference into the law term `(P)` and one residual entropy integral
  (`comparison_splitting`);
* the law half of **`eq:graphon-lagrangian-bound`** — `exists_comparison_gap`, which is
  `eq:graphon-lagrangian-bound` with the law part `(P)` fully estimated by
  `lem:auxiliary-lagrangian-bound` (in its closed-window form `exists_distributionGap_window`)
  and the residual entropy left as an explicit integral.

## What is done elsewhere

This file stops at the law half.  `exists_comparison_gap` carries the residual entropy
integral

  `∫∫ {J_{p_h}(W) - J̃_{p_h}(f ⊗ f)}`

on its left-hand side rather than the paper's `C_{d,ρ}⁻¹‖E‖₂²`, and retains the linearised
`η_hΔ_h(ν)` in place of the paper's `μ_h{t(H,W) - r_h^m}` — the graph-free Lagrangian used throughout the
`SingularEndpoint` layer (see the module docstring of `SingularEndpoint/AuxiliaryLagrangian/DistributionFinal.lean`).  Estimating that
integral is the rest of the paper's proof, over the central square, the mixed rectangles and
the tail–tail square.  The central square — strong convexity, the `𝓜_h'` term (divided by
`Q_h` in each variable) and the orthogonality term — is `SingularEndpoint/GraphonComparison/GraphonComparisonMain.lean`
(`comparisonMain_exists_central_bound`); the mixed rectangles and the tail–tail square, where the
row is collapsed to its average, pinned by the orthogonality `eq:rank-one-orthogonality` and
compared by Jensen, are `SingularEndpoint/GraphonComparison/RowJensen.lean` (`rowJensen_exists_mixed`,
`rowJensen_exists_tailSq`).  `SingularEndpoint/GraphonComparison/GraphonComparisonMaster.lean` adds
the three at a common window radius, giving a closed-window form of
`eq:graphon-lagrangian-bound` as `exists_comparison_master`; the paper-form statement is
`graphon_lagrangian_bound` (`SingularEndpoint/GraphonComparison/GraphonLagrangianBound.lean`).

The two hypotheses of `exists_comparison_gap` correspond to two clauses of the paper's
`eq:graphon-comparison-estimates`.
The first, `|{x : f(x) ∉ 𝓝_ρ}| ≤ Kh⁴` (the clause `ν(𝒯_ρ) ≤ C_{d,ρ}h⁴`, for the closed window),
is supplied along the family by `family_factor_tail_mass`
(`SingularEndpoint/LocalizationRankOne/FactorTail.lean`) in *exactly* this form.  The second, `|∫f^d - q_h| ≤ Kh⁴`, is
sharper than the paper's clause `|Δ_h(ν)| ≤ C_dh²`; it is
`factorTail_abs_qVal_sub_le`, whose family-level instantiation is `family_factor_clause`
(`SingularEndpoint/LocalizationRankOne/LdSharp.lean`), built on `family_ld_sharp` = the sharp `∫W^d` bound.

## Contents

* `comparisonDistribution` — `ν = f_*(unitμ)`, with `comparison_isProbabilityMeasure`,
  `comparison_distribution_compl_Icc` (it is carried by `[0,2]`), `comparison_preimage_Icc`,
  `comparison_preimage_diff`, `comparison_distribution_diff`;
* `comparison_integral`, `comparison_setIntegral` — the change of variables, and its four
  instances `comparison_distribution_moment`, `comparison_distribution_window`, `comparison_distribution_tail`,
  `comparison_distributionJ`/`comparison_distributionJ_gmu`;
* `comparison_integrable_rankOne` — integrability of `J̃_{p_h}(f ⊗ f)` over `gμ`;
* `comparison_distributionJ_distributionMeasure` — `𝒥_h(ν_h) = I_{p_h}(W_h)`;
* `comparison_splitting` — the exact cost splitting;
* `exists_comparison_gap` — the law half of `eq:graphon-lagrangian-bound`;
* `comparison_exists_apriori_factor` — the non-vacuity check for its hypotheses;
* `comparison_measurable_JpTildeH`, `comparison_measurable_PsiT` — measurability of the
  displaced continued entropy `J̃_{p_h}` and of the dual potential `Ψ_h`, shared with
  `SingularEndpoint/GraphonComparison/RowJensen.lean` and `SingularEndpoint/GraphonComparison/GraphonComparisonMain.lean`.
-/

namespace UpperTailOptimizers

open MeasureTheory

variable {d : ℕ}

/-! ## The law of the rank-one factor

`lem:graphon-lagrangian-bound` writes "let `ν` be the distribution of the values of `f`", i.e.
the pushforward `ν = f_#λ` of `sec:auxiliary-lagrangian`.  Since `unitμ` is a probability
measure and `f` is measurable, the pushforward is a probability measure, and the pointwise
bounds `0 ≤ f ≤ 2` of `lem:localization-rank-one` put it on the law interval — the
two standing hypotheses of every statement of the law layer. -/

/-- **`ν`, the law of the rank-one factor `f`** under the uniform measure on `[0,1]`.

Defined for an arbitrary `f : ℝ → ℝ`; the hypotheses that make it the law layer's object —
measurability and `0 ≤ f ≤ 2` — are carried by the lemmas, not by the definition, so that it
applies verbatim to `FactorDecomp.f` (whose `meas_f`, `f_nonneg`, `f_bdd` fields supply them)
and to any other factor. -/
noncomputable def comparisonDistribution (f : ℝ → ℝ) : Measure ℝ := Measure.map f unitμ

/-- The law of `f` is a probability measure, `unitμ` being one. -/
theorem comparison_isProbabilityMeasure {f : ℝ → ℝ} (hf : Measurable f) :
    IsProbabilityMeasure (comparisonDistribution f) :=
  Measure.isProbabilityMeasure_map hf.aemeasurable

/-- A factor valued in `[0,2]` has full preimage of the law interval. -/
theorem comparison_preimage_Icc {f : ℝ → ℝ} (hnn : ∀ x, 0 ≤ f x) (hbd : ∀ x, f x ≤ 2) :
    f ⁻¹' Set.Icc (0 : ℝ) 2 = Set.univ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_univ, iff_true]
  exact ⟨hnn x, hbd x⟩

/-- **The law is carried by the law interval `[0,2]`**, which is the admissibility
hypothesis `ν ([0,2])ᶜ = 0` of every statement of the law layer. -/
theorem comparison_distribution_compl_Icc {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hbd : ∀ x, f x ≤ 2) : comparisonDistribution f (Set.Icc (0 : ℝ) 2)ᶜ = 0 := by
  rw [comparisonDistribution, Measure.map_apply hf measurableSet_Icc.compl, Set.preimage_compl,
    comparison_preimage_Icc hnn hbd, Set.compl_univ, measure_empty]

/-- The preimage of a tail `[0,2] ∖ s` of the law interval is the plain complement
`{x : f(x) ∉ s}` — the `[0,2]` half being vacuous for a factor valued in `[0,2]`.  This is what
identifies the law layer's `ν(T_ρ)` with `λ(Ω_ρ^c)` of the proof of
`lem:graphon-lagrangian-bound` (here for the closed window). -/
theorem comparison_preimage_diff {f : ℝ → ℝ} (hnn : ∀ x, 0 ≤ f x) (hbd : ∀ x, f x ≤ 2)
    (s : Set ℝ) : f ⁻¹' (Set.Icc (0 : ℝ) 2 \ s) = {x | f x ∉ s} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_Icc, Set.mem_ofPred_eq]
  exact ⟨fun hx => hx.2, fun hx => ⟨⟨hnn x, hbd x⟩, hx⟩⟩

/-- **`ν(T_ρ) = |G_ρ^c|`**: the tail mass of the law is the measure of the set where `f` leaves
the window. -/
theorem comparison_distribution_diff {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hbd : ∀ x, f x ≤ 2) {s : Set ℝ} (hs : MeasurableSet s) :
    comparisonDistribution f (Set.Icc (0 : ℝ) 2 \ s) = unitμ {x | f x ∉ s} := by
  rw [comparisonDistribution, Measure.map_apply hf (measurableSet_Icc.diff hs),
    comparison_preimage_diff hnn hbd s]

/-! ## The change of variables -/

/-- **The change of variables** `∫g dν = ∫g(f(x)) dx`.  `MeasureTheory.integral_map` needs only
measurability of `g`; no integrability hypothesis is involved, because both sides are the
junk value `0` when the integrand fails to be integrable. -/
theorem comparison_integral {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    ∫ x, g x ∂(comparisonDistribution f) = ∫ x, g (f x) ∂unitμ :=
  integral_map hf.aemeasurable hg.aestronglyMeasurable

/-- **The change of variables on a set**, `∫_s g dν = ∫_{f⁻¹s} g(f(x)) dx`. -/
theorem comparison_setIntegral {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(comparisonDistribution f) = ∫ x in f ⁻¹' s, g (f x) ∂unitμ :=
  setIntegral_map hs hg.aestronglyMeasurable hf.aemeasurable

/-! ## Measurability of the law integrands

The law layer integrates four functions against `ν`: `x^d`, `Q_h(x)²`, `Ψ_h(x)` and
`J̃_{p_h}(xy)`.  The change of variables needs each of them to be measurable *on all of `ℝ`*,
not merely continuous on `[0,2]`, so the four lemmas below build that from
`Graphon.measurable_Jp`.  The only non-formal step is `Γ̃_d`, which is defined by a case split
at `1`. -/

private theorem measurable_GamTilde (d : ℕ) : Measurable (GamTilde d) := by
  have hq : Measurable fun z : ℝ => Gam d 1 + (z - 1) ^ 2 :=
    measurable_const.add ((measurable_id.sub measurable_const).pow_const 2)
  have hm : Measurable fun z : ℝ => if z ≤ 1 then Gam d z else Gam d 1 + (z - 1) ^ 2 :=
    Measurable.ite (measurableSet_le measurable_id measurable_const)
      (measurable_Gam d) hq
  exact hm

private theorem comparison_measurable_JpTilde (d : ℕ) : Measurable (JpTilde d) := by
  have hm : Measurable fun u : ℝ =>
      Jp (pStar d) (rStar d) + betaD d * (u ^ d - rStar d ^ d) + GamTilde d u :=
    (measurable_const.add
        (((measurable_id.pow_const d).sub measurable_const).const_mul _)).add
      (measurable_GamTilde d)
  exact hm

theorem comparison_measurable_JpTildeH (B : KKTFamily d) (h : ℝ) :
    Measurable (B.JpTildeH h) := by
  have hm : Measurable fun u : ℝ => JpTilde d u + (ell (B.p h) - ell (pStar d)) * u
      + (Jp (B.p h) 0 - Jp (pStar d) 0) :=
    ((comparison_measurable_JpTilde d).add (measurable_id.const_mul _)).add measurable_const
  exact hm

theorem comparison_measurable_PsiT (B : KKTFamily d) (h : ℝ) :
    Measurable (B.PsiT h) := by
  have hJ := comparison_measurable_JpTildeH B h
  have h1 : Measurable fun x : ℝ => B.JpTildeH h (x * B.sVal h) :=
    hJ.comp (measurable_id.mul_const _)
  have h2 : Measurable fun x : ℝ => B.JpTildeH h (x * B.tVal h) :=
    hJ.comp (measurable_id.mul_const _)
  have hm : Measurable fun x : ℝ =>
      2 * (B.alph h * B.JpTildeH h (x * B.sVal h)
          + (1 - B.alph h) * B.JpTildeH h (x * B.tVal h))
        - B.etaVal h * x ^ d - B.kappaVal h :=
    ((((h1.const_mul _).add (h2.const_mul _)).const_mul 2).sub
      ((measurable_id.pow_const d).const_mul _)).sub measurable_const
  exact hm

private theorem comparison_measurable_Qh_sq (B : KKTFamily d) (h : ℝ) :
    Measurable fun x : ℝ => B.Qh h x ^ 2 := by
  have hm : Measurable fun x : ℝ => ((x - B.sVal h) * (x - B.tVal h)) ^ 2 :=
    ((measurable_id.sub measurable_const).mul (measurable_id.sub measurable_const)).pow_const 2
  exact hm

/-! ## The four transported integrals -/

/-- **The `d`-th moment of the law is `∫f^d`** — the law layer's `m_d(ν)` is the Factor
layer's `q = ∫f^d`, so that `Δ_h(ν) = ∫f^d - q_h`. -/
theorem comparison_distribution_moment {f : ℝ → ℝ} (hf : Measurable f) (d : ℕ) :
    ∫ x, x ^ d ∂(comparisonDistribution f) = ∫ x, f x ^ d ∂unitμ := by
  have hg : Measurable fun x : ℝ => x ^ d := measurable_id.pow_const d
  exact comparison_integral hf hg

/-- **The window term `A_ρ = ∫_{𝓝_ρ} Q_h² dν`** is the integral of `Q_h(f(x))²` over the
central set `G_ρ = {x : f(x) ∈ 𝓝_ρ}`. -/
theorem comparison_distribution_window {f : ℝ → ℝ} (hf : Measurable f) (B : KKTFamily d)
    (hh ρ : ℝ) :
    ∫ x in centralWindow d ρ, B.Qh hh x ^ 2 ∂(comparisonDistribution f)
      = ∫ x in {x | f x ∈ centralWindow d ρ}, B.Qh hh (f x) ^ 2 ∂unitμ := by
  have hres := comparison_setIntegral hf (comparison_measurable_Qh_sq B hh)
    (measurableSet_centralWindow d ρ)
  exact hres

/-- **The tail term `∫_{T_ρ} Ψ_h dν`** is the integral of `Ψ_h(f(x))` over the rare rows
`G_ρ^c = {x : f(x) ∉ 𝓝_ρ}` — the shape in which the tail bound `Ψ_h ≥ b_ρ` of
`lem:first-variation-bound` is integrated (`setIntegral_PsiT_ge`, `SingularEndpoint/GraphonComparison/RowJensen.lean`). -/
theorem comparison_distribution_tail {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hbd : ∀ x, f x ≤ 2) (B : KKTFamily d) (hh ρ : ℝ) :
    ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.PsiT hh x ∂(comparisonDistribution f)
      = ∫ x in {x | f x ∉ centralWindow d ρ}, B.PsiT hh (f x) ∂unitμ := by
  rw [comparison_setIntegral hf (comparison_measurable_PsiT B hh)
      (measurableSet_Icc.diff (measurableSet_centralWindow d ρ)),
    comparison_preimage_diff hnn hbd]

/-- **The law functional at the law of `f`** is the continued entropy of the rank-one
graphon `f ⊗ f`, written as an iterated integral.

Both integrations are `MeasureTheory.integral_map`; the outer one needs the inner integral to
be measurable in `x`, which is `MeasureTheory.StronglyMeasurable.integral_prod_right'` applied
to the jointly measurable `(x,y) ↦ J̃_{p_h}(xy)`. -/
theorem comparison_distributionJ (B : KKTFamily d) (hh : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    B.distributionJ hh (comparisonDistribution f)
      = ∫ x, ∫ y, B.JpTildeH hh (f x * f y) ∂unitμ ∂unitμ := by
  have : IsProbabilityMeasure (comparisonDistribution f) := comparison_isProbabilityMeasure hf
  have hJ := comparison_measurable_JpTildeH B hh
  have hjoint : Measurable fun z : ℝ × ℝ => B.JpTildeH hh (z.1 * z.2) :=
    hJ.comp (measurable_fst.mul measurable_snd)
  have houter : StronglyMeasurable
      fun x : ℝ => ∫ y, B.JpTildeH hh (x * y) ∂(comparisonDistribution f) :=
    hjoint.stronglyMeasurable.integral_prod_right'
  have hinner : ∀ x : ℝ, ∫ y, B.JpTildeH hh (x * y) ∂(comparisonDistribution f)
      = ∫ y, B.JpTildeH hh (x * f y) ∂unitμ := by
    intro x
    have hmul : Measurable fun y : ℝ => x * y := measurable_const.mul measurable_id
    exact comparison_integral hf (hJ.comp hmul)
  calc B.distributionJ hh (comparisonDistribution f)
      = ∫ x, (∫ y, B.JpTildeH hh (x * y) ∂(comparisonDistribution f)) ∂(comparisonDistribution f) := rfl
    _ = ∫ x, (∫ y, B.JpTildeH hh (f x * y) ∂(comparisonDistribution f)) ∂unitμ :=
        integral_map hf.aemeasurable houter.aestronglyMeasurable
    _ = ∫ x, ∫ y, B.JpTildeH hh (f x * f y) ∂unitμ ∂unitμ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hinner (f x))

/-- **`J̃_{p_h}(f ⊗ f)` is integrable over `gμ`.**  The factor is valued in `[0,2]`, so the
product is valued in `[0,4]`, which is where the continuation `J̃` is continuous
(`continuousOn_JpTilde`); the bound is then compactness. -/
theorem comparison_integrable_rankOne (hd : 2 ≤ d) (B : KKTFamily d) (hh : ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x) (hbd : ∀ x, f x ≤ 2) :
    Integrable (fun z : ℝ × ℝ => B.JpTildeH hh (f z.1 * f z.2)) gμ := by
  have hcont : ContinuousOn (B.JpTildeH hh) (Set.Icc 0 4) := by
    have hc : ContinuousOn (fun z : ℝ => JpTilde d z
        + (ell (B.p hh) - ell (pStar d)) * z + (Jp (B.p hh) 0 - Jp (pStar d) 0))
        (Set.Icc (0 : ℝ) 4) :=
      ((continuousOn_JpTilde hd).add (continuousOn_const.mul continuous_id.continuousOn)).add
        continuousOn_const
    exact hc
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hmeas : Measurable fun z : ℝ × ℝ => B.JpTildeH hh (f z.1 * f z.2) :=
    (comparison_measurable_JpTildeH B hh).comp
      ((hf.comp measurable_fst).mul (hf.comp measurable_snd))
  refine Integrable.of_bound hmeas.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun z => ?_)
  refine hC _ ⟨mul_nonneg (hnn _) (hnn _), ?_⟩
  nlinarith [hnn z.1, hnn z.2, hbd z.1, hbd z.2]

/-- **The law functional at the law of `f`, as a graphon integral**:
`𝒥_h(ν) = ∫∫ J̃_{p_h}(f(x)f(y))`.  Fubini on the probability square. -/
theorem comparison_distributionJ_gmu (hd : 2 ≤ d) (B : KKTFamily d) (hh : ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x) (hbd : ∀ x, f x ≤ 2) :
    B.distributionJ hh (comparisonDistribution f) = ∫ z, B.JpTildeH hh (f z.1 * f z.2) ∂gμ := by
  have hint := comparison_integrable_rankOne hd B hh hf hnn hbd
  rw [comparison_distributionJ B hh hf, show gμ = unitμ.prod unitμ from rfl, integral_prod _ hint]

/-! ## The splitting at the start of the proof -/

/-- **`I_{p_h}(W_h) = 𝒥_h(ν_h)`**, the identity `𝒥_h(ν_h) = I_{p_h}(W_h)` stated before the
exact decomposition in the proof of `lem:graphon-lagrangian-bound`: the family graphon's cost is
the law functional at the two-atom candidate law.

Both sides are already in closed form — `distributionJ_distributionMeasure` gives `(η_hq_h + κ_h)/2` and
`graphon_Ip_eq_IpScalar` gives `I_{p_h}(W_h) = IpScalar`, so the content is exactly
the closed form `κ_h = 2I_{p_h}(W_h) - η_hq_h`.  The paper fixes `κ_h` only
implicitly, by `Ψ_h(s_h) = 0` in `eq:first-variation`; the closed form is a one-line consequence it does
not display. -/
theorem comparison_distributionJ_distributionMeasure (hd : 2 ≤ d) (B : KKTFamily d) {hh : ℝ}
    (hb : |hh| < B.h₀) :
    B.distributionJ hh (B.distributionMeasure hh) = (B.graphon hb).Ip (B.p hh) := by
  rw [KKTFamily.graphon_Ip_eq_IpScalar hb, KKTFamily.distributionJ_distributionMeasure hd B hb,
    KKTFamily.kappaVal_eq hd hb]
  ring

/-- **The exact splitting of the Lagrangian gap**, the cost part of the exact decomposition in
the proof of `lem:graphon-lagrangian-bound` (without the `μ_h`-terms):

`I_{p_h}(W) - I_{p_h}(W_h) = {𝒥_h(ν) - 𝒥_h(ν_h)} + ∫∫{J_{p_h}(W) - J̃_{p_h}(f ⊗ f)}`.

No smallness and no inequality: this is an identity for every graphon `W` and every measurable
factor `f` valued in `[0,2]`.  The paper splits the second summand further over the central
square, the mixed rectangles and the tail–tail square; that split, and its estimation, is what
this file does not do. -/
theorem comparison_splitting (hd : 2 ≤ d) (B : KKTFamily d) {hh : ℝ} (hb : |hh| < B.h₀)
    (W : Graphon) {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x) (hbd : ∀ x, f x ≤ 2) :
    W.Ip (B.p hh) - (B.graphon hb).Ip (B.p hh)
      = (B.distributionJ hh (comparisonDistribution f) - B.distributionJ hh (B.distributionMeasure hh))
        + ∫ z, (Jp (B.p hh) (W.toFun z.1 z.2) - B.JpTildeH hh (f z.1 * f z.2)) ∂gμ := by
  have hp := B.p_mem hh hb
  have hIW : Integrable (fun z : ℝ × ℝ => Jp (B.p hh) (W.toFun z.1 z.2)) gμ :=
    W.integrable_comp (measurable_Jp _) (continuousOn_Jp_Icc hp.1 hp.2)
  have hIf := comparison_integrable_rankOne hd B hh hf hnn hbd
  have hIpW : W.Ip (B.p hh) = ∫ z, Jp (B.p hh) (W.toFun z.1 z.2) ∂gμ := rfl
  rw [hIpW, integral_sub hIW hIf, comparison_distributionJ_gmu hd B hh hf hnn hbd,
    comparison_distributionJ_distributionMeasure hd B hb]
  ring

/-! ## The law half of `eq:graphon-lagrangian-bound` -/

/-- **`eq:graphon-lagrangian-bound`, law half.**  For each `K ≥ 1` there are a window
radius `ρ > 0`, a constant `M > 0` and a threshold `δ₀ > 0` such that for `0 < h < δ₀` with
`h ≤ 1` inside the family window, every graphon `W` and every measurable `f` valued in `[0,2]`
satisfying the a-priori bounds (cf. `eq:graphon-comparison-estimates`)

* `|{x : f(x) ∉ 𝓝_ρ}| ≤ Kh⁴`  (`eq:factor-tail-mass`, i.e. `family_factor_tail_mass`), and
* `|∫f^d - q_h| ≤ Kh⁴`  (a sharper form of the moment clause `|q(f) - q_h| ≤ C_dh²` of
  `lem:localization-rank-one`),

satisfy

`M⁻¹[A_ρ + ε] + η_hΔ - MΔ² + ∫∫{J_{p_h}(W) - J̃_{p_h}(f ⊗ f)} ≤ I_{p_h}(W) - I_{p_h}(W_h)`

with `A_ρ = ∫_{G_ρ}Q_h(f)²`, `ε = |G_ρ^c|` and `Δ = ∫f^d - q_h`.

Comparing with `eq:graphon-lagrangian-bound`: the law terms `C_{d,ρ}⁻¹[A_{h,ρ}(ν) + ν(𝒯_ρ)]` and
`-C_{d,m}Δ²` are here (with one constant `M`), the Lagrangian term is the layer's graph-free
`η_hΔ` in place of `μ_h{t(H,W) - r_h^m}`, and the residual `C_{d,ρ}⁻¹‖E‖₂²` has **not** been
extracted: it is still carried as the entropy integral, whose estimation is the rest of the
paper's proof.  Nothing
about `W` beyond being a graphon is used, and `f` is not required to solve the Factor
equation — the coupling between the two enters only when that integral is estimated. -/
theorem exists_comparison_gap (hd : 2 ≤ d) (B : KKTFamily d) {K : ℝ} (hK : 1 ≤ K) :
    ∃ ρ > 0, ∃ M : ℝ, 0 < M ∧ ∃ δ₀ > 0,
      ∀ (h : ℝ) (hb : |h| < B.h₀), 0 < h → h < δ₀ → h ≤ 1 →
      ∀ (W : Graphon) (f : ℝ → ℝ), Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 2) →
        (unitμ {x | f x ∉ centralWindow d ρ}).toReal ≤ K * h ^ 4 →
        |(∫ x, f x ^ d ∂unitμ) - B.qVal h| ≤ K * h ^ 4 →
          M⁻¹ * ((∫ x in {x | f x ∈ centralWindow d ρ}, B.Qh h (f x) ^ 2 ∂unitμ)
                  + (unitμ {x | f x ∉ centralWindow d ρ}).toReal)
              + B.etaVal h * ((∫ x, f x ^ d ∂unitμ) - B.qVal h)
              - M * ((∫ x, f x ^ d ∂unitμ) - B.qVal h) ^ 2
              + ∫ z, (Jp (B.p h) (W.toFun z.1 z.2) - B.JpTildeH h (f z.1 * f z.2)) ∂gμ
            ≤ W.Ip (B.p h) - (B.graphon hb).Ip (B.p h) := by
  obtain ⟨ρ, hρ0, M, hM0, δ₀, hδ0, hgap⟩ := KKTFamily.exists_distributionGap_window hd B hK
  refine ⟨ρ, hρ0, M, hM0, δ₀, hδ0, ?_⟩
  intro h hb hh0 hhδ hh1 W f hf hnn hbd htail hmom
  have htail' :
      (comparisonDistribution f (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal ≤ K * h ^ 4 := by
    rw [comparison_distribution_diff hf hnn hbd (measurableSet_centralWindow d ρ)]
    exact htail
  have hmom' : |(∫ x, x ^ d ∂(comparisonDistribution f)) - B.qVal h| ≤ K * h ^ 4 := by
    rw [comparison_distribution_moment hf d]
    exact hmom
  have key := hgap h hh0 hhδ hh1 hb (comparisonDistribution f) (comparison_isProbabilityMeasure hf)
    (comparison_distribution_compl_Icc hf hnn hbd) htail' hmom'
  rw [comparison_distribution_window hf B h ρ,
    comparison_distribution_diff hf hnn hbd (measurableSet_centralWindow d ρ),
    comparison_distribution_moment hf d] at key
  have hsplit := comparison_splitting hd B hb W hf hnn hbd
  linarith [key, hsplit]

/-! ## Non-vacuity

`exists_comparison_gap` quantifies over the factors `f` satisfying `eq:graphon-comparison-estimates`,
so it would be trivially true if no such factor existed.  It does: the constant factor
`f ≡ q_h^{1/d}` has `Δ_h(ν) = 0` exactly and an **empty** tail set, because `q_h → q_0 = u_*^d`
(`qVal_zero`, `hasDerivAt_qVal_zero`) puts its `d`-th root inside every window `𝓝_ρ` once `h` is
small.  Both a-priori bounds then hold for every `K ≥ 0` and every `h`. -/

/-- **The a-priori hypotheses of `exists_comparison_gap` are satisfiable.**  For every window
radius `ρ > 0` there is a threshold below which a measurable factor `f : ℝ → [0,2]` exists with
an empty tail set `{x : f(x) ∉ 𝓝_ρ}` and with `∫f^d = q_h` on the nose.

The witness is the constant `q_h^{1/d}`; the only analytic input is the continuity of `q_h` at
the singular endpoint together with `q_0 = u_*^d`.  Nothing here claims such an `f` comes from a Factor
decomposition — the point is only that the hypothesis set of `exists_comparison_gap` is not
empty. -/
theorem comparison_exists_apriori_factor (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ → |h| < B.h₀ →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 2) ∧
        {x : ℝ | f x ∉ centralWindow d ρ} = ∅ ∧ (∫ x, f x ^ d ∂unitμ) = B.qVal h := by
  have hdne : d ≠ 0 := by omega
  have hroot : ContinuousAt (fun t : ℝ => t ^ ((d : ℝ)⁻¹)) (B.qVal 0) :=
    Real.continuousAt_rpow_const _ _ (Or.inr (by positivity))
  have hqc : ContinuousAt B.qVal 0 := (hasDerivAt_qVal_zero B).continuousAt
  have hc : ContinuousAt (fun t : ℝ => (B.qVal t) ^ ((d : ℝ)⁻¹)) 0 := hroot.comp hqc
  have hval : (B.qVal 0) ^ ((d : ℝ)⁻¹) = uStar d := by
    rw [KKTFamily.qVal_zero B]
    exact Real.pow_rpow_inv_natCast (uStar_nonneg hd) hdne
  have hev : ∀ᶠ t : ℝ in nhds (0 : ℝ), |(B.qVal t) ^ ((d : ℝ)⁻¹) - uStar d| < min ρ 1 := by
    have h := Metric.tendsto_nhds.mp hc (min ρ 1) (lt_min hρ one_pos)
    simpa [Real.dist_eq, hval] using h
  obtain ⟨δ, hδ, hprop⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, ?_⟩
  intro h hh0 hhδ hhb
  have hdist : dist h (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
    exact hhδ
  have habs := hprop hdist
  have hin : |(B.qVal h) ^ ((d : ℝ)⁻¹) - uStar d| < ρ := lt_of_lt_of_le habs (min_le_left _ _)
  have hone : |(B.qVal h) ^ ((d : ℝ)⁻¹) - uStar d| < 1 := lt_of_lt_of_le habs (min_le_right _ _)
  refine ⟨fun _ => (B.qVal h) ^ ((d : ℝ)⁻¹), measurable_const,
    fun _ => Real.rpow_nonneg (KKTFamily.qVal_pos hhb).le _, fun _ => ?_, ?_, ?_⟩
  · have hu := uStar_lt_one hd
    have hlt := abs_lt.mp hone
    linarith [hlt.2]
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact (factorTail_mem_centralWindow_iff d ρ _).mpr hin.le
  · rw [integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    exact Real.rpow_inv_natCast_pow (KKTFamily.qVal_pos hhb).le hdne

end UpperTailOptimizers
