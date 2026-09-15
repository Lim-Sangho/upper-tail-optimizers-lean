import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.KernelOp

/-!
# The `L⁴` bridge: raw-function estimates ↦ a fixed point (Section 5)

The existence of the decomposition in `lem:localization-rank-one` is obtained by a **normalised contraction** rather than
by the paper's variational argument: the paper maximises `Q_W` over the unit ball of
`L^{d/(d-1)}` and quotes weak compactness, which this Mathlib cannot supply (no reflexivity
for normed spaces, no `(L^p)* = L^q`).  Banach's fixed-point theorem replaces it, and Banach
needs a **complete metric space**.

`SingularEndpoint/LocalizationRankOne/KernelOp.lean` deliberately works with raw functions `ℝ → ℝ` and the *functional*
`Lnorm μ p h = (∫ |h|^p)^{1/p}`, which is only a pseudometric: two functions equal a.e. have
`Lnorm` distance zero without being equal.  This file is the crossing into
`MeasureTheory.Lp ℝ 4 unitμ` and back:

* the dictionary between `Lnorm unitμ 4` and the `Lp` norm and distance, in both directions;
* a **pointwise** (not a.e.) representative in `[0, M]` for a class that satisfies
  `0 ≤ F ≤ M` a.e. — which is what `SingularEndpoint/LocalizationRankOne/Factor.lean`'s `FactorDecomp` needs, since its
  fields `f_nonneg` and `f_bdd` are universally quantified over *every* point;
* the invariant set `lpBridgeSet M = {0 ≤ F ≤ M, ∫ F = 1}`: nonempty, convex, closed, and
  hence complete;
* a one-line packaging of Banach's theorem on that set, with its uniqueness companion (a
  uniqueness statement that `lem:localization-rank-one` itself does not make).

**Nothing about the Factor map itself is proved here.**  The three contraction estimates
(invariance, contraction, and the closeness bound `eq:rank-one-reduction-bounds`) are not in
this file, nor is `eq:rank-one-orthogonality`; this file only guarantees that, once
those estimates are available as `Lnorm` inequalities on raw functions, they can be fed to
`lpBridgeSet_exists_fixedPoint` and read back as a pointwise-bounded measurable factor.  So
no `eq:…` label of the paper is realised here; the file is the metric-space scaffolding for
the Lean construction of the decomposition in `lem:localization-rank-one`.

## Contents

* `lpBridgeFactOneLeFour` — the `Fact (1 ≤ 4)` instance that Mathlib's `Lp` normed-space
  instances need at the exponent `4` (Mathlib ships it only for `1`, `2` and `∞`);
* `lpBridge_Lnorm_congr`, `lpBridge_Lnorm_one` — `Lnorm` respects a.e. equality, and
  `Lnorm μ 1 h = ∫ |h|`;
* `lpBridge_toReal_eLpNorm`, `lpBridge_toReal_eLpNorm_four` — `(eLpNorm f p μ).toReal =
  Lnorm μ p.toReal f`, the one computation that connects the two vocabularies;
* `lpBridge_memLp`, `lpBridge_norm_toLp`, `lpBridge_dist_toLp` — raw ↦ `Lp`;
* `lpBridge_dist_eq` — `Lp` ↦ raw;
* `lpBridge_exists_pointwise_repr` — the truncated representative `max 0 (min M ·)`;
* `lpBridgeSet`, `mem_lpBridgeSet_iff`, `lpBridgeSet_ae`, `lpBridgeSet_nonempty`,
  `lpBridgeSet_isClosed`, `lpBridgeSet_isComplete`, and the two-way
  pair `lpBridgeSet_exists_repr` / `toLp_mem_lpBridgeSet`;
* `lpBridge_dist_integral_le`, `lpBridge_continuous_integral` — the unit-mass constraint is
  closed because `F ↦ ∫ F` is `1`-Lipschitz on `L⁴` of a probability space;
* `lpBridge_exists_fixedPoint`, `lpBridge_fixedPoint_unique`,
  `lpBridge_existsUnique_fixedPoint`, `lpBridgeSet_exists_fixedPoint` — Banach.
-/

namespace UpperTailOptimizers

open MeasureTheory

open scoped ENNReal NNReal

/-- Mathlib's `Lp` normed-group, normed-space and completeness instances are all gated on
`Fact (1 ≤ p)`, and Mathlib provides that `Fact` only for `p = 1`, `2`, `∞`.  The normalised
contraction construction runs at `p = 4`, so the instance has to be declared here.  It is named
(rather than left anonymous) so that a second declaration of the same `Fact` elsewhere in the
development cannot clash with it. -/
instance lpBridgeFactOneLeFour : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-! ## `Lnorm` versus `eLpNorm`

`Lnorm` (`SingularEndpoint/LocalizationRankOne/KernelOp.lean`) is a Bochner integral of a real power; `eLpNorm` is an
`ℝ≥0∞`-valued lower integral.  The two agree after `ENNReal.toReal`, with no integrability
hypothesis: when `f ∉ L^p` both sides are `0` (the Bochner integral of a non-integrable
function is `0`, and `(∞).toReal = 0`).
-/

/-- `Lnorm` only sees the a.e. class of its argument. -/
theorem lpBridge_Lnorm_congr {α : Type*} [MeasurableSpace α] {μ : Measure α} (p : ℝ)
    {f g : α → ℝ} (h : f =ᵐ[μ] g) : Lnorm μ p f = Lnorm μ p g := by
  unfold Lnorm
  refine congrArg (· ^ (1 / p)) (integral_congr_ae ?_)
  filter_upwards [h] with x hx
  rw [hx]

/-- `Lnorm μ 1 h = ∫ |h|`: the exponent-`1` case, used to compare the mass functional with
the `L⁴` distance. -/
theorem lpBridge_Lnorm_one {α : Type*} [MeasurableSpace α] {μ : Measure α} (h : α → ℝ) :
    Lnorm μ 1 h = ∫ x, |h x| ∂μ := by
  simp [Lnorm]

/-- **The dictionary.**  `(eLpNorm f p μ).toReal = Lnorm μ p.toReal f` for any a.e.-strongly
measurable real `f` and any finite nonzero exponent.

The proof is `integral_eq_lintegral_of_nonneg_ae` applied to `|f|^p`, together with
`‖f x‖ₑ ^ p = ENNReal.ofReal (|f x|^p)`.  No integrability is assumed: if `f ∉ L^p` both
sides are zero. -/
theorem lpBridge_toReal_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hptop : p ≠ ⊤) {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f p μ).toReal = Lnorm μ p.toReal f := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hcont : Continuous fun t : ℝ => |t| ^ p.toReal :=
    (Real.continuous_rpow_const hpr.le).comp continuous_abs
  have hmeas : AEStronglyMeasurable (fun x => |f x| ^ p.toReal) μ :=
    hcont.comp_aestronglyMeasurable hf
  have hlint : ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ = ∫⁻ x, ENNReal.ofReal (|f x| ^ p.toReal) ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hpr.le]
  have hint : ∫ x, |f x| ^ p.toReal ∂μ = (∫⁻ x, ENNReal.ofReal (|f x| ^ p.toReal) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _) hmeas
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, ← ENNReal.toReal_rpow, hlint, ← hint, Lnorm]

/-- The exponent-`4` case of `lpBridge_toReal_eLpNorm`, at the measure the contraction
construction uses. -/
theorem lpBridge_toReal_eLpNorm_four {f : ℝ → ℝ} (hf : AEStronglyMeasurable f unitμ) :
    (eLpNorm f 4 unitμ).toReal = Lnorm unitμ 4 f := by
  have h := lpBridge_toReal_eLpNorm (μ := unitμ) (p := 4) (by norm_num) (by norm_num) hf
  rwa [show (4 : ℝ≥0∞).toReal = (4 : ℝ) by norm_num] at h

/-! ## Raw functions into `Lp ℝ 4 unitμ` -/

/-- A bounded measurable function on the unit interval is in `L⁴`: the `MemLp` witness that
turns a contraction iterate into an element of `Lp ℝ 4 unitμ`. -/
theorem lpBridge_memLp {f : ℝ → ℝ} (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) :
    MemLp f 4 unitμ :=
  MemLp.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)

/-- The norm of a lifted function is its `Lnorm`. -/
theorem lpBridge_norm_toLp {f : ℝ → ℝ} (hf : MemLp f 4 unitμ) :
    ‖hf.toLp f‖ = Lnorm unitμ 4 f := by
  rw [Lp.norm_toLp, lpBridge_toReal_eLpNorm_four hf.1]

/-- **The distance dictionary.**  The `Lp`-distance of two lifted functions is the `Lnorm`
of their difference: `‖f - g‖₄ = dist (toLp f) (toLp g)`.  This is the identity that lets a
contraction estimate proved with the raw-function vocabulary of `SingularEndpoint/LocalizationRankOne/KernelOp.lean` be
handed to Banach's theorem. -/
theorem lpBridge_dist_toLp {f g : ℝ → ℝ} (hf : MemLp f 4 unitμ) (hg : MemLp g 4 unitμ) :
    dist (hf.toLp f) (hg.toLp g) = Lnorm unitμ 4 (fun x => f x - g x) := by
  rw [dist_eq_norm, ← MemLp.toLp_sub hf hg, lpBridge_norm_toLp (hf.sub hg)]
  rfl

/-- Read back: the `Lp`-distance is the `Lnorm` of the difference of the coercions. -/
theorem lpBridge_dist_eq (F G : Lp ℝ 4 unitμ) :
    dist F G = Lnorm unitμ 4 (fun x => F x - G x) := by
  rw [Lp.dist_def,
    lpBridge_toReal_eLpNorm_four ((Lp.aestronglyMeasurable F).sub (Lp.aestronglyMeasurable G))]
  rfl

/-- **The pointwise representative.**  An element of `Lp ℝ 4 unitμ` which is a.e. between `0`
and `M` has a measurable representative taking values in `[0, M]` at *every* point.

This is what `SingularEndpoint/LocalizationRankOne/Factor.lean` needs: the fields `f_nonneg` and `f_bdd` of
`FactorDecomp` are universally quantified over all `x`, not a.e.  The representative is the
truncation `max 0 (min M (g x))` of a measurable representative `g`; truncation does not move
the a.e. class because the class already lies in `[0, M]`. -/
theorem lpBridge_exists_pointwise_repr {M : ℝ} (hM : 0 ≤ M) {F : Lp ℝ 4 unitμ}
    (h0 : ∀ᵐ x ∂unitμ, 0 ≤ F x) (hle : ∀ᵐ x ∂unitμ, F x ≤ M) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ M) ∧ f =ᵐ[unitμ] F ∧
      ∃ hf : MemLp f 4 unitμ, hf.toLp f = F := by
  have hae := Lp.aestronglyMeasurable F
  have hgmeas : Measurable (hae.mk ⇑F) := hae.measurable_mk
  have hgae : ⇑F =ᵐ[unitμ] hae.mk ⇑F := hae.ae_eq_mk
  have hmeas : Measurable fun x => max 0 (min M (hae.mk (⇑F) x)) :=
    measurable_const.max (measurable_const.min hgmeas)
  have hnn : ∀ x, 0 ≤ max 0 (min M (hae.mk (⇑F) x)) := fun _ => le_max_left _ _
  have hbd : ∀ x, max 0 (min M (hae.mk (⇑F) x)) ≤ M := fun _ => max_le hM (min_le_left _ _)
  have heq : (fun x => max 0 (min M (hae.mk (⇑F) x))) =ᵐ[unitμ] ⇑F := by
    filter_upwards [h0, hle, hgae] with x hx0 hxM hxg
    rw [← hxg, min_eq_right hxM, max_eq_right hx0]
  have hmem : MemLp (fun x => max 0 (min M (hae.mk (⇑F) x))) 4 unitμ :=
    lpBridge_memLp hmeas M fun x => by rw [abs_of_nonneg (hnn x)]; exact hbd x
  exact ⟨_, hmeas, hnn, hbd, heq, hmem,
    ((MemLp.toLp_eq_toLp_iff hmem (Lp.memLp F)).mpr heq).trans (Lp.toLp_coeFn F (Lp.memLp F))⟩

/-! ## The invariant set

The contraction iteration is run on the set of `L⁴` classes that are nonnegative, bounded by a
fixed `M`, and of unit mass.  The first two conditions are order conditions, closed because
`Lp ℝ 4 unitμ` is an ordered topological group; the third is closed because the mass
functional is `1`-Lipschitz.
-/

/-- The constant class of `Lp ℝ 4 unitμ` is a.e. equal to the constant. -/
theorem lpBridge_const_ae (c : ℝ) : ∀ᵐ x ∂unitμ, (Lp.const 4 unitμ c) x = c :=
  Lp.coeFn_const (p := 4) (μ := unitμ) (c := c)

/-- The mass functional is `1`-Lipschitz on `L⁴` of a probability space:
`|∫ F - ∫ G| ≤ ‖F - G‖₄`.  This is Hölder `‖·‖₁ ≤ ‖·‖₄`
(`MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le`) after the triangle inequality. -/
theorem lpBridge_dist_integral_le (F G : Lp ℝ 4 unitμ) :
    |(∫ x, F x ∂unitμ) - ∫ x, G x ∂unitμ| ≤ dist F G := by
  have hF : Integrable (⇑F) unitμ := (Lp.memLp F).integrable (by norm_num)
  have hG : Integrable (⇑G) unitμ := (Lp.memLp G).integrable (by norm_num)
  have hsm : AEStronglyMeasurable (fun x => F x - G x) unitμ :=
    (Lp.aestronglyMeasurable F).sub (Lp.aestronglyMeasurable G)
  have htop : eLpNorm (fun x => F x - G x) 4 unitμ ≠ ⊤ := ((Lp.memLp F).sub (Lp.memLp G)).2.ne
  calc |(∫ x, F x ∂unitμ) - ∫ x, G x ∂unitμ| = |∫ x, (F x - G x) ∂unitμ| := by
        rw [integral_sub hF hG]
    _ ≤ ∫ x, |F x - G x| ∂unitμ := abs_integral_le_integral_abs
    _ = (eLpNorm (fun x => F x - G x) 1 unitμ).toReal := by
        rw [lpBridge_toReal_eLpNorm (μ := unitμ) (p := 1) (by norm_num) (by norm_num) hsm,
          show (1 : ℝ≥0∞).toReal = (1 : ℝ) by norm_num, lpBridge_Lnorm_one]
    _ ≤ (eLpNorm (fun x => F x - G x) 4 unitμ).toReal :=
        ENNReal.toReal_mono htop (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hsm)
    _ = dist F G := by rw [lpBridge_dist_eq]; exact lpBridge_toReal_eLpNorm_four hsm

/-- The mass functional `F ↦ ∫ F` is continuous on `Lp ℝ 4 unitμ`, by
`lpBridge_dist_integral_le`. -/
theorem lpBridge_continuous_integral :
    Continuous fun F : Lp ℝ 4 unitμ => ∫ x, F x ∂unitμ := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun F G => ?_)
  rw [Real.dist_eq, NNReal.coe_one, one_mul]
  exact lpBridge_dist_integral_le F G

/-- The invariant set of the normalised contraction iteration: the `L⁴` classes `F` with
`0 ≤ F ≤ M` and `∫ F = 1`.

The mass constraint is the normalisation `N(φ) = T_W(φ^{d-1}) / ∫ T_W(φ^{d-1})` of the
construction; the two-sided bound is what makes the power map `t ↦ t^{d-1}` Lipschitz
(`abs_pow_sub_pow_le_deg`) and what `SingularEndpoint/LocalizationRankOne/Factor.lean` needs pointwise. -/
def lpBridgeSet (M : ℝ) : Set (Lp ℝ 4 unitμ) :=
  {F | 0 ≤ F} ∩ {F | F ≤ Lp.const 4 unitμ M} ∩ {F | ∫ x, F x ∂unitμ = 1}

/-- Membership in `lpBridgeSet` unfolded. -/
theorem mem_lpBridgeSet_iff {M : ℝ} {F : Lp ℝ 4 unitμ} :
    F ∈ lpBridgeSet M ↔ 0 ≤ F ∧ F ≤ Lp.const 4 unitμ M ∧ ∫ x, F x ∂unitμ = 1 := by
  simp only [lpBridgeSet, Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]

/-- The a.e. form of the two bounds of `lpBridgeSet`, as needed by
`lpBridge_exists_pointwise_repr`. -/
theorem lpBridgeSet_ae {M : ℝ} {F : Lp ℝ 4 unitμ} (hF : F ∈ lpBridgeSet M) :
    (∀ᵐ x ∂unitμ, 0 ≤ F x) ∧ (∀ᵐ x ∂unitμ, F x ≤ M) := by
  rw [mem_lpBridgeSet_iff] at hF
  constructor
  · filter_upwards [(Lp.coeFn_nonneg F).mpr hF.1] with x hx
    exact hx
  · filter_upwards [(Lp.coeFn_le F (Lp.const 4 unitμ M)).mpr hF.2.1, lpBridge_const_ae M]
      with x hx hc
    rw [hc] at hx
    exact hx

/-- `lpBridgeSet M` is nonempty as soon as `1 ≤ M`: it contains the constant `1`, which is
the starting point of the contraction iteration (and its exact fixed point when `W` is
constant). -/
theorem lpBridgeSet_nonempty {M : ℝ} (hM : 1 ≤ M) :
    Lp.const 4 unitμ (1 : ℝ) ∈ lpBridgeSet M := by
  refine mem_lpBridgeSet_iff.mpr ⟨?_, ?_, ?_⟩
  · refine (Lp.coeFn_nonneg _).mp ?_
    filter_upwards [lpBridge_const_ae (1 : ℝ)] with x hx
    rw [hx]
    exact zero_le_one
  · refine (Lp.coeFn_le _ _).mp ?_
    filter_upwards [lpBridge_const_ae (1 : ℝ), lpBridge_const_ae M] with x hx hy
    rw [hx, hy]
    exact hM
  · rw [integral_congr_ae (lpBridge_const_ae (1 : ℝ))]
    simp

/-- `lpBridgeSet M` is closed: two order conditions and one continuous-functional
condition. -/
theorem lpBridgeSet_isClosed (M : ℝ) : IsClosed (lpBridgeSet M) :=
  ((isClosed_le continuous_const continuous_id).inter
      (isClosed_le continuous_id continuous_const)).inter
    (isClosed_eq lpBridge_continuous_integral continuous_const)

/-- **The set Banach's theorem is applied to is complete**: `Lp ℝ 4 unitμ` is complete and
`lpBridgeSet M` is closed in it. -/
theorem lpBridgeSet_isComplete (M : ℝ) : IsComplete (lpBridgeSet M) :=
  (lpBridgeSet_isClosed M).isComplete

/-- The pointwise representative of a member of `lpBridgeSet M`: measurable, valued in
`[0, M]` at every point, of unit mass, and representing `F`.  This is the form in which the
output of the contraction iteration is handed to `SingularEndpoint/LocalizationRankOne/Factor.lean`. -/
theorem lpBridgeSet_exists_repr {M : ℝ} (hM : 0 ≤ M) {F : Lp ℝ 4 unitμ}
    (hF : F ∈ lpBridgeSet M) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ M) ∧
      (∫ x, f x ∂unitμ) = 1 ∧ ∃ hf : MemLp f 4 unitμ, hf.toLp f = F := by
  obtain ⟨h0, hle⟩ := lpBridgeSet_ae hF
  obtain ⟨f, hmeas, hnn, hbd, hae, hlp⟩ := lpBridge_exists_pointwise_repr hM h0 hle
  exact ⟨f, hmeas, hnn, hbd,
    (integral_congr_ae hae).trans (mem_lpBridgeSet_iff.mp hF).2.2, hlp⟩

/-- The converse direction of `lpBridgeSet_exists_repr`: a raw function with the three
pointwise properties lands in `lpBridgeSet M`.  This is how the `Set.MapsTo` hypothesis of
`lpBridgeSet_exists_fixedPoint` is discharged, the contraction map being defined on raw
functions. -/
theorem toLp_mem_lpBridgeSet {M : ℝ} {f : ℝ → ℝ} (hf : MemLp f 4 unitμ) (hnn : ∀ x, 0 ≤ f x)
    (hbd : ∀ x, f x ≤ M) (hint : ∫ x, f x ∂unitμ = 1) : hf.toLp f ∈ lpBridgeSet M := by
  refine mem_lpBridgeSet_iff.mpr ⟨(Lp.coeFn_nonneg _).mp ?_, (Lp.coeFn_le _ _).mp ?_, ?_⟩
  · filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
    exact hnn x
  · filter_upwards [hf.coeFn_toLp, lpBridge_const_ae M] with x hx hc
    rw [hx, hc]
    exact hbd x
  · rw [integral_congr_ae hf.coeFn_toLp]
    exact hint

/-! ## Banach's theorem, packaged -/

/-- **The fixed-point wrapper.**  A self-map of a complete set which contracts on that set
has a fixed point in it.  This is `ContractingWith.exists_fixedPoint'` with the `ℝ≥0`/`edist`
bookkeeping discharged: the Lipschitz hypothesis is stated with `dist` and a constant
`k < 1`, quantified only over points of `S`. -/
theorem lpBridge_exists_fixedPoint {S : Set (Lp ℝ 4 unitμ)} (hSc : IsComplete S)
    {N : Lp ℝ 4 unitμ → Lp ℝ 4 unitμ} (hmaps : Set.MapsTo N S S) {k : ℝ≥0} (hk : k < 1)
    (hlip : ∀ F ∈ S, ∀ G ∈ S, dist (N F) (N G) ≤ (k : ℝ) * dist F G)
    {F₀ : Lp ℝ 4 unitμ} (hF₀ : F₀ ∈ S) : ∃ F ∈ S, N F = F := by
  have hcon : ContractingWith k (hmaps.restrict N S S) := by
    refine ⟨hk, LipschitzWith.of_dist_le_mul ?_⟩
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    simpa [Subtype.dist_eq, Set.MapsTo.val_restrict_apply] using hlip x hx y hy
  obtain ⟨F, hFS, hfix, -, -⟩ := hcon.exists_fixedPoint' hSc hmaps hF₀ (edist_ne_top _ _)
  exact ⟨F, hFS, hfix⟩

/-- **Uniqueness**: two fixed points in `S` of a map that contracts on `S` coincide.  No
completeness is needed for this half.  `lem:localization-rank-one` asserts only the
existence of its decomposition; uniqueness of the contraction fixed point is an addition of
the Lean construction (compare `factorMain_unique`). -/
theorem lpBridge_fixedPoint_unique {S : Set (Lp ℝ 4 unitμ)}
    {N : Lp ℝ 4 unitμ → Lp ℝ 4 unitμ} {k : ℝ≥0} (hk : k < 1)
    (hlip : ∀ F ∈ S, ∀ G ∈ S, dist (N F) (N G) ≤ (k : ℝ) * dist F G)
    {F G : Lp ℝ 4 unitμ} (hF : F ∈ S) (hG : G ∈ S) (hFf : N F = F) (hGf : N G = G) : F = G := by
  have h := hlip F hF G hG
  rw [hFf, hGf] at h
  rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist F G) with h0 | h0
  · exact dist_eq_zero.mp h0.symm
  · refine absurd h (not_le.mpr ?_)
    have hk' : (k : ℝ) < 1 := by exact_mod_cast hk
    have := mul_lt_mul_of_pos_right hk' h0
    linarith

/-- Existence *and* uniqueness in one statement, the shape in which the contraction construction
consumes Banach's theorem. -/
theorem lpBridge_existsUnique_fixedPoint {S : Set (Lp ℝ 4 unitμ)} (hSc : IsComplete S)
    {N : Lp ℝ 4 unitμ → Lp ℝ 4 unitμ} (hmaps : Set.MapsTo N S S) {k : ℝ≥0} (hk : k < 1)
    (hlip : ∀ F ∈ S, ∀ G ∈ S, dist (N F) (N G) ≤ (k : ℝ) * dist F G)
    {F₀ : Lp ℝ 4 unitμ} (hF₀ : F₀ ∈ S) :
    ∃ F ∈ S, N F = F ∧ ∀ G ∈ S, N G = G → G = F := by
  obtain ⟨F, hFS, hfix⟩ := lpBridge_exists_fixedPoint hSc hmaps hk hlip hF₀
  exact ⟨F, hFS, hfix, fun G hG hGf => lpBridge_fixedPoint_unique hk hlip hG hFS hGf hfix⟩

/-- **The one-liner.**  A map preserving `lpBridgeSet M` and contracting on it has a unique
fixed point there.  Combined with `lpBridgeSet_exists_repr`, this delivers the measurable
`f : ℝ → ℝ` with `0 ≤ f ≤ M` pointwise and `∫ f = 1` that the nonlinear Factor decomposition
of `lem:localization-rank-one` asks for. -/
theorem lpBridgeSet_exists_fixedPoint {M : ℝ} (hM : 1 ≤ M)
    {N : Lp ℝ 4 unitμ → Lp ℝ 4 unitμ} (hmaps : Set.MapsTo N (lpBridgeSet M) (lpBridgeSet M))
    {k : ℝ≥0} (hk : k < 1)
    (hlip : ∀ F ∈ lpBridgeSet M, ∀ G ∈ lpBridgeSet M, dist (N F) (N G) ≤ (k : ℝ) * dist F G) :
    ∃ F ∈ lpBridgeSet M, N F = F ∧ ∀ G ∈ lpBridgeSet M, N G = G → G = F :=
  lpBridge_existsUnique_fixedPoint (lpBridgeSet_isComplete M) hmaps hk hlip
    (lpBridgeSet_nonempty hM)

end UpperTailOptimizers
