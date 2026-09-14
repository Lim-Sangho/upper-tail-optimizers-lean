import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.IntermediateValue
import UpperTailOptimizers.Preliminaries.Graphons.Basic

/-!
# The distribution transport of a measurable subset of `[0,1]`

`thm:singular-endpoint`'s uniqueness clause needs a measure-preserving self-map of `[0,1]`
carrying a prescribed measurable set `A` onto the interval `[0,|A|]`, so that a two-valued
Factor factor can be relabelled onto the family graphon's step function.  Mathlib has the
Borel isomorphism theorem but no measure-preserving existence result, and
`Mathlib/Probability/CDF.lean` has no probability integral transform, so the transport is
built here.

The map is the restricted distribution function

`m_S(x) = |S ∩ (-∞, x]|`,

which is monotone and `1`-Lipschitz, hence continuous, and pushes `volume|_S` forward to
`volume|_{[0,|S|]}`.  Nothing in this file is specific to Section 5; it is general measure
theory and would belong in `Mathlib` if it were polished.

## Contents

* `cdfT` — the restricted distribution function `m_S`;
* `cdfT_nonneg`, `cdfT_mono`, `cdfT_sub_le`, `lipschitzWith_cdfT`, `continuous_cdfT` — its
  regularity;
* `cdfT_of_le_zero`, `cdfT_of_one_le`, `cdfT_le` — its endpoint values and upper bound for
  `S ⊆ [0,1]`;
* `exists_cdfT_level` — its sublevel sets are half-lines on which the level is attained;
* **`map_cdfT`** — the transport: `Measure.map (m_S) (volume|_S) = volume|_{[0,|S|]}`;
* `relabel`, `measurable_relabel`, **`measurePreserving_relabel`** — the relabelling map
  `σ`, which sends `A` onto `[0,|A|]` and the rest of `[0,1]` onto `[|A|,1]`, and is
  measure-preserving for `unitμ`;
* `relabel_mem_of_mem` — `σ` carries `A` into `[0,|A|]`;
* `volume_cdfT_eq_zero_eq_zero` — the null exceptional set, the level `0` at which the
  detection property can fail;
* **`relabel_mem_Icc_iff_mem_ae`** — `σ x ∈ [0,|A|] ↔ x ∈ A` off a null set, so `σ` *detects*
  `A`; this is what converts a two-valued function on `A` into a step function of `σ`;
* `ae_gμ_of_ae_unitμ` — lifting an a.e. statement on `[0,1]` to both coordinates.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory Set

/-- **The restricted distribution function** `m_S(x) = |S ∩ (-∞, x]|`. -/
noncomputable def cdfT (S : Set ℝ) (x : ℝ) : ℝ := (volume (S ∩ Set.Iic x)).toReal

theorem cdfT_nonneg (S : Set ℝ) (x : ℝ) : 0 ≤ cdfT S x := ENNReal.toReal_nonneg

/-- `S ∩ (-∞,y]` splits as `S ∩ (-∞,x]` together with `S ∩ (x,y]`. -/
private theorem volume_inter_Iic_eq {S : Set ℝ} (hS : MeasurableSet S) {x y : ℝ} (hxy : x ≤ y) :
    volume (S ∩ Set.Iic y) = volume (S ∩ Set.Iic x) + volume (S ∩ Set.Ioc x y) := by
  have hdisj : Disjoint (S ∩ Set.Iic x) (S ∩ Set.Ioc x y) := by
    refine Set.disjoint_left.mpr fun a ha hb => ?_
    exact absurd hb.2.1 (not_lt.mpr ha.2)
  have hunion : S ∩ Set.Iic y = (S ∩ Set.Iic x) ∪ (S ∩ Set.Ioc x y) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc, Set.mem_union]
    constructor
    · rintro ⟨haS, hay⟩
      rcases le_or_gt a x with h | h
      · exact Or.inl ⟨haS, h⟩
      · exact Or.inr ⟨haS, h, hay⟩
    · rintro (⟨haS, hax⟩ | ⟨haS, -, hay⟩)
      · exact ⟨haS, le_trans hax hxy⟩
      · exact ⟨haS, hay⟩
  rw [hunion, measure_union hdisj (hS.inter measurableSet_Ioc)]

/-- `S ∩ (-∞,x]` has finite measure once `S` does — indeed always, since it is contained in a
half-line intersected with `S`; the hypothesis is what makes `toReal` faithful. -/
private theorem volume_inter_Iic_ne_top {S : Set ℝ} (hfin : volume S ≠ ⊤) (x : ℝ) :
    volume (S ∩ Set.Iic x) ≠ ⊤ :=
  ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)

/-- **`m_S` is monotone.** -/
theorem cdfT_mono {S : Set ℝ} (hfin : volume S ≠ ⊤) : Monotone (cdfT S) := by
  intro x y hxy
  refine ENNReal.toReal_mono (volume_inter_Iic_ne_top hfin y) ?_
  exact measure_mono (Set.inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr hxy))

/-- **`m_S` increases by at most the length of the interval**: `m_S y - m_S x ≤ y - x`. -/
theorem cdfT_sub_le {S : Set ℝ} (hS : MeasurableSet S) (hfin : volume S ≠ ⊤) {x y : ℝ}
    (hxy : x ≤ y) : cdfT S y - cdfT S x ≤ y - x := by
  have hsplit := volume_inter_Iic_eq hS hxy
  have hIoc : volume (S ∩ Set.Ioc x y) ≤ ENNReal.ofReal (y - x) := by
    refine le_trans (measure_mono Set.inter_subset_right) ?_
    rw [Real.volume_Ioc]
  have hx := volume_inter_Iic_ne_top hfin x
  have hy := volume_inter_Iic_ne_top hfin y
  have hIocfin : volume (S ∩ Set.Ioc x y) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hIoc
  have htoReal : cdfT S y = cdfT S x + (volume (S ∩ Set.Ioc x y)).toReal := by
    rw [cdfT, cdfT, hsplit, ENNReal.toReal_add hx hIocfin]
  have hle : (volume (S ∩ Set.Ioc x y)).toReal ≤ y - x := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hIoc
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  linarith

/-- **`m_S` is `1`-Lipschitz.** -/
theorem lipschitzWith_cdfT {S : Set ℝ} (hS : MeasurableSet S) (hfin : volume S ≠ ⊤) :
    LipschitzWith 1 (cdfT S) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
  rcases le_total x y with h | h
  · have h1 : cdfT S x ≤ cdfT S y := cdfT_mono hfin h
    have h2 : cdfT S y - cdfT S x ≤ y - x := cdfT_sub_le hS hfin h
    rw [abs_of_nonpos (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 : cdfT S y ≤ cdfT S x := cdfT_mono hfin h
    have h2 : cdfT S x - cdfT S y ≤ x - y := cdfT_sub_le hS hfin h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- **`m_S` is continuous**, being `1`-Lipschitz.  This is where the absence of atoms in
Lebesgue measure enters: a measure with an atom would have a jump here. -/
theorem continuous_cdfT {S : Set ℝ} (hS : MeasurableSet S) (hfin : volume S ≠ ⊤) :
    Continuous (cdfT S) := (lipschitzWith_cdfT hS hfin).continuous

/-- `m_S(x) = 0` for `x ≤ 0` when `S ⊆ [0,1]`: the sliver `S ∩ (-∞,x]` is contained in `{0}`
at `x = 0` and empty below. -/
theorem cdfT_of_le_zero {S : Set ℝ} (hSsub : S ⊆ Set.Icc 0 1) {x : ℝ} (hx : x ≤ 0) :
    cdfT S x = 0 := by
  have hsub : S ∩ Set.Iic x ⊆ ({0} : Set ℝ) := by
    rintro a ⟨haS, hax⟩
    have h0 := (hSsub haS).1
    have : a ≤ 0 := le_trans hax hx
    exact Set.mem_singleton_iff.mpr (le_antisymm this h0)
  have : volume (S ∩ Set.Iic x) = 0 :=
    measure_mono_null hsub (by simp)
  rw [cdfT, this, ENNReal.toReal_zero]

/-- `m_S(x) = |S|` for `1 ≤ x` when `S ⊆ [0,1]`. -/
theorem cdfT_of_one_le {S : Set ℝ} (hSsub : S ⊆ Set.Icc 0 1) {x : ℝ} (hx : 1 ≤ x) :
    cdfT S x = (volume S).toReal := by
  have : S ∩ Set.Iic x = S := by
    refine Set.inter_eq_self_of_subset_left fun a haS => ?_
    exact le_trans (hSsub haS).2 hx
  rw [cdfT, this]

/-- `m_S ≤ |S|` everywhere. -/
theorem cdfT_le (S : Set ℝ) (hfin : volume S ≠ ⊤) (x : ℝ) : cdfT S x ≤ (volume S).toReal :=
  ENNReal.toReal_mono hfin (measure_mono Set.inter_subset_left)


/-! ## The level sets of `m_S`, and the pushforward -/

/-- `|S| < ∞` for `S ⊆ [0,1]`. -/
private theorem volume_ne_top_of_subset_unit {S : Set ℝ} (hSsub : S ⊆ Set.Icc 0 1) :
    volume S ≠ ⊤ := by
  have h1 : volume S ≤ volume (Set.Icc (0 : ℝ) 1) := measure_mono hSsub
  rw [Real.volume_Icc] at h1
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1

/-- **The sublevel sets of `m_S` are half-lines on which `m_S` attains the level.**

`{x : m_S x ≤ y}` is closed (continuity) and downward closed (monotonicity), and for
`0 ≤ y < |S|` it is bounded above because `m_S 1 = |S| > y`.  A nonempty closed bounded-above
downward-closed set is `Iic` of its supremum, and the intermediate value theorem puts a point
of level exactly `y` below that supremum, so the level is attained there. -/
theorem exists_cdfT_level {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc 0 1)
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y < (volume S).toReal) :
    ∃ c : ℝ, {x : ℝ | cdfT S x ≤ y} = Set.Iic c ∧ cdfT S c = y := by
  have hfin := volume_ne_top_of_subset_unit hSsub
  have hcont := continuous_cdfT hS hfin
  have h0 : cdfT S 0 = 0 := cdfT_of_le_zero hSsub le_rfl
  have h1 : cdfT S 1 = (volume S).toReal := cdfT_of_one_le hSsub le_rfl
  have hmem : y ∈ Set.Icc (cdfT S 0) (cdfT S 1) := by rw [h0, h1]; exact ⟨hy0, hy.le⟩
  obtain ⟨c₀, -, hc₀⟩ :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn hmem
  have hclosed : IsClosed {x : ℝ | cdfT S x ≤ y} := isClosed_le hcont continuous_const
  have hne : ({x : ℝ | cdfT S x ≤ y}).Nonempty := ⟨c₀, hc₀.le⟩
  have hdown : ∀ {u v : ℝ}, u ≤ v → v ∈ {x : ℝ | cdfT S x ≤ y} → u ∈ {x : ℝ | cdfT S x ≤ y} :=
    fun huv hv => le_trans (cdfT_mono hfin huv) hv
  have hbdd : BddAbove {x : ℝ | cdfT S x ≤ y} := by
    refine ⟨1, fun x hx => ?_⟩
    by_contra hlt
    push Not at hlt
    have hone : (1 : ℝ) ∈ {x : ℝ | cdfT S x ≤ y} := hdown hlt.le hx
    have h2 : cdfT S 1 ≤ y := hone
    rw [h1] at h2
    linarith
  have hc : sSup {x : ℝ | cdfT S x ≤ y} ∈ {x : ℝ | cdfT S x ≤ y} :=
    hclosed.csSup_mem hne hbdd
  refine ⟨sSup {x : ℝ | cdfT S x ≤ y}, ?_, le_antisymm hc ?_⟩
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    exact ⟨fun hx => le_csSup hbdd hx, fun hx => hdown hx hc⟩
  · have hc₀le : c₀ ≤ sSup {x : ℝ | cdfT S x ≤ y} :=
      le_csSup hbdd hc₀.le
    have h3 := cdfT_mono hfin hc₀le
    rw [hc₀] at h3
    exact h3

/-- **The distribution transport.**  For measurable `S ⊆ [0,1]`, the map `m_S` pushes
`volume|_S` forward to `volume|_{[0,|S|]}`.

This is the measure-theoretic content of `thm:singular-endpoint`'s uniqueness clause: it
is what lets a two-valued Factor factor be relabelled onto the family graphon's step
function.  The proof is `MeasureTheory.Measure.ext_of_Iic`: on `Iic a` the two sides are `0`
for `a < 0` and `|S|` for `a ≥ |S|`, while for `0 ≤ a < |S|` the left side is
`|S ∩ Iic c| = m_S c = a` by `exists_cdfT_level`. -/
theorem map_cdfT {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc 0 1) :
    Measure.map (cdfT S) (volume.restrict S)
      = volume.restrict (Set.Icc 0 (volume S).toReal) := by
  have hfin := volume_ne_top_of_subset_unit hSsub
  have hmeas : Measurable (cdfT S) := (continuous_cdfT hS hfin).measurable
  have : IsFiniteMeasure (Measure.map (cdfT S) (volume.restrict S)) := by
    constructor
    rw [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hfin
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply hmeas measurableSet_Iic,
    Measure.restrict_apply (hmeas measurableSet_Iic),
    Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge a 0 with hneg | hnonneg
  · have hL : cdfT S ⁻¹' Set.Iic a ∩ S = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hx
      exact absurd hx (not_le.mpr (lt_of_lt_of_le hneg (cdfT_nonneg S x)))
    have hR : Set.Iic a ∩ Set.Icc 0 (volume S).toReal = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h1 h2 h3
      linarith
    rw [hL, hR]
  · rcases lt_or_ge a (volume S).toReal with hab | hab
    · obtain ⟨c, hcset, hcval⟩ := exists_cdfT_level hS hSsub hnonneg hab
      have hL : cdfT S ⁻¹' Set.Iic a ∩ S = S ∩ Set.Iic c := by
        have hpre : cdfT S ⁻¹' Set.Iic a = Set.Iic c := hcset
        rw [hpre, Set.inter_comm]
      have hR : Set.Iic a ∩ Set.Icc 0 (volume S).toReal = Set.Icc 0 a := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨h1, h2, -⟩
          exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h2, h1, by linarith⟩
      rw [hL, hR, Real.volume_Icc, sub_zero,
        ← ENNReal.ofReal_toReal (volume_inter_Iic_ne_top hfin c)]
      exact congrArg ENNReal.ofReal hcval
    · have hL : cdfT S ⁻¹' Set.Iic a ∩ S = S := by
        refine Set.inter_eq_self_of_subset_right fun x hx => ?_
        simp only [Set.mem_preimage, Set.mem_Iic]
        exact le_trans (cdfT_le S hfin x) hab
      have hR : Set.Iic a ∩ Set.Icc 0 (volume S).toReal
          = Set.Icc 0 (volume S).toReal :=
        Set.inter_eq_self_of_subset_right fun x hx => le_trans hx.2 hab
      rw [hL, hR, Real.volume_Icc, sub_zero, ENNReal.ofReal_toReal hfin]

/-! ## The inverse transport

`m_S` is inverted, modulo null sets, by the quantile map `q_S(y) = sup {x ∈ [0,1] : m_S x ≤ y}`.
Clamping the supremum to `[0,1]` makes `q_S` monotone on all of `ℝ`, hence measurable, with
junk value `0` below `0`.
-/

/-- **The quantile map** of a measurable `S ⊆ [0,1]`: the right endpoint of the sublevel set
`{x ∈ [0,1] : m_S x ≤ y}`.  It inverts `cdfT S` modulo null sets. -/
noncomputable def qInv (S : Set ℝ) (y : ℝ) : ℝ :=
  sSup {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ cdfT S x ≤ y}

private theorem qInv_set_bddAbove (S : Set ℝ) (y : ℝ) :
    BddAbove {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ cdfT S x ≤ y} :=
  ⟨1, fun _ hx => hx.1.2⟩

theorem qInv_mono (S : Set ℝ) : Monotone (qInv S) := by
  intro y₁ y₂ hy
  rcases Set.eq_empty_or_nonempty {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ cdfT S x ≤ y₁} with he | hne
  · rw [qInv, he, Real.sSup_empty]
    rcases Set.eq_empty_or_nonempty {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ cdfT S x ≤ y₂} with he2 | hne2
    · rw [qInv, he2, Real.sSup_empty]
    · exact le_csSup_of_le (qInv_set_bddAbove S y₂) hne2.choose_spec hne2.choose_spec.1.1
  · exact csSup_le_csSup (qInv_set_bddAbove S y₂) hne
      (fun x hx => ⟨hx.1, le_trans hx.2 hy⟩)

theorem measurable_qInv (S : Set ℝ) : Measurable (qInv S) := (qInv_mono S).measurable

/-- On the range `0 ≤ y < |S|` the quantile map hits the level exactly, and the sublevel set
of `m_S` is `Iic` of it. -/
theorem qInv_spec {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc 0 1)
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y < (volume S).toReal) :
    {x : ℝ | cdfT S x ≤ y} = Set.Iic (qInv S y) ∧ cdfT S (qInv S y) = y := by
  obtain ⟨c, hcset, hcval⟩ := exists_cdfT_level hS hSsub hy0 hy
  have hfin := volume_ne_top_of_subset_unit hSsub
  have h0mem : (0 : ℝ) ∈ {x : ℝ | cdfT S x ≤ y} := by
    simp only [Set.mem_ofPred_eq, cdfT_of_le_zero hSsub le_rfl]; exact hy0
  have h0c : (0 : ℝ) ≤ c := by rw [hcset] at h0mem; exact h0mem
  have hc1 : c ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have : (1 : ℝ) ∈ Set.Iic c := le_of_lt hlt
    rw [← hcset] at this
    have h1 : cdfT S 1 ≤ y := this
    rw [cdfT_of_one_le hSsub le_rfl] at h1
    linarith
  have hqc : qInv S y = c := by
    have hsub : {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ cdfT S x ≤ y} = Set.Icc 0 c := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_Icc]
      constructor
      · rintro ⟨⟨hx0, -⟩, hxy⟩
        have : x ∈ Set.Iic c := by rw [← hcset]; exact hxy
        exact ⟨hx0, this⟩
      · rintro ⟨hx0, hxc⟩
        refine ⟨⟨hx0, le_trans hxc hc1⟩, ?_⟩
        have : x ∈ Set.Iic c := hxc
        rw [← hcset] at this
        exact this
    rw [qInv, hsub, csSup_Icc h0c]
  rw [hqc]
  exact ⟨hcset, hcval⟩

theorem cdfT_qInv {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc 0 1)
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y < (volume S).toReal) : cdfT S (qInv S y) = y :=
  (qInv_spec hS hSsub hy0 hy).2

/-- The Galois property: on the range, `m_S x ≤ y ↔ x ≤ q_S y`. -/
theorem cdfT_le_iff_le_qInv {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc 0 1)
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y < (volume S).toReal) (x : ℝ) :
    cdfT S x ≤ y ↔ x ≤ qInv S y := by
  have h := (qInv_spec hS hSsub hy0 hy).1
  constructor
  · intro hx; have : x ∈ Set.Iic (qInv S y) := by rw [← h]; exact hx
    exact this
  · intro hx
    have : x ∈ {x : ℝ | cdfT S x ≤ y} := by rw [h]; exact hx
    exact this

theorem qInv_nonneg (S : Set ℝ) (y : ℝ) : 0 ≤ qInv S y := by
  rcases Set.eq_empty_or_nonempty {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ cdfT S x ≤ y} with he | hne
  · rw [qInv, he, Real.sSup_empty]
  · exact le_csSup_of_le (qInv_set_bddAbove S y) hne.choose_spec hne.choose_spec.1.1

theorem qInv_le_one (S : Set ℝ) (y : ℝ) : qInv S y ≤ 1 :=
  Real.sSup_le (fun _ hx => hx.1.2) (by norm_num)

/-- Above the total mass the quantile map is pinned at `1`. -/
theorem qInv_of_volume_le {S : Set ℝ} (hSsub : S ⊆ Set.Icc 0 1)
    {y : ℝ} (hy : (volume S).toReal ≤ y) : qInv S y = 1 := by
  have hfin := volume_ne_top_of_subset_unit hSsub
  have hset : {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ cdfT S x ≤ y} = Set.Icc 0 1 := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    exact ⟨fun h => h.1, fun h => ⟨h, le_trans (cdfT_le S hfin x) hy⟩⟩
  rw [qInv, hset, csSup_Icc (by norm_num : (0:ℝ) ≤ 1)]

/-- **The inverse transport.**  The quantile map pushes `volume|_{[0,|S|]}` forward to
`volume|_S`, so `[0,|S|]` and `S` are isomorphic as measure spaces.

The proof is `MeasureTheory.Measure.ext_of_Iic` again.  For `0 ≤ a < 1` the sublevel set
`{y ∈ [0,|S|] : q_S y ≤ a}` is squeezed between `[0, m_S a)` and `[0, m_S a]` by the Galois
property `m_S x ≤ y ↔ x ≤ q_S y`, so it has volume `m_S a = |S ∩ (-∞,a]|`. -/
theorem map_qInv {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc 0 1) :
    Measure.map (qInv S) (volume.restrict (Set.Icc 0 (volume S).toReal))
      = volume.restrict S := by
  have hfin := volume_ne_top_of_subset_unit hSsub
  have hmeas := measurable_qInv S
  have hαnn : (0:ℝ) ≤ (volume S).toReal := ENNReal.toReal_nonneg
  have : IsFiniteMeasure (Measure.map (qInv S) (volume.restrict (Set.Icc 0 (volume S).toReal))) := by
    constructor
    rw [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply hmeas measurableSet_Iic,
    Measure.restrict_apply (hmeas measurableSet_Iic),
    Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge a 0 with hneg | ha0
  · have hL : qInv S ⁻¹' Set.Iic a ∩ Set.Icc 0 (volume S).toReal = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hy
      exact absurd hy (not_le.mpr (lt_of_lt_of_le hneg (qInv_nonneg S y)))
    have hR : Set.Iic a ∩ S = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_and]
      intro hx hxS
      exact absurd hx (not_le.mpr (lt_of_lt_of_le hneg (hSsub hxS).1))
    rw [hL, hR]
  · rcases lt_or_ge a 1 with ha1 | ha1
    · -- the interesting range: sandwich the sublevel set between `Ico` and `Icc`
      have hβα : cdfT S a ≤ (volume S).toReal := cdfT_le S hfin a
      have hβ0 : 0 ≤ cdfT S a := cdfT_nonneg S a
      have hsub1 : Set.Ico 0 (cdfT S a)
          ⊆ qInv S ⁻¹' Set.Iic a ∩ Set.Icc 0 (volume S).toReal := by
        intro y hy
        have hyα : y < (volume S).toReal := lt_of_lt_of_le hy.2 hβα
        refine ⟨?_, ⟨hy.1, hyα.le⟩⟩
        simp only [Set.mem_preimage, Set.mem_Iic]
        by_contra hlt
        push Not at hlt
        have := (cdfT_le_iff_le_qInv hS hSsub hy.1 hyα a).mpr hlt.le
        linarith [hy.2]
      have hsub2 : qInv S ⁻¹' Set.Iic a ∩ Set.Icc 0 (volume S).toReal
          ⊆ Set.Icc 0 (cdfT S a) := by
        intro y hy
        obtain ⟨hple, hymem⟩ := hy
        simp only [Set.mem_preimage, Set.mem_Iic] at hple
        refine ⟨hymem.1, ?_⟩
        rcases lt_or_ge y (volume S).toReal with hyα | hyα
        · have hq := cdfT_qInv hS hSsub hymem.1 hyα
          have := cdfT_mono hfin hple
          rw [hq] at this
          exact this
        · rw [qInv_of_volume_le hSsub hyα] at hple
          linarith
      have hvol : volume (qInv S ⁻¹' Set.Iic a ∩ Set.Icc 0 (volume S).toReal)
          = ENNReal.ofReal (cdfT S a) := by
        have h1 : volume (Set.Ico (0:ℝ) (cdfT S a))
            ≤ volume (qInv S ⁻¹' Set.Iic a ∩ Set.Icc 0 (volume S).toReal) := measure_mono hsub1
        have h2 : volume (qInv S ⁻¹' Set.Iic a ∩ Set.Icc 0 (volume S).toReal)
            ≤ volume (Set.Icc (0:ℝ) (cdfT S a)) := measure_mono hsub2
        rw [Real.volume_Ico, sub_zero] at h1
        rw [Real.volume_Icc, sub_zero] at h2
        exact le_antisymm h2 h1
      rw [hvol, cdfT, ENNReal.ofReal_toReal (volume_inter_Iic_ne_top hfin a), Set.inter_comm]
    · have hL : qInv S ⁻¹' Set.Iic a ∩ Set.Icc 0 (volume S).toReal
          = Set.Icc 0 (volume S).toReal :=
        Set.inter_eq_self_of_subset_right fun y _ => by
          simp only [Set.mem_preimage, Set.mem_Iic]
          exact le_trans (qInv_le_one S y) ha1
      have hR : Set.Iic a ∩ S = S :=
        Set.inter_eq_self_of_subset_right fun x hx =>
          le_trans (hSsub hx).2 ha1
      rw [hL, hR, Real.volume_Icc, sub_zero, ENNReal.ofReal_toReal hfin]

theorem measurePreserving_cdfT {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc 0 1) :
    MeasurePreserving (cdfT S) (volume.restrict S)
      (volume.restrict (Set.Icc 0 (volume S).toReal)) :=
  ⟨(continuous_cdfT hS (volume_ne_top_of_subset_unit hSsub)).measurable, map_cdfT hS hSsub⟩

theorem measurePreserving_qInv {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc 0 1) :
    MeasurePreserving (qInv S) (volume.restrict (Set.Icc 0 (volume S).toReal))
      (volume.restrict S) :=
  ⟨measurable_qInv S, map_qInv hS hSsub⟩

/-- `q_S` is a left inverse of `m_S` almost everywhere on `S`.

Pointwise `x ≤ q_S(m_S x)`, because `x` itself lies in the sublevel set whose supremum
`q_S(m_S x)` is.  The composite is measure-preserving on `volume|_S` by `map_cdfT` and
`map_qInv`, so it has the same integral as the identity; a nonnegative function with zero
integral vanishes almost everywhere. -/
theorem qInv_cdfT_ae {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc 0 1) :
    ∀ᵐ x ∂(volume.restrict S), qInv S (cdfT S x) = x := by
  have hfin := volume_ne_top_of_subset_unit hSsub
  have hmc : Measurable (cdfT S) := (continuous_cdfT hS hfin).measurable
  have hmq : Measurable (qInv S) := measurable_qInv S
  have : IsFiniteMeasure (volume.restrict S) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hfin
  -- the composite is measure-preserving on `volume|_S`
  have hmcomp : Measurable fun x => qInv S (cdfT S x) := hmq.comp hmc
  have hmp : MeasurePreserving (fun x => qInv S (cdfT S x))
      (volume.restrict S) (volume.restrict S) :=
    (measurePreserving_qInv hS hSsub).comp (measurePreserving_cdfT hS hSsub)
  -- pointwise lower bound
  have hge : ∀ᵐ x ∂(volume.restrict S), x ≤ qInv S (cdfT S x) := by
    refine (ae_restrict_iff' hS).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    exact le_csSup (qInv_set_bddAbove S (cdfT S x)) ⟨hSsub hx, le_rfl⟩
  -- both sides are integrable, being bounded by `1`
  have hIid : Integrable (fun x : ℝ => x) (volume.restrict S) := by
    refine (integrable_const (1 : ℝ)).mono' measurable_id.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hS).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hSsub hx).1]
    exact (hSsub hx).2
  have hIcomp : Integrable (fun x : ℝ => qInv S (cdfT S x)) (volume.restrict S) := by
    refine (integrable_const (1 : ℝ)).mono' hmcomp.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (qInv_nonneg S _)]
    exact qInv_le_one S _
  -- equal integrals
  have hint : ∫ x, qInv S (cdfT S x) ∂(volume.restrict S) = ∫ x, x ∂(volume.restrict S) := by
    have h : ∫ y, y ∂(Measure.map (fun x => qInv S (cdfT S x)) (volume.restrict S))
        = ∫ x, qInv S (cdfT S x) ∂(volume.restrict S) :=
      integral_map hmcomp.aemeasurable
        (by rw [hmp.map_eq]; exact measurable_id.aestronglyMeasurable)
    rw [hmp.map_eq] at h
    exact h.symm
  -- a nonnegative function with zero integral vanishes a.e.
  have hzero : ∫ x, (qInv S (cdfT S x) - x) ∂(volume.restrict S) = 0 := by
    rw [integral_sub hIcomp hIid, hint, sub_self]
  have hnn : 0 ≤ᵐ[volume.restrict S] fun x => qInv S (cdfT S x) - x :=
    hge.mono fun x hx => sub_nonneg.mpr hx
  have := (integral_eq_zero_iff_of_nonneg_ae hnn (hIcomp.sub hIid)).mp hzero
  exact this.mono fun x hx => by linarith [sub_eq_zero.mp hx]

/-- `q_S` is a right inverse of `m_S` on `[0,|S|]` almost everywhere: the identity holds at
every `y < |S|`, and the single endpoint is null. -/
theorem cdfT_qInv_ae {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc 0 1) :
    ∀ᵐ y ∂(volume.restrict (Set.Icc 0 (volume S).toReal)), cdfT S (qInv S y) = y := by
  have hnull : volume.restrict (Set.Icc 0 (volume S).toReal) {(volume S).toReal} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton _)]
    exact measure_mono_null Set.inter_subset_left (by simp)
  filter_upwards [compl_mem_ae_iff.mpr hnull, ae_restrict_mem measurableSet_Icc]
    with y hy hymem
  have hyne : y ≠ (volume S).toReal := fun h => hy (by simp [h])
  rcases lt_or_ge y (volume S).toReal with hlt | hge
  · exact cdfT_qInv hS hSsub hymem.1 hlt
  · exact absurd (le_antisymm hymem.2 hge) hyne

/-! ## The relabelling map

`σ` sends `A` onto `[0,|A|]` by `m_A` and the rest of `[0,1]` onto `[|A|,1]` by
`|A| + m_{[0,1]∖A}`.  Each half is `map_cdfT`; the two images meet only in the null set
`{|A|}`. -/

/-- **The relabelling map** of `thm:singular-endpoint`'s uniqueness clause. -/
noncomputable def relabel (A : Set ℝ) (x : ℝ) : ℝ :=
  Set.indicator A (cdfT A) x
    + Set.indicator Aᶜ (fun y => (volume A).toReal + cdfT (Set.Icc 0 1 \ A) y) x

theorem measurable_relabel {A : Set ℝ} (hA : MeasurableSet A) (hAsub : A ⊆ Set.Icc 0 1) :
    Measurable (relabel A) := by
  have hfinA := volume_ne_top_of_subset_unit hAsub
  have hBsub : Set.Icc (0 : ℝ) 1 \ A ⊆ Set.Icc 0 1 := Set.sdiff_subset
  have hfinB := volume_ne_top_of_subset_unit hBsub
  exact ((continuous_cdfT hA hfinA).measurable.indicator hA).add
    (((continuous_cdfT (measurableSet_Icc.diff hA) hfinB).measurable.const_add _).indicator
      hA.compl)

/-- **The relabelling map is measure-preserving.**

`unitμ` splits as `volume|_A + volume|_{[0,1]∖A}`; `map_cdfT` sends the first to
`volume|_{[0,|A|]}` and, after a translation by `|A|`, the second to `volume|_{[|A|,1]}`; and
`Measure.restrict_union_add_inter` reassembles those into `volume|_{[0,1]} = unitμ`, the
intersection `{|A|}` being null. -/
theorem measurePreserving_relabel {A : Set ℝ} (hA : MeasurableSet A)
    (hAsub : A ⊆ Set.Icc 0 1) : MeasurePreserving (relabel A) unitμ unitμ := by
  have hmeas := measurable_relabel hA hAsub
  have hfinA := volume_ne_top_of_subset_unit hAsub
  have hBmeas : MeasurableSet (Set.Icc (0 : ℝ) 1 \ A) := measurableSet_Icc.diff hA
  have hBsub : Set.Icc (0 : ℝ) 1 \ A ⊆ Set.Icc 0 1 := Set.sdiff_subset
  have hfinB := volume_ne_top_of_subset_unit hBsub
  have hunitdef : unitμ = volume.restrict (Set.Icc (0 : ℝ) 1) := rfl
  obtain ⟨α, hα⟩ : ∃ t : ℝ, t = (volume A).toReal := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ t : ℝ, t = (volume (Set.Icc (0 : ℝ) 1 \ A)).toReal := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by rw [hα]; exact ENNReal.toReal_nonneg
  have hβ0 : 0 ≤ β := by rw [hβ]; exact ENNReal.toReal_nonneg
  -- `|A| + |[0,1] ∖ A| = 1`
  have hsum : α + β = 1 := by
    have hunion : A ∪ (Set.Icc (0 : ℝ) 1 \ A) = Set.Icc 0 1 := by
      rw [Set.union_sdiff_cancel hAsub]
    have hdisj : Disjoint A (Set.Icc (0 : ℝ) 1 \ A) := Set.disjoint_sdiff_right
    have hm : volume A + volume (Set.Icc (0 : ℝ) 1 \ A) = volume (Set.Icc (0 : ℝ) 1) := by
      rw [← measure_union hdisj hBmeas, hunion]
    rw [Real.volume_Icc] at hm
    have := congrArg ENNReal.toReal hm
    rw [ENNReal.toReal_add hfinA hfinB, ENNReal.toReal_ofReal (by norm_num)] at this
    rw [hα, hβ]; linarith
  have hα1 : α ≤ 1 := by linarith
  -- the splitting of `unitμ`
  have hsplit : unitμ = volume.restrict A + volume.restrict (Set.Icc (0 : ℝ) 1 \ A) := by
    have hru := Measure.restrict_union (μ := (volume : Measure ℝ)) (s := A)
      Set.disjoint_sdiff_right hBmeas
    rw [Set.union_sdiff_cancel hAsub] at hru
    exact hunitdef.trans hru
  -- the two halves
  have hpieceA : Measure.map (relabel A) (volume.restrict A)
      = volume.restrict (Set.Icc 0 α) := by
    have hae : relabel A =ᵐ[volume.restrict A] cdfT A := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hA]
      refine Filter.Eventually.of_forall fun x hx => ?_
      rw [relabel, Set.indicator_of_mem hx,
        Set.indicator_of_notMem (by simpa using hx), add_zero]
    rw [Measure.map_congr hae, map_cdfT hA hAsub, hα]
  have hpieceB : Measure.map (relabel A) (volume.restrict (Set.Icc (0 : ℝ) 1 \ A))
      = volume.restrict (Set.Icc α 1) := by
    have hae : relabel A
        =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1 \ A)]
        fun x => α + cdfT (Set.Icc (0 : ℝ) 1 \ A) x := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hBmeas]
      refine Filter.Eventually.of_forall fun x hx => ?_
      rw [relabel, Set.indicator_of_notMem hx.2,
        Set.indicator_of_mem (show x ∈ Aᶜ from hx.2), zero_add, hα]
    rw [Measure.map_congr hae]
    have hcomp : (fun x : ℝ => α + cdfT (Set.Icc (0 : ℝ) 1 \ A) x)
        = (fun y : ℝ => α + y) ∘ cdfT (Set.Icc (0 : ℝ) 1 \ A) := rfl
    rw [hcomp, ← Measure.map_map (measurable_const_add α)
      (continuous_cdfT hBmeas hfinB).measurable, map_cdfT hBmeas hBsub, ← hβ]
    -- translate `[0,β]` to `[α,1]`
    have hpre : (fun y : ℝ => α + y) ⁻¹' Set.Icc α 1 = Set.Icc 0 β := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    have hres := Measure.restrict_map (μ := (volume : Measure ℝ)) (measurable_const_add α)
      (measurableSet_Icc (a := α) (b := (1 : ℝ)))
    rw [hpre] at hres
    rw [← hres, (measurePreserving_add_left volume α).map_eq]
  -- reassemble
  refine ⟨hmeas, ?_⟩
  conv_lhs => rw [hsplit]
  rw [Measure.map_add _ _ hmeas, hpieceA, hpieceB]
  have hunion : Set.Icc (0 : ℝ) α ∪ Set.Icc α 1 = Set.Icc 0 1 :=
    Set.Icc_union_Icc_eq_Icc hα0 hα1
  have hinter : Set.Icc (0 : ℝ) α ∩ Set.Icc α 1 = {α} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨-, h2⟩, h3, -⟩
      exact le_antisymm h2 h3
    · rintro rfl
      exact ⟨⟨hα0, le_rfl⟩, le_rfl, hα1⟩
  have hadd := Measure.restrict_union_add_inter (μ := (volume : Measure ℝ))
    (Set.Icc (0 : ℝ) α) (measurableSet_Icc (a := α) (b := (1 : ℝ)))
  rw [hunion, hinter] at hadd
  have hnull : (volume : Measure ℝ).restrict {α} = 0 := by
    rw [Measure.restrict_eq_zero, Real.volume_singleton]
  rw [hnull, add_zero] at hadd
  rw [← hadd]
  exact hunitdef.symm

/-! ## Where `σ` sends things

`σ` maps `A` into `[0,|A|]` and `[0,1] ∖ A` into `[|A|,1]`, and — off a null set — the first
inclusion is strict at the top and the second at the bottom.  That the two exceptional sets are
null is immediate from `map_cdfT`: they are the preimages of the single points `|A|` and `0`,
which carry no mass in the image measures. -/

theorem relabel_mem_of_mem {A : Set ℝ} (hAsub : A ⊆ Set.Icc 0 1)
    {x : ℝ} (hx : x ∈ A) : relabel A x ∈ Set.Icc 0 (volume A).toReal := by
  have hfinA := volume_ne_top_of_subset_unit hAsub
  have he : relabel A x = cdfT A x := by
    rw [relabel, Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx), add_zero]
  rw [he]
  exact ⟨cdfT_nonneg A x, cdfT_le A hfinA x⟩

/-- **The level `0` is attained on a null set.** -/
theorem volume_cdfT_eq_zero_eq_zero {S : Set ℝ} (hS : MeasurableSet S)
    (hSsub : S ⊆ Set.Icc 0 1) : volume (S ∩ {x : ℝ | cdfT S x = 0}) = 0 := by
  have hfin := volume_ne_top_of_subset_unit hSsub
  have hmeas : Measurable (cdfT S) := (continuous_cdfT hS hfin).measurable
  have h := congrArg (fun μ : Measure ℝ => μ {(0 : ℝ)}) (map_cdfT hS hSsub)
  rw [Measure.map_apply hmeas (measurableSet_singleton _),
    Measure.restrict_apply (hmeas (measurableSet_singleton _)),
    Measure.restrict_apply (measurableSet_singleton _)] at h
  have hR : ({(0 : ℝ)} : Set ℝ) ∩ Set.Icc 0 (volume S).toReal = {(0 : ℝ)} := by
    refine Set.inter_eq_self_of_subset_left fun x hx => ?_
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨le_rfl, ENNReal.toReal_nonneg⟩
  rw [hR, Real.volume_singleton] at h
  rw [← h, Set.inter_comm]
  rfl

/-- **`σ` carries `A` onto the standard block `[0,|A|]`, almost everywhere.**  The `Icc` shape
is what matches `bipodalValue`'s vertex class `Set.Icc 0 α`.  On `A` the inclusion is
unconditional (`relabel_mem_of_mem`); off `A` it needs the one exceptional null set
`{cdfT ([0,1]∖A) = 0}`, which `volume_cdfT_eq_zero_eq_zero` shows is null. -/
theorem relabel_mem_Icc_iff_mem_ae {A : Set ℝ} (hA : MeasurableSet A) (hAsub : A ⊆ Set.Icc 0 1) :
    ∀ᵐ x ∂unitμ, (relabel A x ∈ Set.Icc (0 : ℝ) (volume A).toReal ↔ x ∈ A) := by
  have hBmeas : MeasurableSet (Set.Icc (0 : ℝ) 1 \ A) := measurableSet_Icc.diff hA
  have hBsub : Set.Icc (0 : ℝ) 1 \ A ⊆ Set.Icc 0 1 := Set.sdiff_subset
  obtain ⟨E, hE⟩ : ∃ E : Set ℝ,
      E = (Set.Icc (0 : ℝ) 1 \ A) ∩ {x : ℝ | cdfT (Set.Icc (0 : ℝ) 1 \ A) x = 0} := ⟨_, rfl⟩
  have hE0 : unitμ E = 0 := by
    refine le_antisymm ?_ zero_le
    calc unitμ E ≤ volume E := Measure.le_iff'.mp Measure.restrict_le_self E
      _ = 0 := by rw [hE]; exact volume_cdfT_eq_zero_eq_zero hBmeas hBsub
  have hIcc : ∀ᵐ x ∂unitμ, x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [unitμ, ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun x hx => hx
  filter_upwards [hIcc, measure_eq_zero_iff_ae_notMem.mp hE0] with x hx hxE
  by_cases hmem : x ∈ A
  · exact ⟨fun _ => hmem, fun _ => relabel_mem_of_mem hAsub hmem⟩
  · have he : relabel A x = (volume A).toReal + cdfT (Set.Icc (0 : ℝ) 1 \ A) x := by
      rw [relabel, Set.indicator_of_notMem hmem,
        Set.indicator_of_mem (show x ∈ Aᶜ from hmem), zero_add]
    have hpos : cdfT (Set.Icc (0 : ℝ) 1 \ A) x ≠ 0 := fun hcon =>
      hxE (by rw [hE]; exact ⟨⟨hx, hmem⟩, hcon⟩)
    refine ⟨fun hmemIcc => ?_, fun h => absurd h hmem⟩
    exact absurd (le_antisymm (by rw [he] at hmemIcc; linarith [hmemIcc.2])
      (cdfT_nonneg _ x)) hpos

/-! ## The inverse relabelling

`relabel A` is inverted, modulo null sets, by the quantile map of `A` below `|A|` and the
shifted quantile map of `[0,1] ∖ A` above it.  That makes it a relabelling in the sense of
`IsRelabelling`, which is the identification `paper/sections/preliminaries.tex` uses.
-/

/-- **The inverse relabelling** of `relabel A`. -/
noncomputable def invRelabel (A : Set ℝ) (y : ℝ) : ℝ :=
  if y ≤ (volume A).toReal then qInv A y
  else qInv (Set.Icc 0 1 \ A) (y - (volume A).toReal)

theorem measurable_invRelabel (A : Set ℝ) : Measurable (invRelabel A) :=
  Measurable.ite (measurableSet_le measurable_id measurable_const) (measurable_qInv A)
    ((measurable_qInv _).comp (measurable_id.sub_const _))

/-- `m_S` vanishes only on a null subset of `S`: the level `0` is a single point of `[0,|S|]`. -/
private theorem restrict_cdfT_ne_zero {S : Set ℝ} (hS : MeasurableSet S)
    (hSsub : S ⊆ Set.Icc 0 1) : ∀ᵐ x ∂(volume.restrict S), cdfT S x ≠ 0 := by
  have hpre := (measurePreserving_cdfT hS hSsub).measure_preimage
    (measurableSet_singleton (0 : ℝ)).nullMeasurableSet
  rw [Measure.restrict_apply (measurableSet_singleton _)] at hpre
  have hz : volume.restrict S (cdfT S ⁻¹' {(0:ℝ)}) = 0 := by
    rw [hpre]; exact measure_mono_null Set.inter_subset_left (by simp)
  filter_upwards [compl_mem_ae_iff.mpr hz] with x hx
  exact fun h => hx (by simpa using h)

/-- Almost every value of the quantile map lands in `S`. -/
private theorem ae_qInv_mem {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc 0 1) :
    ∀ᵐ y ∂(volume.restrict (Set.Icc 0 (volume S).toReal)), qInv S y ∈ S := by
  have hpre := (measurePreserving_qInv hS hSsub).measure_preimage hS.compl.nullMeasurableSet
  rw [Measure.restrict_apply hS.compl, Set.compl_inter_self, measure_empty] at hpre
  filter_upwards [compl_mem_ae_iff.mpr hpre] with y hy
  exact not_notMem.mp hy

/-- **`relabel A` is a relabelling of `[0,1]`**: measure-preserving, with an inverse that undoes
it almost everywhere in both directions. -/
theorem isRelabelling_relabel {A : Set ℝ} (hA : MeasurableSet A)
    (hAsub : A ⊆ Set.Icc 0 1) : IsRelabelling (relabel A) := by
  classical
  have hBmeas : MeasurableSet (Set.Icc (0:ℝ) 1 \ A) := measurableSet_Icc.diff hA
  have hBsub : Set.Icc (0:ℝ) 1 \ A ⊆ Set.Icc 0 1 := Set.sdiff_subset
  have hfinA := volume_ne_top_of_subset_unit hAsub
  have hfinB := volume_ne_top_of_subset_unit hBsub
  have hα0 : (0:ℝ) ≤ (volume A).toReal := ENNReal.toReal_nonneg
  have hβ0 : (0:ℝ) ≤ (volume (Set.Icc (0:ℝ) 1 \ A)).toReal := ENNReal.toReal_nonneg
  have hsum : (volume A).toReal + (volume (Set.Icc (0:ℝ) 1 \ A)).toReal = 1 := by
    have hm : volume A + volume (Set.Icc (0:ℝ) 1 \ A) = volume (Set.Icc (0:ℝ) 1) := by
      rw [← measure_union Set.disjoint_sdiff_right hBmeas, Set.union_sdiff_cancel hAsub]
    rw [Real.volume_Icc] at hm
    have h := congrArg ENNReal.toReal hm
    rw [ENNReal.toReal_add hfinA hfinB, ENNReal.toReal_ofReal (by norm_num)] at h
    linarith
  have hα1 : (volume A).toReal ≤ 1 := by linarith
  have hrelA : ∀ x ∈ A, relabel A x = cdfT A x := fun x hx => by
    rw [relabel, Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx), add_zero]
  have hrelB : ∀ x ∈ Set.Icc (0:ℝ) 1 \ A,
      relabel A x = (volume A).toReal + cdfT (Set.Icc (0:ℝ) 1 \ A) x := fun x hx => by
    rw [relabel, Set.indicator_of_notMem hx.2, Set.indicator_of_mem (show x ∈ Aᶜ from hx.2),
      zero_add]
  have hsplitS : unitμ = volume.restrict A + volume.restrict (Set.Icc (0:ℝ) 1 \ A) := by
    have hru := Measure.restrict_union (μ := (volume : Measure ℝ))
      Set.disjoint_sdiff_right hBmeas
    rw [Set.union_sdiff_cancel hAsub] at hru
    exact hru
  have hsplitT : unitμ = volume.restrict (Set.Icc 0 (volume A).toReal)
      + volume.restrict (Set.Ioc (volume A).toReal 1) := by
    have hdisj : Disjoint (Set.Icc (0:ℝ) (volume A).toReal)
        (Set.Ioc (volume A).toReal 1) :=
      Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1)
    have hru := Measure.restrict_union (μ := (volume : Measure ℝ)) hdisj measurableSet_Ioc
    rw [Set.Icc_union_Ioc_eq_Icc hα0 hα1] at hru
    exact hru
  -- the shift matching `(|A|,1]` with `[0,|[0,1] ∖ A|]`
  have hshift : MeasurePreserving (fun y : ℝ => y - (volume A).toReal)
      (volume.restrict (Set.Ioc (volume A).toReal 1))
      (volume.restrict (Set.Icc 0 (volume (Set.Icc (0:ℝ) 1 \ A)).toReal)) := by
    have hmp : MeasurePreserving (fun y : ℝ => y - (volume A).toReal)
        (volume : Measure ℝ) volume := by
      simpa [sub_eq_add_neg] using
        measurePreserving_add_right (volume : Measure ℝ) (-(volume A).toReal)
    have hres := hmp.restrict_preimage
      (measurableSet_Ioc (a := (0:ℝ)) (b := (volume (Set.Icc (0:ℝ) 1 \ A)).toReal))
    have hpre : (fun y : ℝ => y - (volume A).toReal) ⁻¹'
        Set.Ioc 0 (volume (Set.Icc (0:ℝ) 1 \ A)).toReal = Set.Ioc (volume A).toReal 1 := by
      ext y
      simp only [Set.mem_preimage, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    rw [hpre] at hres
    rwa [Measure.restrict_congr_set (Ioc_ae_eq_Icc
      (a := (0:ℝ)) (b := (volume (Set.Icc (0:ℝ) 1 \ A)).toReal))] at hres
  have hpieceA : Measure.map (invRelabel A) (volume.restrict (Set.Icc 0 (volume A).toReal))
      = volume.restrict A := by
    have hae : invRelabel A
        =ᵐ[volume.restrict (Set.Icc 0 (volume A).toReal)] qInv A := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall fun y hy => by rw [invRelabel, if_pos hy.2]
    rw [Measure.map_congr hae, map_qInv hA hAsub]
  have hmsub : Measurable fun y : ℝ => y - (volume A).toReal := measurable_id.sub_const _
  have hpieceB : Measure.map (invRelabel A) (volume.restrict (Set.Ioc (volume A).toReal 1))
      = volume.restrict (Set.Icc (0:ℝ) 1 \ A) := by
    have hae : invRelabel A =ᵐ[volume.restrict (Set.Ioc (volume A).toReal 1)]
        fun y => qInv (Set.Icc (0:ℝ) 1 \ A) (y - (volume A).toReal) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall fun y hy => by
        rw [invRelabel, if_neg (not_le.mpr hy.1)]
    rw [Measure.map_congr hae,
      show (fun y : ℝ => qInv (Set.Icc (0:ℝ) 1 \ A) (y - (volume A).toReal))
        = qInv (Set.Icc (0:ℝ) 1 \ A) ∘ (fun y : ℝ => y - (volume A).toReal) from rfl,
      ← Measure.map_map (measurable_qInv _) hmsub, hshift.map_eq,
      map_qInv hBmeas hBsub]
  refine ⟨measurePreserving_relabel hA hAsub, invRelabel A,
    ⟨measurable_invRelabel A, ?_⟩, ?_, ?_⟩
  · rw [hsplitT, Measure.map_add _ _ (measurable_invRelabel A), hpieceA, hpieceB, ← hsplitS]
    exact hsplitT
  · -- `invRelabel ∘ relabel = id` a.e.
    rw [hsplitS, ae_add_measure_iff]
    refine ⟨?_, ?_⟩
    · filter_upwards [qInv_cdfT_ae hA hAsub, ae_restrict_mem hA] with x hx hxA
      rw [hrelA x hxA, invRelabel, if_pos (cdfT_le A hfinA x), hx]
    · filter_upwards [qInv_cdfT_ae hBmeas hBsub, ae_restrict_mem hBmeas,
        restrict_cdfT_ne_zero hBmeas hBsub] with x hx hxB hne
      have hpos : 0 < cdfT (Set.Icc (0:ℝ) 1 \ A) x :=
        lt_of_le_of_ne (cdfT_nonneg _ x) (Ne.symm hne)
      rw [hrelB x hxB, invRelabel, if_neg (by linarith), add_sub_cancel_left, hx]
  · -- `relabel ∘ invRelabel = id` a.e.
    rw [hsplitT, ae_add_measure_iff]
    refine ⟨?_, ?_⟩
    · filter_upwards [cdfT_qInv_ae hA hAsub, ae_qInv_mem hA hAsub,
        ae_restrict_mem measurableSet_Icc] with y hy hmem hyIcc
      rw [invRelabel, if_pos hyIcc.2, hrelA _ hmem, hy]
    · filter_upwards [hshift.quasiMeasurePreserving.ae (cdfT_qInv_ae hBmeas hBsub),
        hshift.quasiMeasurePreserving.ae (ae_qInv_mem hBmeas hBsub),
        ae_restrict_mem measurableSet_Ioc] with y hy hmem hyIoc
      rw [invRelabel, if_neg (not_le.mpr hyIoc.1), hrelB _ hmem, hy, add_sub_cancel]

/-- Lifting an a.e. statement on `[0,1]` to both coordinates of `[0,1]²`. -/
theorem ae_gμ_of_ae_unitμ {q : ℝ → Prop} (h : ∀ᵐ x ∂unitμ, q x) :
    ∀ᵐ z ∂gμ, q z.1 ∧ q z.2 := by
  have h1 : ∀ᵐ z ∂gμ, q z.1 := Measure.quasiMeasurePreserving_fst.ae h
  have h2 : ∀ᵐ z ∂gμ, q z.2 := Measure.quasiMeasurePreserving_snd.ae h
  filter_upwards [h1, h2] with z hz1 hz2 using ⟨hz1, hz2⟩

end SingularEndpoint

end UpperTailOptimizers
