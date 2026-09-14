import UpperTailOptimizers.Preliminaries.Graphons.Basic

/-!
# The cross lemma

For a symmetric measurable `S ⊆ ℝ²`, with sections of `unitμ`-measure `s_x`, and a convex
`φ ≥ 0` on `[0,1]` with `φ(0) = 0`,

  `∫ φ(s_x) dx ≤ φ(1)(|S|/2 + |S|²/τ²) + (φ(τ)/τ)|S|`   (`0 < τ ≤ 1`).

The point is the factor `1/2`: rows of large section measure form a set `I` with
`|I| ≤ |S|/τ`, and by symmetry `S ∩ (I × Iᶜ)` and `S ∩ (Iᶜ × I)` are disjoint copies of each
other inside `S`.  This is `kb:lem:cross` of the bipodality draft; near-equality forces `S`
to be a cross `(I × Iᶜ) ∪ (Iᶜ × I)`.
-/

namespace UpperTailOptimizers

open MeasureTheory Set Filter

/-- The section measure `s_x = |{y : (x,y) ∈ S}|`. -/
noncomputable def sectionMeasure (S : Set (ℝ × ℝ)) (x : ℝ) : ℝ :=
  (unitμ (Prod.mk x ⁻¹' S)).toReal

theorem sectionMeasure_mem_Icc (S : Set (ℝ × ℝ)) (x : ℝ) :
    sectionMeasure S x ∈ Icc (0:ℝ) 1 :=
  ⟨ENNReal.toReal_nonneg, by
    unfold sectionMeasure
    have h : unitμ (Prod.mk x ⁻¹' S) ≤ 1 := prob_le_one
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h)⟩

theorem measurable_sectionMeasure {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) :
    Measurable (sectionMeasure S) :=
  (measurable_measure_prodMk_left hS).ennreal_toReal

/-- `∫_A s_x = |S ∩ (A × ℝ)|`. -/
theorem setIntegral_sectionMeasure {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ∫ x in A, sectionMeasure S x ∂unitμ = (gμ (S ∩ A ×ˢ univ)).toReal := by
  have hSA : MeasurableSet (S ∩ A ×ˢ univ) := hS.inter (hA.prod MeasurableSet.univ)
  unfold gμ
  rw [Measure.prod_apply hSA]
  have hlin : ∫⁻ x, unitμ (Prod.mk x ⁻¹' (S ∩ A ×ˢ univ)) ∂unitμ
      = ∫⁻ x in A, unitμ (Prod.mk x ⁻¹' S) ∂unitμ := by
    rw [← lintegral_indicator hA]
    congr 1
    funext x
    by_cases hx : x ∈ A
    · simp [hx, Set.indicator_of_mem]
    · have : Prod.mk x ⁻¹' (S ∩ A ×ˢ univ) = ∅ := by ext y; simp [hx]
      simp [hx, this, Set.indicator_of_notMem]
  rw [hlin]
  unfold sectionMeasure
  exact integral_toReal (measurable_measure_prodMk_left hS).aemeasurable
    (Eventually.of_forall (fun x => measure_lt_top _ _))

/-- **The cross lemma.** -/
theorem integral_convex_sectionMeasure_le {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hsymm : ∀ x y, (x, y) ∈ S ↔ (y, x) ∈ S) {φ : ℝ → ℝ} (hφc : ConvexOn ℝ (Icc 0 1) φ)
    (hφ0 : φ 0 = 0) (hφnn : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ φ s) (hφm : Measurable φ)
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ∫ x, φ (sectionMeasure S x) ∂unitμ
      ≤ φ 1 * ((gμ S).toReal / 2 + (gμ S).toReal ^ 2 / τ ^ 2) + φ τ / τ * (gμ S).toReal := by
  classical
  set s := sectionMeasure S with hs
  set σ : ℝ := (gμ S).toReal with hσ
  have hsm : Measurable s := measurable_sectionMeasure hS
  set I : Set ℝ := {x | τ ≤ s x} with hI
  have hIm : MeasurableSet I := measurableSet_le measurable_const hsm
  -- pointwise convexity bounds
  have hle1 : ∀ t ∈ Icc (0:ℝ) 1, φ t ≤ t * φ 1 := by
    intro t ht
    have h := hφc.2 (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
      (sub_nonneg.mpr ht.2) ht.1 (by ring)
    simpa [hφ0] using h
  have hleτ : ∀ t ∈ Icc (0:ℝ) τ, φ t ≤ t / τ * φ τ := by
    intro t ht
    have hτmem : τ ∈ Icc (0:ℝ) 1 := ⟨hτ0.le, hτ1⟩
    have hq0 : 0 ≤ t / τ := div_nonneg ht.1 hτ0.le
    have hq1 : t / τ ≤ 1 := (div_le_one hτ0).mpr ht.2
    have h := hφc.2 (left_mem_Icc.mpr zero_le_one) hτmem (sub_nonneg.mpr hq1) hq0 (by ring)
    have hpt : (1 - t / τ) • (0:ℝ) + (t / τ) • τ = t := by
      simp only [smul_eq_mul, mul_zero, zero_add]; field_simp
    rw [hpt] at h
    simpa [hφ0] using h
  -- total mass and the mass over `I`
  have htot : ∫ x, s x ∂unitμ = σ := by
    have h := setIntegral_sectionMeasure hS MeasurableSet.univ
    rw [Measure.restrict_univ] at h
    rw [h]; congr 2; ext p; simp
  have hsint : Integrable s unitμ :=
    Integrable.of_bound hsm.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sectionMeasure_mem_Icc S x).1]
        exact (sectionMeasure_mem_Icc S x).2)
  have hφint : Integrable (fun x => φ (s x)) unitμ := by
    obtain ⟨M, hM⟩ : ∃ M, ∀ t ∈ Icc (0:ℝ) 1, |φ t| ≤ M :=
      ⟨φ 1, fun t ht => by rw [abs_of_nonneg (hφnn t ht)]
                           exact le_trans (hle1 t ht) (by nlinarith [ht.2, hφnn 1 ⟨zero_le_one, le_rfl⟩, ht.1])⟩
    exact Integrable.of_bound (hφm.comp hsm).aestronglyMeasurable M
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hM _ (sectionMeasure_mem_Icc S x))
  -- Markov: `|I| ≤ σ/τ`
  have hImeas : (unitμ I).toReal ≤ σ / τ := by
    rw [le_div_iff₀ hτ0, ← htot]
    have h1 : ∫ x in I, τ ∂unitμ ≤ ∫ x in I, s x ∂unitμ :=
      setIntegral_mono_on (integrable_const τ).integrableOn hsint.integrableOn hIm
        (fun x hx => hx)
    have h2 : ∫ x in I, s x ∂unitμ ≤ ∫ x, s x ∂unitμ :=
      setIntegral_le_integral hsint (Eventually.of_forall fun x => (sectionMeasure_mem_Icc S x).1)
    rw [setIntegral_const, smul_eq_mul] at h1
    have h3 := le_trans h1 h2
    simp only [Measure.real] at h3
    linarith
  -- symmetry: the two off-diagonal pieces of `S` have equal measure
  have hswap : gμ (S ∩ I ×ˢ Iᶜ) = gμ (S ∩ Iᶜ ×ˢ I) := by
    have hmp : MeasurePreserving Prod.swap gμ gμ := by
      unfold gμ; exact Measure.measurePreserving_swap
    have hpre : Prod.swap ⁻¹' (S ∩ Iᶜ ×ˢ I) = S ∩ I ×ˢ Iᶜ := by
      ext ⟨x, y⟩; simp [hsymm x y]
    rw [← hpre, hmp.measure_preimage (hS.inter (hIm.compl.prod hIm)).nullMeasurableSet]
  have hdisj : Disjoint (S ∩ I ×ˢ Iᶜ) (S ∩ Iᶜ ×ˢ I) := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨-, hx, -⟩ ⟨-, hx', -⟩
    exact hx' hx
  have hhalf : 2 * (gμ (S ∩ I ×ˢ Iᶜ)).toReal ≤ σ := by
    have hunion : gμ (S ∩ I ×ˢ Iᶜ) + gμ (S ∩ Iᶜ ×ˢ I) ≤ gμ S := by
      rw [← measure_union hdisj (hS.inter (hIm.compl.prod hIm))]
      exact measure_mono (union_subset inter_subset_left inter_subset_left)
    rw [hswap] at hunion ⊢
    have := ENNReal.toReal_mono (measure_ne_top _ _) hunion
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
    linarith
  -- `∫_I s ≤ |I|² + σ/2`
  have hIint : ∫ x in I, s x ∂unitμ ≤ (σ / τ) ^ 2 + σ / 2 := by
    rw [setIntegral_sectionMeasure hS hIm]
    have hsplit : S ∩ I ×ˢ univ ⊆ (I ×ˢ I) ∪ (S ∩ I ×ˢ Iᶜ) := by
      rintro ⟨x, y⟩ ⟨hS', hx, -⟩
      by_cases hy : y ∈ I
      · exact Or.inl ⟨hx, hy⟩
      · exact Or.inr ⟨hS', hx, hy⟩
    have hm := measure_mono (μ := gμ) hsplit
    have hm2 := le_trans hm (measure_union_le _ _)
    have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,
      measure_ne_top _ _⟩) hm2
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hreal
    have hII : (gμ (I ×ˢ I)).toReal = (unitμ I).toReal ^ 2 := by
      unfold gμ; rw [Measure.prod_prod, ENNReal.toReal_mul]; ring
    have hI0 : 0 ≤ (unitμ I).toReal := ENNReal.toReal_nonneg
    have hsq : (unitμ I).toReal ^ 2 ≤ (σ / τ) ^ 2 := pow_le_pow_left₀ hI0 hImeas 2
    linarith
  -- assemble
  have hsplitInt : ∫ x, φ (s x) ∂unitμ
      = ∫ x in I, φ (s x) ∂unitμ + ∫ x in Iᶜ, φ (s x) ∂unitμ :=
    (integral_add_compl hIm hφint).symm
  have hA : ∫ x in I, φ (s x) ∂unitμ ≤ φ 1 * ∫ x in I, s x ∂unitμ := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hφint.integrableOn (hsint.const_mul _).integrableOn hIm
      (fun x _ => ?_)
    have := hle1 (s x) (sectionMeasure_mem_Icc S x)
    linarith
  have hB : ∫ x in Iᶜ, φ (s x) ∂unitμ ≤ φ τ / τ * σ := by
    have h1 : ∫ x in Iᶜ, φ (s x) ∂unitμ ≤ ∫ x in Iᶜ, φ τ / τ * s x ∂unitμ := by
      refine setIntegral_mono_on hφint.integrableOn (hsint.const_mul _).integrableOn
        hIm.compl (fun x hx => ?_)
      have hxI : s x < τ := not_le.mp hx
      have := hleτ (s x) ⟨(sectionMeasure_mem_Icc S x).1, hxI.le⟩
      calc φ (s x) ≤ s x / τ * φ τ := this
        _ = φ τ / τ * s x := by ring
    have hcoef : 0 ≤ φ τ / τ := div_nonneg (hφnn τ ⟨hτ0.le, hτ1⟩) hτ0.le
    have h2 : ∫ x in Iᶜ, φ τ / τ * s x ∂unitμ ≤ φ τ / τ * σ := by
      rw [integral_const_mul, ← htot]
      exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hsint
        (Eventually.of_forall fun x => (sectionMeasure_mem_Icc S x).1)) hcoef
    linarith
  have hφ1 : 0 ≤ φ 1 := hφnn 1 ⟨zero_le_one, le_rfl⟩
  have hfin : φ 1 * ∫ x in I, s x ∂unitμ ≤ φ 1 * (σ / 2 + σ ^ 2 / τ ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hφ1
    have : (σ / τ) ^ 2 = σ ^ 2 / τ ^ 2 := by ring
    linarith
  linarith

end UpperTailOptimizers
