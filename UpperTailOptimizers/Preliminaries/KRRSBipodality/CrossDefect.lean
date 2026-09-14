import UpperTailOptimizers.Preliminaries.KRRSBipodality.Cross

/-!
# The cross lemma with its defect

`integral_convex_sectionMeasure_le` bounds `∫ φ(s_x)` by `φ(1)|S|/2` up to small terms.  For the
structure of competitors (`kb:prop:structure`) we need the converse information: if `∫ φ(s_x)` is
close to `φ(1)|S|/2`, then `S` is close to a cross `(I × Iᶜ) ∪ (Iᶜ × I)`.  This file records the
defect terms of the cross lemma (`cross_defect`) and turns them into a bound on the symmetric
difference between `S` and the cross over `I = {s_x ≥ 1/2}` (`measure_symmDiff_cross_le`).
-/

namespace UpperTailOptimizers

open MeasureTheory Set Filter

/-- The cross `(I × Iᶜ) ∪ (Iᶜ × I)`. -/
def crossSet (I : Set ℝ) : Set (ℝ × ℝ) := I ×ˢ Iᶜ ∪ Iᶜ ×ˢ I

theorem measurableSet_crossSet {I : Set ℝ} (hI : MeasurableSet I) :
    MeasurableSet (crossSet I) :=
  (hI.prod hI.compl).union (hI.compl.prod hI)

/-- For a symmetric `S`, the pieces `S ∩ (A × B)` and `S ∩ (B × A)` have equal measure. -/
theorem measure_inter_prod_swap {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hsymm : ∀ x y, (x, y) ∈ S ↔ (y, x) ∈ S) {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) : gμ (S ∩ A ×ˢ B) = gμ (S ∩ B ×ˢ A) := by
  have hmp : MeasurePreserving Prod.swap gμ gμ := by
    unfold gμ; exact Measure.measurePreserving_swap
  have hpre : Prod.swap ⁻¹' (S ∩ B ×ˢ A) = S ∩ A ×ˢ B := by
    ext ⟨x, y⟩; simp [hsymm x y, and_comm]
  rw [← hpre, hmp.measure_preimage (hS.inter (hB.prod hA)).nullMeasurableSet]

theorem sectionMeasure_integrable (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    Integrable (sectionMeasure S) unitμ :=
  Integrable.of_bound (measurable_sectionMeasure hS).aestronglyMeasurable 1
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sectionMeasure_mem_Icc S x).1]
      exact (sectionMeasure_mem_Icc S x).2)

/-- `∫ s_x = |S|`. -/
theorem integral_sectionMeasure {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) :
    ∫ x, sectionMeasure S x ∂unitμ = (gμ S).toReal := by
  have h := setIntegral_sectionMeasure hS MeasurableSet.univ
  rw [Measure.restrict_univ] at h
  rw [h]; congr 2; ext p; simp

/-- The four pieces of `S` cut out by `I` and `Iᶜ`: `|S| = |S∩I×I| + 2|S∩I×Iᶜ| + |S∩Iᶜ×Iᶜ|`. -/
theorem measure_eq_four_pieces {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hsymm : ∀ x y, (x, y) ∈ S ↔ (y, x) ∈ S) {I : Set ℝ} (hI : MeasurableSet I) :
    (gμ S).toReal = (gμ (S ∩ I ×ˢ I)).toReal + 2 * (gμ (S ∩ I ×ˢ Iᶜ)).toReal
      + (gμ (S ∩ Iᶜ ×ˢ Iᶜ)).toReal := by
  have hswap := measure_inter_prod_swap hS hsymm hI hI.compl
  have h1 : S = (S ∩ I ×ˢ univ) ∪ (S ∩ Iᶜ ×ˢ univ) := by
    ext ⟨x, y⟩; by_cases hx : x ∈ I <;> simp [hx]
  have hrow : ∀ J : Set ℝ, MeasurableSet J →
      gμ (S ∩ J ×ˢ univ) = gμ (S ∩ J ×ˢ I) + gμ (S ∩ J ×ˢ Iᶜ) := by
    intro J hJ
    have hsplit : S ∩ J ×ˢ univ = (S ∩ J ×ˢ I) ∪ (S ∩ J ×ˢ Iᶜ) := by
      ext ⟨x, y⟩; by_cases hy : y ∈ I <;> simp [hy]
    rw [hsplit, measure_union _ (hS.inter (hJ.prod hI.compl))]
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨-, -, hy⟩ ⟨-, -, hy'⟩
    exact hy' hy
  have htot : gμ S = gμ (S ∩ I ×ˢ univ) + gμ (S ∩ Iᶜ ×ˢ univ) := by
    conv_lhs => rw [h1]
    rw [measure_union _ (hS.inter (hI.compl.prod MeasurableSet.univ))]
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨-, hx, -⟩ ⟨-, hx', -⟩
    exact hx' hx
  rw [htot, hrow I hI, hrow Iᶜ hI.compl, ← hswap]
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

/-- **The cross lemma with its defect terms.**  With `I = {s_x ≥ τ}`,

`∫ φ(s_x) + φ(1)|S ∩ Iᶜ×Iᶜ|/2 + ∫_I (φ(1)s_x - φ(s_x)) ≤ φ(1)|S|/2 + φ(1)|S ∩ I×I|/2 + Cτ|S|`

whenever `φ(s) ≤ C s²` on `[0,1]`. -/
theorem cross_defect {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hsymm : ∀ x y, (x, y) ∈ S ↔ (y, x) ∈ S) {φ : ℝ → ℝ} (hφm : Measurable φ)
    {C : ℝ} (hφq : ∀ s ∈ Icc (0:ℝ) 1, φ s ≤ C * s ^ 2) (hφnn : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ φ s)
    {τ : ℝ} (hτ0 : 0 < τ) :
    ∫ x, φ (sectionMeasure S x) ∂unitμ
        + φ 1 * (gμ (S ∩ {x | τ ≤ sectionMeasure S x}ᶜ ×ˢ {x | τ ≤ sectionMeasure S x}ᶜ)).toReal / 2
        + ∫ x in {x | τ ≤ sectionMeasure S x}, (φ 1 * sectionMeasure S x - φ (sectionMeasure S x)) ∂unitμ
      ≤ φ 1 * (gμ S).toReal / 2
        + φ 1 * (gμ (S ∩ {x | τ ≤ sectionMeasure S x} ×ˢ {x | τ ≤ sectionMeasure S x})).toReal / 2
        + C * τ * (gμ S).toReal := by
  classical
  set s := sectionMeasure S with hs
  set I : Set ℝ := {x | τ ≤ s x} with hI
  have hsm : Measurable s := measurable_sectionMeasure hS
  have hIm : MeasurableSet I := measurableSet_le measurable_const hsm
  have hsint := sectionMeasure_integrable S hS
  have hφb : ∀ x, |φ (s x)| ≤ |C| := fun x => by
    have hmem := sectionMeasure_mem_Icc S x
    rw [abs_of_nonneg (hφnn _ hmem)]
    calc φ (s x) ≤ C * s x ^ 2 := hφq _ hmem
      _ ≤ |C| * 1 := by
          have h1 : s x ^ 2 ≤ 1 := by nlinarith [hmem.1, hmem.2]
          nlinarith [le_abs_self C, abs_nonneg C, sq_nonneg (s x)]
      _ = |C| := mul_one _
  have hφint : Integrable (fun x => φ (s x)) unitμ :=
    Integrable.of_bound (hφm.comp hsm).aestronglyMeasurable |C|
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hφb x)
  have hφ1 : 0 ≤ φ 1 := hφnn 1 ⟨zero_le_one, le_rfl⟩
  -- the mass over `I`
  have hIs : ∫ x in I, s x ∂unitμ
      = (gμ (S ∩ I ×ˢ I)).toReal + (gμ (S ∩ I ×ˢ Iᶜ)).toReal := by
    rw [setIntegral_sectionMeasure hS hIm]
    have hsplit : S ∩ I ×ˢ univ = (S ∩ I ×ˢ I) ∪ (S ∩ I ×ˢ Iᶜ) := by
      ext ⟨x, y⟩; by_cases hy : y ∈ I <;> simp [hy]
    rw [hsplit, measure_union _ (hS.inter (hIm.prod hIm.compl)),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨-, -, hy⟩ ⟨-, -, hy'⟩
    exact hy' hy
  have hfour := measure_eq_four_pieces hS hsymm hIm
  -- the integral over `I`
  have hA : ∫ x in I, φ (s x) ∂unitμ
      = φ 1 * ∫ x in I, s x ∂unitμ - ∫ x in I, (φ 1 * s x - φ (s x)) ∂unitμ := by
    rw [integral_sub (hsint.const_mul _).integrableOn hφint.integrableOn, integral_const_mul]
    ring
  -- the integral over `Iᶜ`
  have hB : ∫ x in Iᶜ, φ (s x) ∂unitμ ≤ C * τ * (gμ S).toReal := by
    have h1 : ∫ x in Iᶜ, φ (s x) ∂unitμ ≤ ∫ x in Iᶜ, C * τ * s x ∂unitμ := by
      refine setIntegral_mono_on hφint.integrableOn (hsint.const_mul _).integrableOn
        hIm.compl (fun x hx => ?_)
      have hxI : s x < τ := not_le.mp hx
      have hmem := sectionMeasure_mem_Icc S x
      have hC : 0 ≤ C := by
        have := hφq 1 ⟨zero_le_one, le_rfl⟩
        nlinarith [hφnn 1 ⟨zero_le_one, le_rfl⟩]
      calc φ (s x) ≤ C * s x ^ 2 := hφq _ hmem
        _ = C * s x * s x := by ring
        _ ≤ C * τ * s x := by
            apply mul_le_mul_of_nonneg_right _ hmem.1
            exact mul_le_mul_of_nonneg_left hxI.le hC
    have hC : 0 ≤ C * τ := by
      have := hφq 1 ⟨zero_le_one, le_rfl⟩
      nlinarith [hφnn 1 ⟨zero_le_one, le_rfl⟩]
    have h2 : ∫ x in Iᶜ, C * τ * s x ∂unitμ ≤ C * τ * (gμ S).toReal := by
      rw [integral_const_mul, ← integral_sectionMeasure hS]
      exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hsint
        (Eventually.of_forall fun x => (sectionMeasure_mem_Icc S x).1)) hC
    linarith
  have hsplitInt : ∫ x, φ (s x) ∂unitμ
      = ∫ x in I, φ (s x) ∂unitμ + ∫ x in Iᶜ, φ (s x) ∂unitμ :=
    (integral_add_compl hIm hφint).symm
  rw [hsplitInt, hA, hIs]
  have hpieces : (gμ (S ∩ I ×ˢ Iᶜ)).toReal
      = ((gμ S).toReal - (gμ (S ∩ I ×ˢ I)).toReal - (gμ (S ∩ Iᶜ ×ˢ Iᶜ)).toReal) / 2 := by
    linarith
  rw [hpieces]
  nlinarith [hB, hφ1]

/-- `|(A × ℝ) \ S| = ∫_A (1 - s_x)`. -/
theorem measure_prod_univ_diff {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) {A : Set ℝ}
    (hA : MeasurableSet A) :
    (gμ ((A ×ˢ univ) \ S)).toReal = ∫ x in A, (1 - sectionMeasure S x) ∂unitμ := by
  have hAu : gμ (A ×ˢ univ) = unitμ A := by
    unfold gμ; rw [Measure.prod_prod, measure_univ, mul_one]
  have hsplit : gμ (A ×ˢ univ) = gμ ((A ×ˢ univ) \ S) + gμ (S ∩ A ×ˢ univ) := by
    rw [← measure_union _ (hS.inter (hA.prod MeasurableSet.univ))]
    · congr 1; ext p; by_cases hp : p ∈ S <;> simp [hp]
    · rw [Set.disjoint_left]; rintro p ⟨-, hp⟩ ⟨hp', -⟩; exact hp hp'
  have hreal : (unitμ A).toReal = (gμ ((A ×ˢ univ) \ S)).toReal + (gμ (S ∩ A ×ˢ univ)).toReal := by
    rw [← hAu, hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  rw [integral_sub (integrable_const 1).integrableOn (sectionMeasure_integrable S hS).integrableOn,
    setIntegral_sectionMeasure hS hA, setIntegral_const, smul_eq_mul, mul_one]
  simp only [Measure.real]
  linarith

/-- **The symmetric difference with the cross.**  With `I_τ = {s_x ≥ τ}`, `I = {s_x ≥ 1/2}` and
`τ ≤ 1/2`, the part of `S` off the cross over `I`, and the part of the cross off `S`, are bounded
by the defect terms of `cross_defect`. -/
theorem measure_symmDiff_cross_le_aux {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hsymm : ∀ x y, (x, y) ∈ S ↔ (y, x) ∈ S) {τ : ℝ} (hτ : τ ≤ 1 / 2) :
    (gμ ((S \ crossSet {x | 1 / 2 ≤ sectionMeasure S x})
        ∪ (crossSet {x | 1 / 2 ≤ sectionMeasure S x} \ S))).toReal
      ≤ (gμ (S ∩ {x | τ ≤ sectionMeasure S x} ×ˢ {x | τ ≤ sectionMeasure S x})).toReal
        + (gμ (S ∩ {x | τ ≤ sectionMeasure S x}ᶜ ×ˢ {x | τ ≤ sectionMeasure S x}ᶜ)).toReal
        + 2 * ∫ x in {x | τ ≤ sectionMeasure S x} \ {x | 1 / 2 ≤ sectionMeasure S x},
            sectionMeasure S x ∂unitμ
        + 2 * ∫ x in {x | 1 / 2 ≤ sectionMeasure S x}, (1 - sectionMeasure S x) ∂unitμ := by
  classical
  set s := sectionMeasure S with hs
  set Iτ : Set ℝ := {x | τ ≤ s x} with hIτ
  set I : Set ℝ := {x | 1 / 2 ≤ s x} with hIdef
  have hsm : Measurable s := measurable_sectionMeasure hS
  have hIτm : MeasurableSet Iτ := measurableSet_le measurable_const hsm
  have hIm : MeasurableSet I := measurableSet_le measurable_const hsm
  have hsub : I ⊆ Iτ := fun x hx => le_trans hτ hx
  have hJm : MeasurableSet (Iτ \ I) := hIτm.diff hIm
  -- the covering
  have hcover : (S \ crossSet I) ∪ (crossSet I \ S)
      ⊆ (S ∩ Iτ ×ˢ Iτ) ∪ (S ∩ Iτᶜ ×ˢ Iτᶜ) ∪ (S ∩ (Iτ \ I) ×ˢ univ) ∪ (S ∩ univ ×ˢ (Iτ \ I))
        ∪ ((I ×ˢ univ) \ S) ∪ (Iᶜ ×ˢ I \ S) := by
    rintro ⟨x, y⟩ hp
    rcases hp with ⟨hS', hnX⟩ | ⟨hX, hnS⟩
    · have hnX' : ¬ ((x ∈ I ∧ y ∉ I) ∨ (x ∉ I ∧ y ∈ I)) := by
        simpa [crossSet] using hnX
      by_cases hxI : x ∈ I
      · have hyI : y ∈ I := by
          by_contra hyI
          exact hnX' (Or.inl ⟨hxI, hyI⟩)
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hS', hsub hxI, hsub hyI⟩))))
      · have hyI : y ∉ I := by
          intro hyI
          exact hnX' (Or.inr ⟨hxI, hyI⟩)
        by_cases hxτ : x ∈ Iτ
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hS', ⟨hxτ, hxI⟩, Set.mem_univ _⟩)))
        · by_cases hyτ : y ∈ Iτ
          · exact Or.inl (Or.inl (Or.inr ⟨hS', Set.mem_univ _, ⟨hyτ, hyI⟩⟩))
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hS', hxτ, hyτ⟩))))
    · rcases hX with ⟨hxI, hyI⟩ | ⟨hxI, hyI⟩
      · exact Or.inl (Or.inr ⟨⟨hxI, Set.mem_univ _⟩, hnS⟩)
      · exact Or.inr ⟨⟨hxI, hyI⟩, hnS⟩
  have hswap1 : gμ (S ∩ univ ×ˢ (Iτ \ I)) = gμ (S ∩ (Iτ \ I) ×ˢ univ) :=
    measure_inter_prod_swap hS hsymm MeasurableSet.univ hJm
  have hswap2 : gμ (Iᶜ ×ˢ I \ S) ≤ gμ ((I ×ˢ univ) \ S) := by
    have hmp : MeasurePreserving Prod.swap gμ gμ := by
      unfold gμ; exact Measure.measurePreserving_swap
    have hpre : Prod.swap ⁻¹' (I ×ˢ Iᶜ \ S) = Iᶜ ×ˢ I \ S := by
      ext ⟨x, y⟩; simp [hsymm y x, and_comm]
    rw [← hpre, hmp.measure_preimage ((hIm.prod hIm.compl).diff hS).nullMeasurableSet]
    exact measure_mono (Set.sdiff_subset_sdiff_left (Set.prod_mono le_rfl (Set.subset_univ _)))
  have hbound := measure_mono (μ := gμ) hcover
  have hunion : gμ ((S ∩ Iτ ×ˢ Iτ) ∪ (S ∩ Iτᶜ ×ˢ Iτᶜ) ∪ (S ∩ (Iτ \ I) ×ˢ univ)
        ∪ (S ∩ univ ×ˢ (Iτ \ I)) ∪ ((I ×ˢ univ) \ S) ∪ (Iᶜ ×ˢ I \ S))
      ≤ gμ (S ∩ Iτ ×ˢ Iτ) + gμ (S ∩ Iτᶜ ×ˢ Iτᶜ) + gμ (S ∩ (Iτ \ I) ×ˢ univ)
        + gμ (S ∩ (Iτ \ I) ×ˢ univ) + gμ ((I ×ˢ univ) \ S) + gμ ((I ×ˢ univ) \ S) := by
    refine le_trans (measure_union_le _ _) (add_le_add ?_ hswap2)
    refine le_trans (measure_union_le _ _) (add_le_add ?_ le_rfl)
    refine le_trans (measure_union_le _ _) (add_le_add ?_ (le_of_eq hswap1))
    refine le_trans (measure_union_le _ _) (add_le_add ?_ le_rfl)
    exact measure_union_le _ _
  have htot := le_trans hbound hunion
  have hreal := ENNReal.toReal_mono (by simp [measure_ne_top]) htot
  simp only [ENNReal.toReal_add, measure_ne_top, ne_eq, not_false_eq_true,
    ENNReal.add_eq_top, or_self] at hreal
  rw [setIntegral_sectionMeasure hS hJm, ← measure_prod_univ_diff hS hIm]
  linarith

/-- The tent bound from convexity: `φ(1)s - φ(s) ≥ 2γ min(s, 1-s)` where
`γ = φ(1)/2 - φ(1/2)`. -/
theorem convex_tent_left {φ : ℝ → ℝ} (hφc : ConvexOn ℝ (Icc 0 1) φ) (hφ0 : φ 0 = 0)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    2 * (φ 1 / 2 - φ (1 / 2)) * s ≤ φ 1 * s - φ s := by
  have h := hφc.2 (left_mem_Icc.mpr zero_le_one) (show (1/2 : ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
    (show (0:ℝ) ≤ 1 - 2 * s by linarith) (show (0:ℝ) ≤ 2 * s by linarith) (by ring)
  have hpt : (1 - 2 * s) • (0:ℝ) + (2 * s) • (1 / 2 : ℝ) = s := by
    simp only [smul_eq_mul]; ring
  rw [hpt, hφ0] at h
  simp only [smul_eq_mul, mul_zero, zero_add] at h
  nlinarith

theorem convex_tent_right {φ : ℝ → ℝ} (hφc : ConvexOn ℝ (Icc 0 1) φ)
    {s : ℝ} (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    2 * (φ 1 / 2 - φ (1 / 2)) * (1 - s) ≤ φ 1 * s - φ s := by
  have h := hφc.2 (show (1/2 : ℝ) ∈ Icc (0:ℝ) 1 by norm_num) (right_mem_Icc.mpr zero_le_one)
    (show (0:ℝ) ≤ 2 - 2 * s by linarith) (show (0:ℝ) ≤ 2 * s - 1 by linarith) (by ring)
  have hpt : (2 - 2 * s) • (1 / 2 : ℝ) + (2 * s - 1) • (1:ℝ) = s := by
    simp only [smul_eq_mul]; ring
  rw [hpt] at h
  simp only [smul_eq_mul] at h
  nlinarith

/-- A convex `φ` on `[0,1]` with `φ(0) = 0` lies below its chord: `φ(s) ≤ s φ(1)`. -/
theorem convex_le_chord {φ : ℝ → ℝ} (hφc : ConvexOn ℝ (Icc 0 1) φ) (hφ0 : φ 0 = 0) {s : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) : φ s ≤ s * φ 1 := by
  have h := hφc.2 (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
    (sub_nonneg.mpr hs.2) hs.1 (by ring)
  simpa [hφ0] using h

/-- Markov: `|{s_x ≥ τ}| ≤ |S|/τ`. -/
theorem measure_sectionMeasure_ge_le {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) {τ : ℝ}
    (hτ0 : 0 < τ) : (unitμ {x | τ ≤ sectionMeasure S x}).toReal ≤ (gμ S).toReal / τ := by
  have hsm := measurable_sectionMeasure hS
  have hIm : MeasurableSet {x | τ ≤ sectionMeasure S x} := measurableSet_le measurable_const hsm
  have hsint := sectionMeasure_integrable S hS
  rw [le_div_iff₀ hτ0, ← integral_sectionMeasure hS]
  have h1 : ∫ x in {x | τ ≤ sectionMeasure S x}, τ ∂unitμ
      ≤ ∫ x in {x | τ ≤ sectionMeasure S x}, sectionMeasure S x ∂unitμ :=
    setIntegral_mono_on (integrable_const τ).integrableOn hsint.integrableOn hIm (fun x hx => hx)
  have h2 : ∫ x in {x | τ ≤ sectionMeasure S x}, sectionMeasure S x ∂unitμ
      ≤ ∫ x, sectionMeasure S x ∂unitμ :=
    setIntegral_le_integral hsint (Eventually.of_forall fun x => (sectionMeasure_mem_Icc S x).1)
  rw [setIntegral_const, smul_eq_mul] at h1
  simp only [Measure.real] at h1
  linarith

/-- **Near-equality in the cross lemma forces a cross.**  Let `γ ≤ φ(1)/2 - φ(1/2)` be positive,
`0 < τ ≤ 1/2`, `I = {s_x ≥ 1/2}`, and let
`E = (φ(1)|S|/2 - ∫ φ(s_x)) + φ(1)(|S|/τ)²/2 + Cτ|S|`.  Then

* `|S △ ((I × Iᶜ) ∪ (Iᶜ × I))| ≤ (|S|/τ)² + 2E/γ`;
* `∫ φ(s_x) ≤ φ(1)|I| + C(E/(2γ) + τ|S|)`. -/
theorem cross_structure {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hsymm : ∀ x y, (x, y) ∈ S ↔ (y, x) ∈ S) {φ : ℝ → ℝ} (hφm : Measurable φ)
    (hφc : ConvexOn ℝ (Icc 0 1) φ) (hφ0 : φ 0 = 0)
    {C : ℝ} (hφq : ∀ s ∈ Icc (0:ℝ) 1, φ s ≤ C * s ^ 2) (hφnn : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ φ s)
    {γ : ℝ} (hγ : 0 < γ) (hγle : γ ≤ φ 1 / 2 - φ (1 / 2))
    {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2) :
    (gμ ((S \ crossSet {x | 1 / 2 ≤ sectionMeasure S x})
        ∪ (crossSet {x | 1 / 2 ≤ sectionMeasure S x} \ S))).toReal
      ≤ ((gμ S).toReal / τ) ^ 2 + 2 / γ * ((φ 1 * (gμ S).toReal / 2
          - ∫ x, φ (sectionMeasure S x) ∂unitμ)
          + φ 1 * ((gμ S).toReal / τ) ^ 2 / 2 + C * τ * (gμ S).toReal) ∧
    ∫ x, φ (sectionMeasure S x) ∂unitμ
      ≤ φ 1 * (unitμ {x | 1 / 2 ≤ sectionMeasure S x}).toReal
        + C * (1 / (2 * γ) * ((φ 1 * (gμ S).toReal / 2 - ∫ x, φ (sectionMeasure S x) ∂unitμ)
          + φ 1 * ((gμ S).toReal / τ) ^ 2 / 2 + C * τ * (gμ S).toReal) + τ * (gμ S).toReal) := by
  classical
  set s := sectionMeasure S with hs
  set σ : ℝ := (gμ S).toReal with hσ
  set Iτ : Set ℝ := {x | τ ≤ s x} with hIτ
  set I : Set ℝ := {x | 1 / 2 ≤ s x} with hIdef
  set E : ℝ := (φ 1 * σ / 2 - ∫ x, φ (s x) ∂unitμ) + φ 1 * (σ / τ) ^ 2 / 2 + C * τ * σ with hE
  have hsm : Measurable s := measurable_sectionMeasure hS
  have hIτm : MeasurableSet Iτ := measurableSet_le measurable_const hsm
  have hIm : MeasurableSet I := measurableSet_le measurable_const hsm
  have hsub : I ⊆ Iτ := fun x hx => le_trans hτ hx
  have hsint := sectionMeasure_integrable S hS
  have hφ1 : 0 ≤ φ 1 := hφnn 1 ⟨zero_le_one, le_rfl⟩
  have hφh : 0 ≤ φ (1 / 2) := hφnn _ (by norm_num)
  have hC : 0 ≤ C := by
    have := hφq 1 ⟨zero_le_one, le_rfl⟩
    nlinarith
  have hσ0 : 0 ≤ σ := ENNReal.toReal_nonneg
  have hφb : ∀ x, |φ (s x)| ≤ |C| := fun x => by
    have hmem := sectionMeasure_mem_Icc S x
    rw [abs_of_nonneg (hφnn _ hmem)]
    calc φ (s x) ≤ C * s x ^ 2 := hφq _ hmem
      _ ≤ |C| * 1 := by
          have h1 : s x ^ 2 ≤ 1 := by nlinarith [hmem.1, hmem.2]
          nlinarith [le_abs_self C, abs_nonneg C, sq_nonneg (s x)]
      _ = |C| := mul_one _
  have hφint : Integrable (fun x => φ (s x)) unitμ :=
    Integrable.of_bound (hφm.comp hsm).aestronglyMeasurable |C|
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hφb x)
  have hgint : Integrable (fun x => φ 1 * s x - φ (s x)) unitμ := (hsint.const_mul _).sub hφint
  -- the defect inequality
  have hdef := cross_defect hS hsymm hφm hφq hφnn hτ0
  have hAle : (gμ (S ∩ Iτ ×ˢ Iτ)).toReal ≤ (σ / τ) ^ 2 := by
    have h1 : gμ (S ∩ Iτ ×ˢ Iτ) ≤ gμ (Iτ ×ˢ Iτ) := measure_mono Set.inter_subset_right
    have h2 : (gμ (Iτ ×ˢ Iτ)).toReal = (unitμ Iτ).toReal ^ 2 := by
      unfold gμ; rw [Measure.prod_prod, ENNReal.toReal_mul]; ring
    have h3 := measure_sectionMeasure_ge_le hS hτ0
    have h4 : (unitμ Iτ).toReal ^ 2 ≤ (σ / τ) ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg h3 2
    have := ENNReal.toReal_mono (measure_ne_top _ _) h1
    linarith
  have hA0 : 0 ≤ (gμ (S ∩ Iτ ×ˢ Iτ)).toReal := ENNReal.toReal_nonneg
  have hC0 : 0 ≤ (gμ (S ∩ Iτᶜ ×ˢ Iτᶜ)).toReal := ENNReal.toReal_nonneg
  -- consequences of the defect inequality
  have hgE : ∫ x in Iτ, (φ 1 * s x - φ (s x)) ∂unitμ ≤ E := by
    have : φ 1 * (gμ (S ∩ Iτᶜ ×ˢ Iτᶜ)).toReal / 2 ≥ 0 := by positivity
    have h := mul_le_mul_of_nonneg_left hAle hφ1
    simp only [hE]
    nlinarith [hdef]
  have hCE : φ 1 * (gμ (S ∩ Iτᶜ ×ˢ Iτᶜ)).toReal / 2 ≤ E := by
    have hg0 : 0 ≤ ∫ x in Iτ, (φ 1 * s x - φ (s x)) ∂unitμ := by
      refine setIntegral_nonneg hIτm fun x _ => ?_
      have := convex_le_chord hφc hφ0 (sectionMeasure_mem_Icc S x)
      linarith
    have h := mul_le_mul_of_nonneg_left hAle hφ1
    simp only [hE]
    nlinarith [hdef]
  -- the tent bounds
  have hgsplit : ∫ x in Iτ, (φ 1 * s x - φ (s x)) ∂unitμ
      = ∫ x in Iτ \ I, (φ 1 * s x - φ (s x)) ∂unitμ + ∫ x in I, (φ 1 * s x - φ (s x)) ∂unitμ := by
    rw [← setIntegral_union Set.disjoint_sdiff_left hIm hgint.integrableOn hgint.integrableOn,
      Set.sdiff_union_of_subset hsub]
  have htent1 : 2 * γ * ∫ x in Iτ \ I, s x ∂unitμ
      ≤ ∫ x in Iτ \ I, (φ 1 * s x - φ (s x)) ∂unitμ := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hsint.const_mul _).integrableOn hgint.integrableOn
      (hIτm.diff hIm) fun x hx => ?_
    have hmem := sectionMeasure_mem_Icc S x
    have hlt : s x < 1 / 2 := not_le.mp hx.2
    have := convex_tent_left hφc hφ0 hmem.1 hlt.le
    nlinarith [hmem.1]
  have htent2 : 2 * γ * ∫ x in I, (1 - s x) ∂unitμ
      ≤ ∫ x in I, (φ 1 * s x - φ (s x)) ∂unitμ := by
    rw [← integral_const_mul]
    have hint1 : Integrable (fun x => 2 * γ * (1 - s x)) unitμ :=
      ((integrable_const 1).sub hsint).const_mul _
    refine setIntegral_mono_on hint1.integrableOn hgint.integrableOn hIm fun x hx => ?_
    have hmem := sectionMeasure_mem_Icc S x
    have := convex_tent_right hφc hx hmem.2
    nlinarith [hmem.2]
  have hint1 : 0 ≤ ∫ x in Iτ \ I, s x ∂unitμ :=
    setIntegral_nonneg (hIτm.diff hIm) fun x _ => (sectionMeasure_mem_Icc S x).1
  have hint2 : 0 ≤ ∫ x in I, (1 - s x) ∂unitμ :=
    setIntegral_nonneg hIm fun x _ => sub_nonneg.mpr (sectionMeasure_mem_Icc S x).2
  have hsum : ∫ x in Iτ \ I, s x ∂unitμ + ∫ x in I, (1 - s x) ∂unitμ ≤ E / (2 * γ) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hgE, hgsplit, htent1, htent2]
  constructor
  · have haux := measure_symmDiff_cross_le_aux hS hsymm hτ
    have hCτ : (gμ (S ∩ Iτᶜ ×ˢ Iτᶜ)).toReal ≤ E / γ := by
      have hφ1γ : 2 * γ ≤ φ 1 := by linarith
      rw [le_div_iff₀ hγ]
      nlinarith [hCE, hC0]
    have hfin : 2 * (∫ x in Iτ \ I, s x ∂unitμ) + 2 * (∫ x in I, (1 - s x) ∂unitμ) ≤ E / γ := by
      have : E / (2 * γ) = E / γ / 2 := by field_simp
      nlinarith [hsum]
    calc _ ≤ (gμ (S ∩ Iτ ×ˢ Iτ)).toReal + (gμ (S ∩ Iτᶜ ×ˢ Iτᶜ)).toReal
          + 2 * ∫ x in Iτ \ I, s x ∂unitμ + 2 * ∫ x in I, (1 - s x) ∂unitμ := haux
      _ ≤ (σ / τ) ^ 2 + E / γ + E / γ := by linarith
      _ = (σ / τ) ^ 2 + 2 / γ * E := by ring
  · -- the lower bound on `|I|`
    have hsplitInt : ∫ x, φ (s x) ∂unitμ
        = ∫ x in I, φ (s x) ∂unitμ + ∫ x in Iᶜ, φ (s x) ∂unitμ :=
      (integral_add_compl hIm hφint).symm
    have hI1 : ∫ x in I, φ (s x) ∂unitμ ≤ φ 1 * (unitμ I).toReal := by
      have hpt : ∀ x ∈ I, φ (s x) ≤ φ 1 := fun x _ => by
        have hmem := sectionMeasure_mem_Icc S x
        calc φ (s x) ≤ s x * φ 1 := convex_le_chord hφc hφ0 hmem
          _ ≤ 1 * φ 1 := mul_le_mul_of_nonneg_right hmem.2 hφ1
          _ = φ 1 := one_mul _
      have h := setIntegral_mono_on hφint.integrableOn (integrable_const (φ 1)).integrableOn hIm hpt
      rw [setIntegral_const, smul_eq_mul] at h
      simp only [Measure.real] at h
      linarith
    have hI2 : ∫ x in Iᶜ, φ (s x) ∂unitμ ≤ C * (∫ x in Iτ \ I, s x ∂unitμ + τ * σ) := by
      have hIc : Iᶜ = (Iτ \ I) ∪ Iτᶜ := by
        ext x; simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff]
        constructor
        · intro hx; by_cases h : x ∈ Iτ
          · exact Or.inl ⟨h, hx⟩
          · exact Or.inr h
        · rintro (⟨-, h⟩ | h)
          · exact h
          · exact fun hI => h (hsub hI)
      have hdisj : Disjoint (Iτ \ I) Iτᶜ := Set.disjoint_left.mpr fun x hx hx' => hx' hx.1
      rw [hIc, setIntegral_union hdisj hIτm.compl hφint.integrableOn hφint.integrableOn]
      have h1 : ∫ x in Iτ \ I, φ (s x) ∂unitμ ≤ C * ∫ x in Iτ \ I, s x ∂unitμ := by
        rw [← integral_const_mul]
        refine setIntegral_mono_on hφint.integrableOn (hsint.const_mul _).integrableOn
          (hIτm.diff hIm) fun x _ => ?_
        have hmem := sectionMeasure_mem_Icc S x
        calc φ (s x) ≤ C * s x ^ 2 := hφq _ hmem
          _ ≤ C * s x := by
              apply mul_le_mul_of_nonneg_left _ hC
              calc s x ^ 2 = s x * s x := sq _
                _ ≤ 1 * s x := mul_le_mul_of_nonneg_right hmem.2 hmem.1
                _ = s x := one_mul _
      have h2 : ∫ x in Iτᶜ, φ (s x) ∂unitμ ≤ C * τ * σ := by
        have h3 : ∫ x in Iτᶜ, φ (s x) ∂unitμ ≤ ∫ x in Iτᶜ, C * τ * s x ∂unitμ := by
          refine setIntegral_mono_on hφint.integrableOn (hsint.const_mul _).integrableOn
            hIτm.compl fun x hx => ?_
          have hxI : s x < τ := not_le.mp hx
          have hmem := sectionMeasure_mem_Icc S x
          calc φ (s x) ≤ C * s x ^ 2 := hφq _ hmem
            _ = C * s x * s x := by ring
            _ ≤ C * τ * s x := by
                apply mul_le_mul_of_nonneg_right _ hmem.1
                exact mul_le_mul_of_nonneg_left hxI.le hC
        have h4 : ∫ x in Iτᶜ, C * τ * s x ∂unitμ ≤ C * τ * σ := by
          rw [integral_const_mul, hσ, ← integral_sectionMeasure hS]
          exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hsint
            (Eventually.of_forall fun x => (sectionMeasure_mem_Icc S x).1)) (by positivity)
        linarith
      calc ∫ x in Iτ \ I, φ (s x) ∂unitμ + ∫ x in Iτᶜ, φ (s x) ∂unitμ
          ≤ C * ∫ x in Iτ \ I, s x ∂unitμ + C * τ * σ := add_le_add h1 h2
        _ = C * (∫ x in Iτ \ I, s x ∂unitμ + τ * σ) := by rw [mul_add, mul_assoc]
    have hsum' : ∫ x in Iτ \ I, s x ∂unitμ ≤ 1 / (2 * γ) * E := by
      have : E / (2 * γ) = 1 / (2 * γ) * E := by ring
      linarith
    calc ∫ x, φ (s x) ∂unitμ
        = ∫ x in I, φ (s x) ∂unitμ + ∫ x in Iᶜ, φ (s x) ∂unitμ := hsplitInt
      _ ≤ φ 1 * (unitμ I).toReal + C * (∫ x in Iτ \ I, s x ∂unitμ + τ * σ) := add_le_add hI1 hI2
      _ ≤ φ 1 * (unitμ I).toReal + C * (1 / (2 * γ) * E + τ * σ) := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hsum' le_rfl) hC)

end UpperTailOptimizers
