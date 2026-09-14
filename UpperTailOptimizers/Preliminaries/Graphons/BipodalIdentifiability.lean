import UpperTailOptimizers.Preliminaries.Graphons.BipodalBridge

/-!
# Identifiability of the parameters of a nonconstant two-block graphon

`thm:krrs-bipodality` (`paper/sections/appendix_preliminaries.tex`) speaks of *the* parameters
`(c, q₁₁, q₁₂, q₂₂)` of the entropy maximizer, which is only unique up to relabelling.  That
these parameters are well defined is the content of this file: a nonconstant two-block kernel
whose smaller block is `[0,c]` with `c < 1/2` determines `c` and the three levels, even after a
measure-preserving relabelling.

* `eq_of_ae_eq_of_const_on_prod` — two a.e.-equal kernels that are constant on a product of
  sets of positive measure take the same constant there;
* `bipodalValue_of_mem_of_mem` and its three companions — the value of the two-block kernel on
  each of the four block products;
* `bipodalValue_ae_eq_unique` — if two nonconstant two-block kernels on blocks `A`, `B` agree
  a.e., `A` is not null and `Aᶜ ∩ Bᶜ` is not null, then `A = B` a.e. and the three levels
  coincide;
* `unitμ_Icc_eq_ofReal` — `unitμ [0,c] = c` as an extended real;
* `bipodal_params_eq_of_relabel` — the relabelling-invariant form: two graphons that are a.e.
  two-block on `[0,c]`, `[0,c']` with `c, c' ∈ (0,1/2)` and nonconstant levels, and that differ
  by a relabelling, have `c = c'` and the same levels.

## Proof

Cut `[0,1]` into the four cells `A ∩ B`, `A ∩ Bᶜ`, `Aᶜ ∩ B`, `Aᶜ ∩ Bᶜ`; both kernels are
constant on each product of two cells.  On `(Aᶜ ∩ Bᶜ)²` this gives `q₂₂ = p₂₂`.  If `A ∩ Bᶜ`
were not null, the products `(A ∩ Bᶜ)²` and `(A ∩ Bᶜ) × (Aᶜ ∩ Bᶜ)` would give
`q₁₁ = p₂₂ = q₁₂`, so the first kernel would be constant; symmetrically for `Aᶜ ∩ B`.  Hence
`A ∩ B` carries all of `A`, and the products `(A ∩ B)²`, `(A ∩ B) × (Aᶜ ∩ Bᶜ)` give
`q₁₁ = p₁₁`, `q₁₂ = p₁₂`.  A relabelling `σ` turns the block `[0,c]` into `σ⁻¹[0,c]`, of the same
measure `c`, and `c + c' < 1` makes `Aᶜ ∩ Bᶜ` non-null.
-/

namespace UpperTailOptimizers

open MeasureTheory

/-- **Two a.e.-equal kernels agree on a non-null product where both are constant.**  If
`F = G` `gμ`-a.e., `F ≡ x` and `G ≡ y` on `S × T`, and `S`, `T` have positive `unitμ`-measure,
then `x = y`. -/
theorem eq_of_ae_eq_of_const_on_prod {F G : ℝ × ℝ → ℝ} (hFG : ∀ᵐ z ∂gμ, F z = G z)
    {S T : Set ℝ} (hS : unitμ S ≠ 0) (hT : unitμ T ≠ 0) {x y : ℝ}
    (hF : ∀ z ∈ S ×ˢ T, F z = x) (hG : ∀ z ∈ S ×ˢ T, G z = y) : x = y := by
  by_contra hxy
  have hsub : S ×ˢ T ⊆ {z | ¬F z = G z} := fun z hz => by
    simp only [Set.mem_ofPred_eq, hF z hz, hG z hz]
    exact hxy
  have h0 : gμ (S ×ˢ T) = 0 := measure_mono_null hsub (ae_iff.mp hFG)
  rw [gμ, Measure.prod_prod] at h0
  exact mul_ne_zero hS hT h0

/-! ### The two-block value on the four cells -/

/-- The two-block value on `A × A` is `q₁₁`. -/
theorem bipodalValue_of_mem_of_mem {A : Set ℝ} {q11 q12 q22 : ℝ} {z : ℝ × ℝ} (h1 : z.1 ∈ A)
    (h2 : z.2 ∈ A) : bipodalValue A q11 q12 q22 z = q11 := by
  simp [bipodalValue, h1, h2]

/-- The two-block value on `A × Aᶜ` is `q₁₂`. -/
theorem bipodalValue_of_mem_of_notMem {A : Set ℝ} {q11 q12 q22 : ℝ} {z : ℝ × ℝ} (h1 : z.1 ∈ A)
    (h2 : z.2 ∉ A) : bipodalValue A q11 q12 q22 z = q12 := by
  simp [bipodalValue, h1, h2]

/-- The two-block value on `Aᶜ × A` is `q₁₂`. -/
theorem bipodalValue_of_notMem_of_mem {A : Set ℝ} {q11 q12 q22 : ℝ} {z : ℝ × ℝ} (h1 : z.1 ∉ A)
    (h2 : z.2 ∈ A) : bipodalValue A q11 q12 q22 z = q12 := by
  simp [bipodalValue, h1, h2]

/-- The two-block value on `Aᶜ × Aᶜ` is `q₂₂`. -/
theorem bipodalValue_of_notMem_of_notMem {A : Set ℝ} {q11 q12 q22 : ℝ} {z : ℝ × ℝ}
    (h1 : z.1 ∉ A) (h2 : z.2 ∉ A) : bipodalValue A q11 q12 q22 z = q22 := by
  simp [bipodalValue, h1, h2]

/-- **Identifiability of a nonconstant two-block kernel.**  Let two two-block kernels, on
blocks `A` and `B`, with levels `(q₁₁,q₁₂,q₂₂)` and `(p₁₁,p₁₂,p₂₂)` that are not all equal,
agree `gμ`-a.e.  If `A` and `Aᶜ ∩ Bᶜ` are not `unitμ`-null, then `A` and `B` agree up to null
sets and the levels coincide. -/
theorem bipodalValue_ae_eq_unique {A B : Set ℝ} {q11 q12 q22 p11 p12 p22 : ℝ}
    (hA : unitμ A ≠ 0) (hAB : unitμ (Aᶜ ∩ Bᶜ) ≠ 0)
    (hq : ¬(q11 = q12 ∧ q12 = q22)) (hp : ¬(p11 = p12 ∧ p12 = p22))
    (h : ∀ᵐ z ∂gμ, bipodalValue A q11 q12 q22 z = bipodalValue B p11 p12 p22 z) :
    unitμ (A ∩ Bᶜ) = 0 ∧ unitμ (Aᶜ ∩ B) = 0 ∧ q11 = p11 ∧ q12 = p12 ∧ q22 = p22 := by
  -- the common value of the two kernels on a product of two non-null cells
  have key : ∀ {S T : Set ℝ}, unitμ S ≠ 0 → unitμ T ≠ 0 → ∀ {x y : ℝ},
      (∀ z ∈ S ×ˢ T, bipodalValue A q11 q12 q22 z = x) →
      (∀ z ∈ S ×ˢ T, bipodalValue B p11 p12 p22 z = y) → x = y := by
    intro S T hS hT x y hF hG
    exact eq_of_ae_eq_of_const_on_prod h hS hT hF hG
  have h22 : q22 = p22 :=
    key hAB hAB (fun z hz => bipodalValue_of_notMem_of_notMem hz.1.1 hz.2.1)
      (fun z hz => bipodalValue_of_notMem_of_notMem hz.1.2 hz.2.2)
  have hAB' : unitμ (A ∩ Bᶜ) = 0 := by
    by_contra hne
    have e1 : q12 = p22 :=
      key hne hAB (fun z hz => bipodalValue_of_mem_of_notMem hz.1.1 hz.2.1)
        (fun z hz => bipodalValue_of_notMem_of_notMem hz.1.2 hz.2.2)
    have e2 : q11 = p22 :=
      key hne hne (fun z hz => bipodalValue_of_mem_of_mem hz.1.1 hz.2.1)
        (fun z hz => bipodalValue_of_notMem_of_notMem hz.1.2 hz.2.2)
    exact hq ⟨e2.trans e1.symm, e1.trans h22.symm⟩
  have hBA' : unitμ (Aᶜ ∩ B) = 0 := by
    by_contra hne
    have e1 : q22 = p12 :=
      key hne hAB (fun z hz => bipodalValue_of_notMem_of_notMem hz.1.1 hz.2.1)
        (fun z hz => bipodalValue_of_mem_of_notMem hz.1.2 hz.2.2)
    have e2 : q22 = p11 :=
      key hne hne (fun z hz => bipodalValue_of_notMem_of_notMem hz.1.1 hz.2.1)
        (fun z hz => bipodalValue_of_mem_of_mem hz.1.2 hz.2.2)
    exact hp ⟨e2.symm.trans e1, e1.symm.trans h22⟩
  -- `A ∩ B` carries all of `A`
  have hI : unitμ (A ∩ B) ≠ 0 := by
    intro h0
    refine hA (measure_mono_null (fun x hx => ?_) (measure_union_null h0 hAB'))
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx, hxB⟩
    · exact Or.inr ⟨hx, hxB⟩
  have h11 : q11 = p11 :=
    key hI hI (fun z hz => bipodalValue_of_mem_of_mem hz.1.1 hz.2.1)
      (fun z hz => bipodalValue_of_mem_of_mem hz.1.2 hz.2.2)
  have h12 : q12 = p12 :=
    key hI hAB (fun z hz => bipodalValue_of_mem_of_notMem hz.1.1 hz.2.1)
      (fun z hz => bipodalValue_of_mem_of_notMem hz.1.2 hz.2.2)
  exact ⟨hAB', hBA', h11, h12, h22⟩

/-- `unitμ [0,c] = c` for `c ∈ [0,1]`, as an extended real. -/
theorem unitμ_Icc_eq_ofReal {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    unitμ (Set.Icc 0 c) = ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top unitμ (Set.Icc 0 c)), unitμ_Icc_toReal hc0 hc1]

/-- **The parameters of a nonconstant bipodal graphon are relabelling invariants.**  Let `W` be
a.e. the two-block kernel on `[0,c]` with levels `(q₁₁,q₁₂,q₂₂)`, and `W'` the one on `[0,c']`
with levels `(p₁₁,p₁₂,p₂₂)`, where `c, c' ∈ (0,1/2)` (the first block is the smaller one) and
neither triple of levels is constant.  If `W'` is `W` relabelled by `σ`, then `c = c'` and the
levels coincide. -/
theorem bipodal_params_eq_of_relabel {W W' : Graphon} {σ : ℝ → ℝ} (hσ : IsRelabelling σ)
    {c c' q11 q12 q22 p11 p12 p22 : ℝ} (hc : c ∈ Set.Ioo (0:ℝ) (1 / 2))
    (hc' : c' ∈ Set.Ioo (0:ℝ) (1 / 2))
    (hq : ¬(q11 = q12 ∧ q12 = q22)) (hp : ¬(p11 = p12 ∧ p12 = p22))
    (hW : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = bipodalValue (Set.Icc 0 c) q11 q12 q22 z)
    (hW' : ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = bipodalValue (Set.Icc 0 c') p11 p12 p22 z)
    (h : ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) :
    c = c' ∧ q11 = p11 ∧ q12 = p12 ∧ q22 = p22 := by
  set A : Set ℝ := σ ⁻¹' Set.Icc 0 c with hAdef
  set B : Set ℝ := Set.Icc 0 c' with hBdef
  have hAm : MeasurableSet A := hσ.measurable measurableSet_Icc
  have hBm : MeasurableSet B := measurableSet_Icc
  have hμA : unitμ A = ENNReal.ofReal c := by
    rw [hAdef, hσ.measurePreserving.measure_preimage measurableSet_Icc.nullMeasurableSet,
      unitμ_Icc_eq_ofReal hc.1.le (by linarith [hc.2])]
  have hμB : unitμ B = ENNReal.ofReal c' := unitμ_Icc_eq_ofReal hc'.1.le (by linarith [hc'.2])
  -- the relabelled kernel is the two-block kernel on `σ⁻¹[0,c]`
  have hmp : MeasurePreserving (Prod.map σ σ) gμ gμ :=
    hσ.measurePreserving.prod hσ.measurePreserving
  have hpull : (fun z : ℝ × ℝ => W.toFun (σ z.1) (σ z.2)) =ᵐ[gμ]
      fun z => bipodalValue (Set.Icc 0 c) q11 q12 q22 (σ z.1, σ z.2) :=
    hmp.quasiMeasurePreserving.ae_eq hW
  have hae : ∀ᵐ z ∂gμ, bipodalValue A q11 q12 q22 z = bipodalValue B p11 p12 p22 z := by
    filter_upwards [h, hpull, hW'] with z hz hpz hz'
    rw [← hz', hz, hpz]
    rfl
  -- the blocks are non-null, and so is the complement of their union
  have hA0 : unitμ A ≠ 0 := by
    rw [hμA]; exact ENNReal.ofReal_pos.mpr hc.1 |>.ne'
  have hAB0 : unitμ (Aᶜ ∩ Bᶜ) ≠ 0 := by
    intro h0
    have hcover : (Set.univ : Set ℝ) ⊆ (A ∪ B) ∪ (Aᶜ ∩ Bᶜ) := by
      intro x _
      by_cases hxA : x ∈ A
      · exact Or.inl (Or.inl hxA)
      · by_cases hxB : x ∈ B
        · exact Or.inl (Or.inr hxB)
        · exact Or.inr ⟨hxA, hxB⟩
    have h1 : (1 : ENNReal) ≤ ENNReal.ofReal (c + c') := by
      calc (1 : ENNReal) = unitμ Set.univ := measure_univ.symm
        _ ≤ unitμ ((A ∪ B) ∪ (Aᶜ ∩ Bᶜ)) := measure_mono hcover
        _ ≤ unitμ (A ∪ B) + unitμ (Aᶜ ∩ Bᶜ) := measure_union_le _ _
        _ ≤ unitμ A + unitμ B + 0 := by
          rw [h0, add_zero, add_zero]; exact measure_union_le _ _
        _ = ENNReal.ofReal (c + c') := by
          rw [add_zero, hμA, hμB, ENNReal.ofReal_add hc.1.le hc'.1.le]
    have h2 : ENNReal.ofReal (c + c') < 1 :=
      ENNReal.ofReal_lt_one.mpr (by linarith [hc.2, hc'.2])
    exact absurd h1 (not_le.mpr h2)
  obtain ⟨hAB, hBA, h11, h12, h22⟩ := bipodalValue_ae_eq_unique hA0 hAB0 hq hp hae
  -- `A` and `B` both have the measure of `A ∩ B`
  have hμAeq : unitμ A = unitμ (A ∩ B) := by
    rw [← measure_inter_add_sdiff A hBm, Set.sdiff_eq, hAB, add_zero]
  have hμBeq : unitμ B = unitμ (A ∩ B) := by
    rw [← measure_inter_add_sdiff B hAm, Set.sdiff_eq, Set.inter_comm B Aᶜ, hBA, add_zero,
      Set.inter_comm]
  have hcc : ENNReal.ofReal c = ENNReal.ofReal c' := by
    rw [← hμA, ← hμB, hμAeq, hμBeq]
  exact ⟨(ENNReal.ofReal_eq_ofReal_iff hc.1.le hc'.1.le).mp hcc, h11, h12, h22⟩

end UpperTailOptimizers
