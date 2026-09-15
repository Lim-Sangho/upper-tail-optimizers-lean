import UpperTailOptimizers.Preliminaries.KRRSBipodality.EulerLagrange

/-!
# Pinned densities through one row

For a `d`-regular `H`, a pinned density `t_{ab}(W;x,y)` depends on `x` through the `d-1` edges at
`a`.  Replacing every other factor by `ε` costs at most the `L¹` distances of the row of `y`
and of `W` from `ε`, and what remains factorizes over the neighbours of `a`:

  `|t_{ab}(W;x,y) - ε^{m-d} d_W(x)^{d-1}| ≤ m (‖W(y,·) - ε‖₁ + ‖W - ε‖₁)`.

## Contents

* `integral_prod_coord` — a product of one-coordinate functions over distinct coordinates;
* `Graphon.abs_pinned_sub_row_le` — the one-row factorization;
* `Graphon.abs_gammaW_sub_row_le` — its consequence for `Γ_W`.
-/

namespace UpperTailOptimizers

open MeasureTheory Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `∫ ∏_{k ∈ K} f(z_k) = (∫ f)^{|K|}`. -/
theorem integral_prod_coord (K : Finset V) (f : ℝ → ℝ) :
    ∫ z : V → ℝ, ∏ k ∈ K, f (z k) ∂(Measure.pi fun _ : V => unitμ)
      = (∫ t, f t ∂unitμ) ^ K.card := by
  classical
  set F : V → ℝ → ℝ := fun i t => if i ∈ K then f t else 1 with hF
  have hpt : ∀ z : V → ℝ, ∏ k ∈ K, f (z k) = ∏ i, F i (z i) := by
    intro z
    simp only [hF]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
    congr 1
    ext i; simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_fintype_prod_eq_prod]
  have hval : ∀ i, ∫ t, F i t ∂unitμ = if i ∈ K then ∫ t, f t ∂unitμ else 1 := by
    intro i
    by_cases hi : i ∈ K <;> simp [hF, hi]
  simp only [hval]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  simp

namespace Graphon

variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The row distance `∫ |W(y,·) - ε|`. -/
noncomputable def rowDist (W : Graphon) (ε y : ℝ) : ℝ := ∫ t, |W.toFun y t - ε| ∂unitμ

/-- The distance `∬ |W - ε|`. -/
noncomputable def constDist (W : Graphon) (ε : ℝ) : ℝ := ∫ p : ℝ × ℝ, |W.toFun p.1 p.2 - ε| ∂gμ

theorem rowDist_nonneg (W : Graphon) (ε y : ℝ) : 0 ≤ W.rowDist ε y :=
  integral_nonneg fun _ => abs_nonneg _

theorem constDist_nonneg (W : Graphon) (ε : ℝ) : 0 ≤ W.constDist ε :=
  integral_nonneg fun _ => abs_nonneg _

set_option maxHeartbeats 1000000 in
/-- **The one-row factorization of a pinned density.** -/
theorem abs_pinned_sub_row_le (W : Graphon) {d : ℕ} (hreg : ∀ v, H.degree v = d) {a b : V}
    (hab : H.Adj a b) {ε : ℝ} (hε : ε ∈ Icc (0:ℝ) 1) (x y : ℝ) :
    |W.pinned H a b x y - ε ^ (H.edgeFinset.card - d) * W.degFun x ^ (d - 1)|
      ≤ H.edgeFinset.card * (W.rowDist ε y + W.constDist ε) := by
  classical
  set π : Measure (V → ℝ) := Measure.pi fun _ : V => unitμ with hπ
  have hne : a ≠ b := hab.ne
  set T : Finset (Sym2 V) := H.edgeFinset.erase s(a, b) with hT
  set ℓ : (V → ℝ) → (V → ℝ) := fun z => pinLab a b (z, (x, y)) with hℓ
  have hℓm : Measurable ℓ := (measurable_pinLab a b).comp (measurable_id.prodMk measurable_const)
  set g : Sym2 V → (V → ℝ) → ℝ := fun e z => if a ∈ e then W.gEdge (ℓ z) e else ε with hg
  have hgmem : ∀ e z, g e z ∈ Icc (0:ℝ) 1 := fun e z => by
    simp only [hg]; split_ifs
    · exact W.gEdge_mem_Icc _ e
    · exact hε
  have hgm : ∀ e, Measurable fun z => g e z := fun e => by
    simp only [hg]; split_ifs
    · exact (W.measurable_gEdge e).comp hℓm
    · exact measurable_const
  -- the pointwise telescoping bound
  have hpt : ∀ z, |∏ e ∈ T, W.gEdge (ℓ z) e - ∏ e ∈ T, g e z|
      ≤ ∑ e ∈ T.filter (fun e => a ∉ e), |W.gEdge (ℓ z) e - ε| := by
    intro z
    refine le_trans (abs_prod_sub_prod_le_sum T _ _ (fun e _ => W.gEdge_mem_Icc _ e)
      (fun e _ => hgmem e z)) (le_of_eq ?_)
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : a ∈ e <;> simp [hg, h]
  -- each off-row term
  have hterm : ∀ e ∈ T.filter (fun e => a ∉ e),
      ∫ z, |W.gEdge (ℓ z) e - ε| ∂π ≤ W.rowDist ε y + W.constDist ε := by
    intro e he
    have heT := (Finset.mem_filter.mp he).1
    have hae := (Finset.mem_filter.mp he).2
    have heE : e ∈ H.edgeFinset := Finset.mem_of_mem_erase heT
    revert heE hae
    induction e using Sym2.ind with
    | _ p q =>
      intro hae heE
      have hpq : p ≠ q := H.ne_of_adj (SimpleGraph.mem_edgeFinset.mp heE)
      rw [Sym2.mem_iff] at hae
      push Not at hae
      have hpa : p ≠ a := Ne.symm hae.1
      have hqa : q ≠ a := Ne.symm hae.2
      have hrow0 := W.rowDist_nonneg ε y
      have hconst0 := W.constDist_nonneg ε
      by_cases hpb : p = b
      · subst hpb
        have hqb : q ≠ p := Ne.symm hpq
        have hval : ∀ z, |W.gEdge (ℓ z) s(p, q) - ε| = |W.toFun y (z q) - ε| := fun z => by
          simp only [hℓ, gEdge_mk, pinLab_apply_right, pinLab_apply_of_ne hqa hqb]
        rw [integral_congr_ae (Filter.Eventually.of_forall hval)]
        have h := integral_pi_eval_comp (V := V) q (G := fun t => |W.toFun y t - ε|)
          ((measurable_toFun_right W y).sub measurable_const).abs
        rw [h]
        show W.rowDist ε y ≤ W.rowDist ε y + W.constDist ε
        linarith
      · by_cases hqb : q = b
        · subst hqb
          have hval : ∀ z, |W.gEdge (ℓ z) s(p, q) - ε| = |W.toFun y (z p) - ε| := fun z => by
            simp only [hℓ, gEdge_mk, pinLab_apply_right, pinLab_apply_of_ne hpa hpb]
            rw [W.symm']
          rw [integral_congr_ae (Filter.Eventually.of_forall hval)]
          have h := integral_pi_eval_comp (V := V) p (G := fun t => |W.toFun y t - ε|)
            ((measurable_toFun_right W y).sub measurable_const).abs
          rw [h]
          show W.rowDist ε y ≤ W.rowDist ε y + W.constDist ε
          linarith
        · have hval : ∀ z, |W.gEdge (ℓ z) s(p, q) - ε| = |W.toFun (z p) (z q) - ε| := fun z => by
            simp only [hℓ, gEdge_mk, pinLab_apply_of_ne hpa hpb, pinLab_apply_of_ne hqa hqb]
          rw [integral_congr_ae (Filter.Eventually.of_forall hval)]
          have hmp := measurePreserving_pair (V := V) hpq
          have hmeas : Measurable fun w : ℝ × ℝ => |W.toFun w.1 w.2 - ε| :=
            (W.measurable_uncurry.sub measurable_const).abs
          have h : ∫ z : V → ℝ, |W.toFun (z p) (z q) - ε| ∂π = W.constDist ε := by
            have h1 := integral_map (μ := π) hmp.measurable.aemeasurable
              (hmeas.aestronglyMeasurable
                (μ := Measure.map (fun z : V → ℝ => (z p, z q)) π))
            rw [hmp.map_eq] at h1
            exact h1.symm
          rw [h]
          linarith
  -- the factorized comparison product
  have hTa : T.filter (fun e => a ∈ e) = ((H.neighborFinset a).erase b).image (fun k => s(a, k)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_erase, hT,
      SimpleGraph.mem_neighborFinset, SimpleGraph.mem_edgeFinset]
    constructor
    · rintro ⟨⟨hne', he⟩, hae⟩
      refine ⟨Sym2.Mem.other hae, ⟨?_, ?_⟩, Sym2.other_spec hae⟩
      · intro h
        apply hne'
        rw [← Sym2.other_spec hae, h]
      · have hspec := Sym2.other_spec hae
        rw [← hspec] at he
        exact he
    · rintro ⟨k, ⟨hkb, hak⟩, rfl⟩
      refine ⟨⟨fun h => hkb (Sym2.congr_right.mp h), hak⟩, Sym2.mem_mk_left a k⟩
  have hinj : Set.InjOn (fun k => s(a, k)) ((H.neighborFinset a).erase b : Set V) :=
    fun k₁ _ k₂ _ h => Sym2.congr_right.mp h
  have hcardTa : (T.filter (fun e => a ∈ e)).card = d - 1 := by
    rw [hTa, Finset.card_image_of_injOn hinj,
      Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset H a b).mpr hab),
      SimpleGraph.card_neighborFinset_eq_degree, hreg]
  have hcardT : T.card = H.edgeFinset.card - 1 := by
    rw [hT, Finset.card_erase_of_mem (SimpleGraph.mem_edgeFinset.mpr hab)]
  have hcardTn : (T.filter (fun e => a ∉ e)).card = H.edgeFinset.card - d := by
    have h := Finset.card_filter_add_card_filter_not (s := T) (p := fun e => a ∈ e)
    have hd1 : 1 ≤ d := by
      rw [← hreg a]; exact Finset.card_pos.mpr ⟨b, (SimpleGraph.mem_neighborFinset H a b).mpr hab⟩
    have hmd : d ≤ H.edgeFinset.card := by
      rw [← hreg a, ← SimpleGraph.card_incidenceFinset_eq_degree]
      exact Finset.card_le_card (H.incidenceFinset_subset a)
    omega
  have hprodg : ∀ z, ∏ e ∈ T, g e z
      = ε ^ (H.edgeFinset.card - d) * ∏ k ∈ (H.neighborFinset a).erase b, W.toFun x (z k) := by
    intro z
    rw [← Finset.prod_filter_mul_prod_filter_not T (fun e => a ∈ e)]
    have h1 : ∏ e ∈ T.filter (fun e => a ∈ e), g e z
        = ∏ k ∈ (H.neighborFinset a).erase b, W.toFun x (z k) := by
      rw [hTa, Finset.prod_image hinj]
      refine Finset.prod_congr rfl fun k hk => ?_
      have hkb : k ≠ b := (Finset.mem_erase.mp hk).1
      have hka : k ≠ a := fun h => by
        have := (SimpleGraph.mem_neighborFinset H a k).mp (Finset.mem_of_mem_erase hk)
        rw [h] at this; exact H.ne_of_adj this rfl
      simp only [hg, Sym2.mem_mk_left, if_true, hℓ, gEdge_mk, pinLab_apply_left hne,
        pinLab_apply_of_ne hka hkb]
    have h2 : ∏ e ∈ T.filter (fun e => a ∉ e), g e z = ε ^ (H.edgeFinset.card - d) := by
      rw [Finset.prod_congr rfl (g := fun _ => ε) (fun e he => by
        simp only [hg, if_neg (Finset.mem_filter.mp he).2]), Finset.prod_const, hcardTn]
    rw [h1, h2, mul_comm]
  have hintg : ∫ z, ∏ e ∈ T, g e z ∂π = ε ^ (H.edgeFinset.card - d) * W.degFun x ^ (d - 1) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hprodg), integral_const_mul]
    congr 1
    have h := integral_prod_coord ((H.neighborFinset a).erase b) (fun t => W.toFun x t)
    rw [h, Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset H a b).mpr hab),
      SimpleGraph.card_neighborFinset_eq_degree, hreg]
    rfl
  -- integrate the telescoping bound
  have hint1 : Integrable (fun z => ∏ e ∈ T, W.gEdge (ℓ z) e) π :=
    integrable_of_abs_le ((W.measurable_prod_gEdge T).comp hℓm) 1 fun z => by
      rw [abs_of_nonneg (W.prod_gEdge_mem_Icc _ _).1]; exact (W.prod_gEdge_mem_Icc _ _).2
  have hint2 : Integrable (fun z => ∏ e ∈ T, g e z) π :=
    integrable_of_abs_le (Finset.measurable_prod _ fun e _ => hgm e) 1 fun z => by
      have hmem : ∏ e ∈ T, g e z ∈ Icc (0:ℝ) 1 :=
        ⟨Finset.prod_nonneg fun e _ => (hgmem e z).1,
          Finset.prod_le_one (fun e _ => (hgmem e z).1) fun e _ => (hgmem e z).2⟩
      rw [abs_of_nonneg hmem.1]; exact hmem.2
  have hintterm : ∀ e ∈ T.filter (fun e => a ∉ e),
      Integrable (fun z => |W.gEdge (ℓ z) e - ε|) π := fun e _ =>
    integrable_of_abs_le (((W.measurable_gEdge e).comp hℓm).sub measurable_const).abs 1 fun z => by
      rw [abs_abs]
      have := W.gEdge_mem_Icc (ℓ z) e
      rw [abs_le]; constructor <;> linarith [this.1, this.2, hε.1, hε.2]
  have hpinned : W.pinned H a b x y = ∫ z, ∏ e ∈ T, W.gEdge (ℓ z) e ∂π := rfl
  rw [hpinned, ← hintg, ← integral_sub hint1 hint2]
  calc |∫ z, (∏ e ∈ T, W.gEdge (ℓ z) e - ∏ e ∈ T, g e z) ∂π|
      ≤ ∫ z, |∏ e ∈ T, W.gEdge (ℓ z) e - ∏ e ∈ T, g e z| ∂π := abs_integral_le_integral_abs
    _ ≤ ∫ z, ∑ e ∈ T.filter (fun e => a ∉ e), |W.gEdge (ℓ z) e - ε| ∂π :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
          (integrable_finsetSum _ hintterm) (Filter.Eventually.of_forall hpt)
    _ = ∑ e ∈ T.filter (fun e => a ∉ e), ∫ z, |W.gEdge (ℓ z) e - ε| ∂π :=
        integral_finsetSum _ hintterm
    _ ≤ ∑ _e ∈ T.filter (fun e => a ∉ e), (W.rowDist ε y + W.constDist ε) :=
        Finset.sum_le_sum hterm
    _ = ((T.filter (fun e => a ∉ e)).card : ℝ) * (W.rowDist ε y + W.constDist ε) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ H.edgeFinset.card * (W.rowDist ε y + W.constDist ε) := by
        apply mul_le_mul_of_nonneg_right _ (add_nonneg (W.rowDist_nonneg ε y) (W.constDist_nonneg ε))
        rw [hcardTn]; exact_mod_cast Nat.sub_le _ _

/-- **The one-row factorization of `Γ_W`**:
`|Γ_W(x,y) - m ε^{m-d} d_W(x)^{d-1}| ≤ m² (‖W(y,·) - ε‖₁ + ‖W - ε‖₁)`. -/
theorem abs_gammaW_sub_row_le (W : Graphon) {d : ℕ} (hreg : ∀ v, H.degree v = d) {ε : ℝ}
    (hε : ε ∈ Icc (0:ℝ) 1) (x y : ℝ) :
    |W.gammaW H x y - H.edgeFinset.card * (ε ^ (H.edgeFinset.card - d) * W.degFun x ^ (d - 1))|
      ≤ H.edgeFinset.card * (H.edgeFinset.card * (W.rowDist ε y + W.constDist ε)) := by
  classical
  set c : ℝ := ε ^ (H.edgeFinset.card - d) * W.degFun x ^ (d - 1) with hc
  set B : ℝ := H.edgeFinset.card * (W.rowDist ε y + W.constDist ε) with hB
  have hedge : ∀ e ∈ H.edgeFinset, |W.pinnedEdge H x y e - c| ≤ B := by
    intro e he
    revert he
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      have hab : H.Adj a b := SimpleGraph.mem_edgeFinset.mp he
      have h1 := W.abs_pinned_sub_row_le H hreg hab hε x y
      have h2 := W.abs_pinned_sub_row_le H hreg hab.symm hε x y
      show |(W.pinned H a b x y + W.pinned H b a x y) / 2 - c| ≤ B
      have e : (W.pinned H a b x y + W.pinned H b a x y) / 2 - c
          = ((W.pinned H a b x y - c) + (W.pinned H b a x y - c)) / 2 := by ring
      rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have := abs_add_le (W.pinned H a b x y - c) (W.pinned H b a x y - c)
      linarith
  have hsum : W.gammaW H x y - H.edgeFinset.card * c
      = ∑ e ∈ H.edgeFinset, (W.pinnedEdge H x y e - c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [hsum]
  calc |∑ e ∈ H.edgeFinset, (W.pinnedEdge H x y e - c)|
      ≤ ∑ e ∈ H.edgeFinset, |W.pinnedEdge H x y e - c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ H.edgeFinset, B := Finset.sum_le_sum hedge
    _ = H.edgeFinset.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

end Graphon

end UpperTailOptimizers
