import UpperTailOptimizers.Preliminaries.KRRSBipodality.Pointwise

/-!
# The contraction estimate

Two rows `x, x'` of a maximizer satisfy `W(x,·) = λ(α + β Γ_W(x,·))`, and `Γ_W(x,y)` depends on the
row of `x` only through the `d-1` edges at the vertex carrying `x`.  Telescoping those edges gives

  `|Γ_W(x,y) - Γ_W(x',y)| ≤ m(d-1) (c^{d-2} ε^{m-d} ρ + 2m S (R_x + R_{x'} + R_y + ‖W-ε‖₁))`,

where `ρ = ‖W(x,·) - W(x',·)‖₁`, `S` bounds `|W(x,·) - W(x',·)|`, and `R` are row distances
from the class values (`c` at the vertex of `x`, `ε` elsewhere).  Combined with the Lipschitz
constant `2c(1-c)` of `λ` at the class value this gives `ρ ≤ (κ_c + o(1)) ρ` with
`κ_c = 2c(1-c)|β| m(d-1) c^{d-2} ε^{m-d}` (draft `kb:prop:bipodal`).

## Contents

* `abs_prod_sub_prod_le_sum_mul_prod_max`, `prod_le_prod_add_sum_posPart` — product algebra;
* `Graphon.abs_pinned_sub_pinned_crude`, `Graphon.abs_pinned_sub_pinned_le`;
* `Graphon.abs_gammaW_sub_gammaW_crude`, `Graphon.abs_gammaW_sub_gammaW_le`;
* `Graphon.rowDiff_le_contraction`.
-/

set_option linter.unusedSectionVars false

namespace UpperTailOptimizers

open MeasureTheory Set SingularEndpoint

/-! ### Product algebra -/

theorem prod_le_prod_max {ι : Type*} (T : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ T, f i ∈ Icc (0:ℝ) 1) :
    ∏ i ∈ T, f i ≤ ∏ i ∈ T, max (f i) (g i) :=
  Finset.prod_le_prod (fun i hi => (hf i hi).1) fun _ _ => le_max_left _ _

theorem prod_max_mem {ι : Type*} (T : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ T, f i ∈ Icc (0:ℝ) 1) (hg : ∀ i ∈ T, g i ∈ Icc (0:ℝ) 1) :
    ∏ i ∈ T, max (f i) (g i) ∈ Icc (0:ℝ) 1 :=
  ⟨Finset.prod_nonneg fun i hi => le_trans (hf i hi).1 (le_max_left _ _),
    Finset.prod_le_one (fun i hi => le_trans (hf i hi).1 (le_max_left _ _))
      fun i hi => max_le (hf i hi).2 (hg i hi).2⟩

/-- `|∏f - ∏g| ≤ ∑_k |f_k - g_k| ∏_{e ≠ k} max(f_e, g_e)` on `[0,1]`. -/
theorem abs_prod_sub_prod_le_sum_mul_prod_max {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ T, f i ∈ Icc (0:ℝ) 1) (hg : ∀ i ∈ T, g i ∈ Icc (0:ℝ) 1) :
    |∏ i ∈ T, f i - ∏ i ∈ T, g i|
      ≤ ∑ k ∈ T, |f k - g k| * ∏ e ∈ T.erase k, max (f e) (g e) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert j T hj ih =>
    have hfT : ∀ i ∈ T, f i ∈ Icc (0:ℝ) 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgT : ∀ i ∈ T, g i ∈ Icc (0:ℝ) 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hfj := hf j (Finset.mem_insert_self j T)
    have hgj := hg j (Finset.mem_insert_self j T)
    have ih' := ih hfT hgT
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj,
      Finset.erase_insert hj]
    have hsum : ∑ k ∈ T, |f k - g k| * ∏ e ∈ (insert j T).erase k, max (f e) (g e)
        = max (f j) (g j) * ∑ k ∈ T, |f k - g k| * ∏ e ∈ T.erase k, max (f e) (g e) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkj : k ≠ j := fun h => hj (h ▸ hk)
      rw [Finset.erase_insert_of_ne (Ne.symm hkj), Finset.prod_insert (fun h => hj (Finset.mem_of_mem_erase h))]
      ring
    rw [hsum]
    have e : f j * ∏ i ∈ T, f i - g j * ∏ i ∈ T, g i
        = (f j - g j) * ∏ i ∈ T, f i + g j * (∏ i ∈ T, f i - ∏ i ∈ T, g i) := by ring
    rw [e]
    have hPf := prod_le_prod_max T (g := g) hfT
    have hPf0 : 0 ≤ ∏ i ∈ T, f i := Finset.prod_nonneg fun i hi => (hfT i hi).1
    calc |(f j - g j) * ∏ i ∈ T, f i + g j * (∏ i ∈ T, f i - ∏ i ∈ T, g i)|
        ≤ |f j - g j| * ∏ i ∈ T, f i + g j * |∏ i ∈ T, f i - ∏ i ∈ T, g i| := by
          have := abs_add_le ((f j - g j) * ∏ i ∈ T, f i) (g j * (∏ i ∈ T, f i - ∏ i ∈ T, g i))
          rw [abs_mul, abs_mul, abs_of_nonneg hPf0, abs_of_nonneg hgj.1] at this
          exact this
      _ ≤ |f j - g j| * ∏ i ∈ T, max (f i) (g i)
          + max (f j) (g j) * ∑ k ∈ T, |f k - g k| * ∏ e ∈ T.erase k, max (f e) (g e) :=
          add_le_add (mul_le_mul_of_nonneg_left hPf (abs_nonneg _))
            (mul_le_mul (le_max_right _ _) ih' (abs_nonneg _) (le_trans hfj.1 (le_max_left _ _)))

/-- `∏ v ≤ ∏ b + ∑ (v - b)⁺` on `[0,1]`. -/
theorem prod_le_prod_add_sum_posPart {ι : Type*} [DecidableEq ι] (T : Finset ι) (v b : ι → ℝ)
    (hv : ∀ i ∈ T, v i ∈ Icc (0:ℝ) 1) (hb : ∀ i ∈ T, b i ∈ Icc (0:ℝ) 1) :
    ∏ i ∈ T, v i ≤ ∏ i ∈ T, b i + ∑ i ∈ T, max (v i - b i) 0 := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert j T hj ih =>
    have hvT : ∀ i ∈ T, v i ∈ Icc (0:ℝ) 1 := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have hbT : ∀ i ∈ T, b i ∈ Icc (0:ℝ) 1 := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hvj := hv j (Finset.mem_insert_self j T)
    have hbj := hb j (Finset.mem_insert_self j T)
    have ih' := ih hvT hbT
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have hPv : ∏ i ∈ T, v i ∈ Icc (0:ℝ) 1 :=
      ⟨Finset.prod_nonneg fun i hi => (hvT i hi).1,
        Finset.prod_le_one (fun i hi => (hvT i hi).1) fun i hi => (hvT i hi).2⟩
    have hS0 : 0 ≤ ∑ i ∈ T, max (v i - b i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
    have h1 : v j ≤ b j + max (v j - b j) 0 := by
      have := le_max_left (v j - b j) 0; linarith
    have hm0 : 0 ≤ max (v j - b j) 0 := le_max_right _ _
    calc v j * ∏ i ∈ T, v i ≤ (b j + max (v j - b j) 0) * ∏ i ∈ T, v i :=
          mul_le_mul_of_nonneg_right h1 hPv.1
      _ = b j * ∏ i ∈ T, v i + max (v j - b j) 0 * ∏ i ∈ T, v i := by ring
      _ ≤ b j * (∏ i ∈ T, b i + ∑ i ∈ T, max (v i - b i) 0) + max (v j - b j) 0 * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left ih' hbj.1) (mul_le_mul_of_nonneg_left hPv.2 hm0)
      _ ≤ b j * ∏ i ∈ T, b i + (max (v j - b j) 0 + ∑ i ∈ T, max (v i - b i) 0) := by
          have : b j * ∑ i ∈ T, max (v i - b i) 0 ≤ ∑ i ∈ T, max (v i - b i) 0 := by
            calc b j * ∑ i ∈ T, max (v i - b i) 0 ≤ 1 * ∑ i ∈ T, max (v i - b i) 0 :=
                  mul_le_mul_of_nonneg_right hbj.2 hS0
              _ = _ := one_mul _
          nlinarith

theorem max_sub_posPart_le {p q b : ℝ} : max (max p q - b) 0 ≤ |p - b| + |q - b| := by
  refine max_le ?_ (by positivity)
  rcases le_total p q with h | h
  · rw [max_eq_right h]; have := le_abs_self (q - b); have := abs_nonneg (p - b); linarith
  · rw [max_eq_left h]; have := le_abs_self (p - b); have := abs_nonneg (q - b); linarith

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-! ### Pinned densities of two rows -/

namespace Graphon

theorem edges_at_erase {d : ℕ} (hreg : ∀ v, H.degree v = d) {a b : V} (hab : H.Adj a b) :
    (H.edgeFinset.erase s(a, b)).filter (fun e => a ∈ e)
        = ((H.neighborFinset a).erase b).image (fun k => s(a, k)) ∧
      ((H.edgeFinset.erase s(a, b)).filter (fun e => a ∈ e)).card = d - 1 ∧
      ((H.edgeFinset.erase s(a, b)).filter (fun e => a ∉ e)).card = H.edgeFinset.card - d := by
  classical
  set T := H.edgeFinset.erase s(a, b) with hT
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
  exact ⟨hTa, hcardTa, hcardTn⟩

theorem gEdge_pinLab_of_notMem {a b : V} {e : Sym2 V} (hae : a ∉ e) (W : Graphon) (z : V → ℝ)
    (x x' y : ℝ) : W.gEdge (pinLab a b (z, (x, y))) e = W.gEdge (pinLab a b (z, (x', y))) e := by
  induction e using Sym2.ind with
  | _ p q =>
    rw [Sym2.mem_iff] at hae
    push Not at hae
    have hp : pinLab a b (z, (x, y)) p = pinLab a b (z, (x', y)) p := by
      simp only [pinLab]
      by_cases hpb : p = b
      · rw [hpb, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hpb, Function.update_of_ne hpb, Function.update_of_ne (Ne.symm hae.1),
          Function.update_of_ne (Ne.symm hae.1)]
    have hq : pinLab a b (z, (x, y)) q = pinLab a b (z, (x', y)) q := by
      simp only [pinLab]
      by_cases hqb : q = b
      · rw [hqb, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hqb, Function.update_of_ne hqb, Function.update_of_ne (Ne.symm hae.2),
          Function.update_of_ne (Ne.symm hae.2)]
    simp only [gEdge_mk, hp, hq]

theorem gEdge_pinLab_at {a b j : V} (hab : a ≠ b) (hja : j ≠ a) (hjb : j ≠ b) (W : Graphon)
    (z : V → ℝ) (x y : ℝ) : W.gEdge (pinLab a b (z, (x, y))) s(a, j) = W.toFun x (z j) := by
  rw [gEdge_mk, pinLab_apply_left hab, pinLab_apply_of_ne hja hjb]

theorem measurable_pinLab_const (a b : V) (x y : ℝ) :
    Measurable fun z : V → ℝ => pinLab a b (z, (x, y)) :=
  (measurable_pinLab a b).comp (measurable_id.prodMk measurable_const)

/-- **The crude row Lipschitz bound**: `|t_{ab}(x,y) - t_{ab}(x',y)| ≤ (d-1) ‖W(x,·) - W(x',·)‖₁`. -/
theorem abs_pinned_sub_pinned_crude (W : Graphon) {d : ℕ} (hreg : ∀ v, H.degree v = d) {a b : V}
    (hab : H.Adj a b) (x x' y : ℝ) :
    |W.pinned H a b x y - W.pinned H a b x' y|
      ≤ (d - 1 : ℕ) * ∫ s, |W.toFun x s - W.toFun x' s| ∂unitμ := by
  classical
  set π : Measure (V → ℝ) := Measure.pi fun _ : V => unitμ with hπ
  have hne : a ≠ b := hab.ne
  set T := H.edgeFinset.erase s(a, b) with hT
  obtain ⟨hTa, hcardTa, -⟩ := edges_at_erase H hreg hab
  set ℓ := fun z : V → ℝ => pinLab a b (z, (x, y)) with hℓ
  set ℓ' := fun z : V → ℝ => pinLab a b (z, (x', y)) with hℓ'
  have hpt : ∀ z, |∏ e ∈ T, W.gEdge (ℓ z) e - ∏ e ∈ T, W.gEdge (ℓ' z) e|
      ≤ ∑ j ∈ (H.neighborFinset a).erase b, |W.toFun x (z j) - W.toFun x' (z j)| := by
    intro z
    refine le_trans (abs_prod_sub_prod_le_sum T _ _ (fun e _ => W.gEdge_mem_Icc _ e)
      (fun e _ => W.gEdge_mem_Icc _ e)) (le_of_eq ?_)
    rw [← Finset.sum_filter_add_sum_filter_not T (fun e => a ∈ e)]
    have h0 : ∑ e ∈ T.filter (fun e => a ∉ e), |W.gEdge (ℓ z) e - W.gEdge (ℓ' z) e| = 0 :=
      Finset.sum_eq_zero fun e he => by
        rw [hℓ, hℓ', gEdge_pinLab_of_notMem (Finset.mem_filter.mp he).2 W z x x' y, sub_self, abs_zero]
    rw [h0, add_zero, hTa, Finset.sum_image (fun k₁ _ k₂ _ h => Sym2.congr_right.mp h)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjb : j ≠ b := (Finset.mem_erase.mp hj).1
    have hja : j ≠ a := fun h => by
      have := (SimpleGraph.mem_neighborFinset H a j).mp (Finset.mem_of_mem_erase hj)
      rw [h] at this; exact H.ne_of_adj this rfl
    simp only [hℓ, hℓ', gEdge_pinLab_at hne hja hjb]
  have hint1 : Integrable (fun z => ∏ e ∈ T, W.gEdge (ℓ z) e) π :=
    integrable_of_abs_le ((W.measurable_prod_gEdge T).comp (measurable_pinLab_const a b x y)) 1
      fun z => by rw [abs_of_nonneg (W.prod_gEdge_mem_Icc _ _).1]; exact (W.prod_gEdge_mem_Icc _ _).2
  have hint2 : Integrable (fun z => ∏ e ∈ T, W.gEdge (ℓ' z) e) π :=
    integrable_of_abs_le ((W.measurable_prod_gEdge T).comp (measurable_pinLab_const a b x' y)) 1
      fun z => by rw [abs_of_nonneg (W.prod_gEdge_mem_Icc _ _).1]; exact (W.prod_gEdge_mem_Icc _ _).2
  have hmrow : Measurable fun t => |W.toFun x t - W.toFun x' t| :=
    ((measurable_toFun_right W x).sub (measurable_toFun_right W x')).abs
  have hintj : ∀ j ∈ (H.neighborFinset a).erase b,
      Integrable (fun z : V → ℝ => |W.toFun x (z j) - W.toFun x' (z j)|) π := fun j _ =>
    integrable_of_abs_le (hmrow.comp (measurable_pi_apply j)) 1 fun z => by
      rw [abs_abs, abs_le]
      constructor <;> linarith [(W.mem_Icc x (z j)).1, (W.mem_Icc x (z j)).2,
        (W.mem_Icc x' (z j)).1, (W.mem_Icc x' (z j)).2]
  have hp1 : W.pinned H a b x y = ∫ z, ∏ e ∈ T, W.gEdge (ℓ z) e ∂π := rfl
  have hp2 : W.pinned H a b x' y = ∫ z, ∏ e ∈ T, W.gEdge (ℓ' z) e ∂π := rfl
  rw [hp1, hp2, ← integral_sub hint1 hint2]
  calc |∫ z, (∏ e ∈ T, W.gEdge (ℓ z) e - ∏ e ∈ T, W.gEdge (ℓ' z) e) ∂π|
      ≤ ∫ z, |∏ e ∈ T, W.gEdge (ℓ z) e - ∏ e ∈ T, W.gEdge (ℓ' z) e| ∂π :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z, ∑ j ∈ (H.neighborFinset a).erase b, |W.toFun x (z j) - W.toFun x' (z j)| ∂π :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
          (integrable_finsetSum _ hintj) (Filter.Eventually.of_forall hpt)
    _ = ∑ j ∈ (H.neighborFinset a).erase b, ∫ z, |W.toFun x (z j) - W.toFun x' (z j)| ∂π :=
        integral_finsetSum _ hintj
    _ = ∑ _j ∈ (H.neighborFinset a).erase b, ∫ s, |W.toFun x s - W.toFun x' s| ∂unitμ :=
        Finset.sum_congr rfl fun j _ => integral_pi_eval_comp j hmrow
    _ = (d - 1 : ℕ) * ∫ s, |W.toFun x s - W.toFun x' s| ∂unitμ := by
        rw [Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset H a b).mpr hab),
          SimpleGraph.card_neighborFinset_eq_degree, hreg]

/-- **The crude row Lipschitz bound for `Γ_W`.** -/
theorem abs_gammaW_sub_gammaW_crude (W : Graphon) {d : ℕ} (hreg : ∀ v, H.degree v = d)
    (x x' y : ℝ) :
    |W.gammaW H x y - W.gammaW H x' y|
      ≤ H.edgeFinset.card * ((d - 1 : ℕ) * ∫ s, |W.toFun x s - W.toFun x' s| ∂unitμ) := by
  classical
  set B : ℝ := (d - 1 : ℕ) * ∫ s, |W.toFun x s - W.toFun x' s| ∂unitμ with hB
  have hedge : ∀ e ∈ H.edgeFinset, |W.pinnedEdge H x y e - W.pinnedEdge H x' y e| ≤ B := by
    intro e he
    revert he
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      have hab : H.Adj a b := SimpleGraph.mem_edgeFinset.mp he
      have h1 := W.abs_pinned_sub_pinned_crude H hreg hab x x' y
      have h2 := W.abs_pinned_sub_pinned_crude H hreg hab.symm x x' y
      show |(W.pinned H a b x y + W.pinned H b a x y) / 2
        - (W.pinned H a b x' y + W.pinned H b a x' y) / 2| ≤ B
      have e : (W.pinned H a b x y + W.pinned H b a x y) / 2
          - (W.pinned H a b x' y + W.pinned H b a x' y) / 2
          = ((W.pinned H a b x y - W.pinned H a b x' y)
            + (W.pinned H b a x y - W.pinned H b a x' y)) / 2 := by ring
      rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have := abs_add_le (W.pinned H a b x y - W.pinned H a b x' y)
        (W.pinned H b a x y - W.pinned H b a x' y)
      linarith
  unfold gammaW
  rw [← Finset.sum_sub_distrib]
  calc |∑ e ∈ H.edgeFinset, (W.pinnedEdge H x y e - W.pinnedEdge H x' y e)|
      ≤ ∑ e ∈ H.edgeFinset, |W.pinnedEdge H x y e - W.pinnedEdge H x' y e| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ H.edgeFinset, B := Finset.sum_le_sum hedge
    _ = H.edgeFinset.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

end Graphon

namespace Graphon

theorem ae_abs_sub_eval_le (W : Graphon) {x x' S : ℝ}
    (hxx' : ∀ᵐ s ∂unitμ, |W.toFun x s - W.toFun x' s| ≤ S) (j : V) :
    ∀ᵐ z ∂(Measure.pi fun _ : V => unitμ), |W.toFun x (z j) - W.toFun x' (z j)| ≤ S :=
  (measurePreserving_eval (μ := fun _ : V => unitμ) j).quasiMeasurePreserving.ae hxx'

set_option maxHeartbeats 4000000 in
/-- **The refined row Lipschitz bound for pinned densities.** -/
theorem abs_pinned_sub_pinned_le (W : Graphon) {d : ℕ} (hreg : ∀ v, H.degree v = d) {a b : V}
    (hab : H.Adj a b) {c ε S : ℝ} (hc : c ∈ Icc (0:ℝ) 1) (hε : ε ∈ Icc (0:ℝ) 1) (hS : 0 ≤ S)
    {x x' : ℝ} (hxx' : ∀ᵐ s ∂unitμ, |W.toFun x s - W.toFun x' s| ≤ S) (y : ℝ) :
    |W.pinned H a b x y - W.pinned H a b x' y|
      ≤ (d - 1 : ℕ) * (c ^ (d - 2) * ε ^ (H.edgeFinset.card - d)
          * ∫ s, |W.toFun x s - W.toFun x' s| ∂unitμ
        + S * (H.edgeFinset.card * (2 * (W.rowDist c x + W.rowDist c x' + W.rowDist ε y
          + W.constDist ε)))) := by
  classical
  set π : Measure (V → ℝ) := Measure.pi fun _ : V => unitμ with hπ
  have hne : a ≠ b := hab.ne
  set T := H.edgeFinset.erase s(a, b) with hT
  obtain ⟨hTa, hcardTa, hcardTn⟩ := edges_at_erase H hreg hab
  set Nb := (H.neighborFinset a).erase b with hNb
  have hNbmem : ∀ j ∈ Nb, j ≠ a ∧ j ≠ b := fun j hj => by
    refine ⟨fun h => ?_, (Finset.mem_erase.mp hj).1⟩
    have := (SimpleGraph.mem_neighborFinset H a j).mp (Finset.mem_of_mem_erase hj)
    rw [h] at this; exact H.ne_of_adj this rfl
  have hinj : Set.InjOn (fun k => s(a, k)) (Nb : Set V) := fun k₁ _ k₂ _ h => Sym2.congr_right.mp h
  set ℓ := fun z : V → ℝ => pinLab a b (z, (x, y)) with hℓ
  set ℓ' := fun z : V → ℝ => pinLab a b (z, (x', y)) with hℓ'
  set bv : Sym2 V → ℝ := fun e => if a ∈ e then c else ε with hbv
  have hbvI : ∀ e, bv e ∈ Icc (0:ℝ) 1 := fun e => by
    simp only [hbv]; split_ifs
    · exact hc
    · exact hε
  set D : (V → ℝ) → Sym2 V → ℝ := fun z e => |W.gEdge (ℓ z) e - bv e| + |W.gEdge (ℓ' z) e - bv e|
    with hD
  have hD0 : ∀ z e, 0 ≤ D z e := fun z e => add_nonneg (abs_nonneg _) (abs_nonneg _)
  set R : ℝ := W.rowDist c x + W.rowDist c x' + W.rowDist ε y + W.constDist ε with hR
  set B : ℝ := c ^ (d - 2) * ε ^ (H.edgeFinset.card - d) with hB
  set ρ : ℝ := ∫ s, |W.toFun x s - W.toFun x' s| ∂unitμ with hρ
  have hR0 : 0 ≤ R := by
    have := W.rowDist_nonneg c x; have := W.rowDist_nonneg c x'
    have := W.rowDist_nonneg ε y; have := W.constDist_nonneg ε
    linarith
  have hB0 : 0 ≤ B := mul_nonneg (pow_nonneg hc.1 _) (pow_nonneg hε.1 _)
  -- the product of the reference values off an edge at `a`
  have hBk : ∀ j ∈ Nb, ∏ e ∈ T.erase s(a, j), bv e = B := by
    intro j hj
    have hk : s(a, j) ∈ T.filter (fun e => a ∈ e) := by
      rw [hTa]; exact Finset.mem_image_of_mem _ hj
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have h1 : (T.erase s(a, j)).filter (fun e => a ∈ e) = (T.filter (fun e => a ∈ e)).erase s(a, j) :=
      Finset.filter_erase _ _ _
    have h2 : (T.erase s(a, j)).filter (fun e => ¬a ∈ e) = T.filter (fun e => ¬a ∈ e) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨-, he⟩, hae⟩; exact ⟨he, hae⟩
      · rintro ⟨he, hae⟩
        exact ⟨⟨fun h => hae (h ▸ Sym2.mem_mk_left a j), he⟩, hae⟩
    rw [h1, h2, Finset.card_erase_of_mem hk, hcardTa, hcardTn]
    have : d - 1 - 1 = d - 2 := by omega
    rw [this]
  -- the pointwise telescoping bound
  have hpt : ∀ z, |∏ e ∈ T, W.gEdge (ℓ z) e - ∏ e ∈ T, W.gEdge (ℓ' z) e|
      ≤ ∑ j ∈ Nb, |W.toFun x (z j) - W.toFun x' (z j)| * (B + ∑ e ∈ T, D z e) := by
    intro z
    refine le_trans (abs_prod_sub_prod_le_sum_mul_prod_max T _ _ (fun e _ => W.gEdge_mem_Icc _ e)
      (fun e _ => W.gEdge_mem_Icc _ e)) ?_
    rw [← Finset.sum_filter_add_sum_filter_not T (fun e => a ∈ e)]
    have h0 : ∑ k ∈ T.filter (fun e => ¬a ∈ e), |W.gEdge (ℓ z) k - W.gEdge (ℓ' z) k|
        * ∏ e ∈ T.erase k, max (W.gEdge (ℓ z) e) (W.gEdge (ℓ' z) e) = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [hℓ, hℓ', gEdge_pinLab_of_notMem (Finset.mem_filter.mp hk).2 W z x x' y, sub_self,
          abs_zero, zero_mul]
    rw [h0, add_zero, hTa, Finset.sum_image hinj]
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hja, hjb⟩ := hNbmem j hj
    have e1 : W.gEdge (ℓ z) s(a, j) = W.toFun x (z j) := gEdge_pinLab_at hne hja hjb W z x y
    have e2 : W.gEdge (ℓ' z) s(a, j) = W.toFun x' (z j) := gEdge_pinLab_at hne hja hjb W z x' y
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have h2 := prod_le_prod_add_sum_posPart (T.erase s(a, j))
      (fun e => max (W.gEdge (ℓ z) e) (W.gEdge (ℓ' z) e)) bv
      (fun e _ => ⟨le_trans (W.gEdge_mem_Icc _ e).1 (le_max_left _ _),
        max_le (W.gEdge_mem_Icc _ e).2 (W.gEdge_mem_Icc _ e).2⟩) (fun e _ => hbvI e)
    rw [hBk j hj] at h2
    have h3 : ∑ e ∈ T.erase s(a, j), max (max (W.gEdge (ℓ z) e) (W.gEdge (ℓ' z) e) - bv e) 0
        ≤ ∑ e ∈ T, D z e :=
      le_trans (Finset.sum_le_sum fun e _ => max_sub_posPart_le)
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ T)
          (fun e _ _ => hD0 z e))
    linarith
  -- the integrals of the defects
  have hDm : ∀ e, Measurable fun z => D z e := fun e =>
    ((((W.measurable_gEdge e).comp (measurable_pinLab_const a b x y)).sub measurable_const).abs).add
      ((((W.measurable_gEdge e).comp (measurable_pinLab_const a b x' y)).sub measurable_const).abs)
  have hDb : ∀ e z, |D z e| ≤ 2 := fun e z => by
    have h1 := W.gEdge_mem_Icc (ℓ z) e
    have h2 := W.gEdge_mem_Icc (ℓ' z) e
    have h3 := hbvI e
    rw [abs_of_nonneg (hD0 z e)]
    simp only [hD]
    have t1 : |W.gEdge (ℓ z) e - bv e| ≤ 1 := by rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]
    have t2 : |W.gEdge (ℓ' z) e - bv e| ≤ 1 := by rw [abs_le]; constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
    linarith
  have hDint : ∀ e ∈ T, ∫ z, D z e ∂π ≤ 2 * R := by
    intro e he
    have hi1 : Integrable (fun z => |W.gEdge (ℓ z) e - bv e|) π :=
      integrable_of_abs_le ((((W.measurable_gEdge e).comp (measurable_pinLab_const a b x y)).sub
        measurable_const).abs) 1 fun z => by
          rw [abs_abs, abs_le]
          constructor <;> linarith [(W.gEdge_mem_Icc (ℓ z) e).1, (W.gEdge_mem_Icc (ℓ z) e).2,
            (hbvI e).1, (hbvI e).2]
    have hi2 : Integrable (fun z => |W.gEdge (ℓ' z) e - bv e|) π :=
      integrable_of_abs_le ((((W.measurable_gEdge e).comp (measurable_pinLab_const a b x' y)).sub
        measurable_const).abs) 1 fun z => by
          rw [abs_abs, abs_le]
          constructor <;> linarith [(W.gEdge_mem_Icc (ℓ' z) e).1, (W.gEdge_mem_Icc (ℓ' z) e).2,
            (hbvI e).1, (hbvI e).2]
    have hsplit : ∫ z, D z e ∂π
        = ∫ z, |W.gEdge (ℓ z) e - bv e| ∂π + ∫ z, |W.gEdge (ℓ' z) e - bv e| ∂π := by
      simp only [hD]; exact integral_add hi1 hi2
    rw [hsplit]
    by_cases hae : a ∈ e
    · -- an edge at `a`
      have hmem : e ∈ T.filter (fun e => a ∈ e) := Finset.mem_filter.mpr ⟨he, hae⟩
      rw [hTa] at hmem
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hmem
      obtain ⟨hja, hjb⟩ := hNbmem j hj
      have hbe : bv s(a, j) = c := by simp only [hbv, Sym2.mem_mk_left, if_true]
      have e1 : ∀ z, |W.gEdge (ℓ z) s(a, j) - bv s(a, j)| = |W.toFun x (z j) - c| := fun z => by
        rw [gEdge_pinLab_at hne hja hjb W z x y, hbe]
      have e2 : ∀ z, |W.gEdge (ℓ' z) s(a, j) - bv s(a, j)| = |W.toFun x' (z j) - c| := fun z => by
        rw [gEdge_pinLab_at hne hja hjb W z x' y, hbe]
      rw [integral_congr_ae (Filter.Eventually.of_forall e1),
        integral_congr_ae (Filter.Eventually.of_forall e2),
        integral_pi_eval_comp j (G := fun t => |W.toFun x t - c|)
          ((measurable_toFun_right W x).sub measurable_const).abs,
        integral_pi_eval_comp j (G := fun t => |W.toFun x' t - c|)
          ((measurable_toFun_right W x').sub measurable_const).abs]
      show W.rowDist c x + W.rowDist c x' ≤ 2 * R
      have := W.rowDist_nonneg ε y; have := W.constDist_nonneg ε
      have := W.rowDist_nonneg c x; have := W.rowDist_nonneg c x'
      linarith
    · -- an edge off `a`: both labellings agree
      have hbe : bv e = ε := by simp only [hbv, if_neg hae]
      have e1 : ∀ z, |W.gEdge (ℓ' z) e - bv e| = |W.gEdge (ℓ z) e - bv e| := fun z => by
        rw [hℓ, hℓ', gEdge_pinLab_of_notMem hae W z x x' y]
      rw [integral_congr_ae (Filter.Eventually.of_forall e1), hbe]
      have heE : e ∈ H.edgeFinset := Finset.mem_of_mem_erase he
      have hoff : ∫ z, |W.gEdge (ℓ z) e - ε| ∂π ≤ W.rowDist ε y + W.constDist ε := by
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
      have := W.rowDist_nonneg c x; have := W.rowDist_nonneg c x'
      linarith
  -- integrate
  have hmrow : Measurable fun t => |W.toFun x t - W.toFun x' t| :=
    ((measurable_toFun_right W x).sub (measurable_toFun_right W x')).abs
  have hfj : ∀ j, Integrable (fun z : V → ℝ => |W.toFun x (z j) - W.toFun x' (z j)|) π := fun j =>
    integrable_of_abs_le (hmrow.comp (measurable_pi_apply j)) 1 fun z => by
      rw [abs_abs, abs_le]
      constructor <;> linarith [(W.mem_Icc x (z j)).1, (W.mem_Icc x (z j)).2,
        (W.mem_Icc x' (z j)).1, (W.mem_Icc x' (z j)).2]
  have hfb : ∀ (j : V) (z : V → ℝ), |W.toFun x (z j) - W.toFun x' (z j)| ≤ 1 := fun j z => by
    rw [abs_le]
    constructor <;> linarith [(W.mem_Icc x (z j)).1, (W.mem_Icc x (z j)).2,
      (W.mem_Icc x' (z j)).1, (W.mem_Icc x' (z j)).2]
  have hterm : ∀ j ∈ Nb, ∫ z, |W.toFun x (z j) - W.toFun x' (z j)| * (B + ∑ e ∈ T, D z e) ∂π
      ≤ B * ρ + S * (T.card * (2 * R)) := by
    intro j _
    have hgm : Measurable fun z => B + ∑ e ∈ T, D z e :=
      measurable_const.add (Finset.measurable_sum _ fun e _ => hDm e)
    have hint : Integrable (fun z => |W.toFun x (z j) - W.toFun x' (z j)| * (B + ∑ e ∈ T, D z e)) π :=
      integrable_of_abs_le ((hmrow.comp (measurable_pi_apply j)).mul hgm) (1 * (B + T.card * 2))
        fun z => by
          rw [abs_mul]
          have hs : |B + ∑ e ∈ T, D z e| ≤ B + T.card * 2 := by
            calc |B + ∑ e ∈ T, D z e| ≤ |B| + |∑ e ∈ T, D z e| := abs_add_le _ _
              _ ≤ B + ∑ e ∈ T, |D z e| := by
                  rw [abs_of_nonneg hB0]; gcongr; exact Finset.abs_sum_le_sum_abs _ _
              _ ≤ B + ∑ _e ∈ T, (2:ℝ) := by gcongr with e _; exact hDb e z
              _ = B + T.card * 2 := by rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul (by rw [abs_abs]; exact hfb j z) hs (abs_nonneg _) zero_le_one
    have hDi : ∀ e ∈ T, Integrable (fun z => D z e) π := fun e _ =>
      integrable_of_abs_le (hDm e) 2 fun z => hDb e z
    have hae : ∀ᵐ z ∂π, |W.toFun x (z j) - W.toFun x' (z j)| * (B + ∑ e ∈ T, D z e)
        ≤ B * |W.toFun x (z j) - W.toFun x' (z j)| + S * ∑ e ∈ T, D z e := by
      filter_upwards [W.ae_abs_sub_eval_le hxx' j] with z hz
      have hsum0 : 0 ≤ ∑ e ∈ T, D z e := Finset.sum_nonneg fun e _ => hD0 z e
      have : |W.toFun x (z j) - W.toFun x' (z j)| * (B + ∑ e ∈ T, D z e)
          = B * |W.toFun x (z j) - W.toFun x' (z j)|
            + |W.toFun x (z j) - W.toFun x' (z j)| * ∑ e ∈ T, D z e := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_right hz hsum0
      linarith
    calc ∫ z, |W.toFun x (z j) - W.toFun x' (z j)| * (B + ∑ e ∈ T, D z e) ∂π
        ≤ ∫ z, (B * |W.toFun x (z j) - W.toFun x' (z j)| + S * ∑ e ∈ T, D z e) ∂π :=
          integral_mono_ae hint (((hfj j).const_mul B).add ((integrable_finsetSum _ hDi).const_mul S))
            hae
      _ = B * ρ + S * ∑ e ∈ T, ∫ z, D z e ∂π := by
          rw [integral_add ((hfj j).const_mul B) ((integrable_finsetSum _ hDi).const_mul S),
            integral_const_mul, integral_const_mul, integral_finsetSum _ hDi,
            integral_pi_eval_comp j hmrow]
      _ ≤ B * ρ + S * ∑ _e ∈ T, 2 * R := by gcongr with e he; exact hDint e he
      _ = B * ρ + S * (T.card * (2 * R)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hint1 : Integrable (fun z => ∏ e ∈ T, W.gEdge (ℓ z) e) π :=
    integrable_of_abs_le ((W.measurable_prod_gEdge T).comp (measurable_pinLab_const a b x y)) 1
      fun z => by rw [abs_of_nonneg (W.prod_gEdge_mem_Icc _ _).1]; exact (W.prod_gEdge_mem_Icc _ _).2
  have hint2 : Integrable (fun z => ∏ e ∈ T, W.gEdge (ℓ' z) e) π :=
    integrable_of_abs_le ((W.measurable_prod_gEdge T).comp (measurable_pinLab_const a b x' y)) 1
      fun z => by rw [abs_of_nonneg (W.prod_gEdge_mem_Icc _ _).1]; exact (W.prod_gEdge_mem_Icc _ _).2
  have hintsum : Integrable (fun z => ∑ j ∈ Nb, |W.toFun x (z j) - W.toFun x' (z j)|
      * (B + ∑ e ∈ T, D z e)) π := by
    refine integrable_finsetSum _ fun j _ => ?_
    refine integrable_of_abs_le ((hmrow.comp (measurable_pi_apply j)).mul
      (measurable_const.add (Finset.measurable_sum _ fun e _ => hDm e))) (1 * (B + T.card * 2))
      fun z => ?_
    rw [abs_mul]
    have hs : |B + ∑ e ∈ T, D z e| ≤ B + T.card * 2 := by
      calc |B + ∑ e ∈ T, D z e| ≤ |B| + |∑ e ∈ T, D z e| := abs_add_le _ _
        _ ≤ B + ∑ e ∈ T, |D z e| := by
            rw [abs_of_nonneg hB0]; gcongr; exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ B + ∑ _e ∈ T, (2:ℝ) := by gcongr with e _; exact hDb e z
        _ = B + T.card * 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul (by rw [abs_abs]; exact hfb j z) hs (abs_nonneg _) zero_le_one
  have hp1 : W.pinned H a b x y = ∫ z, ∏ e ∈ T, W.gEdge (ℓ z) e ∂π := rfl
  have hp2 : W.pinned H a b x' y = ∫ z, ∏ e ∈ T, W.gEdge (ℓ' z) e ∂π := rfl
  have hTcard : (T.card : ℝ) ≤ H.edgeFinset.card := by
    exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
  rw [hp1, hp2, ← integral_sub hint1 hint2]
  calc |∫ z, (∏ e ∈ T, W.gEdge (ℓ z) e - ∏ e ∈ T, W.gEdge (ℓ' z) e) ∂π|
      ≤ ∫ z, |∏ e ∈ T, W.gEdge (ℓ z) e - ∏ e ∈ T, W.gEdge (ℓ' z) e| ∂π :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z, ∑ j ∈ Nb, |W.toFun x (z j) - W.toFun x' (z j)| * (B + ∑ e ∈ T, D z e) ∂π :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _) hintsum
          (Filter.Eventually.of_forall hpt)
    _ = ∑ j ∈ Nb, ∫ z, |W.toFun x (z j) - W.toFun x' (z j)| * (B + ∑ e ∈ T, D z e) ∂π := by
        refine integral_finsetSum _ fun j _ => ?_
        refine integrable_of_abs_le ((hmrow.comp (measurable_pi_apply j)).mul
          (measurable_const.add (Finset.measurable_sum _ fun e _ => hDm e))) (1 * (B + T.card * 2))
          fun z => ?_
        rw [abs_mul]
        have hs : |B + ∑ e ∈ T, D z e| ≤ B + T.card * 2 := by
          calc |B + ∑ e ∈ T, D z e| ≤ |B| + |∑ e ∈ T, D z e| := abs_add_le _ _
            _ ≤ B + ∑ e ∈ T, |D z e| := by
                rw [abs_of_nonneg hB0]; gcongr; exact Finset.abs_sum_le_sum_abs _ _
            _ ≤ B + ∑ _e ∈ T, (2:ℝ) := by gcongr with e _; exact hDb e z
            _ = B + T.card * 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul (by rw [abs_abs]; exact hfb j z) hs (abs_nonneg _) zero_le_one
    _ ≤ ∑ _j ∈ Nb, (B * ρ + S * (T.card * (2 * R))) := Finset.sum_le_sum hterm
    _ = (Nb.card : ℝ) * (B * ρ + S * (T.card * (2 * R))) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d - 1 : ℕ) * (B * ρ + S * (H.edgeFinset.card * (2 * R))) := by
        have hNbc : Nb.card = d - 1 := by
          rw [hNb, Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset H a b).mpr hab),
            SimpleGraph.card_neighborFinset_eq_degree, hreg]
        rw [hNbc]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        gcongr

set_option maxHeartbeats 1000000 in
/-- **The refined row Lipschitz bound for `Γ_W`.** -/
theorem abs_gammaW_sub_gammaW_le (W : Graphon) {d : ℕ} (hreg : ∀ v, H.degree v = d)
    {c ε S : ℝ} (hc : c ∈ Icc (0:ℝ) 1) (hε : ε ∈ Icc (0:ℝ) 1) (hS : 0 ≤ S)
    {x x' : ℝ} (hxx' : ∀ᵐ s ∂unitμ, |W.toFun x s - W.toFun x' s| ≤ S) (y : ℝ) :
    |W.gammaW H x y - W.gammaW H x' y|
      ≤ H.edgeFinset.card * ((d - 1 : ℕ) * (c ^ (d - 2) * ε ^ (H.edgeFinset.card - d)
          * ∫ s, |W.toFun x s - W.toFun x' s| ∂unitμ
        + S * (H.edgeFinset.card * (2 * (W.rowDist c x + W.rowDist c x' + W.rowDist ε y
          + W.constDist ε))))) := by
  classical
  set B : ℝ := (d - 1 : ℕ) * (c ^ (d - 2) * ε ^ (H.edgeFinset.card - d)
      * ∫ s, |W.toFun x s - W.toFun x' s| ∂unitμ
    + S * (H.edgeFinset.card * (2 * (W.rowDist c x + W.rowDist c x' + W.rowDist ε y
      + W.constDist ε)))) with hB
  have hedge : ∀ e ∈ H.edgeFinset, |W.pinnedEdge H x y e - W.pinnedEdge H x' y e| ≤ B := by
    intro e he
    revert he
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      have hab : H.Adj a b := SimpleGraph.mem_edgeFinset.mp he
      have h1 := W.abs_pinned_sub_pinned_le H hreg hab hc hε hS hxx' y
      have h2 := W.abs_pinned_sub_pinned_le H hreg hab.symm hc hε hS hxx' y
      show |(W.pinned H a b x y + W.pinned H b a x y) / 2
        - (W.pinned H a b x' y + W.pinned H b a x' y) / 2| ≤ B
      have e : (W.pinned H a b x y + W.pinned H b a x y) / 2
          - (W.pinned H a b x' y + W.pinned H b a x' y) / 2
          = ((W.pinned H a b x y - W.pinned H a b x' y)
            + (W.pinned H b a x y - W.pinned H b a x' y)) / 2 := by ring
      rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have := abs_add_le (W.pinned H a b x y - W.pinned H a b x' y)
        (W.pinned H b a x y - W.pinned H b a x' y)
      linarith
  unfold gammaW
  rw [← Finset.sum_sub_distrib]
  calc |∑ e ∈ H.edgeFinset, (W.pinnedEdge H x y e - W.pinnedEdge H x' y e)|
      ≤ ∑ e ∈ H.edgeFinset, |W.pinnedEdge H x y e - W.pinnedEdge H x' y e| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ H.edgeFinset, B := Finset.sum_le_sum hedge
    _ = H.edgeFinset.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

theorem measurable_gammaW_right (W : Graphon) (x : ℝ) : Measurable fun y => W.gammaW H x y := by
  have h : Measurable (Function.uncurry (W.gammaW H)) := W.measurable_gammaW H
  exact h.of_uncurry_left

set_option maxHeartbeats 2000000 in
/-- **The contraction inequality** for two rows of a maximizer with class value `c`:
`ρ ≤ (2c(1-c)|β| m(d-1) c^{d-2} ε^{m-d} + error) ρ`. -/
theorem rowDiff_le_contraction (W : Graphon) {d : ℕ} (hreg : ∀ v, H.degree v = d)
    {α β c ε : ℝ} (hc : c ∈ Icc (0:ℝ) 1) (hε : ε ∈ Icc (0:ℝ) 1) {x x' : ℝ}
    (hx : ∀ᵐ y ∂unitμ, W.toFun x y ∈ Ioo (0:ℝ) 1 ∧ dS0 (W.toFun x y) = α + β * W.gammaW H x y)
    (hx' : ∀ᵐ y ∂unitμ, W.toFun x' y ∈ Ioo (0:ℝ) 1 ∧ dS0 (W.toFun x' y) = α + β * W.gammaW H x' y) :
    ∫ y, |W.toFun x y - W.toFun x' y| ∂unitμ
      ≤ (2 * (c * (1 - c)) * |β| * (H.edgeFinset.card * (d - 1 : ℕ))
            * (c ^ (d - 2) * ε ^ (H.edgeFinset.card - d))
          + 2 * |β| ^ 2 * (H.edgeFinset.card * (d - 1 : ℕ)) ^ 2 * H.edgeFinset.card
            * (W.rowDist c x + W.rowDist c x' + 2 * W.constDist ε)
          + 2 * |β| * (H.edgeFinset.card * (d - 1 : ℕ)) * (W.rowDist c x + W.rowDist c x'))
        * ∫ y, |W.toFun x y - W.toFun x' y| ∂unitμ := by
  set m : ℝ := (H.edgeFinset.card : ℝ) with hm
  set M₁ : ℝ := m * (d - 1 : ℕ) with hM₁
  set ρ : ℝ := ∫ y, |W.toFun x y - W.toFun x' y| ∂unitμ with hρ
  set B : ℝ := c ^ (d - 2) * ε ^ (H.edgeFinset.card - d) with hB
  set Rx : ℝ := W.rowDist c x + W.rowDist c x' with hRx
  set κ₁ : ℝ := W.constDist ε with hκ₁
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hM₁0 : 0 ≤ M₁ := mul_nonneg hm0 (Nat.cast_nonneg _)
  have hρ0 : 0 ≤ ρ := integral_nonneg fun _ => abs_nonneg _
  have hB0 : 0 ≤ B := mul_nonneg (pow_nonneg hc.1 _) (pow_nonneg hε.1 _)
  have hRx0 : 0 ≤ Rx := add_nonneg (W.rowDist_nonneg c x) (W.rowDist_nonneg c x')
  have hκ₁0 : 0 ≤ κ₁ := W.constDist_nonneg ε
  have hcc : c * (1 - c) ≤ 1 := by nlinarith [hc.1, hc.2]
  have hcc0 : 0 ≤ c * (1 - c) := mul_nonneg hc.1 (by linarith [hc.2])
  -- the crude bound and the sup bound
  have hcr : ∀ y, |W.gammaW H x y - W.gammaW H x' y| ≤ M₁ * ρ := fun y => by
    have := W.abs_gammaW_sub_gammaW_crude H hreg x x' y
    rw [hM₁, hρ]; linarith
  set S : ℝ := |β| * (M₁ * ρ) / 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hsup : ∀ᵐ s ∂unitμ, |W.toFun x s - W.toFun x' s| ≤ S := by
    filter_upwards [hx, hx'] with s hs hs'
    have e1 : W.toFun x s = logistic (α + β * W.gammaW H x s) := by
      rw [← hs.2, logistic_dS0 hs.1.1 hs.1.2]
    have e2 : W.toFun x' s = logistic (α + β * W.gammaW H x' s) := by
      rw [← hs'.2, logistic_dS0 hs'.1.1 hs'.1.2]
    rw [e1, e2]
    calc _ ≤ |(α + β * W.gammaW H x s) - (α + β * W.gammaW H x' s)| / 2 := abs_logistic_sub_le _ _
      _ = |β| * |W.gammaW H x s - W.gammaW H x' s| / 2 := by rw [← abs_mul]; congr 2; ring
      _ ≤ |β| * (M₁ * ρ) / 2 := by gcongr; exact hcr s
  -- the pointwise bound
  have hpt : ∀ᵐ y ∂unitμ, |W.toFun x y - W.toFun x' y|
      ≤ 2 * (c * (1 - c)) * |β| * |W.gammaW H x y - W.gammaW H x' y|
        + 2 * |β| * (M₁ * ρ) * (|W.toFun x y - c| + |W.toFun x' y - c|) := by
    filter_upwards [hx, hx'] with y hy hy'
    have h1 := abs_sub_le_mul_abs_dS0_sub hy.1 hy'.1 hc
    rw [hy.2, hy'.2] at h1
    have e : |α + β * W.gammaW H x y - (α + β * W.gammaW H x' y)|
        = |β| * |W.gammaW H x y - W.gammaW H x' y| := by rw [← abs_mul]; congr 1; ring
    rw [e] at h1
    have h2 := hcr y
    have h3 : 0 ≤ |W.toFun x y - c| + |W.toFun x' y - c| := by positivity
    calc |W.toFun x y - W.toFun x' y|
        ≤ 2 * (c * (1 - c) + |W.toFun x y - c| + |W.toFun x' y - c|)
          * (|β| * |W.gammaW H x y - W.gammaW H x' y|) := h1
      _ = 2 * (c * (1 - c)) * |β| * |W.gammaW H x y - W.gammaW H x' y|
          + 2 * |β| * |W.gammaW H x y - W.gammaW H x' y| * (|W.toFun x y - c| + |W.toFun x' y - c|) := by
          ring
      _ ≤ _ := by
          gcongr
  -- integrability
  have hΓm : Measurable fun y => |W.gammaW H x y - W.gammaW H x' y| :=
    ((W.measurable_gammaW_right H x).sub (W.measurable_gammaW_right H x')).abs
  have hΓi : Integrable (fun y => |W.gammaW H x y - W.gammaW H x' y|) unitμ :=
    integrable_of_abs_le hΓm (2 * m) fun y => by
      rw [abs_abs]
      have h1 := W.gammaW_nonneg H x y; have h2 := W.gammaW_le H x y
      have h3 := W.gammaW_nonneg H x' y; have h4 := W.gammaW_le H x' y
      rw [abs_le]; constructor <;> linarith
  have hcx : Integrable (fun y => |W.toFun x y - c|) unitμ := W.integrable_abs_row_sub x hc
  have hcx' : Integrable (fun y => |W.toFun x' y - c|) unitμ := W.integrable_abs_row_sub x' hc
  have hdiffi : Integrable (fun y => |W.toFun x y - W.toFun x' y|) unitμ :=
    integrable_of_abs_le ((measurable_toFun_right W x).sub (measurable_toFun_right W x')).abs 1
      fun y => by
        rw [abs_abs, abs_le]
        constructor <;> linarith [(W.mem_Icc x y).1, (W.mem_Icc x y).2, (W.mem_Icc x' y).1,
          (W.mem_Icc x' y).2]
  -- the refined bound for `Γ`, integrated
  have hΓint : ∫ y, |W.gammaW H x y - W.gammaW H x' y| ∂unitμ
      ≤ M₁ * (B * ρ + S * (m * (2 * (Rx + 2 * κ₁)))) := by
    have href : ∀ y, |W.gammaW H x y - W.gammaW H x' y|
        ≤ M₁ * (B * ρ + S * (m * (2 * (Rx + W.rowDist ε y + κ₁)))) := fun y => by
      have := W.abs_gammaW_sub_gammaW_le H hreg hc hε hS0 hsup y
      have e : (H.edgeFinset.card : ℝ) * ((d - 1 : ℕ) * (c ^ (d - 2) * ε ^ (H.edgeFinset.card - d)
          * ∫ s, |W.toFun x s - W.toFun x' s| ∂unitμ
        + S * (H.edgeFinset.card * (2 * (W.rowDist c x + W.rowDist c x' + W.rowDist ε y
          + W.constDist ε)))))
          = M₁ * (B * ρ + S * (m * (2 * (Rx + W.rowDist ε y + κ₁)))) := by
        rw [hM₁, hB, hρ, hRx, hκ₁, hm]; ring
      linarith
    have e : ∀ y, M₁ * (B * ρ + S * (m * (2 * (Rx + W.rowDist ε y + κ₁))))
        = M₁ * (B * ρ + S * (m * (2 * (Rx + κ₁)))) + (M₁ * S * m * 2) * W.rowDist ε y := fun y => by
      ring
    have hri : Integrable (fun y => M₁ * (B * ρ + S * (m * (2 * (Rx + κ₁))))
        + (M₁ * S * m * 2) * W.rowDist ε y) unitμ :=
      (integrable_const _).add ((W.integrable_rowDist hε).const_mul _)
    calc ∫ y, |W.gammaW H x y - W.gammaW H x' y| ∂unitμ
        ≤ ∫ y, (M₁ * (B * ρ + S * (m * (2 * (Rx + κ₁)))) + (M₁ * S * m * 2) * W.rowDist ε y) ∂unitμ :=
          integral_mono hΓi hri fun y => (href y).trans (le_of_eq (e y))
      _ = M₁ * (B * ρ + S * (m * (2 * (Rx + κ₁)))) + (M₁ * S * m * 2) * κ₁ := by
          rw [integral_add (f := fun _ => M₁ * (B * ρ + S * (m * (2 * (Rx + κ₁)))))
              (g := fun y => (M₁ * S * m * 2) * W.rowDist ε y) (integrable_const _)
              ((W.integrable_rowDist hε).const_mul _), integral_const, integral_const_mul,
            W.integral_rowDist ε]
          simp only [probReal_univ, one_smul]
          rfl
      _ = M₁ * (B * ρ + S * (m * (2 * (Rx + 2 * κ₁)))) := by ring
  -- integrate the pointwise bound
  have hrhs : Integrable (fun y => 2 * (c * (1 - c)) * |β| * |W.gammaW H x y - W.gammaW H x' y|
      + 2 * |β| * (M₁ * ρ) * (|W.toFun x y - c| + |W.toFun x' y - c|)) unitμ :=
    (hΓi.const_mul _).add ((hcx.add hcx').const_mul _)
  have hint := integral_mono_ae hdiffi hrhs hpt
  have hrhs_eq : ∫ y, (2 * (c * (1 - c)) * |β| * |W.gammaW H x y - W.gammaW H x' y|
      + 2 * |β| * (M₁ * ρ) * (|W.toFun x y - c| + |W.toFun x' y - c|)) ∂unitμ
      = 2 * (c * (1 - c)) * |β| * ∫ y, |W.gammaW H x y - W.gammaW H x' y| ∂unitμ
        + 2 * |β| * (M₁ * ρ) * Rx := by
    rw [integral_add (f := fun y => 2 * (c * (1 - c)) * |β| * |W.gammaW H x y - W.gammaW H x' y|)
      (g := fun y => 2 * |β| * (M₁ * ρ) * (|W.toFun x y - c| + |W.toFun x' y - c|))
      (hΓi.const_mul _) ((hcx.add hcx').const_mul _), integral_const_mul, integral_const_mul,
      integral_add hcx hcx']
    rfl
  rw [hrhs_eq] at hint
  have h1 : 2 * (c * (1 - c)) * |β| * ∫ y, |W.gammaW H x y - W.gammaW H x' y| ∂unitμ
      ≤ 2 * (c * (1 - c)) * |β| * (M₁ * (B * ρ + S * (m * (2 * (Rx + 2 * κ₁))))) :=
    mul_le_mul_of_nonneg_left hΓint (by positivity)
  have h2 : 2 * (c * (1 - c)) * |β| * (M₁ * (S * (m * (2 * (Rx + 2 * κ₁)))))
      ≤ 2 * |β| ^ 2 * M₁ ^ 2 * m * (Rx + 2 * κ₁) * ρ := by
    have e : 2 * (c * (1 - c)) * |β| * (M₁ * (S * (m * (2 * (Rx + 2 * κ₁)))))
        = (c * (1 - c)) * (2 * |β| ^ 2 * M₁ ^ 2 * m * (Rx + 2 * κ₁) * ρ) := by
      rw [hS]; ring
    rw [e]
    have h0 : 0 ≤ 2 * |β| ^ 2 * M₁ ^ 2 * m * (Rx + 2 * κ₁) * ρ := by positivity
    nlinarith
  have e3 : (2 * (c * (1 - c)) * |β| * M₁ * B + 2 * |β| ^ 2 * M₁ ^ 2 * m * (Rx + 2 * κ₁)
      + 2 * |β| * M₁ * Rx) * ρ
      = 2 * (c * (1 - c)) * |β| * (M₁ * (B * ρ)) + 2 * |β| ^ 2 * M₁ ^ 2 * m * (Rx + 2 * κ₁) * ρ
        + 2 * |β| * (M₁ * ρ) * Rx := by ring
  have e4 : 2 * (c * (1 - c)) * |β| * (M₁ * (B * ρ + S * (m * (2 * (Rx + 2 * κ₁)))))
      = 2 * (c * (1 - c)) * |β| * (M₁ * (B * ρ))
        + 2 * (c * (1 - c)) * |β| * (M₁ * (S * (m * (2 * (Rx + 2 * κ₁))))) := by ring
  show ρ ≤ (2 * (c * (1 - c)) * |β| * M₁ * B + 2 * |β| ^ 2 * M₁ ^ 2 * m * (Rx + 2 * κ₁)
      + 2 * |β| * M₁ * Rx) * ρ
  rw [e3]
  linarith

end Graphon

end UpperTailOptimizers
