import UpperTailOptimizers.Bipodality.PinnedDensity
import UpperTailOptimizers.Bipodality.Competitors

/-!
# Perturbations and the constraint correction

A maximizer of `s` on `{e = ε, t(H,·) = τ}` is compared with perturbed graphons.  A perturbation
generally moves the two constraints; it is corrected along two fixed directions `χ₁, χ₂`
supported where the graphon stays away from `0` and `1`.  Because `e` is linear, the correction
can be solved along a line on which `e` is constant, and there `t(H,·)` changes sign, so the
intermediate value theorem suffices.

## Contents

* `abs_prod_add_sub_linear_le` — second-order control of a product of perturbed factors;
* `Graphon.abs_tDensity_sub_linear_le` — `t(H, W + δ) = t(H, W) + ∬ δ Γ_W + O(‖δ‖∞²)`;
* `Graphon.entropy_add_ge` — `s(W + δ) ≥ s(W) + ∬ S₀'(W) δ - (2/η)∬ δ²` away from `{0,1}`.
-/

namespace UpperTailOptimizers

open MeasureTheory Set

/-! ### Products of perturbed factors -/

theorem abs_prod_add_le {ι : Type*} [DecidableEq ι] (T : Finset ι) (w δ : ι → ℝ) {r : ℝ}
    (hr1 : r ≤ 1) (hw : ∀ i ∈ T, |w i| ≤ 1) (hδ : ∀ i ∈ T, |δ i| ≤ r) :
    |∏ i ∈ T, (w i + δ i)| ≤ 2 ^ T.card := by
  rw [Finset.abs_prod]
  calc ∏ i ∈ T, |w i + δ i| ≤ ∏ _i ∈ T, (2:ℝ) :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i hi =>
          le_trans (abs_add_le _ _) (by linarith [hw i hi, hδ i hi])
    _ = 2 ^ T.card := Finset.prod_const _

theorem abs_prod_add_sub_prod_le {ι : Type*} [DecidableEq ι] (T : Finset ι) (w δ : ι → ℝ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hw : ∀ i ∈ T, |w i| ≤ 1) (hδ : ∀ i ∈ T, |δ i| ≤ r) :
    |∏ i ∈ T, (w i + δ i) - ∏ i ∈ T, w i| ≤ (2 ^ T.card - 1) * r := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have hwT : ∀ i ∈ T, |w i| ≤ 1 := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hδT : ∀ i ∈ T, |δ i| ≤ r := fun i hi => hδ i (Finset.mem_insert_of_mem hi)
    have hIH := ih hwT hδT
    have hP := abs_prod_add_le T w δ hr1 hwT hδT
    have hwa := hw a (Finset.mem_insert_self a T)
    have hδa := hδ a (Finset.mem_insert_self a T)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hsplit : (w a + δ a) * ∏ i ∈ T, (w i + δ i) - w a * ∏ i ∈ T, w i
        = w a * (∏ i ∈ T, (w i + δ i) - ∏ i ∈ T, w i) + δ a * ∏ i ∈ T, (w i + δ i) := by ring
    rw [hsplit]
    have h1 : |w a * (∏ i ∈ T, (w i + δ i) - ∏ i ∈ T, w i)| ≤ (2 ^ T.card - 1) * r := by
      rw [abs_mul]
      calc |w a| * |∏ i ∈ T, (w i + δ i) - ∏ i ∈ T, w i| ≤ 1 * ((2 ^ T.card - 1) * r) :=
            mul_le_mul hwa hIH (abs_nonneg _) zero_le_one
        _ = (2 ^ T.card - 1) * r := one_mul _
    have h2 : |δ a * ∏ i ∈ T, (w i + δ i)| ≤ r * 2 ^ T.card := by
      rw [abs_mul]; exact mul_le_mul hδa hP (abs_nonneg _) hr0
    calc |w a * (∏ i ∈ T, (w i + δ i) - ∏ i ∈ T, w i) + δ a * ∏ i ∈ T, (w i + δ i)|
        ≤ |w a * (∏ i ∈ T, (w i + δ i) - ∏ i ∈ T, w i)| + |δ a * ∏ i ∈ T, (w i + δ i)| :=
          abs_add_le _ _
      _ ≤ (2 ^ T.card - 1) * r + r * 2 ^ T.card := add_le_add h1 h2
      _ = (2 ^ (T.card + 1) - 1) * r := by ring

/-- **Second-order control of a perturbed product.** -/
theorem abs_prod_add_sub_linear_le {ι : Type*} [DecidableEq ι] (T : Finset ι) (w δ : ι → ℝ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hw : ∀ i ∈ T, |w i| ≤ 1) (hδ : ∀ i ∈ T, |δ i| ≤ r) :
    |∏ i ∈ T, (w i + δ i) - ∏ i ∈ T, w i - ∑ i ∈ T, δ i * ∏ j ∈ T.erase i, w j|
      ≤ 2 ^ T.card * r ^ 2 := by
  induction T using Finset.induction_on with
  | empty => simp; positivity
  | insert a T ha ih =>
    have hwT : ∀ i ∈ T, |w i| ≤ 1 := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hδT : ∀ i ∈ T, |δ i| ≤ r := fun i hi => hδ i (Finset.mem_insert_of_mem hi)
    have hIH := ih hwT hδT
    have hPQ := abs_prod_add_sub_prod_le T w δ hr0 hr1 hwT hδT
    have hwa := hw a (Finset.mem_insert_self a T)
    have hδa := hδ a (Finset.mem_insert_self a T)
    have hlin : ∑ i ∈ insert a T, δ i * ∏ j ∈ (insert a T).erase i, w j
        = δ a * ∏ j ∈ T, w j + w a * ∑ i ∈ T, δ i * ∏ j ∈ T.erase i, w j := by
      rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hia : a ≠ i := fun h => ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne hia, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring
    rw [Finset.prod_insert ha, Finset.prod_insert ha, hlin, Finset.card_insert_of_notMem ha]
    have hsplit : (w a + δ a) * ∏ i ∈ T, (w i + δ i) - w a * ∏ i ∈ T, w i
        - (δ a * ∏ j ∈ T, w j + w a * ∑ i ∈ T, δ i * ∏ j ∈ T.erase i, w j)
        = w a * (∏ i ∈ T, (w i + δ i) - ∏ i ∈ T, w i - ∑ i ∈ T, δ i * ∏ j ∈ T.erase i, w j)
          + δ a * (∏ i ∈ T, (w i + δ i) - ∏ i ∈ T, w i) := by ring
    rw [hsplit]
    have h1 : |w a * (∏ i ∈ T, (w i + δ i) - ∏ i ∈ T, w i
        - ∑ i ∈ T, δ i * ∏ j ∈ T.erase i, w j)| ≤ 2 ^ T.card * r ^ 2 := by
      rw [abs_mul]
      calc _ ≤ 1 * (2 ^ T.card * r ^ 2) := mul_le_mul hwa hIH (abs_nonneg _) zero_le_one
        _ = 2 ^ T.card * r ^ 2 := one_mul _
    have h2 : |δ a * (∏ i ∈ T, (w i + δ i) - ∏ i ∈ T, w i)| ≤ r * ((2 ^ T.card - 1) * r) := by
      rw [abs_mul]; exact mul_le_mul hδa hPQ (abs_nonneg _) hr0
    have hpow : (0:ℝ) ≤ 2 ^ T.card := by positivity
    calc _ ≤ |w a * (∏ i ∈ T, (w i + δ i) - ∏ i ∈ T, w i
            - ∑ i ∈ T, δ i * ∏ j ∈ T.erase i, w j)|
          + |δ a * (∏ i ∈ T, (w i + δ i) - ∏ i ∈ T, w i)| := abs_add_le _ _
      _ ≤ 2 ^ T.card * r ^ 2 + r * ((2 ^ T.card - 1) * r) := add_le_add h1 h2
      _ = 2 ^ (T.card + 1) * r ^ 2 - r ^ 2 := by ring
      _ ≤ 2 ^ (T.card + 1) * r ^ 2 := by nlinarith [sq_nonneg r]

/-! ### The first-order expansion of `t(H,·)` -/

namespace Graphon

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- **`t(H, W + δ) = t(H, W) + ∬ δ Γ_W + O(‖δ‖∞²)`.** -/
theorem abs_tDensity_sub_linear_le (W W₂ : Graphon) {δ : ℝ → ℝ → ℝ}
    (hδ : ∀ x y, W₂.toFun x y = W.toFun x y + δ x y)
    (hδm : Measurable fun p : ℝ × ℝ => δ p.1 p.2) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hδb : ∀ x y, |δ x y| ≤ r) :
    |W₂.tDensity H - W.tDensity H - ∫ p : ℝ × ℝ, δ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ|
      ≤ 2 ^ H.edgeFinset.card * r ^ 2 := by
  classical
  have hδs : ∀ x y, δ x y = δ y x := fun x y => by
    have h1 := hδ x y
    have h2 := hδ y x
    rw [W₂.symm' x y, W.symm' x y] at h1
    linarith
  set π : Measure (V → ℝ) := Measure.pi fun _ : V => unitμ with hπ
  set δE : (V → ℝ) → Sym2 V → ℝ := fun z e =>
    Sym2.lift ⟨fun a b => δ (z a) (z b), fun a b => hδs (z a) (z b)⟩ e with hδE
  have hsplitE : ∀ z e, W₂.gEdge z e = W.gEdge z e + δE z e := by
    intro z e
    induction e using Sym2.ind with
    | _ a b => exact hδ (z a) (z b)
  have hδEb : ∀ z e, |δE z e| ≤ r := by
    intro z e
    induction e using Sym2.ind with
    | _ a b => exact hδb (z a) (z b)
  have hδEm : ∀ e, Measurable fun z : V → ℝ => δE z e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      have hpair : Measurable fun z : V → ℝ => (z a, z b) :=
        (measurable_pi_apply a).prodMk (measurable_pi_apply b)
      exact hδm.comp hpair
  have hwb : ∀ (z : V → ℝ) (e : Sym2 V), |W.gEdge z e| ≤ 1 := fun z e => by
    rw [abs_of_nonneg (W.gEdge_mem_Icc z e).1]; exact (W.gEdge_mem_Icc z e).2
  -- the linear term
  have hlin := W.sum_integral_mul_prod_erase_eq H hδm hδb hδs
  -- integrability
  have hint₂ : Integrable (fun z : V → ℝ => ∏ e ∈ H.edgeFinset, W₂.gEdge z e) π :=
    integrable_of_abs_le (W₂.measurable_prod_gEdge _) 1 fun z => by
      rw [abs_of_nonneg (W₂.prod_gEdge_mem_Icc _ _).1]; exact (W₂.prod_gEdge_mem_Icc _ _).2
  have hint₁ : Integrable (fun z : V → ℝ => ∏ e ∈ H.edgeFinset, W.gEdge z e) π :=
    integrable_of_abs_le (W.measurable_prod_gEdge _) 1 fun z => by
      rw [abs_of_nonneg (W.prod_gEdge_mem_Icc _ _).1]; exact (W.prod_gEdge_mem_Icc _ _).2
  have hintL : ∀ e ∈ H.edgeFinset, Integrable (fun z : V → ℝ =>
      δE z e * ∏ e' ∈ H.edgeFinset.erase e, W.gEdge z e') π := fun e _ =>
    integrable_of_abs_le ((hδEm e).mul (W.measurable_prod_gEdge _)) r fun z => by
      rw [abs_mul, abs_of_nonneg (W.prod_gEdge_mem_Icc _ _).1]
      calc |δE z e| * ∏ e' ∈ H.edgeFinset.erase e, W.gEdge z e' ≤ r * 1 :=
            mul_le_mul (hδEb z e) (W.prod_gEdge_mem_Icc _ _).2 (W.prod_gEdge_mem_Icc _ _).1 hr0
        _ = r := mul_one r
  have hsumint : Integrable (fun z : V → ℝ => ∑ e ∈ H.edgeFinset,
      δE z e * ∏ e' ∈ H.edgeFinset.erase e, W.gEdge z e') π := integrable_finsetSum _ hintL
  have htexp : W₂.tDensity H - W.tDensity H
      - ∑ e ∈ H.edgeFinset, ∫ z, δE z e * ∏ e' ∈ H.edgeFinset.erase e, W.gEdge z e' ∂π
      = ∫ z, (∏ e ∈ H.edgeFinset, (W.gEdge z e + δE z e) - ∏ e ∈ H.edgeFinset, W.gEdge z e
          - ∑ e ∈ H.edgeFinset, δE z e * ∏ e' ∈ H.edgeFinset.erase e, W.gEdge z e') ∂π := by
    have h2 : W₂.tDensity H = ∫ z, ∏ e ∈ H.edgeFinset, W₂.gEdge z e ∂π := rfl
    have h1 : W.tDensity H = ∫ z, ∏ e ∈ H.edgeFinset, W.gEdge z e ∂π := rfl
    simp only [← hsplitE]
    rw [integral_sub (f := fun z => ∏ e ∈ H.edgeFinset, W₂.gEdge z e
        - ∏ e ∈ H.edgeFinset, W.gEdge z e)
      (g := fun z => ∑ e ∈ H.edgeFinset, δE z e * ∏ e' ∈ H.edgeFinset.erase e, W.gEdge z e')
      (hint₂.sub hint₁) hsumint,
      integral_sub (f := fun z => ∏ e ∈ H.edgeFinset, W₂.gEdge z e)
        (g := fun z => ∏ e ∈ H.edgeFinset, W.gEdge z e) hint₂ hint₁,
      integral_finsetSum _ hintL, h2, h1]
  have hpt : ∀ z : V → ℝ, |∏ e ∈ H.edgeFinset, (W.gEdge z e + δE z e)
      - ∏ e ∈ H.edgeFinset, W.gEdge z e
      - ∑ e ∈ H.edgeFinset, δE z e * ∏ e' ∈ H.edgeFinset.erase e, W.gEdge z e'|
      ≤ 2 ^ H.edgeFinset.card * r ^ 2 := fun z =>
    abs_prod_add_sub_linear_le _ (W.gEdge z) (δE z) hr0 hr1 (fun e _ => hwb z e)
      (fun e _ => hδEb z e)
  rw [← hlin]
  show |W₂.tDensity H - W.tDensity H
      - ∑ e ∈ H.edgeFinset, ∫ z, δE z e * ∏ e' ∈ H.edgeFinset.erase e, W.gEdge z e' ∂π|
      ≤ 2 ^ H.edgeFinset.card * r ^ 2
  rw [htexp]
  calc |∫ z, (∏ e ∈ H.edgeFinset, (W.gEdge z e + δE z e) - ∏ e ∈ H.edgeFinset, W.gEdge z e
        - ∑ e ∈ H.edgeFinset, δE z e * ∏ e' ∈ H.edgeFinset.erase e, W.gEdge z e') ∂π|
      ≤ ∫ z, |∏ e ∈ H.edgeFinset, (W.gEdge z e + δE z e) - ∏ e ∈ H.edgeFinset, W.gEdge z e
        - ∑ e ∈ H.edgeFinset, δE z e * ∏ e' ∈ H.edgeFinset.erase e, W.gEdge z e'| ∂π :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _z, (2:ℝ) ^ H.edgeFinset.card * r ^ 2 ∂π := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall hpt)
    _ = 2 ^ H.edgeFinset.card * r ^ 2 := by simp

end Graphon

/-! ### The second-order expansion of the entropy -/

theorem S0_add_ge {η w δ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) (hw : w ∈ Icc η (1 - η))
    (hδ : |δ| ≤ η / 2) : S0 w + dS0 w * δ - 2 / η * δ ^ 2 ≤ S0 (w + δ) := by
  set f : ℝ → ℝ := fun x => S0 x - S0 w - dS0 w * (x - w) with hf
  set f' : ℝ → ℝ := fun x => dS0 x - dS0 w with hf'
  set f'' : ℝ → ℝ := fun x => -1 / (2 * (x * (1 - x))) with hf''
  have hmem : ∀ x ∈ Icc (w - η / 2) (w + η / 2), η / 2 ≤ x ∧ x ≤ 1 - η / 2 := fun x hx => by
    constructor <;> linarith [hx.1, hx.2, hw.1, hw.2]
  have hd1 : ∀ x ∈ Icc (w - η / 2) (w + η / 2), HasDerivAt f (f' x) x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hmem x hx
    have hx0 : x ≠ 0 := by intro h; rw [h] at h1; linarith
    have hx1 : x ≠ 1 := by intro h; rw [h] at h2; linarith
    have h := ((hasDerivAt_S0 hx0 hx1).sub_const (S0 w)).sub
      (((hasDerivAt_id x).sub_const w).const_mul (dS0 w))
    simp only [mul_one] at h
    exact h
  have hd2 : ∀ x ∈ Icc (w - η / 2) (w + η / 2), HasDerivAt f' (f'' x) x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hmem x hx
    have hx0 : x ≠ 0 := by intro h; rw [h] at h1; linarith
    have hx1 : x ≠ 1 := by intro h; rw [h] at h2; linarith
    exact (hasDerivAt_dS0 hx0 hx1).sub_const (dS0 w)
  have hlow : ∀ x ∈ Icc (w - η / 2) (w + η / 2), -(4 / η) ≤ f'' x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hmem x hx
    have hprod : η / 4 ≤ x * (1 - x) := by nlinarith
    have hpos : 0 < 2 * (x * (1 - x)) := by nlinarith
    simp only [hf'']
    rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ hpos hη]
    nlinarith
  have hq := quadratic_lower_of_deriv2_ge (f := f) (f' := f') (f'' := f'') (c := w)
    (a := w - η / 2) (b := w + η / 2) (by linarith) (by linarith) hd1 hd2 hlow
    (by simp [hf]) (by simp [hf']) (w + δ)
    ⟨by linarith [(abs_le.mp hδ).1], by linarith [(abs_le.mp hδ).2]⟩
  simp only [hf] at hq
  have : -(4 / η) / 2 * (w + δ - w) ^ 2 = -(2 / η * δ ^ 2) := by ring
  linarith

theorem measurable_dS0 : Measurable dS0 := by
  unfold dS0
  exact ((Real.measurable_log.comp (measurable_const.sub measurable_id)).sub
    Real.measurable_log).div_const 2

theorem exists_abs_dS0_le {η : ℝ} (hη : 0 < η) : ∃ L, ∀ w ∈ Icc η (1 - η), |dS0 w| ≤ L := by
  have hc : ContinuousOn dS0 (Icc η (1 - η)) := by
    intro w hw
    have hw0 : w ≠ 0 := by intro h; rw [h] at hw; linarith [hw.1]
    have hw1 : w ≠ 1 := by intro h; rw [h] at hw; linarith [hw.2]
    exact (hasDerivAt_dS0 hw0 hw1).continuousAt.continuousWithinAt
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := η) (b := 1 - η)).exists_bound_of_continuousOn hc
  exact ⟨L, fun w hw => by simpa [Real.norm_eq_abs] using hL w hw⟩

namespace Graphon

/-- **The second-order expansion of the entropy** for a perturbation supported away from
`{0,1}`. -/
theorem entropy_add_ge (W W₂ : Graphon) {δ : ℝ → ℝ → ℝ}
    (hδ : ∀ x y, W₂.toFun x y = W.toFun x y + δ x y)
    (hδm : Measurable fun p : ℝ × ℝ => δ p.1 p.2) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hsupp : ∀ x y, δ x y ≠ 0 → W.toFun x y ∈ Icc η (1 - η))
    (hδb : ∀ x y, |δ x y| ≤ η / 2) :
    W.entropy + ∫ p : ℝ × ℝ, dS0 (W.toFun p.1 p.2) * δ p.1 p.2 ∂gμ
        - 2 / η * ∫ p : ℝ × ℝ, δ p.1 p.2 ^ 2 ∂gμ ≤ W₂.entropy := by
  obtain ⟨L, hL⟩ := exists_abs_dS0_le hη
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hL η ⟨le_rfl, by linarith⟩)
  rw [W.entropy_eq_integral_S0, W₂.entropy_eq_integral_S0]
  have hpt : ∀ p : ℝ × ℝ, S0 (W.toFun p.1 p.2) + dS0 (W.toFun p.1 p.2) * δ p.1 p.2
      - 2 / η * δ p.1 p.2 ^ 2 ≤ S0 (W₂.toFun p.1 p.2) := by
    intro p
    by_cases h0 : δ p.1 p.2 = 0
    · rw [hδ, h0]; simp
    · rw [hδ]; exact S0_add_ge hη hη1 (hsupp _ _ h0) (hδb _ _)
  have hS0c : Continuous S0 := by
    have h : S0 = fun u => Real.binEntropy u / 2 := by
      funext u; unfold S0; rw [shannonH_eq_binEntropy]
    rw [h]; exact Real.binEntropy_continuous.div_const 2
  have hint1 : Integrable (fun p : ℝ × ℝ => S0 (W.toFun p.1 p.2)) gμ :=
    W.integrable_comp hS0c.measurable hS0c.continuousOn
  have hint2 : Integrable (fun p : ℝ × ℝ => S0 (W₂.toFun p.1 p.2)) gμ :=
    W₂.integrable_comp hS0c.measurable hS0c.continuousOn
  have hint3 : Integrable (fun p : ℝ × ℝ => dS0 (W.toFun p.1 p.2) * δ p.1 p.2) gμ := by
    refine integrable_of_abs_le ((measurable_dS0.comp W.measurable_uncurry).mul hδm) (L * (η / 2))
      fun p => ?_
    by_cases h0 : δ p.1 p.2 = 0
    · rw [h0, mul_zero, abs_zero]; positivity
    · rw [abs_mul]
      exact mul_le_mul (hL _ (hsupp _ _ h0)) (hδb _ _) (abs_nonneg _) hL0
  have hint4 : Integrable (fun p : ℝ × ℝ => δ p.1 p.2 ^ 2) gμ :=
    integrable_of_abs_le (hδm.pow_const 2) ((η / 2) ^ 2) fun p => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hδb _ _) 2
  have hint5 : Integrable (fun p : ℝ × ℝ => S0 (W.toFun p.1 p.2)
      + dS0 (W.toFun p.1 p.2) * δ p.1 p.2 - 2 / η * δ p.1 p.2 ^ 2) gμ :=
    (hint1.add hint3).sub (hint4.const_mul _)
  have h := integral_mono hint5 hint2 hpt
  rw [integral_sub (f := fun p : ℝ × ℝ => S0 (W.toFun p.1 p.2) + dS0 (W.toFun p.1 p.2) * δ p.1 p.2)
      (g := fun p : ℝ × ℝ => 2 / η * δ p.1 p.2 ^ 2) (hint1.add hint3) (hint4.const_mul _),
    integral_add (f := fun p : ℝ × ℝ => S0 (W.toFun p.1 p.2))
      (g := fun p : ℝ × ℝ => dS0 (W.toFun p.1 p.2) * δ p.1 p.2) hint1 hint3,
    integral_const_mul] at h
  exact h

/-- A clamped graphon: `max 0 (min 1 f)` for a symmetric measurable `f`. -/
noncomputable def ofClamp (f : ℝ → ℝ → ℝ) (hs : ∀ x y, f x y = f y x)
    (hm : Measurable fun p : ℝ × ℝ => f p.1 p.2) : Graphon where
  toFun x y := max 0 (min 1 (f x y))
  symm' x y := by rw [hs]
  meas' := measurable_const.max (measurable_const.min hm)
  nonneg' _ _ := le_max_left _ _
  le_one' _ _ := max_le zero_le_one (min_le_left _ _)

theorem ofClamp_apply_of_mem {f : ℝ → ℝ → ℝ} (hs : ∀ x y, f x y = f y x)
    (hm : Measurable fun p : ℝ × ℝ => f p.1 p.2) {x y : ℝ} (h : f x y ∈ Icc (0:ℝ) 1) :
    (ofClamp f hs hm).toFun x y = f x y := by
  show max 0 (min 1 (f x y)) = f x y
  rw [min_eq_right h.2, max_eq_right h.1]

end Graphon

/-! ### The constraint correction -/

section Correction

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- `∬ (a χ₁ + b χ₂) = a ∬ χ₁ + b ∬ χ₂` plus the graphon. -/
theorem edgeDensity_add_dirs (W W₂ : Graphon) {χ₁ χ₂ : ℝ → ℝ → ℝ}
    (hχ₁m : Measurable fun p : ℝ × ℝ => χ₁ p.1 p.2) (hχ₂m : Measurable fun p : ℝ × ℝ => χ₂ p.1 p.2)
    (hχ₁b : ∀ x y, |χ₁ x y| ≤ 1) (hχ₂b : ∀ x y, |χ₂ x y| ≤ 1) {u₁ u₂ : ℝ}
    (hW₂ : ∀ x y, W₂.toFun x y = W.toFun x y + u₁ * χ₁ x y + u₂ * χ₂ x y) :
    W₂.edgeDensity = W.edgeDensity + u₁ * ∫ p : ℝ × ℝ, χ₁ p.1 p.2 ∂gμ
      + u₂ * ∫ p : ℝ × ℝ, χ₂ p.1 p.2 ∂gμ := by
  have hi₁ : Integrable (fun p : ℝ × ℝ => χ₁ p.1 p.2) gμ := integrable_of_abs_le hχ₁m 1 fun p => hχ₁b _ _
  have hi₂ : Integrable (fun p : ℝ × ℝ => χ₂ p.1 p.2) gμ := integrable_of_abs_le hχ₂m 1 fun p => hχ₂b _ _
  show ∫ p, W₂.toFun p.1 p.2 ∂gμ = ∫ p, W.toFun p.1 p.2 ∂gμ + u₁ * ∫ p : ℝ × ℝ, χ₁ p.1 p.2 ∂gμ
      + u₂ * ∫ p : ℝ × ℝ, χ₂ p.1 p.2 ∂gμ
  rw [integral_congr_ae (f := fun p : ℝ × ℝ => W₂.toFun p.1 p.2)
      (g := fun p : ℝ × ℝ => W.toFun p.1 p.2 + u₁ * χ₁ p.1 p.2 + u₂ * χ₂ p.1 p.2)
      (Filter.Eventually.of_forall fun p => hW₂ p.1 p.2),
    integral_add (f := fun p : ℝ × ℝ => W.toFun p.1 p.2 + u₁ * χ₁ p.1 p.2)
      (g := fun p : ℝ × ℝ => u₂ * χ₂ p.1 p.2) (W.integrable_self.add (hi₁.const_mul _))
      (hi₂.const_mul _),
    integral_add (f := fun p : ℝ × ℝ => W.toFun p.1 p.2) (g := fun p : ℝ × ℝ => u₁ * χ₁ p.1 p.2)
      W.integrable_self (hi₁.const_mul _), integral_const_mul, integral_const_mul]

theorem integral_dirs_gammaW (W : Graphon) {χ₁ χ₂ : ℝ → ℝ → ℝ}
    (hχ₁m : Measurable fun p : ℝ × ℝ => χ₁ p.1 p.2) (hχ₂m : Measurable fun p : ℝ × ℝ => χ₂ p.1 p.2)
    (hχ₁b : ∀ x y, |χ₁ x y| ≤ 1) (hχ₂b : ∀ x y, |χ₂ x y| ≤ 1) (u₁ u₂ : ℝ) :
    ∫ p : ℝ × ℝ, (u₁ * χ₁ p.1 p.2 + u₂ * χ₂ p.1 p.2) * W.gammaW H p.1 p.2 ∂gμ
      = u₁ * ∫ p : ℝ × ℝ, χ₁ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ
        + u₂ * ∫ p : ℝ × ℝ, χ₂ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ := by
  have hΓ := W.measurable_gammaW H
  have hb : ∀ {χ : ℝ → ℝ → ℝ}, (Measurable fun p : ℝ × ℝ => χ p.1 p.2) → (∀ x y, |χ x y| ≤ 1) →
      Integrable (fun p : ℝ × ℝ => χ p.1 p.2 * W.gammaW H p.1 p.2) gμ := by
    intro χ hm hbd
    refine integrable_of_abs_le (hm.mul hΓ) H.edgeFinset.card fun p => ?_
    rw [abs_mul, abs_of_nonneg (W.gammaW_nonneg H _ _)]
    calc |χ p.1 p.2| * W.gammaW H p.1 p.2 ≤ 1 * H.edgeFinset.card :=
          mul_le_mul (hbd _ _) (W.gammaW_le H _ _) (W.gammaW_nonneg H _ _) zero_le_one
      _ = H.edgeFinset.card := one_mul _
  have h1 := (hb hχ₁m hχ₁b).const_mul u₁
  have h2 := (hb hχ₂m hχ₂b).const_mul u₂
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add h1 h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only
  ring

set_option maxHeartbeats 3000000 in
/-- **The constraint correction.**  Two directions `χ₁, χ₂`, bounded by `1`, supported where
`W ∈ [η, 1-η]`, with `|det (∬ χ_k, ∬ χ_k Γ_W)| ≥ D₀`, restore any nearby pair of constraint
values, at a cost linear in the displacement. -/
theorem exists_correction {η D₀ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) (hD₀ : 0 < D₀) :
    ∃ ρ₀ K : ℝ, 0 < ρ₀ ∧ 0 < K ∧ ∀ (W : Graphon) (χ₁ χ₂ : ℝ → ℝ → ℝ),
      (Measurable fun p : ℝ × ℝ => χ₁ p.1 p.2) → (Measurable fun p : ℝ × ℝ => χ₂ p.1 p.2) →
      (∀ x y, χ₁ x y = χ₁ y x) → (∀ x y, χ₂ x y = χ₂ y x) →
      (∀ x y, |χ₁ x y| ≤ 1) → (∀ x y, |χ₂ x y| ≤ 1) →
      (∀ x y, χ₁ x y ≠ 0 ∨ χ₂ x y ≠ 0 → W.toFun x y ∈ Icc η (1 - η)) →
      D₀ ≤ |(∫ p : ℝ × ℝ, χ₁ p.1 p.2 ∂gμ) * (∫ p : ℝ × ℝ, χ₂ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ)
            - (∫ p : ℝ × ℝ, χ₂ p.1 p.2 ∂gμ) * (∫ p : ℝ × ℝ, χ₁ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ)| →
      ∀ e₀ t₀ : ℝ, |e₀ - W.edgeDensity| + |t₀ - W.tDensity H| ≤ ρ₀ →
      ∃ u₁ u₂ : ℝ, |u₁| + |u₂| ≤ K * (|e₀ - W.edgeDensity| + |t₀ - W.tDensity H|) ∧
        ∃ W'' : Graphon, (∀ x y, W''.toFun x y = W.toFun x y + u₁ * χ₁ x y + u₂ * χ₂ x y) ∧
          W''.edgeDensity = e₀ ∧ W''.tDensity H = t₀ := by
  classical
  set mR : ℝ := (H.edgeFinset.card : ℝ) with hmR
  have hmR0 : 0 ≤ mR := Nat.cast_nonneg _
  set M : ℝ := 2 ^ H.edgeFinset.card with hM
  have hM1 : 1 ≤ M := one_le_pow₀ (by norm_num)
  set CA : ℝ := 1 + 2 * mR ^ 2 / D₀ with hCA
  have hCA1 : 1 ≤ CA := by rw [hCA]; linarith [show 0 ≤ 2 * mR ^ 2 / D₀ by positivity]
  set Cu : ℝ := 2 * mR / D₀ + 8 * CA / D₀ with hCu
  have hCu0 : 0 < Cu := by positivity
  set ρ₀ : ℝ := min (η / (2 * Cu)) (CA / (M * Cu ^ 2)) with hρ₀
  have hρ₀0 : 0 < ρ₀ := lt_min (by positivity) (by positivity)
  refine ⟨ρ₀, Cu, hρ₀0, hCu0, ?_⟩
  intro W χ₁ χ₂ hχ₁m hχ₂m hχ₁s hχ₂s hχ₁b hχ₂b hsupp hdet e₀ t₀ hρ
  set Δe : ℝ := e₀ - W.edgeDensity with hΔe
  set Δt : ℝ := t₀ - W.tDensity H with hΔt
  set ρ : ℝ := |Δe| + |Δt| with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  rcases eq_or_lt_of_le hρ0 with hρz | hρpos
  · -- nothing to correct
    have hΔe0 : Δe = 0 := by
      have : |Δe| = 0 := by linarith [abs_nonneg Δe, abs_nonneg Δt]
      exact abs_eq_zero.mp this
    have hΔt0 : Δt = 0 := by
      have : |Δt| = 0 := by linarith [abs_nonneg Δe, abs_nonneg Δt]
      exact abs_eq_zero.mp this
    refine ⟨0, 0, ?_, W, fun x y => by ring, by linarith, by linarith⟩
    rw [abs_zero, add_zero]
    exact mul_nonneg hCu0.le hρ0
  -- the coefficients
  set c₁ : ℝ := ∫ p : ℝ × ℝ, χ₁ p.1 p.2 ∂gμ with hc₁
  set c₂ : ℝ := ∫ p : ℝ × ℝ, χ₂ p.1 p.2 ∂gμ with hc₂
  set g₁ : ℝ := ∫ p : ℝ × ℝ, χ₁ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ with hg₁
  set g₂ : ℝ := ∫ p : ℝ × ℝ, χ₂ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ with hg₂
  set D : ℝ := c₁ * g₂ - c₂ * g₁ with hD
  have hcb : ∀ {χ : ℝ → ℝ → ℝ}, (Measurable fun p : ℝ × ℝ => χ p.1 p.2) → (∀ x y, |χ x y| ≤ 1) →
      |∫ p : ℝ × ℝ, χ p.1 p.2 ∂gμ| ≤ 1 := by
    intro χ hm hbd
    have h := norm_integral_le_of_norm_le_const (μ := gμ) (f := fun p : ℝ × ℝ => χ p.1 p.2)
      (Filter.Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hbd p.1 p.2)
    simpa [Real.norm_eq_abs, measureReal_def, gμ] using h
  have hgb : ∀ {χ : ℝ → ℝ → ℝ}, (Measurable fun p : ℝ × ℝ => χ p.1 p.2) → (∀ x y, |χ x y| ≤ 1) →
      |∫ p : ℝ × ℝ, χ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ| ≤ mR := by
    intro χ hm hbd
    have h := norm_integral_le_of_norm_le_const (μ := gμ)
      (f := fun p : ℝ × ℝ => χ p.1 p.2 * W.gammaW H p.1 p.2)
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (W.gammaW_nonneg H _ _)]
        calc |χ p.1 p.2| * W.gammaW H p.1 p.2 ≤ 1 * mR :=
              mul_le_mul (hbd _ _) (W.gammaW_le H _ _) (W.gammaW_nonneg H _ _) zero_le_one
          _ = mR := one_mul _)
    simpa [Real.norm_eq_abs, measureReal_def, gμ] using h
  have hc₁b : |c₁| ≤ 1 := hcb hχ₁m hχ₁b
  have hc₂b : |c₂| ≤ 1 := hcb hχ₂m hχ₂b
  have hg₁b : |g₁| ≤ mR := hgb hχ₁m hχ₁b
  have hg₂b : |g₂| ≤ mR := hgb hχ₂m hχ₂b
  have hDabs : D₀ ≤ |D| := hdet
  set Sc : ℝ := |c₁| + |c₂| with hSc
  have hScD : D₀ ≤ mR * Sc := by
    have h1 : |D| ≤ |c₁| * |g₂| + |c₂| * |g₁| := by
      rw [hD]
      calc |c₁ * g₂ - c₂ * g₁| ≤ |c₁ * g₂| + |c₂ * g₁| := abs_sub _ _
        _ = |c₁| * |g₂| + |c₂| * |g₁| := by rw [abs_mul, abs_mul]
    have h2 : |c₁| * |g₂| + |c₂| * |g₁| ≤ |c₁| * mR + |c₂| * mR :=
      add_le_add (mul_le_mul_of_nonneg_left hg₂b (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hg₁b (abs_nonneg _))
    rw [hSc]; nlinarith
  have hScpos : 0 < Sc := by
    by_contra h
    push Not at h
    have : mR * Sc ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmR0 h
    linarith
  set N : ℝ := c₁ ^ 2 + c₂ ^ 2 with hN
  have hNSc : Sc ^ 2 ≤ 2 * N := by
    rw [hSc, hN, ← sq_abs c₁, ← sq_abs c₂]; nlinarith [sq_nonneg (|c₁| - |c₂|)]
  have hNpos : 0 < N := by nlinarith [sq_pos_of_pos hScpos]
  have hmRpos : 0 < mR := by
    by_contra h
    push Not at h
    have : mR * Sc ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hScpos.le
    linarith
  -- the base point on the level line of `e`
  set u₀₁ : ℝ := Δe / N * c₁ with hu₀₁
  set u₀₂ : ℝ := Δe / N * c₂ with hu₀₂
  have hu₀ : |u₀₁| + |u₀₂| ≤ 2 * mR / D₀ * |Δe| := by
    have h1 : |u₀₁| + |u₀₂| = |Δe| * Sc / N := by
      rw [hu₀₁, hu₀₂, abs_mul, abs_mul, abs_div, abs_of_pos hNpos, hSc]; ring
    have h2 : Sc / N ≤ 2 / Sc := by
      rw [div_le_div_iff₀ hNpos hScpos]; nlinarith
    have h3 : 2 / Sc ≤ 2 * mR / D₀ := by
      rw [div_le_div_iff₀ hScpos hD₀]; nlinarith
    rw [h1, mul_div_assoc]
    calc |Δe| * (Sc / N) ≤ |Δe| * (2 * mR / D₀) :=
          mul_le_mul_of_nonneg_left (le_trans h2 h3) (abs_nonneg _)
      _ = 2 * mR / D₀ * |Δe| := by ring
  -- the level line of `e` and the clamped graphons along it
  set f : ℝ → ℝ → ℝ → ℝ := fun b x y =>
    W.toFun x y + (u₀₁ - b * c₂) * χ₁ x y + (u₀₂ + b * c₁) * χ₂ x y with hf
  have hfs : ∀ b x y, f b x y = f b y x := by
    intro b x y; simp only [hf, W.symm' x y, hχ₁s x y, hχ₂s x y]
  have hfm : ∀ b, Measurable fun p : ℝ × ℝ => f b p.1 p.2 := fun b =>
    (W.measurable_uncurry.add (measurable_const.mul hχ₁m)).add (measurable_const.mul hχ₂m)
  set G : ℝ → Graphon := fun b => Graphon.ofClamp (f b) (hfs b) (hfm b) with hG
  set U : ℝ → ℝ := fun b => |u₀₁ - b * c₂| + |u₀₂ + b * c₁| with hU
  have hUb : ∀ b, U b ≤ 2 * mR / D₀ * |Δe| + |b| * Sc := by
    intro b
    have h1 : |u₀₁ - b * c₂| ≤ |u₀₁| + |b| * |c₂| := by
      rw [← abs_mul]; exact abs_sub _ _
    have h2 : |u₀₂ + b * c₁| ≤ |u₀₂| + |b| * |c₁| := by
      rw [← abs_mul]; exact abs_add_le _ _
    show |u₀₁ - b * c₂| + |u₀₂ + b * c₁| ≤ 2 * mR / D₀ * |Δe| + |b| * Sc
    rw [hSc]; nlinarith [hu₀]
  have hδb : ∀ b, U b ≤ η / 2 → ∀ x y,
      |(u₀₁ - b * c₂) * χ₁ x y + (u₀₂ + b * c₁) * χ₂ x y| ≤ U b := by
    intro b _ x y
    calc |(u₀₁ - b * c₂) * χ₁ x y + (u₀₂ + b * c₁) * χ₂ x y|
        ≤ |u₀₁ - b * c₂| * |χ₁ x y| + |u₀₂ + b * c₁| * |χ₂ x y| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |u₀₁ - b * c₂| * 1 + |u₀₂ + b * c₁| * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hχ₁b x y) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (hχ₂b x y) (abs_nonneg _))
      _ = U b := by simp only [mul_one, hU]
  have hfmem : ∀ b, U b ≤ η / 2 → ∀ x y, f b x y ∈ Icc (0:ℝ) 1 := by
    intro b hb x y
    have hd := hδb b hb x y
    by_cases h0 : χ₁ x y ≠ 0 ∨ χ₂ x y ≠ 0
    · have hW := hsupp x y h0
      have := abs_le.mp (le_trans hd hb)
      show 0 ≤ W.toFun x y + (u₀₁ - b * c₂) * χ₁ x y + (u₀₂ + b * c₁) * χ₂ x y ∧
        W.toFun x y + (u₀₁ - b * c₂) * χ₁ x y + (u₀₂ + b * c₁) * χ₂ x y ≤ 1
      constructor <;> nlinarith [hW.1, hW.2, this.1, this.2]
    · push Not at h0
      show 0 ≤ W.toFun x y + (u₀₁ - b * c₂) * χ₁ x y + (u₀₂ + b * c₁) * χ₂ x y ∧
        W.toFun x y + (u₀₁ - b * c₂) * χ₁ x y + (u₀₂ + b * c₁) * χ₂ x y ≤ 1
      rw [h0.1, h0.2, mul_zero, mul_zero, add_zero, add_zero]
      exact W.mem_Icc x y
  have hGeq : ∀ b, U b ≤ η / 2 → ∀ x y,
      (G b).toFun x y = W.toFun x y + (u₀₁ - b * c₂) * χ₁ x y + (u₀₂ + b * c₁) * χ₂ x y :=
    fun b hb x y => Graphon.ofClamp_apply_of_mem (hfs b) (hfm b) (hfmem b hb x y)
  -- `e` is constant along the line
  have he_line : ∀ b, U b ≤ η / 2 → (G b).edgeDensity = e₀ := by
    intro b hb
    rw [edgeDensity_add_dirs W (G b) hχ₁m hχ₂m hχ₁b hχ₂b (hGeq b hb)]
    have hN' : c₁ * c₁ + c₂ * c₂ = N := by rw [hN]; ring
    have : (u₀₁ - b * c₂) * c₁ + (u₀₂ + b * c₁) * c₂ = Δe := by
      rw [hu₀₁, hu₀₂]
      field_simp
      rw [hN]; ring
    rw [← hc₁, ← hc₂]
    linarith
  -- `t` along the line
  set A₀ : ℝ := W.tDensity H - t₀ + (u₀₁ * g₁ + u₀₂ * g₂) with hA₀
  have ht_line : ∀ b, U b ≤ η / 2 →
      |(G b).tDensity H - t₀ - (A₀ + b * D)| ≤ M * U b ^ 2 := by
    intro b hb
    have hU1 : U b ≤ 1 := by linarith
    have hU0 : 0 ≤ U b := by positivity
    have hexp := Graphon.abs_tDensity_sub_linear_le H W (G b)
      (δ := fun x y => (u₀₁ - b * c₂) * χ₁ x y + (u₀₂ + b * c₁) * χ₂ x y)
      (fun x y => by rw [hGeq b hb x y]; ring)
      ((measurable_const.mul hχ₁m).add (measurable_const.mul hχ₂m)) hU0 hU1 (hδb b hb)
    have hlin := integral_dirs_gammaW H W hχ₁m hχ₂m hχ₁b hχ₂b (u₀₁ - b * c₂) (u₀₂ + b * c₁)
    rw [hlin, ← hg₁, ← hg₂] at hexp
    have : (G b).tDensity H - t₀ - (A₀ + b * D)
        = (G b).tDensity H - W.tDensity H - ((u₀₁ - b * c₂) * g₁ + (u₀₂ + b * c₁) * g₂) := by
      rw [hA₀, hD]; ring
    rw [this]
    exact hexp
  -- continuity of `t` along the line
  have hcont : Continuous fun b => (G b).tDensity H := by
    have hF : ∀ z : V → ℝ, Continuous fun b => ∏ e ∈ H.edgeFinset, (G b).gEdge z e := by
      intro z
      refine continuous_finsetProd _ fun e _ => ?_
      induction e using Sym2.ind with
      | _ a c =>
        show Continuous fun b => max 0 (min 1 (W.toFun (z a) (z c) + (u₀₁ - b * c₂) * χ₁ (z a) (z c)
          + (u₀₂ + b * c₁) * χ₂ (z a) (z c)))
        fun_prop
    have h := continuous_of_dominated (μ := Measure.pi fun _ : V => unitμ)
      (F := fun b z => ∏ e ∈ H.edgeFinset, (G b).gEdge z e) (bound := fun _ => (1:ℝ))
      (fun b => ((G b).measurable_prod_gEdge _).aestronglyMeasurable)
      (fun b => Filter.Eventually.of_forall fun z => by
        show ‖∏ e ∈ H.edgeFinset, (G b).gEdge z e‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg ((G b).prod_gEdge_mem_Icc _ _).1]
        exact ((G b).prod_gEdge_mem_Icc _ _).2)
      (integrable_const _) (Filter.Eventually.of_forall hF)
    exact h
  -- the size of `A₀`
  have hA₀b : |A₀| ≤ CA * ρ := by
    have h1 : |u₀₁ * g₁ + u₀₂ * g₂| ≤ mR * (|u₀₁| + |u₀₂|) := by
      calc |u₀₁ * g₁ + u₀₂ * g₂| ≤ |u₀₁| * |g₁| + |u₀₂| * |g₂| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ |u₀₁| * mR + |u₀₂| * mR :=
            add_le_add (mul_le_mul_of_nonneg_left hg₁b (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hg₂b (abs_nonneg _))
        _ = mR * (|u₀₁| + |u₀₂|) := by ring
    have h2 : mR * (|u₀₁| + |u₀₂|) ≤ 2 * mR ^ 2 / D₀ * |Δe| := by
      calc mR * (|u₀₁| + |u₀₂|) ≤ mR * (2 * mR / D₀ * |Δe|) := mul_le_mul_of_nonneg_left hu₀ hmR0
        _ = 2 * mR ^ 2 / D₀ * |Δe| := by ring
    have h3 : |A₀| ≤ |Δt| + |u₀₁ * g₁ + u₀₂ * g₂| := by
      have : A₀ = -Δt + (u₀₁ * g₁ + u₀₂ * g₂) := by rw [hA₀, hΔt]; ring
      rw [this]
      calc |-Δt + (u₀₁ * g₁ + u₀₂ * g₂)| ≤ |-Δt| + |u₀₁ * g₁ + u₀₂ * g₂| := abs_add_le _ _
        _ = |Δt| + |u₀₁ * g₁ + u₀₂ * g₂| := by rw [abs_neg]
    have h4 : 2 * mR ^ 2 / D₀ * |Δe| ≤ 2 * mR ^ 2 / D₀ * ρ :=
      mul_le_mul_of_nonneg_left (by rw [hρdef]; linarith [abs_nonneg Δt]) (by positivity)
    have h5 : CA * ρ = ρ + 2 * mR ^ 2 / D₀ * ρ := by rw [hCA]; ring
    have h6 : |Δt| ≤ ρ := by rw [hρdef]; linarith [abs_nonneg Δe]
    linarith
  -- the window
  set B : ℝ := 4 * CA * ρ / D₀ with hB
  have hB0 : 0 < B := by positivity
  have hρρ₀ : ρ ≤ ρ₀ := hρ
  have hCuρ : Cu * ρ ≤ η / 2 := by
    have h1 : ρ ≤ η / (2 * Cu) := le_trans hρρ₀ (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hUwin : ∀ b ∈ Icc (-B) B, U b ≤ Cu * ρ := by
    intro b hb
    have hbabs : |b| ≤ B := abs_le.mpr ⟨hb.1, hb.2⟩
    have hSc2 : Sc ≤ 2 := by rw [hSc]; linarith
    have h1 := hUb b
    have h2 : |b| * Sc ≤ B * 2 := mul_le_mul hbabs hSc2 hScpos.le hB0.le
    have h3 : 2 * mR / D₀ * |Δe| ≤ 2 * mR / D₀ * ρ :=
      mul_le_mul_of_nonneg_left (by rw [hρdef]; linarith [abs_nonneg Δt]) (by positivity)
    have h4 : Cu * ρ = 2 * mR / D₀ * ρ + B * 2 := by rw [hCu, hB]; ring
    linarith
  have hRwin : ∀ b ∈ Icc (-B) B, M * U b ^ 2 ≤ CA * ρ := by
    intro b hb
    have hU0 : 0 ≤ U b := by positivity
    have h1 : U b ^ 2 ≤ (Cu * ρ) ^ 2 := pow_le_pow_left₀ hU0 (hUwin b hb) 2
    have h2 : ρ ≤ CA / (M * Cu ^ 2) := le_trans hρρ₀ (min_le_right _ _)
    have h3 : M * Cu ^ 2 * ρ ≤ CA := by
      rw [le_div_iff₀ (by positivity)] at h2; linarith
    calc M * U b ^ 2 ≤ M * (Cu * ρ) ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (M * Cu ^ 2 * ρ) * ρ := by ring
      _ ≤ CA * ρ := mul_le_mul_of_nonneg_right h3 hρ0
  have hwin : ∀ b ∈ Icc (-B) B, U b ≤ η / 2 := fun b hb => le_trans (hUwin b hb) hCuρ
  have hBmem : B ∈ Icc (-B) B := ⟨by linarith, le_rfl⟩
  have hnBmem : -B ∈ Icc (-B) B := ⟨le_rfl, by linarith⟩
  have htB := ht_line B (hwin B hBmem)
  have htnB := ht_line (-B) (hwin (-B) hnBmem)
  have hRB := hRwin B hBmem
  have hRnB := hRwin (-B) hnBmem
  have hBD : B * D₀ = 4 * CA * ρ := by rw [hB]; field_simp
  have hCAρ : 0 < CA * ρ := by positivity
  -- the intermediate value theorem
  have hA₀l := (abs_le.mp hA₀b).1
  have hA₀u := (abs_le.mp hA₀b).2
  have htB1 := (abs_le.mp htB).1
  have htB2 := (abs_le.mp htB).2
  have htnB1 := (abs_le.mp htnB).1
  have htnB2 := (abs_le.mp htnB).2
  obtain ⟨b, hbmem, hbt⟩ : ∃ b ∈ Icc (-B) B, (G b).tDensity H = t₀ := by
    rcases le_or_gt 0 D with hDs | hDs
    · have hDD : D₀ ≤ D := by rw [abs_of_nonneg hDs] at hDabs; exact hDabs
      have h2 : B * D₀ ≤ B * D := mul_le_mul_of_nonneg_left hDD hB0.le
      have h3 : -B * D = -(B * D) := by ring
      have hup : t₀ ≤ (G B).tDensity H := by
        linarith only [htB1, hRB, hA₀l, h2, hBD, hCAρ]
      have hlo : (G (-B)).tDensity H ≤ t₀ := by
        linarith only [htnB2, hRnB, hA₀u, h2, hBD, hCAρ, h3]
      obtain ⟨b, hb, hbt⟩ := intermediate_value_Icc (by linarith only [hB0] : -B ≤ B)
        hcont.continuousOn ⟨hlo, hup⟩
      exact ⟨b, hb, hbt⟩
    · have hDD : D₀ ≤ -D := by rw [abs_of_neg hDs] at hDabs; exact hDabs
      have h2 : B * D₀ ≤ B * (-D) := mul_le_mul_of_nonneg_left hDD hB0.le
      have h3 : -B * D = B * (-D) := by ring
      have h4 : B * D = -(B * (-D)) := by ring
      have hup : t₀ ≤ (G (-B)).tDensity H := by
        linarith only [htnB1, hRnB, hA₀l, h2, hBD, hCAρ, h3]
      have hlo : (G B).tDensity H ≤ t₀ := by
        linarith only [htB2, hRB, hA₀u, h2, hBD, hCAρ, h4]
      obtain ⟨b, hb, hbt⟩ := intermediate_value_Icc' (by linarith only [hB0] : -B ≤ B)
        hcont.continuousOn ⟨hlo, hup⟩
      exact ⟨b, hb, hbt⟩
  refine ⟨u₀₁ - b * c₂, u₀₂ + b * c₁, hUwin b hbmem, G b, hGeq b (hwin b hbmem),
    he_line b (hwin b hbmem), hbt⟩

end Correction

end UpperTailOptimizers
