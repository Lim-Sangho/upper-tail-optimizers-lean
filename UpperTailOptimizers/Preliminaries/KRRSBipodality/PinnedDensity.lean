import UpperTailOptimizers.Preliminaries.KRRSBipodality.StarTerms

/-!
# Pinned homomorphism densities

For an ordered pair `(a,b)` of adjacent vertices of `H` and a graphon `W`, the **pinned density**
`t_{ab}(W;x,y)` is the density of `H` with the factor on `s(a,b)` removed and the labels of `a`
and `b` pinned to `x` and `y`.  Averaging over the two orientations and summing over the edges gives
the kernel `Γ_W(x,y)` of the first variation of `t(H,·)`:

  `d/ds t(H, W + sχ)|_{s=0} = ∑_e ∫ χ_e ∏_{e' ≠ e} W_{e'} = ∬ Γ_W χ`   (`χ` symmetric).

## Contents

* `pinLab`, `measurePreserving_pinLab` — re-randomising two coordinates at once;
* `Graphon.gEdge`, `Graphon.pinned`, `Graphon.gammaW` — the pinned densities and `Γ_W`;
* `integral_mul_prod_erase_eq` — resampling the pinned coordinates;
* `sum_integral_mul_prod_erase_eq` — the first-variation identity.
-/

namespace UpperTailOptimizers

open MeasureTheory SingularEndpoint

variable {V : Type*}

/-- Pinning two labels: `(z, (x, y)) ↦ z[a ↦ x][b ↦ y]`. -/
def pinLab [DecidableEq V] (a b : V) (p : (V → ℝ) × (ℝ × ℝ)) : V → ℝ :=
  Function.update (Function.update p.1 a p.2.1) b p.2.2

theorem pinLab_apply_left [DecidableEq V] {a b : V} (hab : a ≠ b) (p : (V → ℝ) × (ℝ × ℝ)) :
    pinLab a b p a = p.2.1 := by
  simp [pinLab, Function.update_of_ne hab]

theorem pinLab_apply_right [DecidableEq V] (a b : V) (p : (V → ℝ) × (ℝ × ℝ)) : pinLab a b p b = p.2.2 := by
  simp [pinLab]

theorem pinLab_apply_of_ne [DecidableEq V] {a b w : V} (hwa : w ≠ a) (hwb : w ≠ b) (p : (V → ℝ) × (ℝ × ℝ)) :
    pinLab a b p w = p.1 w := by
  simp [pinLab, Function.update_of_ne hwa, Function.update_of_ne hwb]

/-- **Re-randomising two coordinates preserves the product measure.** -/
theorem measurePreserving_pinLab [Fintype V] [DecidableEq V] (a b : V) :
    MeasurePreserving (pinLab a b) ((Measure.pi fun _ : V => unitμ).prod gμ)
      (Measure.pi fun _ : V => unitμ) := by
  have h1 := measurePreserving_update (ι := V) a
  have h2 := measurePreserving_update (ι := V) b
  have hassoc := MeasurePreserving.symm _
    (measurePreserving_prodAssoc (Measure.pi fun _ : V => unitμ) unitμ unitμ)
  have hmap := h1.prod (MeasurePreserving.id unitμ)
  have hcomp := (h2.comp hmap).comp hassoc
  have heq : ((fun p : (V → ℝ) × ℝ => Function.update p.1 b p.2) ∘
      Prod.map (fun p : (V → ℝ) × ℝ => Function.update p.1 a p.2) id) ∘
        (MeasurableEquiv.prodAssoc (α := V → ℝ) (β := ℝ) (γ := ℝ)).symm = pinLab a b := by
    funext p
    rfl
  rw [heq] at hcomp
  exact hcomp

theorem measurable_pinLab [Fintype V] [DecidableEq V] (a b : V) : Measurable (pinLab (V := V) a b) :=
  (measurePreserving_pinLab a b).measurable

namespace Graphon

/-- The value of `W` on an edge at a labelling. -/
def gEdge (W : Graphon) (z : V → ℝ) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun a b => W.toFun (z a) (z b), fun a b => W.symm' (z a) (z b)⟩ e

theorem gEdge_mk (W : Graphon) (z : V → ℝ) (a b : V) : W.gEdge z s(a, b) = W.toFun (z a) (z b) :=
  rfl

theorem gEdge_mem_Icc (W : Graphon) (z : V → ℝ) (e : Sym2 V) : W.gEdge z e ∈ Set.Icc (0:ℝ) 1 := by
  induction e using Sym2.ind with
  | _ a b => exact W.mem_Icc _ _

theorem measurable_gEdge (W : Graphon) (e : Sym2 V) : Measurable fun z : V → ℝ => W.gEdge z e := by
  induction e using Sym2.ind with
  | _ a b =>
    have hpair : Measurable fun z : V → ℝ => (z a, z b) :=
      (measurable_pi_apply a).prodMk (measurable_pi_apply b)
    exact W.measurable_uncurry.comp hpair

theorem measurable_prod_gEdge [Fintype V] (W : Graphon) (T : Finset (Sym2 V)) :
    Measurable fun z : V → ℝ => ∏ e ∈ T, W.gEdge z e :=
  Finset.measurable_prod _ fun e _ => W.measurable_gEdge e

theorem prod_gEdge_mem_Icc (W : Graphon) (T : Finset (Sym2 V)) (z : V → ℝ) :
    ∏ e ∈ T, W.gEdge z e ∈ Set.Icc (0:ℝ) 1 :=
  ⟨Finset.prod_nonneg fun e _ => (W.gEdge_mem_Icc z e).1,
    Finset.prod_le_one (fun e _ => (W.gEdge_mem_Icc z e).1) fun e _ => (W.gEdge_mem_Icc z e).2⟩

variable [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- **The pinned density** `t_{ab}(W; x, y)`. -/
noncomputable def pinned (W : Graphon) (a b : V) (x y : ℝ) : ℝ :=
  ∫ z : V → ℝ, ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b (z, (x, y))) e
    ∂(Measure.pi fun _ => unitμ)

theorem measurable_pinned_integrand (W : Graphon) (a b : V) :
    Measurable fun q : (V → ℝ) × (ℝ × ℝ) =>
      ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b q) e :=
  (W.measurable_prod_gEdge _).comp (measurable_pinLab a b)

theorem pinned_mem_Icc (W : Graphon) (a b : V) (x y : ℝ) :
    W.pinned H a b x y ∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨integral_nonneg fun z => (W.prod_gEdge_mem_Icc _ _).1, ?_⟩
  have hm : Measurable fun z : V → ℝ =>
      ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b (z, (x, y))) e :=
    (W.measurable_prod_gEdge _).comp
      ((measurable_pinLab a b).comp (measurable_id.prodMk measurable_const))
  have hint : Integrable (fun z : V → ℝ =>
      ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b (z, (x, y))) e)
      (Measure.pi fun _ : V => unitμ) :=
    integrable_of_abs_le hm 1 fun z => by
      rw [abs_of_nonneg (W.prod_gEdge_mem_Icc _ _).1]; exact (W.prod_gEdge_mem_Icc _ _).2
  have h := integral_mono hint (integrable_const (1:ℝ)) fun z => (W.prod_gEdge_mem_Icc
      (H.edgeFinset.erase s(a, b)) (pinLab a b (z, (x, y)))).2
  simpa [pinned] using h

theorem measurable_pinned (W : Graphon) (a b : V) :
    Measurable fun p : ℝ × ℝ => W.pinned H a b p.1 p.2 := by
  have h : StronglyMeasurable fun q : ((V → ℝ) × (ℝ × ℝ)) =>
      ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b q) e :=
    (W.measurable_pinned_integrand H a b).stronglyMeasurable
  have h' : StronglyMeasurable fun q : (ℝ × ℝ) × (V → ℝ) =>
      ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b (q.2, q.1)) e :=
    h.comp_measurable measurable_swap
  exact h'.integral_prod_right'.measurable

/-- **Resampling the pinned coordinates**: for bounded measurable `χ`,
`∫ χ(z_a, z_b) ∏_{e ≠ s(a,b)} W_e dz = ∬ χ(x,y) t_{ab}(W;x,y)`. -/
theorem integral_mul_prod_erase_eq (W : Graphon) {a b : V} (hab : a ≠ b) {χ : ℝ → ℝ → ℝ}
    (hχ : Measurable fun p : ℝ × ℝ => χ p.1 p.2) {C : ℝ} (hχb : ∀ x y, |χ x y| ≤ C) :
    ∫ z : V → ℝ, χ (z a) (z b) * ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge z e
        ∂(Measure.pi fun _ => unitμ)
      = ∫ p : ℝ × ℝ, χ p.1 p.2 * W.pinned H a b p.1 p.2 ∂gμ := by
  set π : Measure (V → ℝ) := Measure.pi fun _ : V => unitμ with hπ
  have hmp := measurePreserving_pinLab (V := V) a b
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hχb 0 0)
  have hFm : Measurable fun z : V → ℝ =>
      χ (z a) (z b) * ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge z e :=
    (hχ.comp ((measurable_pi_apply a).prodMk (measurable_pi_apply b))).mul
      (W.measurable_prod_gEdge _)
  have hstep1 : ∫ z : V → ℝ, χ (z a) (z b) * ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge z e ∂π
      = ∫ q : (V → ℝ) × (ℝ × ℝ), χ (pinLab a b q a) (pinLab a b q b)
          * ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b q) e ∂(π.prod gμ) := by
    have h := integral_map (μ := π.prod gμ) hmp.measurable.aemeasurable
      (hFm.aestronglyMeasurable (μ := Measure.map (pinLab a b) (π.prod gμ)))
    rw [hmp.map_eq] at h
    exact h
  have hpt : ∀ q : (V → ℝ) × (ℝ × ℝ), χ (pinLab a b q a) (pinLab a b q b)
      * ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b q) e
      = χ q.2.1 q.2.2 * ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b q) e := by
    intro q
    rw [pinLab_apply_left hab, pinLab_apply_right]
  rw [hstep1, integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hGm : Measurable fun q : (V → ℝ) × (ℝ × ℝ) =>
      χ q.2.1 q.2.2 * ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b q) e :=
    (hχ.comp measurable_snd).mul (W.measurable_pinned_integrand H a b)
  have hGint : Integrable (fun q : (V → ℝ) × (ℝ × ℝ) =>
      χ q.2.1 q.2.2 * ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b q) e) (π.prod gμ) :=
    integrable_of_abs_le hGm C fun q => by
      rw [abs_mul, abs_of_nonneg (W.prod_gEdge_mem_Icc _ _).1]
      calc |χ q.2.1 q.2.2| * ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b q) e
          ≤ C * 1 := mul_le_mul (hχb _ _) (W.prod_gEdge_mem_Icc _ _).2
            (W.prod_gEdge_mem_Icc _ _).1 hC
        _ = C := mul_one C
  rw [integral_prod_symm _ hGint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show ∫ z, χ p.1 p.2 * ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b (z, p)) e ∂π
    = χ p.1 p.2 * W.pinned H a b p.1 p.2
  rw [integral_const_mul]
  rfl

/-- Pinning in the other order swaps the pinned values. -/
theorem pinned_swap (W : Graphon) {a b : V} (hab : a ≠ b) (x y : ℝ) :
    W.pinned H a b y x = W.pinned H b a x y := by
  unfold pinned
  have hset : H.edgeFinset.erase s(a, b) = H.edgeFinset.erase s(b, a) := by rw [Sym2.eq_swap]
  rw [hset]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have hlab : pinLab a b (z, (y, x)) = pinLab b a (z, (x, y)) := by
    show Function.update (Function.update z a y) b x = Function.update (Function.update z b x) a y
    exact (Function.update_comm hab.symm x y z).symm
  simp only [hlab]

/-- The orientation-averaged pinned density on an edge. -/
noncomputable def pinnedEdge (W : Graphon) (x y : ℝ) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun a b => (W.pinned H a b x y + W.pinned H b a x y) / 2,
    fun a b => by simp only [add_comm]⟩ e

/-- **The kernel `Γ_W` of the first variation of `t(H,·)`.** -/
noncomputable def gammaW (W : Graphon) (x y : ℝ) : ℝ := ∑ e ∈ H.edgeFinset, W.pinnedEdge H x y e

theorem pinnedEdge_mem_Icc (W : Graphon) (x y : ℝ) (e : Sym2 V) :
    W.pinnedEdge H x y e ∈ Set.Icc (0:ℝ) 1 := by
  induction e using Sym2.ind with
  | _ a b =>
    have h1 := W.pinned_mem_Icc H a b x y
    have h2 := W.pinned_mem_Icc H b a x y
    exact ⟨by show 0 ≤ (W.pinned H a b x y + W.pinned H b a x y) / 2; linarith [h1.1, h2.1],
      by show (W.pinned H a b x y + W.pinned H b a x y) / 2 ≤ 1; linarith [h1.2, h2.2]⟩

theorem measurable_pinnedEdge (W : Graphon) (e : Sym2 V) :
    Measurable fun p : ℝ × ℝ => W.pinnedEdge H p.1 p.2 e := by
  induction e using Sym2.ind with
  | _ a b => exact ((W.measurable_pinned H a b).add (W.measurable_pinned H b a)).div_const 2

theorem gammaW_nonneg (W : Graphon) (x y : ℝ) : 0 ≤ W.gammaW H x y :=
  Finset.sum_nonneg fun e _ => (W.pinnedEdge_mem_Icc H x y e).1

theorem gammaW_le (W : Graphon) (x y : ℝ) : W.gammaW H x y ≤ H.edgeFinset.card := by
  calc W.gammaW H x y ≤ ∑ _e ∈ H.edgeFinset, (1:ℝ) :=
        Finset.sum_le_sum fun e _ => (W.pinnedEdge_mem_Icc H x y e).2
    _ = H.edgeFinset.card := by simp

theorem measurable_gammaW (W : Graphon) : Measurable fun p : ℝ × ℝ => W.gammaW H p.1 p.2 :=
  Finset.measurable_sum _ fun e _ => W.measurable_pinnedEdge H e

theorem pinnedEdge_symm (W : Graphon) (x y : ℝ) {e : Sym2 V} (he : e ∈ H.edgeFinset) :
    W.pinnedEdge H x y e = W.pinnedEdge H y x e := by
  revert he
  induction e using Sym2.ind with
  | _ a b =>
    intro he
    have hab : a ≠ b := H.ne_of_adj (SimpleGraph.mem_edgeFinset.mp he)
    show (W.pinned H a b x y + W.pinned H b a x y) / 2 = (W.pinned H a b y x + W.pinned H b a y x) / 2
    rw [W.pinned_swap H hab y x, W.pinned_swap H hab.symm y x]
    ring

theorem gammaW_symm (W : Graphon) (x y : ℝ) : W.gammaW H x y = W.gammaW H y x :=
  Finset.sum_congr rfl fun _ he => W.pinnedEdge_symm H x y he

/-- **The first-variation identity**: for a bounded measurable symmetric `χ`,
`∑_e ∫ χ_e ∏_{e' ≠ e} W_{e'} = ∬ χ Γ_W`. -/
theorem sum_integral_mul_prod_erase_eq (W : Graphon) {χ : ℝ → ℝ → ℝ}
    (hχ : Measurable fun p : ℝ × ℝ => χ p.1 p.2) {C : ℝ} (hχb : ∀ x y, |χ x y| ≤ C)
    (hχs : ∀ x y, χ x y = χ y x) :
    ∑ e ∈ H.edgeFinset, ∫ z : V → ℝ,
        Sym2.lift ⟨fun a b => χ (z a) (z b), fun a b => hχs (z a) (z b)⟩ e
          * ∏ e' ∈ H.edgeFinset.erase e, W.gEdge z e' ∂(Measure.pi fun _ => unitμ)
      = ∫ p : ℝ × ℝ, χ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hχb 0 0)
  have hint : ∀ e ∈ H.edgeFinset,
      Integrable (fun p : ℝ × ℝ => χ p.1 p.2 * W.pinnedEdge H p.1 p.2 e) gμ := by
    intro e _
    refine integrable_of_abs_le (hχ.mul (W.measurable_pinnedEdge H e)) C fun p => ?_
    rw [abs_mul, abs_of_nonneg (W.pinnedEdge_mem_Icc H _ _ e).1]
    calc |χ p.1 p.2| * W.pinnedEdge H p.1 p.2 e ≤ C * 1 :=
          mul_le_mul (hχb _ _) (W.pinnedEdge_mem_Icc H _ _ e).2 (W.pinnedEdge_mem_Icc H _ _ e).1 hC
      _ = C := mul_one C
  have hRHS : ∫ p : ℝ × ℝ, χ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ
      = ∑ e ∈ H.edgeFinset, ∫ p : ℝ × ℝ, χ p.1 p.2 * W.pinnedEdge H p.1 p.2 e ∂gμ := by
    rw [← integral_finsetSum _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [gammaW, Finset.mul_sum]
  rw [hRHS]
  refine Finset.sum_congr rfl fun e he => ?_
  revert he
  induction e using Sym2.ind with
  | _ a b =>
    intro he
    have hab : a ≠ b := H.ne_of_adj (SimpleGraph.mem_edgeFinset.mp he)
    have h1 := W.integral_mul_prod_erase_eq H hab hχ hχb
    have h2 := W.integral_mul_prod_erase_eq H hab.symm hχ hχb
    have hset : H.edgeFinset.erase s(b, a) = H.edgeFinset.erase s(a, b) := by rw [Sym2.eq_swap]
    rw [hset] at h2
    have h2' : ∫ z : V → ℝ, χ (z a) (z b) * ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge z e
          ∂(Measure.pi fun _ => unitμ)
        = ∫ p : ℝ × ℝ, χ p.1 p.2 * W.pinned H b a p.1 p.2 ∂gμ := by
      rw [← h2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hχs (z a) (z b)]
    show ∫ z : V → ℝ, χ (z a) (z b) * ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge z e
        ∂(Measure.pi fun _ => unitμ)
      = ∫ p : ℝ × ℝ, χ p.1 p.2 * ((W.pinned H a b p.1 p.2 + W.pinned H b a p.1 p.2) / 2) ∂gμ
    have hi1 : Integrable (fun p : ℝ × ℝ => χ p.1 p.2 * W.pinned H a b p.1 p.2) gμ :=
      integrable_of_abs_le (hχ.mul (W.measurable_pinned H a b)) C fun p => by
        rw [abs_mul, abs_of_nonneg (W.pinned_mem_Icc H a b _ _).1]
        calc |χ p.1 p.2| * W.pinned H a b p.1 p.2 ≤ C * 1 :=
              mul_le_mul (hχb _ _) (W.pinned_mem_Icc H a b _ _).2 (W.pinned_mem_Icc H a b _ _).1 hC
          _ = C := mul_one C
    have hi2 : Integrable (fun p : ℝ × ℝ => χ p.1 p.2 * W.pinned H b a p.1 p.2) gμ :=
      integrable_of_abs_le (hχ.mul (W.measurable_pinned H b a)) C fun p => by
        rw [abs_mul, abs_of_nonneg (W.pinned_mem_Icc H b a _ _).1]
        calc |χ p.1 p.2| * W.pinned H b a p.1 p.2 ≤ C * 1 :=
              mul_le_mul (hχb _ _) (W.pinned_mem_Icc H b a _ _).2 (W.pinned_mem_Icc H b a _ _).1 hC
          _ = C := mul_one C
    have hsplit : ∫ p : ℝ × ℝ, χ p.1 p.2 * ((W.pinned H a b p.1 p.2 + W.pinned H b a p.1 p.2) / 2) ∂gμ
        = (∫ p : ℝ × ℝ, χ p.1 p.2 * W.pinned H a b p.1 p.2 ∂gμ
          + ∫ p : ℝ × ℝ, χ p.1 p.2 * W.pinned H b a p.1 p.2 ∂gμ) / 2 := by
      rw [← integral_add hi1 hi2, ← integral_div]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only
      ring
    rw [hsplit, ← h1, ← h2']
    ring

end Graphon

/-! ### Telescoping -/

/-- `|∏ f - ∏ g| ≤ ∑ |f - g|` for factors in `[0,1]`. -/
theorem abs_prod_sub_prod_le_sum {ι : Type*} [DecidableEq ι] (T : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ T, f i ∈ Set.Icc (0:ℝ) 1) (hg : ∀ i ∈ T, g i ∈ Set.Icc (0:ℝ) 1) :
    |∏ i ∈ T, f i - ∏ i ∈ T, g i| ≤ ∑ i ∈ T, |f i - g i| := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have hfT : ∀ i ∈ T, f i ∈ Set.Icc (0:ℝ) 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgT : ∀ i ∈ T, g i ∈ Set.Icc (0:ℝ) 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a T)
    have hga := hg a (Finset.mem_insert_self a T)
    have hP : ∏ i ∈ T, f i ∈ Set.Icc (0:ℝ) 1 :=
      ⟨Finset.prod_nonneg fun i hi => (hfT i hi).1,
        Finset.prod_le_one (fun i hi => (hfT i hi).1) fun i hi => (hfT i hi).2⟩
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hsplit : f a * ∏ i ∈ T, f i - g a * ∏ i ∈ T, g i
        = (f a - g a) * ∏ i ∈ T, f i + g a * (∏ i ∈ T, f i - ∏ i ∈ T, g i) := by ring
    rw [hsplit]
    calc |(f a - g a) * ∏ i ∈ T, f i + g a * (∏ i ∈ T, f i - ∏ i ∈ T, g i)|
        ≤ |(f a - g a) * ∏ i ∈ T, f i| + |g a * (∏ i ∈ T, f i - ∏ i ∈ T, g i)| := abs_add_le _ _
      _ = |f a - g a| * ∏ i ∈ T, f i + g a * |∏ i ∈ T, f i - ∏ i ∈ T, g i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hP.1, abs_of_nonneg hga.1]
      _ ≤ |f a - g a| * 1 + 1 * ∑ i ∈ T, |f i - g i| :=
          add_le_add (mul_le_mul_of_nonneg_left hP.2 (abs_nonneg _))
            (mul_le_mul hga.2 (ih hfT hgT) (abs_nonneg _) zero_le_one)
      _ = |f a - g a| + ∑ i ∈ T, |f i - g i| := by ring

namespace Graphon

variable [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- **Pinned densities are Lipschitz in the sup norm.** -/
theorem abs_pinned_sub_le (W W₂ : Graphon) {r : ℝ} (hr : ∀ x y, |W₂.toFun x y - W.toFun x y| ≤ r)
    (a b : V) (x y : ℝ) :
    |W₂.pinned H a b x y - W.pinned H a b x y| ≤ H.edgeFinset.card * r := by
  have hr0 : 0 ≤ r := le_trans (abs_nonneg _) (hr 0 0)
  unfold pinned
  set π : Measure (V → ℝ) := Measure.pi fun _ : V => unitμ with hπ
  have hm : ∀ U : Graphon, Measurable fun z : V → ℝ =>
      ∏ e ∈ H.edgeFinset.erase s(a, b), U.gEdge (pinLab a b (z, (x, y))) e := fun U =>
    (U.measurable_prod_gEdge _).comp
      ((measurable_pinLab a b).comp (measurable_id.prodMk measurable_const))
  have hint : ∀ U : Graphon, Integrable (fun z : V → ℝ =>
      ∏ e ∈ H.edgeFinset.erase s(a, b), U.gEdge (pinLab a b (z, (x, y))) e) π := fun U =>
    integrable_of_abs_le (hm U) 1 fun z => by
      rw [abs_of_nonneg (U.prod_gEdge_mem_Icc _ _).1]; exact (U.prod_gEdge_mem_Icc _ _).2
  rw [← integral_sub (hint W₂) (hint W)]
  have hpt : ∀ z : V → ℝ, |∏ e ∈ H.edgeFinset.erase s(a, b), W₂.gEdge (pinLab a b (z, (x, y))) e
      - ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b (z, (x, y))) e|
      ≤ H.edgeFinset.card * r := by
    intro z
    refine le_trans (abs_prod_sub_prod_le_sum _ _ _ (fun e _ => W₂.gEdge_mem_Icc _ e)
      (fun e _ => W.gEdge_mem_Icc _ e)) ?_
    calc ∑ e ∈ H.edgeFinset.erase s(a, b),
          |W₂.gEdge (pinLab a b (z, (x, y))) e - W.gEdge (pinLab a b (z, (x, y))) e|
        ≤ ∑ _e ∈ H.edgeFinset.erase s(a, b), r := Finset.sum_le_sum fun e _ => by
          induction e using Sym2.ind with
          | _ p q => exact hr _ _
      _ = (H.edgeFinset.erase s(a, b)).card * r := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ H.edgeFinset.card * r := by
          apply mul_le_mul_of_nonneg_right _ hr0
          exact_mod_cast Finset.card_erase_le
  calc |∫ z, (∏ e ∈ H.edgeFinset.erase s(a, b), W₂.gEdge (pinLab a b (z, (x, y))) e
        - ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b (z, (x, y))) e) ∂π|
      ≤ ∫ z, |∏ e ∈ H.edgeFinset.erase s(a, b), W₂.gEdge (pinLab a b (z, (x, y))) e
        - ∏ e ∈ H.edgeFinset.erase s(a, b), W.gEdge (pinLab a b (z, (x, y))) e| ∂π :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _z, (H.edgeFinset.card : ℝ) * r ∂π :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall hpt)
    _ = H.edgeFinset.card * r := by simp

/-- **`Γ_W` is Lipschitz in the sup norm.** -/
theorem abs_gammaW_sub_le (W W₂ : Graphon) {r : ℝ} (hr : ∀ x y, |W₂.toFun x y - W.toFun x y| ≤ r)
    (x y : ℝ) :
    |W₂.gammaW H x y - W.gammaW H x y| ≤ H.edgeFinset.card * (H.edgeFinset.card * r) := by
  unfold gammaW
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ e ∈ H.edgeFinset, |W₂.pinnedEdge H x y e - W.pinnedEdge H x y e|
      ≤ ∑ _e ∈ H.edgeFinset, (H.edgeFinset.card * r : ℝ) := Finset.sum_le_sum fun e _ => by
        induction e using Sym2.ind with
        | _ a b =>
          show |(W₂.pinned H a b x y + W₂.pinned H b a x y) / 2
            - (W.pinned H a b x y + W.pinned H b a x y) / 2| ≤ H.edgeFinset.card * r
          have h1 := W.abs_pinned_sub_le H W₂ hr a b x y
          have h2 := W.abs_pinned_sub_le H W₂ hr b a x y
          have : (W₂.pinned H a b x y + W₂.pinned H b a x y) / 2
              - (W.pinned H a b x y + W.pinned H b a x y) / 2
              = ((W₂.pinned H a b x y - W.pinned H a b x y)
                + (W₂.pinned H b a x y - W.pinned H b a x y)) / 2 := by ring
          rw [this, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          have := abs_add_le (W₂.pinned H a b x y - W.pinned H a b x y)
            (W₂.pinned H b a x y - W.pinned H b a x y)
          linarith
    _ = H.edgeFinset.card * (H.edgeFinset.card * r) := by rw [Finset.sum_const, nsmul_eq_mul]

end Graphon

end UpperTailOptimizers
