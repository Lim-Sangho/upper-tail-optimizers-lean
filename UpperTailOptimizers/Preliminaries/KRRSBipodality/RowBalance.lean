import UpperTailOptimizers.Preliminaries.KRRSBipodality.RowReplace

/-!
# Row balance

For a maximizer `W` with qualifying directions, replacing the rows and columns indexed by a set
`A` of measure `h` by those of an arbitrary point `x₀`, and correcting the two constraints with
the qualifying directions cut off `A`, gives the **row balance**

  `h Φ(x₀) - ∫_A Φ ≤ C h²`,   `Φ = 2σ_W - 2α d_W - β ∑_i T_i`

(draft `kb:lem:row`).  Letting `A` shrink inside a sublevel set of `Φ` shows that `Φ(x₀)` is at
most the essential infimum of `Φ`, for *every* `x₀`.

## Contents

* `Graphon.abs_gammaW_rowReplace_sub_le` — `Γ` barely moves off `A`;
* `cutDir` — a direction cut off `A`;
* `Graphon.balFun` — the row functional `Φ`;
* `QualDirs.row_balance`, `QualDirs.ae_balFun_ge`.
-/

set_option linter.unusedSectionVars false

namespace UpperTailOptimizers

open MeasureTheory Set

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-! ### Rooted densities as functions of the root label -/

section Rooted

variable {κ : ℝ → ℝ → ℝ} (hs : ∀ x y, κ x y = κ y x)

theorem measurable_rootedK (hm : Measurable fun p : ℝ × ℝ => κ p.1 p.2) (i : V) :
    Measurable fun u => rootedK H hs i u := by
  have hF : Measurable fun q : ℝ × (V → ℝ) => kProd H κ hs (Function.update q.2 i q.1) :=
    (measurable_kProd H hs hm).comp (measurable_update'.comp measurable_swap)
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

theorem abs_rootedK_le (hb : ∀ x y, |κ x y| ≤ 1) (i : V) (u : ℝ) : |rootedK H hs i u| ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := Measure.pi fun _ : V => unitμ)
    (f := fun z : V → ℝ => kProd H κ hs (Function.update z i u)) (C := 1)
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact abs_kProd_le H hs hb _)
  simpa [Real.norm_eq_abs, measureReal_def, rootedK] using h

end Rooted

/-- `|h f(x₀) - ∫_A f| ≤ 2h` for `|f| ≤ 1`. -/
theorem abs_mul_sub_setIntegral_le {f : ℝ → ℝ} (hfm : Measurable f) (hfb : ∀ u, |f u| ≤ 1)
    (A : Set ℝ) (x₀ : ℝ) :
    |(unitμ A).toReal * f x₀ - ∫ s in A, f s ∂unitμ| ≤ 2 * (unitμ A).toReal := by
  have h0 : 0 ≤ (unitμ A).toReal := ENNReal.toReal_nonneg
  have h1 : |(unitμ A).toReal * f x₀| ≤ (unitμ A).toReal := by
    rw [abs_mul, abs_of_nonneg h0]
    calc (unitμ A).toReal * |f x₀| ≤ (unitμ A).toReal * 1 := mul_le_mul_of_nonneg_left (hfb x₀) h0
      _ = (unitμ A).toReal := mul_one _
  have h2 : |∫ s in A, f s ∂unitμ| ≤ (unitμ A).toReal := by
    have := norm_integral_le_of_norm_le_const (μ := unitμ.restrict A) (f := f) (C := 1)
      (Filter.Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact hfb s)
    have hreal : (unitμ.restrict A).real univ = (unitμ A).toReal := by
      simp only [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    rw [Real.norm_eq_abs, hreal] at this
    linarith
  have _ := hfm
  calc _ ≤ |(unitμ A).toReal * f x₀| + |∫ s in A, f s ∂unitμ| := abs_sub _ _
    _ ≤ (unitμ A).toReal + (unitμ A).toReal := add_le_add h1 h2
    _ = 2 * (unitμ A).toReal := by ring

namespace Graphon

theorem measurable_rowEnt (W : Graphon) : Measurable W.rowEnt :=
  W.measurable_S0W.stronglyMeasurable.integral_prod_right'.measurable

theorem abs_rowEnt_le (W : Graphon) (u : ℝ) : |W.rowEnt u| ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := unitμ) (f := fun t => S0 (W.toFun u t)) (C := 1)
    (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact W.abs_S0W_le u t)
  simpa [Real.norm_eq_abs, measureReal_def, rowEnt] using h

theorem abs_degFun_le (W : Graphon) (u : ℝ) : |W.degFun u| ≤ 1 := by
  rw [abs_of_nonneg (W.degFun_mem_Icc u).1]; exact (W.degFun_mem_Icc u).2

/-- **The row functional** `Φ(u) = 2σ_W(u) - 2α d_W(u) - β ∑_i T_i(u)`. -/
noncomputable def balFun (W : Graphon) (α β u : ℝ) : ℝ :=
  2 * W.rowEnt u - 2 * α * W.degFun u - β * ∑ i, rootedK H W.symm' i u

theorem measurable_balFun (W : Graphon) (α β : ℝ) : Measurable (W.balFun H α β) :=
  ((measurable_const.mul W.measurable_rowEnt).sub (measurable_const.mul W.measurable_degFun)).sub
    (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      measurable_rootedK H W.symm' W.measurable_uncurry i))

theorem integrable_restrict_of_abs_le {f : ℝ → ℝ} (hfm : Measurable f) {C : ℝ}
    (hfb : ∀ u, |f u| ≤ C) (A : Set ℝ) : Integrable f (unitμ.restrict A) :=
  integrable_of_abs_le hfm C hfb

theorem setIntegral_balFun (W : Graphon) (α β : ℝ) (A : Set ℝ) :
    ∫ s in A, W.balFun H α β s ∂unitμ
      = 2 * ∫ s in A, W.rowEnt s ∂unitμ - 2 * α * ∫ s in A, W.degFun s ∂unitμ
        - β * ∑ i, ∫ s in A, rootedK H W.symm' i s ∂unitμ := by
  have hσ := integrable_restrict_of_abs_le W.measurable_rowEnt W.abs_rowEnt_le A
  have hd := integrable_restrict_of_abs_le W.measurable_degFun W.abs_degFun_le A
  have hT : ∀ i ∈ (Finset.univ : Finset V), Integrable (fun s => rootedK H W.symm' i s)
      (unitμ.restrict A) := fun i _ =>
    integrable_restrict_of_abs_le (measurable_rootedK H W.symm' W.measurable_uncurry i)
      (abs_rootedK_le H W.symm' W.abs_toFun_le i) A
  unfold balFun
  rw [integral_sub (f := fun s => 2 * W.rowEnt s - 2 * α * W.degFun s)
      (g := fun s => β * ∑ i, rootedK H W.symm' i s)
      ((hσ.const_mul 2).sub (hd.const_mul (2 * α))) ((integrable_finsetSum _ hT).const_mul β),
    integral_sub (f := fun s => 2 * W.rowEnt s) (g := fun s => 2 * α * W.degFun s)
      (hσ.const_mul 2) (hd.const_mul (2 * α)),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_finsetSum _ hT]

/-- **The first-order change of `(s, e, t)` under row replacement.** -/
theorem abs_rowReplace_combo_le (W : Graphon) {A : Set ℝ} (hA : MeasurableSet A) (x₀ α β : ℝ) :
    |((W.rowReplace hA x₀).entropy - W.entropy)
        - α * ((W.rowReplace hA x₀).edgeDensity - W.edgeDensity)
        - β * ((W.rowReplace hA x₀).tDensity H - W.tDensity H)
        - ((unitμ A).toReal * W.balFun H α β x₀ - ∫ s in A, W.balFun H α β s ∂unitμ)|
      ≤ (8 + 8 * |α| + 2 * |β| * (Fintype.card V : ℝ) ^ 2) * (unitμ A).toReal ^ 2 := by
  have hs := W.abs_entropy_rowReplace_sub_le hA x₀
  have he := W.abs_edgeDensity_rowReplace_sub_le hA x₀
  have ht := W.abs_tDensity_rowReplace_sub_le H hA x₀
  rw [W.setIntegral_balFun H α β A]
  set h : ℝ := (unitμ A).toReal
  set Es := (W.rowReplace hA x₀).entropy - W.entropy
  set Ee := (W.rowReplace hA x₀).edgeDensity - W.edgeDensity
  set Et := (W.rowReplace hA x₀).tDensity H - W.tDensity H
  set Ls := h * W.rowEnt x₀ - ∫ s in A, W.rowEnt s ∂unitμ
  set Le := h * W.degFun x₀ - ∫ s in A, W.degFun s ∂unitμ
  set Lt := ∑ i, (h * rootedK H W.symm' i x₀ - ∫ s in A, rootedK H W.symm' i s ∂unitμ)
  have hLt : Lt = h * ∑ i, rootedK H W.symm' i x₀ - ∑ i, ∫ s in A, rootedK H W.symm' i s ∂unitμ := by
    simp only [Lt, Finset.sum_sub_distrib, Finset.mul_sum]
  have e : Es - α * Ee - β * Et
      - (h * (2 * W.rowEnt x₀ - 2 * α * W.degFun x₀ - β * ∑ i, rootedK H W.symm' i x₀)
        - (2 * ∫ s in A, W.rowEnt s ∂unitμ - 2 * α * ∫ s in A, W.degFun s ∂unitμ
          - β * ∑ i, ∫ s in A, rootedK H W.symm' i s ∂unitμ))
      = (Es - 2 * Ls) - α * (Ee - 2 * Le) - β * (Et - Lt) := by
    rw [hLt]; simp only [Ls, Le]; ring
  unfold balFun
  rw [e]
  have h2 : 0 ≤ h ^ 2 := sq_nonneg h
  calc |(Es - 2 * Ls) - α * (Ee - 2 * Le) - β * (Et - Lt)|
      ≤ |Es - 2 * Ls| + |α| * |Ee - 2 * Le| + |β| * |Et - Lt| := by
        rw [← abs_mul, ← abs_mul]
        calc _ ≤ |(Es - 2 * Ls) - α * (Ee - 2 * Le)| + |β * (Et - Lt)| := abs_sub _ _
          _ ≤ |Es - 2 * Ls| + |α * (Ee - 2 * Le)| + |β * (Et - Lt)| := by
              linarith [abs_sub (Es - 2 * Ls) (α * (Ee - 2 * Le))]
    _ ≤ 8 * h ^ 2 + |α| * (8 * h ^ 2) + |β| * (2 * (Fintype.card V : ℝ) ^ 2 * h ^ 2) := by
        gcongr
    _ = (8 + 8 * |α| + 2 * |β| * (Fintype.card V : ℝ) ^ 2) * h ^ 2 := by ring

/-! ### `Γ` off the replaced set -/

theorem gEdge_rowReplace (W : Graphon) {A : Set ℝ} (hA : MeasurableSet A) (x₀ : ℝ) (z : V → ℝ)
    (e : Sym2 V) : (W.rowReplace hA x₀).gEdge z e = W.gEdge (fun j => rowRep A x₀ (z j)) e := by
  induction e using Sym2.ind with
  | _ p q => rfl

theorem abs_pinned_rowReplace_sub_le (W : Graphon) {A : Set ℝ} (hA : MeasurableSet A) (x₀ : ℝ)
    (a b : V) {x y : ℝ} (hx : x ∉ A) (hy : y ∉ A) :
    |(W.rowReplace hA x₀).pinned H a b x y - W.pinned H a b x y|
      ≤ (Fintype.card V : ℝ) * (unitμ A).toReal := by
  classical
  set π : Measure (V → ℝ) := Measure.pi fun _ : V => unitμ with hπ
  set T := H.edgeFinset.erase s(a, b) with hT
  set g : (V → ℝ) → ℝ := fun z => ∏ e ∈ T, W.gEdge (pinLab a b (z, (x, y))) e with hg
  have hgm : Measurable g := (W.measurable_prod_gEdge T).comp
    ((measurable_pinLab a b).comp (measurable_id.prodMk measurable_const))
  have hgmem : ∀ z, g z ∈ Icc (0:ℝ) 1 := fun z => W.prod_gEdge_mem_Icc _ _
  have hlab : ∀ z : V → ℝ, (fun j => rowRep A x₀ (pinLab a b (z, (x, y)) j))
      = pinLab a b ((fun j => rowRep A x₀ (z j)), (x, y)) := by
    intro z; funext j
    by_cases hjb : j = b
    · rw [hjb, pinLab_apply_right, pinLab_apply_right, rowRep_of_notMem hy]
    · by_cases hja : j = a
      · have hab : a ≠ b := hja ▸ hjb
        rw [hja, pinLab_apply_left hab, pinLab_apply_left hab, rowRep_of_notMem hx]
      · rw [pinLab_apply_of_ne hja hjb, pinLab_apply_of_ne hja hjb]
  have hA1 : (W.rowReplace hA x₀).pinned H a b x y = ∫ z, g (fun j => rowRep A x₀ (z j)) ∂π := by
    unfold pinned
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [gEdge_rowReplace, hlab]
    rfl
  have hA2 : W.pinned H a b x y = ∫ z, g z ∂π := rfl
  have hrepm : Measurable fun z : V → ℝ => (fun j => rowRep A x₀ (z j)) :=
    measurable_pi_lambda _ fun j => (measurable_rowRep hA x₀).comp (measurable_pi_apply j)
  have hint1 : Integrable (fun z => g (fun j => rowRep A x₀ (z j))) π :=
    integrable_of_abs_le (hgm.comp hrepm) 1 fun z => by
      rw [abs_of_nonneg (hgmem _).1]; exact (hgmem _).2
  have hint2 : Integrable g π :=
    integrable_of_abs_le hgm 1 fun z => by rw [abs_of_nonneg (hgmem _).1]; exact (hgmem _).2
  set cnt : (V → ℝ) → ℝ := fun z => ∑ j, A.indicator (fun _ => (1:ℝ)) (z j) with hcnt
  have hind : ∀ j, Integrable (fun z : V → ℝ => A.indicator (fun _ => (1:ℝ)) (z j)) π := fun j =>
    integrable_of_abs_le ((measurable_const.indicator hA).comp (measurable_pi_apply j)) 1 fun z => by
      by_cases h' : z j ∈ A
      · rw [Set.indicator_of_mem h']; simp
      · rw [Set.indicator_of_notMem h']; simp
  have hcntint : ∫ z, cnt z ∂π = (Fintype.card V : ℝ) * (unitμ A).toReal := by
    rw [integral_finsetSum _ fun j _ => hind j]
    have hj : ∀ j ∈ (Finset.univ : Finset V),
        ∫ z : V → ℝ, A.indicator (fun _ => (1:ℝ)) (z j) ∂π = (unitμ A).toReal := by
      intro j _
      rw [integral_pi_eval_comp j (measurable_const.indicator hA)]
      exact integral_indicator_one hA
    rw [Finset.sum_congr rfl hj, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hpt : ∀ z, |g (fun j => rowRep A x₀ (z j)) - g z| ≤ cnt z := by
    intro z
    by_cases hall : ∀ j, z j ∉ A
    · have : (fun j => rowRep A x₀ (z j)) = z := by
        funext j; exact rowRep_of_notMem (hall j)
      rw [this, sub_self, abs_zero]
      exact Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      have h1 : 1 ≤ cnt z := by
        have := Finset.single_le_sum (f := fun j => A.indicator (fun _ => (1:ℝ)) (z j))
          (fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Finset.mem_univ j)
        simp only [Set.indicator_of_mem hj] at this
        exact this
      obtain ⟨h3, h4⟩ := hgmem (fun j => rowRep A x₀ (z j))
      obtain ⟨h5, h6⟩ := hgmem z
      rw [abs_le]; constructor <;> linarith
  rw [hA1, hA2, ← integral_sub hint1 hint2]
  calc |∫ z, (g (fun j => rowRep A x₀ (z j)) - g z) ∂π|
      ≤ ∫ z, |g (fun j => rowRep A x₀ (z j)) - g z| ∂π := abs_integral_le_integral_abs
    _ ≤ ∫ z, cnt z ∂π := integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
        (integrable_finsetSum _ fun j _ => hind j) (Filter.Eventually.of_forall hpt)
    _ = _ := hcntint

/-- **`Γ` off the replaced set**: `|Γ_{W^A}(x,y) - Γ_W(x,y)| ≤ m v |A|` for `x, y ∉ A`. -/
theorem abs_gammaW_rowReplace_sub_le (W : Graphon) {A : Set ℝ} (hA : MeasurableSet A) (x₀ : ℝ)
    {x y : ℝ} (hx : x ∉ A) (hy : y ∉ A) :
    |(W.rowReplace hA x₀).gammaW H x y - W.gammaW H x y|
      ≤ H.edgeFinset.card * ((Fintype.card V : ℝ) * (unitμ A).toReal) := by
  classical
  set B : ℝ := (Fintype.card V : ℝ) * (unitμ A).toReal with hB
  have hedge : ∀ e : Sym2 V, |(W.rowReplace hA x₀).pinnedEdge H x y e - W.pinnedEdge H x y e| ≤ B := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      have h1 := W.abs_pinned_rowReplace_sub_le H hA x₀ a b hx hy
      have h2 := W.abs_pinned_rowReplace_sub_le H hA x₀ b a hx hy
      show |((W.rowReplace hA x₀).pinned H a b x y + (W.rowReplace hA x₀).pinned H b a x y) / 2
        - (W.pinned H a b x y + W.pinned H b a x y) / 2| ≤ B
      have e : ((W.rowReplace hA x₀).pinned H a b x y + (W.rowReplace hA x₀).pinned H b a x y) / 2
          - (W.pinned H a b x y + W.pinned H b a x y) / 2
          = (((W.rowReplace hA x₀).pinned H a b x y - W.pinned H a b x y)
            + ((W.rowReplace hA x₀).pinned H b a x y - W.pinned H b a x y)) / 2 := by ring
      rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have := abs_add_le ((W.rowReplace hA x₀).pinned H a b x y - W.pinned H a b x y)
        ((W.rowReplace hA x₀).pinned H b a x y - W.pinned H b a x y)
      linarith
  unfold gammaW
  rw [← Finset.sum_sub_distrib]
  calc |∑ e ∈ H.edgeFinset, ((W.rowReplace hA x₀).pinnedEdge H x y e - W.pinnedEdge H x y e)|
      ≤ ∑ e ∈ H.edgeFinset, |(W.rowReplace hA x₀).pinnedEdge H x y e - W.pinnedEdge H x y e| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ H.edgeFinset, B := Finset.sum_le_sum fun e _ => hedge e
    _ = H.edgeFinset.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

end Graphon

/-! ### Directions cut off a set -/

/-- `χ` cut off `A × ℝ ∪ ℝ × A`. -/
noncomputable def cutDir (A : Set ℝ) (χ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  Aᶜ.indicator (fun _ => (1:ℝ)) x * Aᶜ.indicator (fun _ => (1:ℝ)) y * χ x y

theorem cutDir_of_notMem {A : Set ℝ} (χ : ℝ → ℝ → ℝ) {x y : ℝ} (hx : x ∉ A) (hy : y ∉ A) :
    cutDir A χ x y = χ x y := by
  simp [cutDir, Set.indicator_of_mem (show x ∈ Aᶜ from hx), Set.indicator_of_mem (show y ∈ Aᶜ from hy)]

theorem notMem_of_cutDir_ne_zero {A : Set ℝ} {χ : ℝ → ℝ → ℝ} {x y : ℝ} (h : cutDir A χ x y ≠ 0) :
    x ∉ A ∧ y ∉ A ∧ χ x y ≠ 0 := by
  unfold cutDir at h
  refine ⟨fun hx => h ?_, fun hy => h ?_, fun hχ => h ?_⟩
  · rw [Set.indicator_of_notMem (show x ∉ Aᶜ from fun h' => h' hx)]; ring
  · rw [Set.indicator_of_notMem (show y ∉ Aᶜ from fun h' => h' hy)]; ring
  · rw [hχ]; ring

theorem measurable_cutDir {A : Set ℝ} (hA : MeasurableSet A) {χ : ℝ → ℝ → ℝ}
    (hχ : Measurable fun p : ℝ × ℝ => χ p.1 p.2) :
    Measurable fun p : ℝ × ℝ => cutDir A χ p.1 p.2 :=
  (((measurable_const.indicator hA.compl).comp measurable_fst).mul
    ((measurable_const.indicator hA.compl).comp measurable_snd)).mul hχ

theorem cutDir_symm (A : Set ℝ) {χ : ℝ → ℝ → ℝ} (hs : ∀ x y, χ x y = χ y x) (x y : ℝ) :
    cutDir A χ x y = cutDir A χ y x := by
  unfold cutDir; rw [hs]; ring

theorem abs_indicator_one_le (A : Set ℝ) (x : ℝ) : |A.indicator (fun _ => (1:ℝ)) x| ≤ 1 := by
  by_cases h : x ∈ A
  · rw [Set.indicator_of_mem h]; simp
  · rw [Set.indicator_of_notMem h]; simp

theorem abs_cutDir_le (A : Set ℝ) {χ : ℝ → ℝ → ℝ} (hb : ∀ x y, |χ x y| ≤ 1) (x y : ℝ) :
    |cutDir A χ x y| ≤ 1 := by
  unfold cutDir
  rw [abs_mul, abs_mul]
  have h1 := abs_indicator_one_le Aᶜ x
  have h2 := abs_indicator_one_le Aᶜ y
  calc |Aᶜ.indicator (fun _ => (1:ℝ)) x| * |Aᶜ.indicator (fun _ => (1:ℝ)) y| * |χ x y|
      ≤ 1 * 1 * 1 := by gcongr; exact hb x y
    _ = 1 := by ring

theorem abs_cutDir_sub_le (A : Set ℝ) {χ : ℝ → ℝ → ℝ} (hb : ∀ x y, |χ x y| ≤ 1) (x y : ℝ) :
    |cutDir A χ x y - χ x y| ≤ A.indicator (fun _ => (1:ℝ)) x + A.indicator (fun _ => (1:ℝ)) y := by
  by_cases hx : x ∈ A
  · have h0 : cutDir A χ x y = 0 := by
      unfold cutDir; rw [Set.indicator_of_notMem (show x ∉ Aᶜ from fun h' => h' hx)]; ring
    rw [h0, zero_sub, abs_neg, Set.indicator_of_mem hx]
    have := hb x y
    have : 0 ≤ A.indicator (fun _ => (1:ℝ)) y := Set.indicator_nonneg (fun _ _ => zero_le_one) _
    linarith
  · by_cases hy : y ∈ A
    · have h0 : cutDir A χ x y = 0 := by
        unfold cutDir; rw [Set.indicator_of_notMem (show y ∉ Aᶜ from fun h' => h' hy)]; ring
      rw [h0, zero_sub, abs_neg, Set.indicator_of_mem hy]
      have := hb x y
      have : 0 ≤ A.indicator (fun _ => (1:ℝ)) x := Set.indicator_nonneg (fun _ _ => zero_le_one) _
      linarith
    · rw [cutDir_of_notMem χ hx hy, sub_self, abs_zero]
      exact add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem integral_indicator_fst_add_snd (A : Set ℝ) (hA : MeasurableSet A) :
    ∫ p : ℝ × ℝ, (A.indicator (fun _ => (1:ℝ)) p.1 + A.indicator (fun _ => (1:ℝ)) p.2) ∂gμ
      = 2 * (unitμ A).toReal := by
  have h1 : Integrable (fun p : ℝ × ℝ => A.indicator (fun _ => (1:ℝ)) p.1) gμ :=
    integrable_of_abs_le ((measurable_const.indicator hA).comp measurable_fst) 1
      fun p => abs_indicator_one_le A p.1
  have h2 : Integrable (fun p : ℝ × ℝ => A.indicator (fun _ => (1:ℝ)) p.2) gμ :=
    integrable_of_abs_le ((measurable_const.indicator hA).comp measurable_snd) 1
      fun p => abs_indicator_one_le A p.2
  rw [integral_add h1 h2]
  have hA1 : ∫ t, A.indicator (fun _ => (1:ℝ)) t ∂unitμ = (unitμ A).toReal := integral_indicator_one hA
  have e1 : ∫ p : ℝ × ℝ, A.indicator (fun _ => (1:ℝ)) p.1 ∂gμ = (unitμ A).toReal := by
    have := integral_prod (μ := unitμ) (ν := unitμ) (fun p : ℝ × ℝ => A.indicator (fun _ => (1:ℝ)) p.1) h1
    simp only [gμ] at this ⊢
    rw [this]
    simp [hA1]
  have e2 : ∫ p : ℝ × ℝ, A.indicator (fun _ => (1:ℝ)) p.2 ∂gμ = (unitμ A).toReal := by
    have := integral_prod (μ := unitμ) (ν := unitμ) (fun p : ℝ × ℝ => A.indicator (fun _ => (1:ℝ)) p.2) h2
    simp only [gμ] at this ⊢
    rw [this]
    simp [hA1]
  rw [e1, e2]; ring

/-- `|∫ cutDir·g - ∫ χ·g| ≤ 2|A| B` for `|g| ≤ B`. -/
theorem abs_integral_cutDir_mul_sub_le {A : Set ℝ} (hA : MeasurableSet A) {χ : ℝ → ℝ → ℝ}
    (hχ : Measurable fun p : ℝ × ℝ => χ p.1 p.2) (hb : ∀ x y, |χ x y| ≤ 1) {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) {B : ℝ} (hgb : ∀ p, |g p| ≤ B) :
    |∫ p : ℝ × ℝ, cutDir A χ p.1 p.2 * g p ∂gμ - ∫ p : ℝ × ℝ, χ p.1 p.2 * g p ∂gμ|
      ≤ 2 * (unitμ A).toReal * B := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hgb (0, 0))
  have hi1 : Integrable (fun p : ℝ × ℝ => cutDir A χ p.1 p.2 * g p) gμ :=
    integrable_of_abs_le ((measurable_cutDir hA hχ).mul hg) B fun p => by
      rw [abs_mul]
      calc |cutDir A χ p.1 p.2| * |g p| ≤ 1 * B :=
            mul_le_mul (abs_cutDir_le A hb _ _) (hgb p) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
  have hi2 : Integrable (fun p : ℝ × ℝ => χ p.1 p.2 * g p) gμ :=
    integrable_of_abs_le (hχ.mul hg) B fun p => by
      rw [abs_mul]
      calc |χ p.1 p.2| * |g p| ≤ 1 * B := mul_le_mul (hb _ _) (hgb p) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
  have hiI : Integrable (fun p : ℝ × ℝ =>
      B * (A.indicator (fun _ => (1:ℝ)) p.1 + A.indicator (fun _ => (1:ℝ)) p.2)) gμ :=
    (integrable_of_abs_le (((measurable_const.indicator hA).comp measurable_fst).add
      ((measurable_const.indicator hA).comp measurable_snd)) 2 fun p => by
        calc |A.indicator (fun _ => (1:ℝ)) p.1 + A.indicator (fun _ => (1:ℝ)) p.2|
            ≤ |A.indicator (fun _ => (1:ℝ)) p.1| + |A.indicator (fun _ => (1:ℝ)) p.2| := abs_add_le _ _
          _ ≤ 1 + 1 := add_le_add (abs_indicator_one_le A _) (abs_indicator_one_le A _)
          _ = 2 := by norm_num).const_mul B
  rw [← integral_sub hi1 hi2]
  calc |∫ p : ℝ × ℝ, (cutDir A χ p.1 p.2 * g p - χ p.1 p.2 * g p) ∂gμ|
      ≤ ∫ p : ℝ × ℝ, |cutDir A χ p.1 p.2 * g p - χ p.1 p.2 * g p| ∂gμ := abs_integral_le_integral_abs
    _ ≤ ∫ p : ℝ × ℝ, B * (A.indicator (fun _ => (1:ℝ)) p.1 + A.indicator (fun _ => (1:ℝ)) p.2) ∂gμ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => abs_nonneg _) hiI
          (Filter.Eventually.of_forall fun p => ?_)
        show |cutDir A χ p.1 p.2 * g p - χ p.1 p.2 * g p|
          ≤ B * (A.indicator (fun _ => (1:ℝ)) p.1 + A.indicator (fun _ => (1:ℝ)) p.2)
        rw [← sub_mul, abs_mul, mul_comm]
        exact mul_le_mul (hgb p) (abs_cutDir_sub_le A hb _ _) (abs_nonneg _) hB
    _ = 2 * (unitμ A).toReal * B := by
        rw [integral_const_mul, integral_indicator_fst_add_snd A hA]; ring

/-! ### The row balance -/

set_option maxHeartbeats 4000000 in
/-- **The replacement gain is second order.**  Replacing the rows of `A` by the row of `x₀` and
restoring the constraints with the qualifying directions cut off `A` cannot increase the
entropy, which forces `Δs - α Δe - β Δt = O(|A|²)`. -/
theorem QualDirs.rowReplace_gain_le {W : Graphon} {e₀ t₀ : ℝ} (hmax : IsMaximizer H W e₀ t₀)
    (Q : QualDirs H W) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 ≤ C ∧ ∀ (A : Set ℝ) (hA : MeasurableSet A) (x₀ : ℝ),
      (unitμ A).toReal ≤ h₀ →
      ((W.rowReplace hA x₀).entropy - W.entropy)
        - Q.alpha * ((W.rowReplace hA x₀).edgeDensity - W.edgeDensity)
        - Q.beta * ((W.rowReplace hA x₀).tDensity H - W.tDensity H) ≤ C * (unitμ A).toReal ^ 2 := by
  classical
  have hmax' := hmax
  obtain ⟨he, ht, hopt⟩ := hmax
  set mR : ℝ := (H.edgeFinset.card : ℝ) with hmR
  have hmR0 : 0 ≤ mR := Nat.cast_nonneg _
  set vR : ℝ := (Fintype.card V : ℝ) with hvR
  have hvR0 : 0 ≤ vR := Nat.cast_nonneg _
  set M : ℝ := (2:ℝ) ^ H.edgeFinset.card with hM
  have hM0 : 0 < M := by positivity
  have hdetpos : 0 < |Q.det| := abs_pos.mpr Q.det_ne_zero
  obtain ⟨ρ₀, K, hρ₀, hK, hcorr⟩ := exists_correction H (η := Q.η) (D₀ := |Q.det| / 2)
    Q.η_pos Q.η_le (by linarith)
  set Cρ : ℝ := 12 + 2 * vR + 2 * vR ^ 2 with hCρ
  have hCρ0 : 0 < Cρ := by positivity
  set C₁ : ℝ := K * Cρ with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  set Cdet : ℝ := 8 * mR + 2 * mR * vR with hCdet
  have hCdet0 : 0 ≤ Cdet := by positivity
  set h₀ : ℝ := min 1 (min (|Q.det| / (2 * Cdet + 1)) (min (ρ₀ / Cρ) (Q.η / (2 * C₁)))) with hh₀
  have hh₀pos : 0 < h₀ :=
    lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (div_pos Q.η_pos (by positivity))))
  set C : ℝ := 2 / Q.η * C₁ ^ 2 + |Q.beta| * (M * C₁ ^ 2 + C₁ * mR * vR) with hC
  have hη0 := Q.η_pos
  refine ⟨h₀, C, hh₀pos, by positivity, fun A hA x₀ hh => ?_⟩
  set h : ℝ := (unitμ A).toReal with hhdef
  have hh0 : 0 ≤ h := ENNReal.toReal_nonneg
  have hh1 : h ≤ 1 := le_trans hh (min_le_left _ _)
  have hhdet : h ≤ |Q.det| / (2 * Cdet + 1) :=
    le_trans hh (le_trans (min_le_right _ _) (min_le_left _ _))
  have hhρ : h ≤ ρ₀ / Cρ :=
    le_trans hh (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hhη : h ≤ Q.η / (2 * C₁) :=
    le_trans hh (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  set WA : Graphon := W.rowReplace hA x₀ with hWA
  -- the cut directions
  have hm₁ := measurable_cutDir hA Q.meas₁
  have hm₂ := measurable_cutDir hA Q.meas₂
  have hs₁ := cutDir_symm A Q.symm₁
  have hs₂ := cutDir_symm A Q.symm₂
  have hb₁ := abs_cutDir_le A Q.bound₁
  have hb₂ := abs_cutDir_le A Q.bound₂
  have hWAeq : ∀ x y, x ∉ A → y ∉ A → WA.toFun x y = W.toFun x y := fun x y hx hy => by
    rw [hWA, Graphon.rowReplace_apply, rowRep_of_notMem hx, rowRep_of_notMem hy]
  have hsuppW : ∀ x y, cutDir A Q.χ₁ x y ≠ 0 ∨ cutDir A Q.χ₂ x y ≠ 0 →
      x ∉ A ∧ y ∉ A ∧ W.toFun x y ∈ Icc Q.η (1 - Q.η) := by
    intro x y hxy
    rcases hxy with h' | h'
    · obtain ⟨hx, hy, hχ⟩ := notMem_of_cutDir_ne_zero h'
      exact ⟨hx, hy, Q.supp x y (Or.inl hχ)⟩
    · obtain ⟨hx, hy, hχ⟩ := notMem_of_cutDir_ne_zero h'
      exact ⟨hx, hy, Q.supp x y (Or.inr hχ)⟩
  have hsuppA : ∀ x y, cutDir A Q.χ₁ x y ≠ 0 ∨ cutDir A Q.χ₂ x y ≠ 0 →
      WA.toFun x y ∈ Icc Q.η (1 - Q.η) := fun x y hxy => by
    obtain ⟨hx, hy, hW⟩ := hsuppW x y hxy
    rw [hWAeq x y hx hy]; exact hW
  -- the integrals of the cut directions
  have hc : ∀ {χ : ℝ → ℝ → ℝ}, (Measurable fun p : ℝ × ℝ => χ p.1 p.2) → (∀ x y, |χ x y| ≤ 1) →
      |∫ p : ℝ × ℝ, cutDir A χ p.1 p.2 ∂gμ - ∫ p : ℝ × ℝ, χ p.1 p.2 ∂gμ| ≤ 2 * h := by
    intro χ hm hb
    have := abs_integral_cutDir_mul_sub_le hA hm hb (g := fun _ => (1:ℝ)) measurable_const
      (B := 1) (fun _ => by simp)
    simpa only [mul_one] using this
  have hg : ∀ {χ : ℝ → ℝ → ℝ}, (Measurable fun p : ℝ × ℝ => χ p.1 p.2) → (∀ x y, |χ x y| ≤ 1) →
      |∫ p : ℝ × ℝ, cutDir A χ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ
        - ∫ p : ℝ × ℝ, χ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ| ≤ 2 * h * mR := by
    intro χ hm hb
    exact abs_integral_cutDir_mul_sub_le hA hm hb (W.measurable_gammaW H)
      (fun p => by rw [abs_of_nonneg (W.gammaW_nonneg H _ _)]; exact W.gammaW_le H _ _)
  have hgA : ∀ {χ : ℝ → ℝ → ℝ}, (Measurable fun p : ℝ × ℝ => χ p.1 p.2) → (∀ x y, |χ x y| ≤ 1) →
      |∫ p : ℝ × ℝ, cutDir A χ p.1 p.2 * WA.gammaW H p.1 p.2 ∂gμ
        - ∫ p : ℝ × ℝ, cutDir A χ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ| ≤ mR * (vR * h) := by
    intro χ hm hb
    rw [← integral_sub (integrable_bdd_mul_gammaW H WA (measurable_cutDir hA hm) (abs_cutDir_le A hb))
      (integrable_bdd_mul_gammaW H W (measurable_cutDir hA hm) (abs_cutDir_le A hb))]
    have hpt : ∀ p : ℝ × ℝ, |cutDir A χ p.1 p.2 * WA.gammaW H p.1 p.2
        - cutDir A χ p.1 p.2 * W.gammaW H p.1 p.2| ≤ mR * (vR * h) := by
      intro p
      rw [← mul_sub, abs_mul]
      by_cases h0 : cutDir A χ p.1 p.2 = 0
      · rw [h0, abs_zero, zero_mul]; positivity
      · obtain ⟨hx, hy, -⟩ := notMem_of_cutDir_ne_zero h0
        calc |cutDir A χ p.1 p.2| * |WA.gammaW H p.1 p.2 - W.gammaW H p.1 p.2|
            ≤ 1 * (mR * (vR * h)) := mul_le_mul (abs_cutDir_le A hb _ _)
              (W.abs_gammaW_rowReplace_sub_le H hA x₀ hx hy) (abs_nonneg _) zero_le_one
          _ = mR * (vR * h) := one_mul _
    calc |∫ p : ℝ × ℝ, (cutDir A χ p.1 p.2 * WA.gammaW H p.1 p.2
          - cutDir A χ p.1 p.2 * W.gammaW H p.1 p.2) ∂gμ|
        ≤ ∫ p : ℝ × ℝ, |cutDir A χ p.1 p.2 * WA.gammaW H p.1 p.2
          - cutDir A χ p.1 p.2 * W.gammaW H p.1 p.2| ∂gμ := abs_integral_le_integral_abs
      _ ≤ ∫ _p : ℝ × ℝ, mR * (vR * h) ∂gμ := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun p => abs_nonneg _) (integrable_const _)
          (Filter.Eventually.of_forall hpt)
      _ = mR * (vR * h) := by simp [gμ]
  set c₁' : ℝ := ∫ p : ℝ × ℝ, cutDir A Q.χ₁ p.1 p.2 ∂gμ with hc₁'
  set c₂' : ℝ := ∫ p : ℝ × ℝ, cutDir A Q.χ₂ p.1 p.2 ∂gμ with hc₂'
  set g₁' : ℝ := ∫ p : ℝ × ℝ, cutDir A Q.χ₁ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ with hg₁'
  set g₂' : ℝ := ∫ p : ℝ × ℝ, cutDir A Q.χ₂ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ with hg₂'
  set gA₁ : ℝ := ∫ p : ℝ × ℝ, cutDir A Q.χ₁ p.1 p.2 * WA.gammaW H p.1 p.2 ∂gμ with hgA₁
  set gA₂ : ℝ := ∫ p : ℝ × ℝ, cutDir A Q.χ₂ p.1 p.2 * WA.gammaW H p.1 p.2 ∂gμ with hgA₂
  have hc₁b : |Q.c₁| ≤ 1 := by
    have := integral_abs_mul_le_of_bound (f := fun p : ℝ × ℝ => Q.χ₁ p.1 p.2)
      (g := fun _ => (1:ℝ)) (A := 1) (B := 1) (fun p => Q.bound₁ _ _) (fun _ => by simp)
    simpa [QualDirs.c₁] using this
  have hc₂b : |Q.c₂| ≤ 1 := by
    have := integral_abs_mul_le_of_bound (f := fun p : ℝ × ℝ => Q.χ₂ p.1 p.2)
      (g := fun _ => (1:ℝ)) (A := 1) (B := 1) (fun p => Q.bound₂ _ _) (fun _ => by simp)
    simpa [QualDirs.c₂] using this
  have hgA₁b : |gA₁| ≤ mR := by
    have := integral_abs_mul_le_of_bound (f := fun p : ℝ × ℝ => cutDir A Q.χ₁ p.1 p.2)
      (g := fun p : ℝ × ℝ => WA.gammaW H p.1 p.2) (A := 1) (B := mR) (fun p => hb₁ _ _)
      (fun p => by rw [abs_of_nonneg (WA.gammaW_nonneg H _ _)]; exact WA.gammaW_le H _ _)
    simpa using this
  have hgA₂b : |gA₂| ≤ mR := by
    have := integral_abs_mul_le_of_bound (f := fun p : ℝ × ℝ => cutDir A Q.χ₂ p.1 p.2)
      (g := fun p : ℝ × ℝ => WA.gammaW H p.1 p.2) (A := 1) (B := mR) (fun p => hb₂ _ _)
      (fun p => by rw [abs_of_nonneg (WA.gammaW_nonneg H _ _)]; exact WA.gammaW_le H _ _)
    simpa using this
  have hdc₁ : |c₁' - Q.c₁| ≤ 2 * h := hc Q.meas₁ Q.bound₁
  have hdc₂ : |c₂' - Q.c₂| ≤ 2 * h := hc Q.meas₂ Q.bound₂
  have hdg₁ : |gA₁ - Q.g₁| ≤ 2 * h * mR + mR * (vR * h) := by
    have h1 := hg Q.meas₁ Q.bound₁
    have h2 := hgA Q.meas₁ Q.bound₁
    have : gA₁ - Q.g₁ = (gA₁ - g₁') + (g₁' - Q.g₁) := by ring
    rw [this]
    calc _ ≤ |gA₁ - g₁'| + |g₁' - Q.g₁| := abs_add_le _ _
      _ ≤ mR * (vR * h) + 2 * h * mR := add_le_add h2 h1
      _ = _ := by ring
  have hdg₂ : |gA₂ - Q.g₂| ≤ 2 * h * mR + mR * (vR * h) := by
    have h1 := hg Q.meas₂ Q.bound₂
    have h2 := hgA Q.meas₂ Q.bound₂
    have : gA₂ - Q.g₂ = (gA₂ - g₂') + (g₂' - Q.g₂) := by ring
    rw [this]
    calc _ ≤ |gA₂ - g₂'| + |g₂' - Q.g₂| := abs_add_le _ _
      _ ≤ mR * (vR * h) + 2 * h * mR := add_le_add h2 h1
      _ = _ := by ring
  have hdetA : |Q.det| / 2 ≤ |c₁' * gA₂ - c₂' * gA₁| := by
    have e : (c₁' * gA₂ - c₂' * gA₁) - Q.det
        = (c₁' - Q.c₁) * gA₂ + Q.c₁ * (gA₂ - Q.g₂) - ((c₂' - Q.c₂) * gA₁ + Q.c₂ * (gA₁ - Q.g₁)) := by
      unfold QualDirs.det; ring
    have hb : |(c₁' * gA₂ - c₂' * gA₁) - Q.det| ≤ Cdet * h := by
      rw [e]
      have t1 : |(c₁' - Q.c₁) * gA₂| ≤ 2 * h * mR := by
        rw [abs_mul]; exact mul_le_mul hdc₁ hgA₂b (abs_nonneg _) (by positivity)
      have t2 : |Q.c₁ * (gA₂ - Q.g₂)| ≤ 1 * (2 * h * mR + mR * (vR * h)) := by
        rw [abs_mul]; exact mul_le_mul hc₁b hdg₂ (abs_nonneg _) zero_le_one
      have t3 : |(c₂' - Q.c₂) * gA₁| ≤ 2 * h * mR := by
        rw [abs_mul]; exact mul_le_mul hdc₂ hgA₁b (abs_nonneg _) (by positivity)
      have t4 : |Q.c₂ * (gA₁ - Q.g₁)| ≤ 1 * (2 * h * mR + mR * (vR * h)) := by
        rw [abs_mul]; exact mul_le_mul hc₂b hdg₁ (abs_nonneg _) zero_le_one
      calc _ ≤ |(c₁' - Q.c₁) * gA₂ + Q.c₁ * (gA₂ - Q.g₂)|
            + |(c₂' - Q.c₂) * gA₁ + Q.c₂ * (gA₁ - Q.g₁)| := abs_sub _ _
        _ ≤ (|(c₁' - Q.c₁) * gA₂| + |Q.c₁ * (gA₂ - Q.g₂)|)
            + (|(c₂' - Q.c₂) * gA₁| + |Q.c₂ * (gA₁ - Q.g₁)|) :=
            add_le_add (abs_add_le _ _) (abs_add_le _ _)
        _ ≤ 2 * h * mR + 1 * (2 * h * mR + mR * (vR * h))
            + (2 * h * mR + 1 * (2 * h * mR + mR * (vR * h))) := by linarith
        _ = Cdet * h := by rw [hCdet]; ring
    have hsmall : Cdet * h ≤ |Q.det| / 2 := by
      rw [le_div_iff₀ (by positivity)] at hhdet
      nlinarith
    have := abs_sub_abs_le_abs_sub Q.det (Q.det - (c₁' * gA₂ - c₂' * gA₁))
    rw [sub_sub_cancel] at this
    have e3 : |Q.det - (c₁' * gA₂ - c₂' * gA₁)| = |(c₁' * gA₂ - c₂' * gA₁) - Q.det| := abs_sub_comm _ _
    linarith
  -- the constraint defects
  have hΔe : |W.edgeDensity - WA.edgeDensity| ≤ 12 * h := by
    have h1 := W.abs_edgeDensity_rowReplace_sub_le hA x₀
    have h2 := abs_mul_sub_setIntegral_le W.measurable_degFun W.abs_degFun_le A x₀
    have h3 : 8 * h ^ 2 ≤ 8 * h := by nlinarith
    rw [abs_sub_comm]
    have := abs_sub_abs_le_abs_sub (WA.edgeDensity - W.edgeDensity)
      (2 * ((unitμ A).toReal * W.degFun x₀ - ∫ s in A, W.degFun s ∂unitμ))
    have h4 : |2 * ((unitμ A).toReal * W.degFun x₀ - ∫ s in A, W.degFun s ∂unitμ)| ≤ 4 * h := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
    linarith
  have hΔt : |W.tDensity H - WA.tDensity H| ≤ (2 * vR + 2 * vR ^ 2) * h := by
    have h1 := W.abs_tDensity_rowReplace_sub_le H hA x₀
    have h2 : |∑ i, ((unitμ A).toReal * rootedK H W.symm' i x₀
        - ∫ s in A, rootedK H W.symm' i s ∂unitμ)| ≤ vR * (2 * h) := by
      calc _ ≤ ∑ i, |(unitμ A).toReal * rootedK H W.symm' i x₀
            - ∫ s in A, rootedK H W.symm' i s ∂unitμ| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : V, 2 * h := Finset.sum_le_sum fun i _ =>
            abs_mul_sub_setIntegral_le (measurable_rootedK H W.symm' W.measurable_uncurry i)
              (abs_rootedK_le H W.symm' W.abs_toFun_le i) A x₀
        _ = vR * (2 * h) := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have h3 : 2 * vR ^ 2 * h ^ 2 ≤ 2 * vR ^ 2 * h := by
      have : h ^ 2 ≤ h := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    rw [abs_sub_comm]
    have := abs_sub_abs_le_abs_sub (WA.tDensity H - W.tDensity H)
      (∑ i, ((unitμ A).toReal * rootedK H W.symm' i x₀ - ∫ s in A, rootedK H W.symm' i s ∂unitμ))
    have e : (2 * vR + 2 * vR ^ 2) * h = vR * (2 * h) + 2 * vR ^ 2 * h := by ring
    rw [e]
    have h1' : |WA.tDensity H - W.tDensity H - ∑ i, ((unitμ A).toReal * rootedK H W.symm' i x₀
        - ∫ s in A, rootedK H W.symm' i s ∂unitμ)| ≤ 2 * vR ^ 2 * h ^ 2 := by
      simpa [hvR] using h1
    linarith
  have hρ : |W.edgeDensity - WA.edgeDensity| + |W.tDensity H - WA.tDensity H| ≤ ρ₀ := by
    have h1 : Cρ * h ≤ ρ₀ := by rw [le_div_iff₀ hCρ0] at hhρ; linarith
    have e : Cρ * h = 12 * h + (2 * vR + 2 * vR ^ 2) * h := by rw [hCρ]; ring
    linarith
  obtain ⟨u₁, u₂, hu, W'', hW'', he'', ht''⟩ := hcorr WA (cutDir A Q.χ₁) (cutDir A Q.χ₂) hm₁ hm₂
    hs₁ hs₂ hb₁ hb₂ hsuppA (by simpa using hdetA) W.edgeDensity (W.tDensity H) hρ
  have hu' : |u₁| + |u₂| ≤ C₁ * h := by
    have h1 : K * (|W.edgeDensity - WA.edgeDensity| + |W.tDensity H - WA.tDensity H|)
        ≤ K * (Cρ * h) := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      have e : Cρ * h = 12 * h + (2 * vR + 2 * vR ^ 2) * h := by rw [hCρ]; ring
      linarith
    have e : K * (Cρ * h) = C₁ * h := by rw [hC₁]; ring
    linarith
  -- the perturbation
  set δ : ℝ → ℝ → ℝ := fun x y => u₁ * cutDir A Q.χ₁ x y + u₂ * cutDir A Q.χ₂ x y with hδ
  have hW''δ : ∀ x y, W''.toFun x y = WA.toFun x y + δ x y := fun x y => by
    rw [hW'']; simp only [hδ]; ring
  have hδm : Measurable fun p : ℝ × ℝ => δ p.1 p.2 :=
    (measurable_const.mul hm₁).add (measurable_const.mul hm₂)
  have hδb : ∀ x y, |δ x y| ≤ C₁ * h := by
    intro x y
    calc |δ x y| ≤ |u₁ * cutDir A Q.χ₁ x y| + |u₂ * cutDir A Q.χ₂ x y| := abs_add_le _ _
      _ ≤ |u₁| * 1 + |u₂| * 1 := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (hb₁ x y) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (hb₂ x y) (abs_nonneg _))
      _ ≤ C₁ * h := by linarith
  have hC₁h : C₁ * h ≤ Q.η / 2 := by
    rw [le_div_iff₀ (by positivity)] at hhη
    linarith
  have hδsupp : ∀ x y, δ x y ≠ 0 → WA.toFun x y ∈ Icc Q.η (1 - Q.η) := by
    intro x y hxy
    refine hsuppA x y ?_
    by_contra hc'
    push Not at hc'
    apply hxy
    simp only [hδ, hc'.1, hc'.2, mul_zero, add_zero]
  have hent := Graphon.entropy_add_ge WA W'' hW''δ hδm Q.η_pos Q.η_le hδsupp
    (fun x y => le_trans (hδb x y) hC₁h)
  have hmaxW'' := hopt W'' (he''.trans he) (ht''.trans ht)
  -- the linear entropy term
  have hlinS : ∫ p : ℝ × ℝ, dS0 (WA.toFun p.1 p.2) * δ p.1 p.2 ∂gμ
      = Q.alpha * (u₁ * c₁' + u₂ * c₂') + Q.beta * (u₁ * g₁' + u₂ * g₂') := by
    have hpt : ∀ p : ℝ × ℝ, dS0 (WA.toFun p.1 p.2) * δ p.1 p.2
        = u₁ * (dS0 (W.toFun p.1 p.2) * cutDir A Q.χ₁ p.1 p.2)
          + u₂ * (dS0 (W.toFun p.1 p.2) * cutDir A Q.χ₂ p.1 p.2) := by
      intro p
      by_cases h0 : cutDir A Q.χ₁ p.1 p.2 ≠ 0 ∨ cutDir A Q.χ₂ p.1 p.2 ≠ 0
      · obtain ⟨hx, hy, -⟩ := hsuppW p.1 p.2 h0
        rw [hWAeq p.1 p.2 hx hy]; simp only [hδ]; ring
      · push Not at h0
        simp only [hδ, h0.1, h0.2]; ring
    have hi₁ := integrable_dS0_mul W hm₁ hb₁ Q.η_pos
      (fun x y h' => (hsuppW x y (Or.inl h')).2.2)
    have hi₂ := integrable_dS0_mul W hm₂ hb₂ Q.η_pos
      (fun x y h' => (hsuppW x y (Or.inr h')).2.2)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add (hi₁.const_mul u₁) (hi₂.const_mul u₂), integral_const_mul, integral_const_mul]
    have hel₁ := QualDirs.el_linear H hmax' Q hm₁ hs₁ hb₁ Q.η_pos Q.η_le
      (fun x y h' => (hsuppW x y (Or.inl h')).2.2)
    have hel₂ := QualDirs.el_linear H hmax' Q hm₂ hs₂ hb₂ Q.η_pos Q.η_le
      (fun x y h' => (hsuppW x y (Or.inr h')).2.2)
    rw [hel₁, hel₂]
    ring
  have hsqδ : ∫ p : ℝ × ℝ, δ p.1 p.2 ^ 2 ∂gμ ≤ C₁ ^ 2 * h ^ 2 := by
    have hb : ∀ p : ℝ × ℝ, δ p.1 p.2 ^ 2 ≤ C₁ ^ 2 * h ^ 2 := fun p => by
      have := hδb p.1 p.2
      rw [← sq_abs (δ p.1 p.2)]
      calc |δ p.1 p.2| ^ 2 ≤ (C₁ * h) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = C₁ ^ 2 * h ^ 2 := by ring
    calc ∫ p : ℝ × ℝ, δ p.1 p.2 ^ 2 ∂gμ ≤ ∫ _p : ℝ × ℝ, C₁ ^ 2 * h ^ 2 ∂gμ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => sq_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall hb)
      _ = C₁ ^ 2 * h ^ 2 := by simp [gμ]
  -- the constraints at `W''`
  have heW'' : W''.edgeDensity = WA.edgeDensity + u₁ * c₁' + u₂ * c₂' :=
    edgeDensity_add_dirs WA W'' hm₁ hm₂ hb₁ hb₂ hW''
  have hecon : u₁ * c₁' + u₂ * c₂' = W.edgeDensity - WA.edgeDensity := by
    rw [he''] at heW''; linarith
  have hC₁h1 : C₁ * h ≤ 1 := by linarith [Q.η_le]
  have htexp := Graphon.abs_tDensity_sub_linear_le H WA W'' hW''δ hδm
    (mul_nonneg hC₁0.le hh0) hC₁h1 hδb
  have hlinT : ∫ p : ℝ × ℝ, δ p.1 p.2 * WA.gammaW H p.1 p.2 ∂gμ = u₁ * gA₁ + u₂ * gA₂ :=
    integral_dirs_gammaW H WA hm₁ hm₂ hb₁ hb₂ u₁ u₂
  rw [ht'', hlinT] at htexp
  have hgg : |(u₁ * g₁' + u₂ * g₂') - (u₁ * gA₁ + u₂ * gA₂)| ≤ C₁ * h * (mR * (vR * h)) := by
    have e : (u₁ * g₁' + u₂ * g₂') - (u₁ * gA₁ + u₂ * gA₂) = -(u₁ * (gA₁ - g₁') + u₂ * (gA₂ - g₂')) := by
      ring
    rw [e, abs_neg]
    have h1 := hgA Q.meas₁ Q.bound₁
    have h2 := hgA Q.meas₂ Q.bound₂
    calc |u₁ * (gA₁ - g₁') + u₂ * (gA₂ - g₂')| ≤ |u₁| * |gA₁ - g₁'| + |u₂| * |gA₂ - g₂'| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |u₁| * (mR * (vR * h)) + |u₂| * (mR * (vR * h)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
      _ = (|u₁| + |u₂|) * (mR * (vR * h)) := by ring
      _ ≤ C₁ * h * (mR * (vR * h)) := mul_le_mul_of_nonneg_right hu' (by positivity)
  -- assemble
  rw [hlinS] at hent
  have hsq2 : 2 / Q.η * ∫ p : ℝ × ℝ, δ p.1 p.2 ^ 2 ∂gμ ≤ 2 / Q.η * (C₁ ^ 2 * h ^ 2) :=
    mul_le_mul_of_nonneg_left hsqδ (by positivity)
  have hβ1 : |Q.beta * ((u₁ * g₁' + u₂ * g₂') - (W.tDensity H - WA.tDensity H))|
      ≤ |Q.beta| * (M * (C₁ * h) ^ 2 + C₁ * h * (mR * (vR * h))) := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have e : (u₁ * g₁' + u₂ * g₂') - (W.tDensity H - WA.tDensity H)
        = ((u₁ * g₁' + u₂ * g₂') - (u₁ * gA₁ + u₂ * gA₂))
          - (W.tDensity H - WA.tDensity H - (u₁ * gA₁ + u₂ * gA₂)) := by ring
    rw [e]
    calc _ ≤ |(u₁ * g₁' + u₂ * g₂') - (u₁ * gA₁ + u₂ * gA₂)|
          + |W.tDensity H - WA.tDensity H - (u₁ * gA₁ + u₂ * gA₂)| := abs_sub _ _
      _ ≤ C₁ * h * (mR * (vR * h)) + M * (C₁ * h) ^ 2 := add_le_add hgg htexp
      _ = _ := by ring
  have hβ2 := (abs_le.mp hβ1).1
  have e5 : C * h ^ 2 = 2 / Q.η * (C₁ ^ 2 * h ^ 2)
      + |Q.beta| * (M * (C₁ * h) ^ 2 + C₁ * h * (mR * (vR * h))) := by rw [hC]; ring
  rw [e5]
  rw [hecon] at hent
  nlinarith [hent, hmaxW'', hsq2, hβ2]

/-- **Row balance** (draft `kb:lem:row`): `h Φ(x₀) - ∫_A Φ ≤ C h²` for every `x₀` and every
`A` of small measure `h`. -/
theorem QualDirs.row_balance {W : Graphon} {e₀ t₀ : ℝ} (hmax : IsMaximizer H W e₀ t₀)
    (Q : QualDirs H W) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 ≤ C ∧ ∀ (A : Set ℝ), MeasurableSet A → ∀ x₀ : ℝ,
      (unitμ A).toReal ≤ h₀ →
      (unitμ A).toReal * W.balFun H Q.alpha Q.beta x₀ - ∫ s in A, W.balFun H Q.alpha Q.beta s ∂unitμ
        ≤ C * (unitμ A).toReal ^ 2 := by
  obtain ⟨h₀, C, hh₀, hC, hgain⟩ := Q.rowReplace_gain_le H hmax
  refine ⟨h₀, C + (8 + 8 * |Q.alpha| + 2 * |Q.beta| * (Fintype.card V : ℝ) ^ 2), hh₀,
    by positivity, fun A hA x₀ hh => ?_⟩
  have h1 := hgain A hA x₀ hh
  have h2 := W.abs_rowReplace_combo_le H hA x₀ Q.alpha Q.beta
  have h3 := (abs_le.mp h2).1
  nlinarith [h1, h3]

/-- Inside a set of positive measure there are subsets of arbitrarily small positive measure. -/
theorem exists_subset_unitμ_pos_le {B : Set ℝ} (hB : MeasurableSet B) (hB0 : unitμ B ≠ 0) {r : ℝ}
    (hr : 0 < r) : ∃ A ⊆ B, MeasurableSet A ∧ 0 < (unitμ A).toReal ∧ (unitμ A).toReal ≤ r := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / r)
  have hNpos : (0:ℝ) < N := lt_trans (by positivity) hN
  have hlen : 1 / (N:ℝ) ≤ r := by
    rw [div_le_iff₀ hNpos]; rw [div_lt_iff₀ hr] at hN; linarith
  by_contra hcon
  push Not at hcon
  have hnull : ∀ k ∈ Finset.range (N + 1), unitμ (B ∩ Icc ((k:ℝ) / N) ((k + 1) / N)) = 0 := by
    intro k _
    by_contra hne
    have hfin : unitμ (B ∩ Icc ((k:ℝ) / N) ((k + 1) / N)) ≠ ⊤ := measure_ne_top _ _
    have hpos := ENNReal.toReal_pos hne hfin
    have hle : (unitμ (B ∩ Icc ((k:ℝ) / N) ((k + 1) / N))).toReal ≤ r := by
      have h1 : unitμ (B ∩ Icc ((k:ℝ) / N) ((k + 1) / N))
          ≤ volume (Icc ((k:ℝ) / N) ((k + 1) / N)) :=
        le_trans (measure_mono inter_subset_right) (Measure.restrict_le_self _)
      have h2 : volume (Icc ((k:ℝ) / N) ((k + 1) / N)) = ENNReal.ofReal (1 / N) := by
        rw [Real.volume_Icc]; congr 1; field_simp; ring
      rw [h2] at h1
      calc _ ≤ (ENNReal.ofReal (1 / (N:ℝ))).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
        _ = 1 / N := ENNReal.toReal_ofReal (by positivity)
        _ ≤ r := hlen
    exact absurd (hcon _ inter_subset_left (hB.inter measurableSet_Icc) hpos) (not_lt.mpr hle)
  have hsub : B ∩ Icc 0 1 ⊆ ⋃ k ∈ Finset.range (N + 1), B ∩ Icc ((k:ℝ) / N) ((k + 1) / N) := by
    rintro x ⟨hxB, hx0, hx1⟩
    simp only [Set.mem_iUnion, Finset.mem_range]
    have hxN : 0 ≤ x * N := by positivity
    refine ⟨⌊x * N⌋₊, ?_, hxB, ?_, ?_⟩
    · have : ⌊x * N⌋₊ ≤ N := Nat.floor_le_of_le (by nlinarith)
      omega
    · rw [div_le_iff₀ hNpos]; exact Nat.floor_le hxN
    · rw [le_div_iff₀ hNpos]; exact (Nat.lt_floor_add_one _).le
  have h0 : unitμ (B ∩ Icc 0 1) = 0 := by
    apply measure_mono_null hsub
    exact nonpos_iff_eq_zero.mp (le_trans (measure_biUnion_finset_le _ _)
      (by rw [Finset.sum_eq_zero hnull]))
  rw [unitμ_inter_Icc hB] at h0
  exact hB0 h0

/-- **`Φ(x₀)` is at most the essential infimum of `Φ`, for every `x₀`.** -/
theorem QualDirs.ae_balFun_ge {W : Graphon} {e₀ t₀ : ℝ} (hmax : IsMaximizer H W e₀ t₀)
    (Q : QualDirs H W) (x₀ : ℝ) :
    ∀ᵐ x ∂unitμ, W.balFun H Q.alpha Q.beta x₀ ≤ W.balFun H Q.alpha Q.beta x := by
  obtain ⟨h₀, C, hh₀, hC, hbal⟩ := Q.row_balance H hmax
  set Φ := W.balFun H Q.alpha Q.beta with hΦ
  have hΦm : Measurable Φ := W.measurable_balFun H Q.alpha Q.beta
  have hΦb : ∀ u, |Φ u| ≤ 2 + 2 * |Q.alpha| + |Q.beta| * (Fintype.card V : ℝ) := fun u => by
    simp only [hΦ, Graphon.balFun]
    have h1 := W.abs_rowEnt_le u
    have h2 := W.abs_degFun_le u
    have h3 : |∑ i, rootedK H W.symm' i u| ≤ (Fintype.card V : ℝ) := by
      calc _ ≤ ∑ i, |rootedK H W.symm' i u| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : V, (1:ℝ) := Finset.sum_le_sum fun i _ => abs_rootedK_le H W.symm' W.abs_toFun_le i u
        _ = _ := by simp
    calc |2 * W.rowEnt u - 2 * Q.alpha * W.degFun u - Q.beta * ∑ i, rootedK H W.symm' i u|
        ≤ |2 * W.rowEnt u| + |2 * Q.alpha * W.degFun u| + |Q.beta * ∑ i, rootedK H W.symm' i u| := by
          have := abs_sub (2 * W.rowEnt u - 2 * Q.alpha * W.degFun u) (Q.beta * ∑ i, rootedK H W.symm' i u)
          have := abs_sub (2 * W.rowEnt u) (2 * Q.alpha * W.degFun u)
          linarith
      _ ≤ 2 * 1 + 2 * |Q.alpha| * 1 + |Q.beta| * (Fintype.card V : ℝ) := by
          have e1 : |2 * W.rowEnt u| = 2 * |W.rowEnt u| := by
            rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          have e2 : |2 * Q.alpha * W.degFun u| = 2 * |Q.alpha| * |W.degFun u| := by
            rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          have e3 : |Q.beta * ∑ i, rootedK H W.symm' i u| = |Q.beta| * |∑ i, rootedK H W.symm' i u| :=
            abs_mul _ _
          rw [e1, e2, e3]
          gcongr
      _ = _ := by ring
  have hkey : ∀ n : ℕ, unitμ {x | Φ x ≤ Φ x₀ - 1 / ((n:ℝ) + 1)} = 0 := by
    intro n
    set s : ℝ := 1 / ((n:ℝ) + 1) with hs
    have hs0 : 0 < s := by positivity
    by_contra hne
    have hBm : MeasurableSet {x | Φ x ≤ Φ x₀ - s} := measurableSet_le hΦm measurable_const
    obtain ⟨A, hAB, hA, hApos, hAle⟩ := exists_subset_unitμ_pos_le hBm hne
      (r := min h₀ (s / (2 * C + 1))) (lt_min hh₀ (by positivity))
    set h : ℝ := (unitμ A).toReal
    have h1 := hbal A hA x₀ (le_trans hAle (min_le_left _ _))
    have hint : IntegrableOn Φ A unitμ := integrable_of_abs_le hΦm _ hΦb
    have h2 : ∫ u in A, Φ u ∂unitμ ≤ ∫ _u in A, (Φ x₀ - s) ∂unitμ :=
      setIntegral_mono_on hint (integrable_const _) hA fun u hu => hAB hu
    rw [setIntegral_const, smul_eq_mul, measureReal_def] at h2
    have h3 : h ≤ s / (2 * C + 1) := le_trans hAle (min_le_right _ _)
    have h4 : C * h ≤ s / 2 := by
      rw [le_div_iff₀ (by positivity)] at h3
      nlinarith
    -- `h s ≤ C h²` and `C h ≤ s/2` contradict `h > 0`
    have h5 : h * s ≤ C * h ^ 2 := by nlinarith [h1, h2]
    nlinarith
  have hunion : unitμ {x | Φ x < Φ x₀} = 0 := by
    have hsub : {x | Φ x < Φ x₀} ⊆ ⋃ n : ℕ, {x | Φ x ≤ Φ x₀ - 1 / ((n:ℝ) + 1)} := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact Set.mem_iUnion.mpr ⟨n, by simp only [Set.mem_ofPred_eq]; linarith⟩
    exact measure_mono_null hsub (measure_iUnion_null_iff.mpr hkey)
  rw [ae_iff]
  simpa only [not_le] using hunion

end UpperTailOptimizers
