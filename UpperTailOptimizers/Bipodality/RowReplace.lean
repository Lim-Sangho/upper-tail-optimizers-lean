import UpperTailOptimizers.Bipodality.QualFamily

/-!
# Row replacement

For a measurable `A ⊆ ℝ` and a point `x₀`, let `π_A(x) = x₀` on `A` and `π_A(x) = x` off `A`.
Replacing the rows and columns of a kernel indexed by `A` by those of `x₀` changes an edge-product
density to first order in `h = |A|` by the rooted densities:

  `∫ ∏_e κ(π z_e) - ∫ ∏_e κ(z_e) = ∑_i (h T_i(x₀) - ∫_A T_i) + O(v² h²)`,

where `T_i(u)` is the density rooted at `i` with label `u`.  The proof replaces one vertex at a
time.

## Contents

* `rowRep`, `kEdgeVal`, `kProd`, `rootedK` — the objects;
* `abs_integral_kProd_rowRep_sub_le` — the first-order expansion.
-/

set_option linter.unusedSectionVars false

namespace UpperTailOptimizers

open MeasureTheory Set SingularEndpoint

/-- `π_A(x) = x₀` for `x ∈ A`, `x` otherwise. -/
noncomputable def rowRep (A : Set ℝ) (x₀ : ℝ) (x : ℝ) : ℝ := by
  classical exact if x ∈ A then x₀ else x

theorem rowRep_of_mem {A : Set ℝ} {x₀ x : ℝ} (hx : x ∈ A) : rowRep A x₀ x = x₀ := by
  classical simp [rowRep, hx]

theorem rowRep_of_notMem {A : Set ℝ} {x₀ x : ℝ} (hx : x ∉ A) : rowRep A x₀ x = x := by
  classical simp [rowRep, hx]

theorem measurable_rowRep {A : Set ℝ} (hA : MeasurableSet A) (x₀ : ℝ) :
    Measurable (rowRep A x₀) := by
  classical
  have h : rowRep A x₀ = A.piecewise (fun _ => x₀) id := by
    funext x; by_cases hx : x ∈ A <;> simp [rowRep, Set.piecewise, hx]
  rw [h]; exact Measurable.piecewise hA measurable_const measurable_id

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The kernel value on an edge at a labelling. -/
def kEdgeVal (κ : ℝ → ℝ → ℝ) (hs : ∀ x y, κ x y = κ y x) (z : V → ℝ) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun a b => κ (z a) (z b), fun a b => hs (z a) (z b)⟩ e

/-- The edge product of a kernel. -/
def kProd (H : SimpleGraph V) [DecidableRel H.Adj] (κ : ℝ → ℝ → ℝ) (hs : ∀ x y, κ x y = κ y x)
    (z : V → ℝ) : ℝ :=
  ∏ e ∈ H.edgeFinset, kEdgeVal κ hs z e

section

variable (H : SimpleGraph V) [DecidableRel H.Adj] {κ : ℝ → ℝ → ℝ} (hs : ∀ x y, κ x y = κ y x)

theorem measurable_kEdgeVal (hm : Measurable fun p : ℝ × ℝ => κ p.1 p.2) (e : Sym2 V) :
    Measurable fun z : V → ℝ => kEdgeVal κ hs z e := by
  induction e using Sym2.ind with
  | _ a b =>
    have hpair : Measurable fun z : V → ℝ => (z a, z b) :=
      (measurable_pi_apply a).prodMk (measurable_pi_apply b)
    exact hm.comp hpair

theorem measurable_kProd (hm : Measurable fun p : ℝ × ℝ => κ p.1 p.2) :
    Measurable fun z : V → ℝ => kProd H κ hs z :=
  Finset.measurable_prod _ fun e _ => measurable_kEdgeVal hs hm e

theorem abs_kProd_le (hb : ∀ x y, |κ x y| ≤ 1) (z : V → ℝ) : |kProd H κ hs z| ≤ 1 := by
  unfold kProd
  rw [Finset.abs_prod]
  refine Finset.prod_le_one (fun e _ => abs_nonneg _) fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => exact hb _ _

/-- The rooted density `T_i(u) = ∫ ∏_e κ(z[i ↦ u]_e) dz`. -/
noncomputable def rootedK (i : V) (u : ℝ) : ℝ :=
  ∫ z : V → ℝ, kProd H κ hs (Function.update z i u) ∂(Measure.pi fun _ : V => unitμ)

/-- Replace the coordinates in `S` by their images under `π_A`. -/
noncomputable def repS (S : Finset V) (A : Set ℝ) (x₀ : ℝ) (z : V → ℝ) : V → ℝ :=
  fun j => if j ∈ S then rowRep A x₀ (z j) else z j

theorem measurable_repS (S : Finset V) {A : Set ℝ} (hA : MeasurableSet A) (x₀ : ℝ) :
    Measurable (repS S A x₀) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases hj : j ∈ S
  · simp only [repS, hj, if_true]
    exact (measurable_rowRep hA x₀).comp (measurable_pi_apply j)
  · simp only [repS, hj, if_false]
    exact measurable_pi_apply j

theorem repS_insert_update {S : Finset V} {k : V} (hk : k ∉ S) (A : Set ℝ) (x₀ : ℝ) (z : V → ℝ)
    (s : ℝ) : repS (insert k S) A x₀ (Function.update z k s)
      = Function.update (repS S A x₀ z) k (rowRep A x₀ s) := by
  funext j
  by_cases hj : j = k
  · subst hj; simp [repS]
  · have hj' : j ∈ insert k S ↔ j ∈ S := by simp [hj]
    simp only [repS, hj', Function.update_of_ne hj]

theorem repS_update {S : Finset V} {k : V} (hk : k ∉ S) (A : Set ℝ) (x₀ : ℝ) (z : V → ℝ)
    (s : ℝ) : repS S A x₀ (Function.update z k s) = Function.update (repS S A x₀ z) k s := by
  funext j
  by_cases hj : j = k
  · subst hj; simp [repS, hk]
  · simp only [repS, Function.update_of_ne hj]

theorem repS_empty (A : Set ℝ) (x₀ : ℝ) (z : V → ℝ) : repS ∅ A x₀ z = z := by
  funext j; simp [repS]

theorem repS_eq_of_notMem {S : Finset V} {A : Set ℝ} {x₀ : ℝ} {z : V → ℝ}
    (h : ∀ j ∈ S, z j ∉ A) : repS S A x₀ z = z := by
  funext j
  by_cases hj : j ∈ S
  · simp only [repS, hj, if_true, rowRep_of_notMem (h j hj)]
  · simp only [repS, hj, if_false]

end

section Replacement

variable (H : SimpleGraph V) [DecidableRel H.Adj] {κ : ℝ → ℝ → ℝ} (hs : ∀ x y, κ x y = κ y x)

set_option maxHeartbeats 2000000 in
/-- **One vertex of the replacement.** -/
theorem abs_replace_step (hm : Measurable fun p : ℝ × ℝ => κ p.1 p.2) (hb : ∀ x y, |κ x y| ≤ 1)
    {A : Set ℝ} (hA : MeasurableSet A) (x₀ : ℝ) {S : Finset V} {k : V} (hk : k ∉ S) :
    |(∫ z, kProd H κ hs (repS (insert k S) A x₀ z) ∂(Measure.pi fun _ : V => unitμ)
        - ∫ z, kProd H κ hs (repS S A x₀ z) ∂(Measure.pi fun _ : V => unitμ))
      - ((unitμ A).toReal * rootedK H hs k x₀ - ∫ s in A, rootedK H hs k s ∂unitμ)|
      ≤ 4 * S.card * (unitμ A).toReal ^ 2 := by
  classical
  set π : Measure (V → ℝ) := Measure.pi fun _ : V => unitμ with hπ
  set h : ℝ := (unitμ A).toReal with hh
  have hh0 : 0 ≤ h := ENNReal.toReal_nonneg
  have hPm := measurable_kProd H hs hm
  have hPb := abs_kProd_le H hs hb
  -- the two resampled integrands
  set F : (V → ℝ) → ℝ → ℝ := fun z u => kProd H κ hs (Function.update (repS S A x₀ z) k u) with hF
  set G : (V → ℝ) → ℝ → ℝ := fun z u => kProd H κ hs (Function.update z k u) with hG
  have hupd : Measurable fun p : (V → ℝ) × ℝ => Function.update p.1 k p.2 := measurable_update'
  have hFm : Measurable fun p : (V → ℝ) × ℝ => F p.1 p.2 :=
    hPm.comp (hupd.comp ((measurable_repS S hA x₀).prodMap measurable_id))
  have hGm : Measurable fun p : (V → ℝ) × ℝ => G p.1 p.2 := hPm.comp hupd
  have hFb : ∀ z u, |F z u| ≤ 1 := fun z u => hPb _
  have hGb : ∀ z u, |G z u| ≤ 1 := fun z u => hPb _
  have hFmz : ∀ z, Measurable fun u => F z u := fun z =>
    hFm.comp (measurable_const.prodMk measurable_id)
  -- resampling coordinate `k`
  have hI1 : ∫ z, kProd H κ hs (repS (insert k S) A x₀ z) ∂π
      = ∫ z, (∫ s, F z (rowRep A x₀ s) ∂unitμ) ∂π := by
    rw [integral_pi_update k (F := fun z => kProd H κ hs (repS (insert k S) A x₀ z))
      (hPm.comp (measurable_repS (insert k S) hA x₀)) (C := 1) (fun z => hPb _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [hF, repS_insert_update hk]
  have hI2 : ∫ z, kProd H κ hs (repS S A x₀ z) ∂π = ∫ z, (∫ s, F z s ∂unitμ) ∂π := by
    rw [integral_pi_update k (F := fun z => kProd H κ hs (repS S A x₀ z))
      (hPm.comp (measurable_repS S hA x₀)) (C := 1) (fun z => hPb _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [hF, repS_update hk]
  -- the inner integral over the replaced coordinate
  have hinner : ∀ z, ∫ s, F z (rowRep A x₀ s) ∂unitμ
      = h * F z x₀ + ∫ s, F z s ∂unitμ - ∫ s in A, F z s ∂unitμ := by
    intro z
    have hintF : Integrable (fun s => F z s) unitμ := integrable_of_abs_le (hFmz z) 1 (hFb z)
    have hintR : Integrable (fun s => F z (rowRep A x₀ s)) unitμ :=
      integrable_of_abs_le ((hFmz z).comp (measurable_rowRep hA x₀)) 1 fun s => hFb z _
    rw [← integral_add_compl hA hintR, ← integral_add_compl hA hintF]
    have h1 : ∫ s in A, F z (rowRep A x₀ s) ∂unitμ = h * F z x₀ := by
      rw [setIntegral_congr_fun (g := fun _ => F z x₀) hA
        (fun s hs => by simp only [rowRep_of_mem hs]), setIntegral_const, smul_eq_mul]
      rfl
    have h2 : ∫ s in Aᶜ, F z (rowRep A x₀ s) ∂unitμ = ∫ s in Aᶜ, F z s ∂unitμ :=
      setIntegral_congr_fun hA.compl (fun s hs => by simp only [rowRep_of_notMem hs])
    rw [h1, h2]; ring
  -- bounds comparing `F` and `G`
  set cnt : (V → ℝ) → ℝ := fun z => ∑ j ∈ S, A.indicator (fun _ => (1:ℝ)) (z j) with hcnt
  have hcntm : Measurable cnt :=
    Finset.measurable_sum _ fun j _ => (measurable_const.indicator hA).comp (measurable_pi_apply j)
  have hcnt0 : ∀ z, 0 ≤ cnt z := fun z =>
    Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hcntb : ∀ z, cnt z ≤ S.card := fun z => by
    calc cnt z ≤ ∑ _j ∈ S, (1:ℝ) := Finset.sum_le_sum fun j _ => by
          by_cases h' : z j ∈ A
          · rw [Set.indicator_of_mem h']
          · rw [Set.indicator_of_notMem h']; exact zero_le_one
      _ = S.card := by simp
  have hcntint : ∫ z, cnt z ∂π = S.card * h := by
    have hi : ∀ j ∈ S, Integrable (fun z : V → ℝ => A.indicator (fun _ => (1:ℝ)) (z j)) π :=
      fun j _ => integrable_of_abs_le ((measurable_const.indicator hA).comp (measurable_pi_apply j)) 1
        fun z => by
          by_cases h' : z j ∈ A
          · rw [Set.indicator_of_mem h']; simp
          · rw [Set.indicator_of_notMem h']; simp
    rw [integral_finsetSum _ hi]
    have hj : ∀ j ∈ S, ∫ z : V → ℝ, A.indicator (fun _ => (1:ℝ)) (z j) ∂π = h := by
      intro j _
      rw [integral_pi_eval_comp j (measurable_const.indicator hA)]
      exact integral_indicator_one hA
    rw [Finset.sum_congr rfl hj, Finset.sum_const, nsmul_eq_mul]
  have hFG : ∀ z u, |F z u - G z u| ≤ 2 * cnt z := by
    intro z u
    by_cases hall : ∀ j ∈ S, z j ∉ A
    · have : F z u = G z u := by simp only [hF, hG, repS_eq_of_notMem hall]
      rw [this, sub_self, abs_zero]; exact mul_nonneg (by norm_num) (hcnt0 z)
    · push Not at hall
      obtain ⟨j, hjS, hjA⟩ := hall
      have h1 : 1 ≤ cnt z := by
        have := Finset.single_le_sum (f := fun j => A.indicator (fun _ => (1:ℝ)) (z j))
          (fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) hjS
        simp only [Set.indicator_of_mem hjA] at this
        exact this
      calc |F z u - G z u| ≤ |F z u| + |G z u| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (hFb z u) (hGb z u)
        _ ≤ 2 * cnt z := by linarith
  -- the difference of the two integrals
  have hintFx₀ : Integrable (fun z => F z x₀) π :=
    integrable_of_abs_le (hFm.comp (measurable_id.prodMk measurable_const)) 1 fun z => hFb z x₀
  have hintFA : Integrable (fun z => ∫ s in A, F z s ∂unitμ) π := by
    refine integrable_of_abs_le ?_ 1 fun z => ?_
    · exact (hFm.stronglyMeasurable.integral_prod_right' (ν := unitμ.restrict A)).measurable
    · have := norm_integral_le_of_norm_le_const (μ := unitμ.restrict A) (f := fun s => F z s) (C := 1)
        (Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hFb z s)
      have hle : (unitμ.restrict A).real univ ≤ 1 := by
        simp only [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (prob_le_one : unitμ A ≤ 1))
      rw [Real.norm_eq_abs] at this
      linarith [mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 1)]
  have hintF : Integrable (fun z => ∫ s, F z s ∂unitμ) π := by
    refine integrable_of_abs_le (hFm.stronglyMeasurable.integral_prod_right').measurable 1 fun z => ?_
    have := norm_integral_le_of_norm_le_const (μ := unitμ) (f := fun s => F z s) (C := 1)
      (Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hFb z s)
    simpa [Real.norm_eq_abs, measureReal_def] using this
  have hdiff : ∫ z, kProd H κ hs (repS (insert k S) A x₀ z) ∂π - ∫ z, kProd H κ hs (repS S A x₀ z) ∂π
      = h * ∫ z, F z x₀ ∂π - ∫ z, (∫ s in A, F z s ∂unitμ) ∂π := by
    rw [hI1, hI2, integral_congr_ae (Filter.Eventually.of_forall hinner)]
    rw [integral_sub (f := fun z => h * F z x₀ + ∫ s, F z s ∂unitμ)
      (g := fun z => ∫ s in A, F z s ∂unitμ) ((hintFx₀.const_mul h).add hintF) hintFA,
      integral_add (f := fun z => h * F z x₀) (g := fun z => ∫ s, F z s ∂unitμ)
        (hintFx₀.const_mul h) hintF, integral_const_mul]
    ring
  rw [hdiff]
  -- compare with the rooted densities
  have hT : ∀ u, rootedK H hs k u = ∫ z, G z u ∂π := fun u => rfl
  have hcntabs : ∀ z, |cnt z| ≤ S.card := fun z => by rw [abs_of_nonneg (hcnt0 z)]; exact hcntb z
  have hint_cnt : Integrable cnt π := integrable_of_abs_le hcntm S.card hcntabs
  have hA1 : |h * ∫ z, F z x₀ ∂π - h * rootedK H hs k x₀| ≤ h * (2 * (S.card * h)) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hh0, hT]
    apply mul_le_mul_of_nonneg_left _ hh0
    have hintG : Integrable (fun z => G z x₀) π :=
      integrable_of_abs_le (hGm.comp (measurable_id.prodMk measurable_const)) 1 fun z => hGb z x₀
    rw [← integral_sub hintFx₀ hintG]
    calc |∫ z, (F z x₀ - G z x₀) ∂π| ≤ ∫ z, |F z x₀ - G z x₀| ∂π := abs_integral_le_integral_abs
      _ ≤ ∫ z, 2 * cnt z ∂π := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => abs_nonneg _) (hint_cnt.const_mul 2)
          (Filter.Eventually.of_forall fun z => hFG z x₀)
      _ = 2 * (S.card * h) := by rw [integral_const_mul, hcntint]
  have hA2 : |∫ z, (∫ s in A, F z s ∂unitμ) ∂π - ∫ s in A, rootedK H hs k s ∂unitμ|
      ≤ h * (2 * (S.card * h)) := by
    have hswap : ∫ s in A, rootedK H hs k s ∂unitμ = ∫ z, (∫ s in A, G z s ∂unitμ) ∂π := by
      simp only [hT]
      have hint : Integrable (Function.uncurry fun z s => G z s) (π.prod (unitμ.restrict A)) :=
        integrable_of_abs_le hGm 1 fun p => hGb p.1 p.2
      exact (integral_integral_swap hint).symm
    rw [hswap]
    have hintGA : Integrable (fun z => ∫ s in A, G z s ∂unitμ) π := by
      refine integrable_of_abs_le (hGm.stronglyMeasurable.integral_prod_right' (ν := unitμ.restrict A)).measurable 1
        fun z => ?_
      have := norm_integral_le_of_norm_le_const (μ := unitμ.restrict A) (f := fun s => G z s) (C := 1)
        (Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hGb z s)
      have hle : (unitμ.restrict A).real univ ≤ 1 := by
        simp only [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (prob_le_one : unitμ A ≤ 1))
      rw [Real.norm_eq_abs] at this
      linarith [mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 1)]
    rw [← integral_sub hintFA hintGA]
    have hpt : ∀ z, |∫ s in A, F z s ∂unitμ - ∫ s in A, G z s ∂unitμ| ≤ h * (2 * cnt z) := by
      intro z
      have hiF : Integrable (fun s => F z s) (unitμ.restrict A) :=
        integrable_of_abs_le (hFmz z) 1 (hFb z)
      have hiG : Integrable (fun s => G z s) (unitμ.restrict A) :=
        integrable_of_abs_le (hGm.comp (measurable_const.prodMk measurable_id)) 1 (hGb z)
      rw [← integral_sub hiF hiG]
      have := norm_integral_le_of_norm_le_const (μ := unitμ.restrict A) (f := fun s => F z s - G z s)
        (C := 2 * cnt z) (Filter.Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs]; exact hFG z s)
      have hreal : (unitμ.restrict A).real univ = h := by
        simp only [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter, hh]
      rw [Real.norm_eq_abs, hreal] at this
      linarith
    calc |∫ z, (∫ s in A, F z s ∂unitμ - ∫ s in A, G z s ∂unitμ) ∂π|
        ≤ ∫ z, |∫ s in A, F z s ∂unitμ - ∫ s in A, G z s ∂unitμ| ∂π := abs_integral_le_integral_abs
      _ ≤ ∫ z, h * (2 * cnt z) ∂π := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => abs_nonneg _) ((hint_cnt.const_mul 2).const_mul h)
          (Filter.Eventually.of_forall hpt)
      _ = h * (2 * (S.card * h)) := by rw [integral_const_mul, integral_const_mul, hcntint]
  have e1 : h * ∫ z, F z x₀ ∂π - ∫ z, (∫ s in A, F z s ∂unitμ) ∂π
      - (h * rootedK H hs k x₀ - ∫ s in A, rootedK H hs k s ∂unitμ)
      = (h * ∫ z, F z x₀ ∂π - h * rootedK H hs k x₀)
        - (∫ z, (∫ s in A, F z s ∂unitμ) ∂π - ∫ s in A, rootedK H hs k s ∂unitμ) := by ring
  rw [e1]
  calc _ ≤ |h * ∫ z, F z x₀ ∂π - h * rootedK H hs k x₀|
        + |∫ z, (∫ s in A, F z s ∂unitμ) ∂π - ∫ s in A, rootedK H hs k s ∂unitμ| := abs_sub _ _
    _ ≤ h * (2 * (S.card * h)) + h * (2 * (S.card * h)) := add_le_add hA1 hA2
    _ = 4 * S.card * h ^ 2 := by ring

/-- **The replacement of the coordinates in `S`.** -/
theorem abs_replace_finset (hm : Measurable fun p : ℝ × ℝ => κ p.1 p.2) (hb : ∀ x y, |κ x y| ≤ 1)
    {A : Set ℝ} (hA : MeasurableSet A) (x₀ : ℝ) (S : Finset V) :
    |∫ z, kProd H κ hs (repS S A x₀ z) ∂(Measure.pi fun _ : V => unitμ)
        - ∫ z, kProd H κ hs z ∂(Measure.pi fun _ : V => unitμ)
        - ∑ i ∈ S, ((unitμ A).toReal * rootedK H hs i x₀ - ∫ s in A, rootedK H hs i s ∂unitμ)|
      ≤ 2 * S.card ^ 2 * (unitμ A).toReal ^ 2 := by
  induction S using Finset.induction_on with
  | empty => simp [repS_empty]
  | insert k S hk ih =>
    have hstep := abs_replace_step H hs hm hb hA x₀ hk
    rw [Finset.sum_insert hk, Finset.card_insert_of_notMem hk]
    set a1 := ∫ z, kProd H κ hs (repS (insert k S) A x₀ z) ∂(Measure.pi fun _ : V => unitμ)
    set a2 := ∫ z, kProd H κ hs (repS S A x₀ z) ∂(Measure.pi fun _ : V => unitμ)
    set a3 := ∫ z, kProd H κ hs z ∂(Measure.pi fun _ : V => unitμ)
    set tk := (unitμ A).toReal * rootedK H hs k x₀ - ∫ s in A, rootedK H hs k s ∂unitμ
    set tS := ∑ i ∈ S, ((unitμ A).toReal * rootedK H hs i x₀ - ∫ s in A, rootedK H hs i s ∂unitμ)
    have e : a1 - a3 - (tk + tS) = ((a1 - a2) - tk) + (a2 - a3 - tS) := by ring
    rw [e]
    have h0 : (0:ℝ) ≤ (unitμ A).toReal ^ 2 := sq_nonneg _
    calc |((a1 - a2) - tk) + (a2 - a3 - tS)| ≤ |(a1 - a2) - tk| + |a2 - a3 - tS| := abs_add_le _ _
      _ ≤ 4 * S.card * (unitμ A).toReal ^ 2 + 2 * S.card ^ 2 * (unitμ A).toReal ^ 2 :=
          add_le_add hstep ih
      _ ≤ 2 * ((S.card : ℕ) + 1 : ℕ) ^ 2 * (unitμ A).toReal ^ 2 := by
          push_cast
          nlinarith [h0]

/-- **The first-order expansion of row replacement.** -/
theorem abs_integral_kProd_rowRep_sub_le (hm : Measurable fun p : ℝ × ℝ => κ p.1 p.2)
    (hb : ∀ x y, |κ x y| ≤ 1) {A : Set ℝ} (hA : MeasurableSet A) (x₀ : ℝ) :
    |∫ z, kProd H κ hs (fun j => rowRep A x₀ (z j)) ∂(Measure.pi fun _ : V => unitμ)
        - ∫ z, kProd H κ hs z ∂(Measure.pi fun _ : V => unitμ)
        - ∑ i, ((unitμ A).toReal * rootedK H hs i x₀ - ∫ s in A, rootedK H hs i s ∂unitμ)|
      ≤ 2 * (Fintype.card V) ^ 2 * (unitμ A).toReal ^ 2 := by
  have h := abs_replace_finset H hs hm hb hA x₀ Finset.univ
  have hrep : ∀ z : V → ℝ, repS Finset.univ A x₀ z = fun j => rowRep A x₀ (z j) := fun z => by
    funext j; simp [repS]
  simp only [hrep, Finset.card_univ] at h
  exact h

end Replacement

/-! ### Two-vertex specialization -/

theorem edgeFinset_top_fin_two : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by decide

theorem kProd_top_fin_two {κ : ℝ → ℝ → ℝ} (hs : ∀ x y, κ x y = κ y x) (z : Fin 2 → ℝ) :
    kProd (⊤ : SimpleGraph (Fin 2)) κ hs z = κ (z 0) (z 1) := by
  unfold kProd
  rw [edgeFinset_top_fin_two, Finset.prod_singleton]
  rfl

theorem integral_kProd_top_fin_two {κ : ℝ → ℝ → ℝ} (hs : ∀ x y, κ x y = κ y x)
    (hm : Measurable fun p : ℝ × ℝ => κ p.1 p.2) :
    ∫ z : Fin 2 → ℝ, kProd (⊤ : SimpleGraph (Fin 2)) κ hs z ∂(Measure.pi fun _ => unitμ)
      = ∫ p : ℝ × ℝ, κ p.1 p.2 ∂gμ := by
  simp only [kProd_top_fin_two]
  have hmp := measurePreserving_pair (V := Fin 2) (a := 0) (b := 1) (by decide)
  have h1 := integral_map (μ := Measure.pi fun _ : Fin 2 => unitμ) hmp.measurable.aemeasurable
    (hm.aestronglyMeasurable (μ := Measure.map (fun z : Fin 2 → ℝ => (z 0, z 1))
      (Measure.pi fun _ : Fin 2 => unitμ)))
  rw [hmp.map_eq] at h1
  exact h1.symm

theorem rootedK_top_fin_two {κ : ℝ → ℝ → ℝ} (hs : ∀ x y, κ x y = κ y x)
    (hm : Measurable fun p : ℝ × ℝ => κ p.1 p.2) (i : Fin 2) (u : ℝ) :
    rootedK (⊤ : SimpleGraph (Fin 2)) hs i u = ∫ t, κ u t ∂unitμ := by
  unfold rootedK
  simp only [kProd_top_fin_two]
  have hmr : Measurable fun t => κ u t := hm.comp (measurable_const.prodMk measurable_id)
  fin_cases i
  · have : ∀ z : Fin 2 → ℝ, κ (Function.update z 0 u 0) (Function.update z 0 u 1) = κ u (z 1) :=
      fun z => by simp
    simp only [Fin.zero_eta, this]
    exact integral_pi_eval_comp (V := Fin 2) 1 hmr
  · have : ∀ z : Fin 2 → ℝ, κ (Function.update z 1 u 0) (Function.update z 1 u 1) = κ u (z 0) :=
      fun z => by simp [hs]
    simp only [Fin.mk_one, this]
    exact integral_pi_eval_comp (V := Fin 2) 0 hmr

/-! ### The replaced graphon -/

theorem abs_S0_le_one {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) : |S0 u| ≤ 1 := by
  rw [S0_eq_binEntropy_half]
  have h0 := Real.binEntropy_nonneg hu.1 hu.2
  have h1 := Real.binEntropy_le_log_two (p := u)
  have h2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  rw [abs_of_nonneg (by linarith)]
  linarith

namespace Graphon

/-- `W^A(x,y) = W(π_A x, π_A y)`: the rows and columns indexed by `A` replaced by those of `x₀`. -/
noncomputable def rowReplace (W : Graphon) {A : Set ℝ} (hA : MeasurableSet A) (x₀ : ℝ) : Graphon where
  toFun x y := W.toFun (rowRep A x₀ x) (rowRep A x₀ y)
  symm' _ _ := W.symm' _ _
  meas' := W.measurable_uncurry.comp ((measurable_rowRep hA x₀).prodMap (measurable_rowRep hA x₀))
  nonneg' _ _ := W.nonneg' _ _
  le_one' _ _ := W.le_one' _ _

theorem rowReplace_apply (W : Graphon) {A : Set ℝ} (hA : MeasurableSet A) (x₀ x y : ℝ) :
    (W.rowReplace hA x₀).toFun x y = W.toFun (rowRep A x₀ x) (rowRep A x₀ y) := rfl

/-- The row entropy `σ_W(u) = ∫ S₀(W(u,t)) dt`. -/
noncomputable def rowEnt (W : Graphon) (u : ℝ) : ℝ := ∫ t, S0 (W.toFun u t) ∂unitμ

theorem measurable_S0W (W : Graphon) : Measurable fun p : ℝ × ℝ => S0 (W.toFun p.1 p.2) :=
  continuous_S0.measurable.comp W.measurable_uncurry

theorem abs_S0W_le (W : Graphon) (x y : ℝ) : |S0 (W.toFun x y)| ≤ 1 := abs_S0_le_one (W.mem_Icc x y)

theorem abs_toFun_le (W : Graphon) (x y : ℝ) : |W.toFun x y| ≤ 1 := by
  rw [abs_of_nonneg (W.mem_Icc x y).1]; exact (W.mem_Icc x y).2

/-- **The edge density under row replacement.** -/
theorem abs_edgeDensity_rowReplace_sub_le (W : Graphon) {A : Set ℝ} (hA : MeasurableSet A) (x₀ : ℝ) :
    |(W.rowReplace hA x₀).edgeDensity - W.edgeDensity
        - 2 * ((unitμ A).toReal * W.degFun x₀ - ∫ s in A, W.degFun s ∂unitμ)| ≤
      8 * (unitμ A).toReal ^ 2 := by
  have h := abs_integral_kProd_rowRep_sub_le (⊤ : SimpleGraph (Fin 2)) W.symm' W.measurable_uncurry
    W.abs_toFun_le hA x₀
  have hm' : Measurable fun p : ℝ × ℝ => (W.rowReplace hA x₀).toFun p.1 p.2 :=
    (W.rowReplace hA x₀).measurable_uncurry
  have e1 : ∫ z : Fin 2 → ℝ, kProd (⊤ : SimpleGraph (Fin 2)) W.toFun W.symm'
      (fun j => rowRep A x₀ (z j)) ∂(Measure.pi fun _ => unitμ)
      = (W.rowReplace hA x₀).edgeDensity := by
    have := integral_kProd_top_fin_two (W.rowReplace hA x₀).symm' hm'
    show _ = ∫ p : ℝ × ℝ, (W.rowReplace hA x₀).toFun p.1 p.2 ∂gμ
    rw [← this]
    rfl
  have e2 : ∫ z : Fin 2 → ℝ, kProd (⊤ : SimpleGraph (Fin 2)) W.toFun W.symm' z
      ∂(Measure.pi fun _ => unitμ) = W.edgeDensity :=
    integral_kProd_top_fin_two W.symm' W.measurable_uncurry
  have e3 : ∀ i : Fin 2, rootedK (⊤ : SimpleGraph (Fin 2)) W.symm' i = W.degFun := fun i => by
    funext u; rw [rootedK_top_fin_two W.symm' W.measurable_uncurry]; rfl
  simp only [e1, e2, e3, Fin.sum_univ_two, Fintype.card_fin] at h
  have e4 : 2 * ((unitμ A).toReal * W.degFun x₀ - ∫ s in A, W.degFun s ∂unitμ)
      = ((unitμ A).toReal * W.degFun x₀ - ∫ s in A, W.degFun s ∂unitμ)
        + ((unitμ A).toReal * W.degFun x₀ - ∫ s in A, W.degFun s ∂unitμ) := by ring
  rw [e4]
  norm_num at h
  linarith [h]

/-- **The entropy under row replacement.** -/
theorem abs_entropy_rowReplace_sub_le (W : Graphon) {A : Set ℝ} (hA : MeasurableSet A) (x₀ : ℝ) :
    |(W.rowReplace hA x₀).entropy - W.entropy
        - 2 * ((unitμ A).toReal * W.rowEnt x₀ - ∫ s in A, W.rowEnt s ∂unitμ)| ≤
      8 * (unitμ A).toReal ^ 2 := by
  have hs : ∀ x y, S0 (W.toFun x y) = S0 (W.toFun y x) := fun x y => by rw [W.symm']
  have h := abs_integral_kProd_rowRep_sub_le (⊤ : SimpleGraph (Fin 2)) hs W.measurable_S0W
    W.abs_S0W_le hA x₀
  have hs' : ∀ x y, S0 ((W.rowReplace hA x₀).toFun x y) = S0 ((W.rowReplace hA x₀).toFun y x) :=
    fun x y => by rw [(W.rowReplace hA x₀).symm']
  have e1 : ∫ z : Fin 2 → ℝ, kProd (⊤ : SimpleGraph (Fin 2)) (fun x y => S0 (W.toFun x y)) hs
      (fun j => rowRep A x₀ (z j)) ∂(Measure.pi fun _ => unitμ)
      = (W.rowReplace hA x₀).entropy := by
    have := integral_kProd_top_fin_two hs' (W.rowReplace hA x₀).measurable_S0W
    rw [entropy_eq_integral_S0]
    show _ = ∫ p : ℝ × ℝ, S0 ((W.rowReplace hA x₀).toFun p.1 p.2) ∂gμ
    rw [← this]
    rfl
  have e2 : ∫ z : Fin 2 → ℝ, kProd (⊤ : SimpleGraph (Fin 2)) (fun x y => S0 (W.toFun x y)) hs z
      ∂(Measure.pi fun _ => unitμ) = W.entropy := by
    rw [entropy_eq_integral_S0]
    exact integral_kProd_top_fin_two hs W.measurable_S0W
  have e3 : ∀ i : Fin 2, rootedK (⊤ : SimpleGraph (Fin 2)) hs i = W.rowEnt := fun i => by
    funext u; rw [rootedK_top_fin_two hs W.measurable_S0W]; rfl
  simp only [e1, e2, e3, Fin.sum_univ_two, Fintype.card_fin] at h
  have e4 : 2 * ((unitμ A).toReal * W.rowEnt x₀ - ∫ s in A, W.rowEnt s ∂unitμ)
      = ((unitμ A).toReal * W.rowEnt x₀ - ∫ s in A, W.rowEnt s ∂unitμ)
        + ((unitμ A).toReal * W.rowEnt x₀ - ∫ s in A, W.rowEnt s ∂unitμ) := by ring
  rw [e4]
  norm_num at h
  linarith [h]

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- **The `H`-density under row replacement.** -/
theorem abs_tDensity_rowReplace_sub_le (W : Graphon) {A : Set ℝ} (hA : MeasurableSet A) (x₀ : ℝ) :
    |(W.rowReplace hA x₀).tDensity H - W.tDensity H
        - ∑ i, ((unitμ A).toReal * rootedK H W.symm' i x₀ - ∫ s in A, rootedK H W.symm' i s ∂unitμ)| ≤
      2 * (Fintype.card V) ^ 2 * (unitμ A).toReal ^ 2 :=
  abs_integral_kProd_rowRep_sub_le H W.symm' W.measurable_uncurry W.abs_toFun_le hA x₀

end Graphon

end UpperTailOptimizers
