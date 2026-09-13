import UpperTailOptimizers.Bipodality.RowBalance

/-!
# Pointwise structure of maximizers

For a maximizer with Euler–Lagrange multipliers `(α, β)`, the Euler–Lagrange equation on a single
row and the one-row factorization of `Γ_W` show that every row is `L¹`-close to the constant

  `w(x) = λ(α + β γ(d_W(x)))`,   `γ(u) = m ε^{m-d} u^{d-1}`,   `λ = (S₀')⁻¹`,

with an error `|β| m² ‖W - ε‖₁`.  Evaluating the row functional `Φ` of the row balance on such a
row gives `Φ(x) ≈ φ(w(x))` with `φ(u) = 2S₀(u) - 2αu - βvε^{m-d}u^d`, and at the limiting
multipliers `φ = φ(ε) - Γ^gap` exactly.  Row balance then forces `Γ^gap(w(x))` to be small for
almost every `x` (draft `kb:prop:pointwise`).

## Contents

* `Graphon.abs_rootedK_sub_row_le` — the one-row factorization of rooted densities;
* `dS0` / `S0` comparison lemmas;
* `Graphon.integral_abs_sub_rowVal_le`, `Graphon.abs_balFun_sub_phiFun_le`;
* `phiFun_limit_eq`, `gapFun_le_sq`;
* `QualDirs.ae_gapFun_rowVal_le`.
-/

set_option linter.unusedSectionVars false

namespace UpperTailOptimizers

open MeasureTheory Set SingularEndpoint

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-! ### Rooted densities through one row -/

namespace Graphon

theorem kProd_eq_prod_gEdge (W : Graphon) (z : V → ℝ) :
    kProd H W.toFun W.symm' z = ∏ e ∈ H.edgeFinset, W.gEdge z e := rfl

set_option maxHeartbeats 1000000 in
/-- **The one-row factorization of a rooted density**:
`|T_i(u) - ε^{m-d} d_W(u)^d| ≤ m ‖W - ε‖₁`. -/
theorem abs_rootedK_sub_row_le (W : Graphon) {d : ℕ} (hreg : ∀ v, H.degree v = d) {ε : ℝ}
    (hε : ε ∈ Icc (0:ℝ) 1) (i : V) (u : ℝ) :
    |rootedK H W.symm' i u - ε ^ (H.edgeFinset.card - d) * W.degFun u ^ d|
      ≤ H.edgeFinset.card * W.constDist ε := by
  classical
  set π : Measure (V → ℝ) := Measure.pi fun _ : V => unitμ with hπ
  set ℓ : (V → ℝ) → (V → ℝ) := fun z => Function.update z i u with hℓ
  have hℓm : Measurable ℓ := (measurable_update' (a := i)).comp (measurable_id.prodMk measurable_const)
  set g : Sym2 V → (V → ℝ) → ℝ := fun e z => if i ∈ e then W.gEdge (ℓ z) e else ε with hg
  have hgmem : ∀ e z, g e z ∈ Icc (0:ℝ) 1 := fun e z => by
    simp only [hg]; split_ifs
    · exact W.gEdge_mem_Icc _ e
    · exact hε
  have hgm : ∀ e, Measurable fun z => g e z := fun e => by
    simp only [hg]; split_ifs
    · exact (W.measurable_gEdge e).comp hℓm
    · exact measurable_const
  have hpt : ∀ z, |∏ e ∈ H.edgeFinset, W.gEdge (ℓ z) e - ∏ e ∈ H.edgeFinset, g e z|
      ≤ ∑ e ∈ H.edgeFinset.filter (fun e => i ∉ e), |W.gEdge (ℓ z) e - ε| := by
    intro z
    refine le_trans (abs_prod_sub_prod_le_sum H.edgeFinset _ _ (fun e _ => W.gEdge_mem_Icc _ e)
      (fun e _ => hgmem e z)) (le_of_eq ?_)
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : i ∈ e <;> simp [hg, h]
  have hterm : ∀ e ∈ H.edgeFinset.filter (fun e => i ∉ e), ∫ z, |W.gEdge (ℓ z) e - ε| ∂π = W.constDist ε := by
    intro e he
    have hie := (Finset.mem_filter.mp he).2
    have heE : e ∈ H.edgeFinset := (Finset.mem_filter.mp he).1
    revert heE hie
    induction e using Sym2.ind with
    | _ p q =>
      intro hie heE
      have hpq : p ≠ q := H.ne_of_adj (SimpleGraph.mem_edgeFinset.mp heE)
      rw [Sym2.mem_iff] at hie
      push Not at hie
      have hpi : p ≠ i := Ne.symm hie.1
      have hqi : q ≠ i := Ne.symm hie.2
      have hval : ∀ z, |W.gEdge (ℓ z) s(p, q) - ε| = |W.toFun (z p) (z q) - ε| := fun z => by
        simp only [hℓ, gEdge_mk, Function.update_of_ne hpi, Function.update_of_ne hqi]
      rw [integral_congr_ae (Filter.Eventually.of_forall hval)]
      have hmp := measurePreserving_pair (V := V) hpq
      have hmeas : Measurable fun w : ℝ × ℝ => |W.toFun w.1 w.2 - ε| :=
        (W.measurable_uncurry.sub measurable_const).abs
      have h1 := integral_map (μ := π) hmp.measurable.aemeasurable
        (hmeas.aestronglyMeasurable (μ := Measure.map (fun z : V → ℝ => (z p, z q)) π))
      rw [hmp.map_eq] at h1
      exact h1.symm
  have hTa : H.edgeFinset.filter (fun e => i ∈ e) = (H.neighborFinset i).image (fun k => s(i, k)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_edgeFinset]
    constructor
    · rintro ⟨he, hie⟩
      refine ⟨Sym2.Mem.other hie, ?_, Sym2.other_spec hie⟩
      have hspec := Sym2.other_spec hie
      rw [← hspec] at he
      exact he
    · rintro ⟨k, hik, rfl⟩
      exact ⟨hik, Sym2.mem_mk_left i k⟩
  have hinj : Set.InjOn (fun k => s(i, k)) (H.neighborFinset i : Set V) :=
    fun k₁ _ k₂ _ h => Sym2.congr_right.mp h
  have hcardTa : (H.edgeFinset.filter (fun e => i ∈ e)).card = d := by
    rw [hTa, Finset.card_image_of_injOn hinj, SimpleGraph.card_neighborFinset_eq_degree, hreg]
  have hcardTn : (H.edgeFinset.filter (fun e => i ∉ e)).card = H.edgeFinset.card - d := by
    have h := Finset.card_filter_add_card_filter_not (s := H.edgeFinset) (p := fun e => i ∈ e)
    rw [hcardTa] at h
    omega
  have hprodg : ∀ z, ∏ e ∈ H.edgeFinset, g e z
      = ε ^ (H.edgeFinset.card - d) * ∏ k ∈ H.neighborFinset i, W.toFun u (z k) := by
    intro z
    rw [← Finset.prod_filter_mul_prod_filter_not H.edgeFinset (fun e => i ∈ e)]
    have h1 : ∏ e ∈ H.edgeFinset.filter (fun e => i ∈ e), g e z = ∏ k ∈ H.neighborFinset i, W.toFun u (z k) := by
      rw [hTa, Finset.prod_image hinj]
      refine Finset.prod_congr rfl fun k hk => ?_
      have hki : k ≠ i := fun h => by
        have := (SimpleGraph.mem_neighborFinset H i k).mp hk
        rw [h] at this; exact H.ne_of_adj this rfl
      simp only [hg, Sym2.mem_mk_left, if_true, hℓ, gEdge_mk, Function.update_self,
        Function.update_of_ne hki]
    have h2 : ∏ e ∈ H.edgeFinset.filter (fun e => i ∉ e), g e z = ε ^ (H.edgeFinset.card - d) := by
      rw [Finset.prod_congr rfl (g := fun _ => ε) (fun e he => by
        simp only [hg, if_neg (Finset.mem_filter.mp he).2]), Finset.prod_const, hcardTn]
    rw [h1, h2, mul_comm]
  have hintg : ∫ z, ∏ e ∈ H.edgeFinset, g e z ∂π = ε ^ (H.edgeFinset.card - d) * W.degFun u ^ d := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hprodg), integral_const_mul]
    congr 1
    have h := integral_prod_coord (H.neighborFinset i) (fun t => W.toFun u t)
    rw [h, SimpleGraph.card_neighborFinset_eq_degree, hreg]
    rfl
  have hint1 : Integrable (fun z => ∏ e ∈ H.edgeFinset, W.gEdge (ℓ z) e) π :=
    integrable_of_abs_le ((W.measurable_prod_gEdge H.edgeFinset).comp hℓm) 1 fun z => by
      rw [abs_of_nonneg (W.prod_gEdge_mem_Icc _ _).1]; exact (W.prod_gEdge_mem_Icc _ _).2
  have hint2 : Integrable (fun z => ∏ e ∈ H.edgeFinset, g e z) π :=
    integrable_of_abs_le (Finset.measurable_prod _ fun e _ => hgm e) 1 fun z => by
      have hmem : ∏ e ∈ H.edgeFinset, g e z ∈ Icc (0:ℝ) 1 :=
        ⟨Finset.prod_nonneg fun e _ => (hgmem e z).1,
          Finset.prod_le_one (fun e _ => (hgmem e z).1) fun e _ => (hgmem e z).2⟩
      rw [abs_of_nonneg hmem.1]; exact hmem.2
  have hintterm : ∀ e ∈ H.edgeFinset.filter (fun e => i ∉ e),
      Integrable (fun z => |W.gEdge (ℓ z) e - ε|) π := fun e _ =>
    integrable_of_abs_le (((W.measurable_gEdge e).comp hℓm).sub measurable_const).abs 1 fun z => by
      rw [abs_abs]
      have := W.gEdge_mem_Icc (ℓ z) e
      rw [abs_le]; constructor <;> linarith [this.1, this.2, hε.1, hε.2]
  have hrooted : rootedK H W.symm' i u = ∫ z, ∏ e ∈ H.edgeFinset, W.gEdge (ℓ z) e ∂π := rfl
  rw [hrooted, ← hintg, ← integral_sub hint1 hint2]
  calc |∫ z, (∏ e ∈ H.edgeFinset, W.gEdge (ℓ z) e - ∏ e ∈ H.edgeFinset, g e z) ∂π|
      ≤ ∫ z, |∏ e ∈ H.edgeFinset, W.gEdge (ℓ z) e - ∏ e ∈ H.edgeFinset, g e z| ∂π := abs_integral_le_integral_abs
    _ ≤ ∫ z, ∑ e ∈ H.edgeFinset.filter (fun e => i ∉ e), |W.gEdge (ℓ z) e - ε| ∂π :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
          (integrable_finsetSum _ hintterm) (Filter.Eventually.of_forall hpt)
    _ = ∑ e ∈ H.edgeFinset.filter (fun e => i ∉ e), ∫ z, |W.gEdge (ℓ z) e - ε| ∂π :=
        integral_finsetSum _ hintterm
    _ = ((H.edgeFinset.filter (fun e => i ∉ e)).card : ℝ) * W.constDist ε := by
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    _ ≤ H.edgeFinset.card * W.constDist ε := by
        apply mul_le_mul_of_nonneg_right _ (W.constDist_nonneg ε)
        rw [hcardTn]; exact_mod_cast Nat.sub_le _ _

end Graphon

/-! ### Comparison lemmas for `S₀` and `S₀'` -/

theorem dS0_antitoneOn : AntitoneOn dS0 (Ioo (0:ℝ) 1) := by
  intro a ha b hb hab
  unfold dS0
  have h1 : Real.log (1 - b) ≤ Real.log (1 - a) :=
    Real.log_le_log (by linarith [hb.2]) (by linarith)
  have h2 : Real.log a ≤ Real.log b := Real.log_le_log ha.1 hab
  linarith

/-- The mean value theorem for `S₀'`: `b - a = 2ξ(1-ξ) (S₀'(a) - S₀'(b))`. -/
theorem exists_dS0_mvt {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ ξ ∈ Ioo a b, b - a = 2 * (ξ * (1 - ξ)) * (dS0 a - dS0 b) := by
  have hcont : ContinuousOn dS0 (Icc a b) := fun t ht =>
    (hasDerivAt_dS0 (by linarith [ht.1]) (by linarith [ht.2])).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hder⟩ := exists_hasDerivAt_eq_slope dS0 (fun t => -1 / (2 * (t * (1 - t)))) hab hcont
    (fun t ht => hasDerivAt_dS0 (by linarith [ht.1]) (by linarith [ht.2]))
  refine ⟨ξ, hξ, ?_⟩
  have hξ0 : 0 < ξ := by linarith [hξ.1]
  have hξ1 : 0 < 1 - ξ := by linarith [hξ.2]
  have hba : b - a ≠ 0 := by linarith
  rw [eq_div_iff hba] at hder
  field_simp at hder
  linarith

/-- `|a - b| ≤ 2 (c(1-c) + |a-c| + |b-c|) |S₀'(a) - S₀'(b)|` on `(0,1)`, for `c ∈ [0,1]`. -/
theorem abs_sub_le_mul_abs_dS0_sub {a b c : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) (hb : b ∈ Ioo (0:ℝ) 1)
    (hc : c ∈ Icc (0:ℝ) 1) :
    |a - b| ≤ 2 * (c * (1 - c) + |a - c| + |b - c|) * |dS0 a - dS0 b| := by
  have hkey : ∀ {p q : ℝ}, p ∈ Ioo (0:ℝ) 1 → q ∈ Ioo (0:ℝ) 1 → p < q →
      |p - q| ≤ 2 * (c * (1 - c) + |p - c| + |q - c|) * |dS0 p - dS0 q| := by
    intro p q hp hq hpq
    obtain ⟨ξ, hξ, heq⟩ := exists_dS0_mvt hp.1 hpq hq.2
    have hd : 0 ≤ dS0 p - dS0 q := sub_nonneg.mpr (dS0_antitoneOn hp hq hpq.le)
    have hξc : |ξ - c| ≤ |p - c| + |q - c| := by
      rw [abs_le]; constructor
      · have h1 := neg_abs_le (p - c)
        have h2 := abs_nonneg (q - c)
        linarith [hξ.1]
      · have h1 := le_abs_self (q - c)
        have h2 := abs_nonneg (p - c)
        linarith [hξ.2]
    have hξ' : ξ * (1 - ξ) ≤ c * (1 - c) + |ξ - c| := by
      have e : ξ * (1 - ξ) - c * (1 - c) = (ξ - c) * (1 - ξ - c) := by ring
      have h1 : |1 - ξ - c| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2, hp.1, hq.2, hc.1, hc.2]
      have h2 : (ξ - c) * (1 - ξ - c) ≤ |ξ - c| := by
        calc (ξ - c) * (1 - ξ - c) ≤ |(ξ - c) * (1 - ξ - c)| := le_abs_self _
          _ = |ξ - c| * |1 - ξ - c| := abs_mul _ _
          _ ≤ |ξ - c| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ = |ξ - c| := mul_one _
      linarith
    rw [abs_sub_comm, abs_of_pos (by linarith), heq, abs_of_nonneg hd]
    have hξpos : 0 ≤ ξ * (1 - ξ) := mul_nonneg (by linarith [hξ.1, hp.1]) (by linarith [hξ.2, hq.2])
    apply mul_le_mul_of_nonneg_right _ hd
    linarith
  rcases lt_trichotomy a b with h | h | h
  · exact hkey ha hb h
  · subst h; simp
  · have := hkey hb ha h
    rw [abs_sub_comm b a, abs_sub_comm (dS0 b) (dS0 a)] at this
    linarith

/-- `2|a - b| ≤ |S₀'(a) - S₀'(b)|` on `(0,1)`. -/
theorem two_mul_abs_sub_le_abs_dS0_sub {a b : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) (hb : b ∈ Ioo (0:ℝ) 1) :
    2 * |a - b| ≤ |dS0 a - dS0 b| := by
  have hkey : ∀ {p q : ℝ}, p ∈ Ioo (0:ℝ) 1 → q ∈ Ioo (0:ℝ) 1 → p < q →
      2 * |p - q| ≤ |dS0 p - dS0 q| := by
    intro p q hp hq hpq
    obtain ⟨ξ, hξ, heq⟩ := exists_dS0_mvt hp.1 hpq hq.2
    have hd : 0 ≤ dS0 p - dS0 q := sub_nonneg.mpr (dS0_antitoneOn hp hq hpq.le)
    have hξ' : ξ * (1 - ξ) ≤ 1 / 4 := by nlinarith [sq_nonneg (ξ - 1 / 2)]
    rw [abs_sub_comm, abs_of_pos (by linarith), heq, abs_of_nonneg hd]
    have hξpos : 0 ≤ ξ * (1 - ξ) := mul_nonneg (by linarith [hξ.1, hp.1]) (by linarith [hξ.2, hq.2])
    nlinarith
  rcases lt_trichotomy a b with h | h | h
  · exact hkey ha hb h
  · subst h; simp
  · have := hkey hb ha h
    rw [abs_sub_comm b a, abs_sub_comm (dS0 b) (dS0 a)] at this
    exact this

/-- `|λ(p) - λ(q)| ≤ |p - q| / 2`. -/
theorem abs_logistic_sub_le (p q : ℝ) : |logistic p - logistic q| ≤ |p - q| / 2 := by
  have h := two_mul_abs_sub_le_abs_dS0_sub (logistic_mem p) (logistic_mem q)
  rw [dS0_logistic, dS0_logistic] at h
  linarith

/-- `|S₀(a) - S₀(b)| ≤ max(|S₀'(a)|, |S₀'(b)|) |a - b|` on `(0,1)`. -/
theorem abs_S0_sub_le {a b P : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) (hb : b ∈ Ioo (0:ℝ) 1)
    (hPa : |dS0 a| ≤ P) (hPb : |dS0 b| ≤ P) : |S0 a - S0 b| ≤ P * |a - b| := by
  have hkey : ∀ {p q : ℝ}, p ∈ Ioo (0:ℝ) 1 → q ∈ Ioo (0:ℝ) 1 → p < q → |dS0 p| ≤ P → |dS0 q| ≤ P →
      |S0 p - S0 q| ≤ P * |p - q| := by
    intro p q hp hq hpq hPp hPq
    have hcont : ContinuousOn S0 (Icc p q) := continuous_S0.continuousOn
    obtain ⟨ξ, hξ, hder⟩ := exists_hasDerivAt_eq_slope S0 dS0 hpq hcont
      (fun t ht => hasDerivAt_S0 (by linarith [ht.1, hp.1]) (by linarith [ht.2, hq.2]))
    have hξm : ξ ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hξ.1, hp.1], by linarith [hξ.2, hq.2]⟩
    have h1 : dS0 q ≤ dS0 ξ := dS0_antitoneOn hξm hq hξ.2.le
    have h2 : dS0 ξ ≤ dS0 p := dS0_antitoneOn hp hξm hξ.1.le
    have hξP : |dS0 ξ| ≤ P := by
      rw [abs_le] at hPp hPq ⊢; constructor <;> linarith [hPp.1, hPp.2, hPq.1, hPq.2]
    have hqp : q - p ≠ 0 := by linarith
    rw [eq_div_iff hqp] at hder
    rw [abs_sub_comm (S0 p), ← hder, abs_mul, abs_sub_comm p q]
    exact mul_le_mul_of_nonneg_right hξP (abs_nonneg _)
  rcases lt_trichotomy a b with h | h | h
  · exact hkey ha hb h hPa hPb
  · subst h; simp
  · have := hkey hb ha h hPb hPa
    rw [abs_sub_comm, abs_sub_comm b a] at this
    exact this

/-! ### Rows of a maximizer -/

/-- `|u^d - w^d| ≤ d |u - w|` on `[0,1]`. -/
theorem abs_pow_sub_pow_le_of_mem {u w : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (hw : w ∈ Icc (0:ℝ) 1) (n : ℕ) :
    |u ^ n - w ^ n| ≤ n * |u - w| := by
  have h := _root_.abs_pow_sub_pow_le (a := u) (b := w) (n := n)
  have hmax : max |u| |w| ≤ 1 := max_le (by rw [abs_of_nonneg hu.1]; exact hu.2)
    (by rw [abs_of_nonneg hw.1]; exact hw.2)
  have hpow : max |u| |w| ^ (n - 1) ≤ 1 := pow_le_one₀ (le_max_of_le_left (abs_nonneg _)) hmax
  calc |u ^ n - w ^ n| ≤ |u - w| * n * max |u| |w| ^ (n - 1) := h
    _ ≤ |u - w| * n * 1 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = n * |u - w| := by ring

namespace Graphon

/-- The value `w(x) = λ(α + β γ(d_W(x)))` that the row of `x` is close to. -/
noncomputable def rowVal (W : Graphon) (m d : ℕ) (α β ε x : ℝ) : ℝ :=
  logistic (α + β * gammaVal m d ε (W.degFun x))

theorem rowVal_mem (W : Graphon) (m d : ℕ) (α β ε x : ℝ) : W.rowVal m d α β ε x ∈ Ioo (0:ℝ) 1 :=
  logistic_mem _

theorem measurable_rowVal (W : Graphon) (m d : ℕ) (α β ε : ℝ) :
    Measurable fun x => W.rowVal m d α β ε x := by
  have hl : Continuous logistic := by
    unfold logistic
    exact continuous_const.div (continuous_const.add (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))) fun y => by positivity
  unfold rowVal gammaVal
  exact hl.measurable.comp (measurable_const.add (measurable_const.mul (measurable_const.mul
    (measurable_const.mul (W.measurable_degFun.pow_const _)))))

theorem integrable_rowDist (W : Graphon) {ε : ℝ} (hε : ε ∈ Icc (0:ℝ) 1) :
    Integrable (fun y => W.rowDist ε y) unitμ :=
  integrable_of_abs_le (W.measurable_rowDist ε) 1 fun y => by
    rw [abs_of_nonneg (W.rowDist_nonneg ε y)]; exact W.rowDist_le_one hε y

theorem integrable_abs_row_sub (W : Graphon) (x : ℝ) {w : ℝ} (hw : w ∈ Icc (0:ℝ) 1) :
    Integrable (fun y => |W.toFun x y - w|) unitμ :=
  integrable_of_abs_le ((measurable_toFun_right W x).sub measurable_const).abs 1 fun y => by
    rw [abs_abs, abs_le]; constructor <;> linarith [(W.mem_Icc x y).1, (W.mem_Icc x y).2, hw.1, hw.2]

/-- **Rows of a maximizer are nearly constant**: `∫ |W(x,·) - w(x)| ≤ |β| m² ‖W - ε‖₁`. -/
theorem integral_abs_sub_rowVal_le (W : Graphon) {d : ℕ} (hreg : ∀ v, H.degree v = d)
    {α β ε : ℝ} (hε : ε ∈ Icc (0:ℝ) 1) {x : ℝ}
    (hx : ∀ᵐ y ∂unitμ, W.toFun x y ∈ Ioo (0:ℝ) 1 ∧ dS0 (W.toFun x y) = α + β * W.gammaW H x y) :
    ∫ y, |W.toFun x y - W.rowVal H.edgeFinset.card d α β ε x| ∂unitμ
      ≤ |β| * (H.edgeFinset.card : ℝ) ^ 2 * W.constDist ε := by
  set m := H.edgeFinset.card with hm
  set w := W.rowVal m d α β ε x with hw
  have hwI : w ∈ Icc (0:ℝ) 1 := ⟨(W.rowVal_mem m d α β ε x).1.le, (W.rowVal_mem m d α β ε x).2.le⟩
  have hpt : ∀ᵐ y ∂unitμ, |W.toFun x y - w|
      ≤ |β| * ((m : ℝ) * ((m : ℝ) * (W.rowDist ε y + W.constDist ε))) / 2 := by
    filter_upwards [hx] with y hy
    have e1 : W.toFun x y = logistic (α + β * W.gammaW H x y) := by
      rw [← hy.2, logistic_dS0 hy.1.1 hy.1.2]
    rw [e1, hw, rowVal]
    calc |logistic (α + β * W.gammaW H x y) - logistic (α + β * gammaVal m d ε (W.degFun x))|
        ≤ |(α + β * W.gammaW H x y) - (α + β * gammaVal m d ε (W.degFun x))| / 2 :=
          abs_logistic_sub_le _ _
      _ = |β| * |W.gammaW H x y - gammaVal m d ε (W.degFun x)| / 2 := by
          rw [← abs_mul]; congr 2; ring
      _ ≤ |β| * ((m : ℝ) * ((m : ℝ) * (W.rowDist ε y + W.constDist ε))) / 2 := by
          gcongr
          exact W.abs_gammaW_sub_row_le H hreg hε x y
  have hint2 : Integrable (fun y => |β| * ((m : ℝ) * ((m : ℝ) * (W.rowDist ε y + W.constDist ε))) / 2)
      unitμ :=
    ((((W.integrable_rowDist hε).add (integrable_const _)).const_mul _).const_mul _).const_mul _
      |>.div_const _
  calc ∫ y, |W.toFun x y - w| ∂unitμ
      ≤ ∫ y, |β| * ((m : ℝ) * ((m : ℝ) * (W.rowDist ε y + W.constDist ε))) / 2 ∂unitμ :=
        integral_mono_ae (W.integrable_abs_row_sub x hwI) hint2 hpt
    _ = |β| * (m : ℝ) ^ 2 * W.constDist ε := by
        rw [integral_div, integral_const_mul, integral_const_mul, integral_const_mul,
          integral_add (W.integrable_rowDist hε) (integrable_const _), integral_rowDist,
          integral_const]
        simp only [probReal_univ, one_smul]
        ring

theorem abs_degFun_sub_le_integral (W : Graphon) (x w : ℝ) :
    |W.degFun x - w| ≤ ∫ y, |W.toFun x y - w| ∂unitμ := by
  have h : W.degFun x - w = ∫ y, (W.toFun x y - w) ∂unitμ := by
    rw [integral_sub (W.integrable_row x) (integrable_const w)]
    simp [degFun]
  rw [h]
  exact abs_integral_le_integral_abs

theorem abs_rowEnt_sub_le (W : Graphon) {α β : ℝ} {x : ℝ}
    (hx : ∀ᵐ y ∂unitμ, W.toFun x y ∈ Ioo (0:ℝ) 1 ∧ dS0 (W.toFun x y) = α + β * W.gammaW H x y)
    {w : ℝ} (hw : w ∈ Ioo (0:ℝ) 1) (hPw : |dS0 w| ≤ |α| + |β| * H.edgeFinset.card) :
    |W.rowEnt x - S0 w| ≤ (|α| + |β| * H.edgeFinset.card) * ∫ y, |W.toFun x y - w| ∂unitμ := by
  set P : ℝ := |α| + |β| * H.edgeFinset.card with hP
  have hS : Integrable (fun y => S0 (W.toFun x y)) unitμ :=
    integrable_of_abs_le (continuous_S0.measurable.comp (measurable_toFun_right W x)) 1
      fun y => W.abs_S0W_le x y
  have h : W.rowEnt x - S0 w = ∫ y, (S0 (W.toFun x y) - S0 w) ∂unitμ := by
    rw [integral_sub hS (integrable_const _)]
    simp [rowEnt]
  have hpt : ∀ᵐ y ∂unitμ, |S0 (W.toFun x y) - S0 w| ≤ P * |W.toFun x y - w| := by
    filter_upwards [hx] with y hy
    refine abs_S0_sub_le hy.1 hw ?_ hPw
    rw [hy.2]
    calc |α + β * W.gammaW H x y| ≤ |α| + |β * W.gammaW H x y| := abs_add_le _ _
      _ = |α| + |β| * W.gammaW H x y := by rw [abs_mul, abs_of_nonneg (W.gammaW_nonneg H x y)]
      _ ≤ P := by
          have := W.gammaW_le H x y
          have := abs_nonneg β
          rw [hP]; nlinarith
  have hwI : w ∈ Icc (0:ℝ) 1 := ⟨hw.1.le, hw.2.le⟩
  rw [h, ← integral_const_mul]
  calc |∫ y, (S0 (W.toFun x y) - S0 w) ∂unitμ| ≤ ∫ y, |S0 (W.toFun x y) - S0 w| ∂unitμ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, P * |W.toFun x y - w| ∂unitμ :=
        integral_mono_ae ((hS.sub (integrable_const _)).abs)
          ((W.integrable_abs_row_sub x hwI).const_mul P) hpt

end Graphon

/-- `φ(u) = 2S₀(u) - 2αu - β v ε^{m-d} u^d`. -/
noncomputable def phiFun (m d v : ℕ) (α β ε u : ℝ) : ℝ :=
  2 * S0 u - 2 * α * u - β * ((v : ℝ) * (ε ^ (m - d) * u ^ d))

namespace Graphon

/-- **The row functional on a nearly constant row**: `|Φ(x) - φ(w(x))| ≤ C ‖W - ε‖₁`. -/
theorem abs_balFun_sub_phiFun_le (W : Graphon) {d : ℕ} (hreg : ∀ v, H.degree v = d)
    {α β ε : ℝ} (hε : ε ∈ Icc (0:ℝ) 1) {x : ℝ}
    (hx : ∀ᵐ y ∂unitμ, W.toFun x y ∈ Ioo (0:ℝ) 1 ∧ dS0 (W.toFun x y) = α + β * W.gammaW H x y) :
    |W.balFun H α β x - phiFun H.edgeFinset.card d (Fintype.card V) α β ε
        (W.rowVal H.edgeFinset.card d α β ε x)|
      ≤ ((2 * (|α| + |β| * H.edgeFinset.card) + 2 * |α| + |β| * (Fintype.card V * d))
          * (|β| * (H.edgeFinset.card : ℝ) ^ 2) + |β| * (Fintype.card V * H.edgeFinset.card))
        * W.constDist ε := by
  set m := H.edgeFinset.card with hm
  set v := Fintype.card V with hv
  set w := W.rowVal m d α β ε x with hw
  set κ₁ := W.constDist ε with hκ₁
  have hκ₁0 : 0 ≤ κ₁ := W.constDist_nonneg ε
  have hwI : w ∈ Icc (0:ℝ) 1 := ⟨(W.rowVal_mem m d α β ε x).1.le, (W.rowVal_mem m d α β ε x).2.le⟩
  set e := ∫ y, |W.toFun x y - w| ∂unitμ with he
  have he1 : e ≤ |β| * (m : ℝ) ^ 2 * κ₁ := W.integral_abs_sub_rowVal_le H hreg hε hx
  have he0 : 0 ≤ e := integral_nonneg fun _ => abs_nonneg _
  have hd1 : |W.degFun x - w| ≤ e := W.abs_degFun_sub_le_integral x w
  have hPw : |dS0 w| ≤ |α| + |β| * m := by
    rw [hw, rowVal, dS0_logistic]
    have hγ := gammaVal_mem (m := m) (d := d) hε (W.degFun_mem_Icc x)
    calc |α + β * gammaVal m d ε (W.degFun x)| ≤ |α| + |β * gammaVal m d ε (W.degFun x)| :=
          abs_add_le _ _
      _ = |α| + |β| * gammaVal m d ε (W.degFun x) := by rw [abs_mul, abs_of_nonneg hγ.1]
      _ ≤ |α| + |β| * m := by have := abs_nonneg β; nlinarith [hγ.2]
  have hσ := W.abs_rowEnt_sub_le H hx (W.rowVal_mem m d α β ε x) hPw
  have hT : |∑ i, rootedK H W.symm' i x - (v : ℝ) * (ε ^ (m - d) * w ^ d)|
      ≤ (v : ℝ) * (m * κ₁) + (v : ℝ) * (d * e) := by
    have h1 : ∑ i, rootedK H W.symm' i x - (v : ℝ) * (ε ^ (m - d) * w ^ d)
        = ∑ i : V, (rootedK H W.symm' i x - ε ^ (m - d) * W.degFun x ^ d)
          + (v : ℝ) * (ε ^ (m - d) * (W.degFun x ^ d - w ^ d)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    rw [h1]
    have h2 : |∑ i : V, (rootedK H W.symm' i x - ε ^ (m - d) * W.degFun x ^ d)| ≤ (v : ℝ) * (m * κ₁) := by
      calc _ ≤ ∑ i : V, |rootedK H W.symm' i x - ε ^ (m - d) * W.degFun x ^ d| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : V, (m : ℝ) * κ₁ := Finset.sum_le_sum fun i _ => W.abs_rootedK_sub_row_le H hreg hε i x
        _ = (v : ℝ) * (m * κ₁) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h3 : |(v : ℝ) * (ε ^ (m - d) * (W.degFun x ^ d - w ^ d))| ≤ (v : ℝ) * (d * e) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (pow_nonneg hε.1 _)]
      have hp : ε ^ (m - d) ≤ 1 := pow_le_one₀ hε.1 hε.2
      have hdd := abs_pow_sub_pow_le_of_mem (W.degFun_mem_Icc x) hwI d
      have : ε ^ (m - d) * |W.degFun x ^ d - w ^ d| ≤ d * e := by
        calc ε ^ (m - d) * |W.degFun x ^ d - w ^ d| ≤ 1 * (d * |W.degFun x - w|) :=
              mul_le_mul hp hdd (abs_nonneg _) zero_le_one
          _ ≤ d * e := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hd1 (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
    exact le_trans (abs_add_le _ _) (add_le_add h2 h3)
  have hkey : W.balFun H α β x - phiFun m d v α β ε w
      = 2 * (W.rowEnt x - S0 w) - 2 * α * (W.degFun x - w)
        - β * (∑ i, rootedK H W.symm' i x - (v : ℝ) * (ε ^ (m - d) * w ^ d)) := by
    unfold balFun phiFun; ring
  rw [hkey]
  have hP0 : 0 ≤ |α| + |β| * m := by positivity
  calc |2 * (W.rowEnt x - S0 w) - 2 * α * (W.degFun x - w)
        - β * (∑ i, rootedK H W.symm' i x - (v : ℝ) * (ε ^ (m - d) * w ^ d))|
      ≤ 2 * |W.rowEnt x - S0 w| + 2 * |α| * |W.degFun x - w|
        + |β| * |∑ i, rootedK H W.symm' i x - (v : ℝ) * (ε ^ (m - d) * w ^ d)| := by
        have e1 : |2 * (W.rowEnt x - S0 w)| = 2 * |W.rowEnt x - S0 w| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        have e2 : |2 * α * (W.degFun x - w)| = 2 * |α| * |W.degFun x - w| := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        have e3 : |β * (∑ i, rootedK H W.symm' i x - (v : ℝ) * (ε ^ (m - d) * w ^ d))|
            = |β| * |∑ i, rootedK H W.symm' i x - (v : ℝ) * (ε ^ (m - d) * w ^ d)| := abs_mul _ _
        have := abs_sub (2 * (W.rowEnt x - S0 w) - 2 * α * (W.degFun x - w))
          (β * (∑ i, rootedK H W.symm' i x - (v : ℝ) * (ε ^ (m - d) * w ^ d)))
        have := abs_sub (2 * (W.rowEnt x - S0 w)) (2 * α * (W.degFun x - w))
        linarith
    _ ≤ 2 * ((|α| + |β| * m) * e) + 2 * |α| * e + |β| * ((v : ℝ) * (m * κ₁) + (v : ℝ) * (d * e)) := by
        gcongr
    _ = (2 * (|α| + |β| * m) + 2 * |α| + |β| * (v * d)) * e + |β| * (v * m) * κ₁ := by ring
    _ ≤ (2 * (|α| + |β| * m) + 2 * |α| + |β| * (v * d)) * (|β| * (m : ℝ) ^ 2 * κ₁)
          + |β| * (v * m) * κ₁ := by gcongr
    _ = _ := by ring

end Graphon

/-! ### The row functional at the limiting multipliers -/

theorem dN_eq_dS0 (ε z : ℝ) : dN ε z = 2 * (dS0 z - dS0 ε) := by
  unfold dN dS0; ring

/-- `β₀ v ε^{m-d} = ψ_*`: the limiting multiplier is the optimal ratio. -/
theorem beta₀_mul_eq_psiStar {d m v : ℕ} (hd : 2 ≤ d) (hmv : v * d = 2 * m) (hm : 0 < m) {ε : ℝ}
    (hε : ε ∈ Ioo (0:ℝ) 1) (hεr : ε ≠ rStar d) :
    beta₀ m d ε * ((v : ℝ) * ε ^ (m - d)) = psiStar d ε := by
  obtain ⟨hzm, hzne, -⟩ := zetaFun_crit hd hε.1 hε.2 hεr
  have hA := Aavg_zeta_eq_psiStar hd hε hεr
  have hpow : zetaFun d ε ^ (d - 1) ≠ ε ^ (d - 1) := by
    intro h
    exact hzne ((pow_left_inj₀ hzm.1.le hε.1.le (by omega : d - 1 ≠ 0)).mp h)
  have hsub : zetaFun d ε ^ (d - 1) - ε ^ (d - 1) ≠ 0 := sub_ne_zero.mpr hpow
  have hεpow : ε ^ (m - d) ≠ 0 := pow_ne_zero _ hε.1.ne'
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hmvR : (v : ℝ) * d = 2 * m := by exact_mod_cast hmv
  rw [← hA]
  unfold beta₀ Aavg gammaVal
  rw [dN_eq_dS0]
  unfold dD
  have e1 : (m : ℝ) * (ε ^ (m - d) * zetaFun d ε ^ (d - 1)) - m * (ε ^ (m - d) * ε ^ (d - 1))
      = m * ε ^ (m - d) * (zetaFun d ε ^ (d - 1) - ε ^ (d - 1)) := by ring
  have e2 : (d : ℝ) * zetaFun d ε ^ (d - 1) - d * ε ^ (d - 1)
      = d * (zetaFun d ε ^ (d - 1) - ε ^ (d - 1)) := by ring
  rw [e1, e2, div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero (mul_ne_zero hmR hεpow) hsub)
    (mul_ne_zero hdR hsub)]
  linear_combination (dS0 (zetaFun d ε) - dS0 ε) * ε ^ (m - d)
    * (zetaFun d ε ^ (d - 1) - ε ^ (d - 1)) * hmvR

/-- **At the limiting multipliers `φ = φ(ε) - Γ^gap`.** -/
theorem phiFun_limit_eq {d m v : ℕ} (hd : 2 ≤ d) (hmv : v * d = 2 * m) (hm : 0 < m) {ε : ℝ}
    (hε : ε ∈ Ioo (0:ℝ) 1) (hεr : ε ≠ rStar d) (u : ℝ) :
    phiFun m d v (alpha₀ m d ε) (beta₀ m d ε) ε u
      = phiFun m d v (alpha₀ m d ε) (beta₀ m d ε) ε ε - gapFun d ε u := by
  have hψ := beta₀_mul_eq_psiStar hd hmv hm hε hεr
  have hmvR : (v : ℝ) * d = 2 * m := by exact_mod_cast hmv
  have hd1 : d - 1 + 1 = d := by omega
  have hεd : ε ^ d = ε ^ (d - 1) * ε := by rw [← pow_succ, hd1]
  unfold phiFun alpha₀ gapFun Dfun Nfun gammaVal
  rw [← hψ, hεd]
  linear_combination (-(2:ℝ)) * beta₀ m d ε * ε ^ (m - d) * ε ^ (d - 1) * (u - ε) * hmvR
    - beta₀ m d ε * ε ^ (m - d) * ε ^ (d - 1) * (u - ε) * hmvR
    + beta₀ m d ε * ε ^ (m - d) * ε ^ (d - 1) * (u - ε) * hmvR * 2

theorem abs_phiFun_sub_le (m d v : ℕ) {α β α₀ β₀ ε u : ℝ} (hε : ε ∈ Icc (0:ℝ) 1)
    (hu : u ∈ Icc (0:ℝ) 1) :
    |phiFun m d v α β ε u - phiFun m d v α₀ β₀ ε u| ≤ 2 * |α - α₀| + v * |β - β₀| := by
  unfold phiFun
  have e : 2 * S0 u - 2 * α * u - β * ((v : ℝ) * (ε ^ (m - d) * u ^ d))
      - (2 * S0 u - 2 * α₀ * u - β₀ * ((v : ℝ) * (ε ^ (m - d) * u ^ d)))
      = -(2 * (α - α₀) * u) - (β - β₀) * ((v : ℝ) * (ε ^ (m - d) * u ^ d)) := by ring
  rw [e]
  have h1 : |2 * (α - α₀) * u| ≤ 2 * |α - α₀| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg hu.1]
    nlinarith [abs_nonneg (α - α₀), hu.2]
  have h2 : |(β - β₀) * ((v : ℝ) * (ε ^ (m - d) * u ^ d))| ≤ v * |β - β₀| := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (pow_nonneg hε.1 _) (pow_nonneg hu.1 _)) : (0:ℝ) ≤ (v : ℝ) * (ε ^ (m - d) * u ^ d))]
    have hp : ε ^ (m - d) * u ^ d ≤ 1 :=
      mul_le_one₀ (pow_le_one₀ hε.1 hε.2) (pow_nonneg hu.1 _) (pow_le_one₀ hu.1 hu.2)
    have : (v : ℝ) * (ε ^ (m - d) * u ^ d) ≤ v := by
      calc (v : ℝ) * (ε ^ (m - d) * u ^ d) ≤ v * 1 := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
        _ = v := mul_one _
    nlinarith [abs_nonneg (β - β₀)]
  calc |-(2 * (α - α₀) * u) - (β - β₀) * ((v : ℝ) * (ε ^ (m - d) * u ^ d))|
      ≤ |2 * (α - α₀) * u| + |(β - β₀) * ((v : ℝ) * (ε ^ (m - d) * u ^ d))| := by
        have := abs_sub (-(2 * (α - α₀) * u)) ((β - β₀) * ((v : ℝ) * (ε ^ (m - d) * u ^ d)))
        rwa [abs_neg] at this
    _ ≤ _ := add_le_add h1 h2

/-- **`Γ^gap` is at most quadratic near `ε`.** -/
theorem gapFun_le_sq {d : ℕ} (hd : 2 ≤ d) {ε η u : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1) (hεr : ε ≠ rStar d)
    (hη : 0 < η) (hη1 : η ≤ 1 / 2) (hεη : ε ∈ Icc η (1 - η)) (hu : |u - ε| ≤ η / 2) :
    gapFun d ε u ≤ 4 / η * (u - ε) ^ 2 := by
  have hS := S0_add_ge hη hη1 hεη hu
  rw [add_sub_cancel] at hS
  have huI : u ∈ Icc (0:ℝ) 1 := by
    constructor <;> linarith [(abs_le.mp hu).1, (abs_le.mp hu).2, hεη.1, hεη.2]
  have hD := Dfun_nonneg_of_mem hd ⟨hε.1.le, hε.2.le⟩ huI
  have hψ := psiStar_neg hd hε hεr
  unfold gapFun Nfun
  have h1 : psiStar d ε * Dfun d ε u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hψ.le hD
  have e : 4 / η * (u - ε) ^ 2 = 2 * (2 / η * (u - ε) ^ 2) := by ring
  rw [e]
  linarith

/-! ### Almost every row is at a zero of `Γ^gap` -/

/-- The error constant of `Graphon.abs_balFun_sub_phiFun_le`. -/
noncomputable def balErr (m v d : ℕ) (α β : ℝ) : ℝ :=
  (2 * (|α| + |β| * m) + 2 * |α| + |β| * (v * d)) * (|β| * (m : ℝ) ^ 2) + |β| * (v * m)

theorem QualDirs.ae_row_el {W : Graphon} {e₀ t₀ : ℝ} (hmax : IsMaximizer H W e₀ t₀)
    (Q : QualDirs H W) :
    ∀ᵐ x ∂unitμ, ∀ᵐ y ∂unitμ, W.toFun x y ∈ Ioo (0:ℝ) 1 ∧
      dS0 (W.toFun x y) = Q.alpha + Q.beta * W.gammaW H x y :=
  Measure.ae_ae_of_ae_prod (p := fun p : ℝ × ℝ => W.toFun p.1 p.2 ∈ Ioo (0:ℝ) 1 ∧
    dS0 (W.toFun p.1 p.2) = Q.alpha + Q.beta * W.gammaW H p.1 p.2) (Q.el H hmax)

set_option maxHeartbeats 1000000 in
/-- **Row balance at the rows**: for almost every `x`, `Γ^gap(w(x))` is small. -/
theorem QualDirs.ae_gapFun_rowVal_le {W : Graphon} {ε t₀ : ℝ} (hmax : IsMaximizer H W ε t₀)
    (Q : QualDirs H W) {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 0 < H.edgeFinset.card) (hε : ε ∈ Ioo (0:ℝ) 1) (hεr : ε ≠ rStar d) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1 / 2) (hεη : ε ∈ Icc η (1 - η))
    (hsmall : (|Q.beta| * (H.edgeFinset.card : ℝ) ^ 2 + 1) * W.constDist ε ≤ η / 2) :
    ∀ᵐ x ∂unitμ, gapFun d ε (W.rowVal H.edgeFinset.card d Q.alpha Q.beta ε x)
      ≤ 4 / η * ((|Q.beta| * (H.edgeFinset.card : ℝ) ^ 2 + 1) * W.constDist ε) ^ 2
        + 2 * (balErr H.edgeFinset.card (Fintype.card V) d Q.alpha Q.beta * W.constDist ε)
        + 2 * (2 * |Q.alpha - alpha₀ H.edgeFinset.card d ε|
          + Fintype.card V * |Q.beta - beta₀ H.edgeFinset.card d ε|) := by
  classical
  set m := H.edgeFinset.card with hmdef
  set v := Fintype.card V with hvdef
  set α := Q.alpha with hα
  set β := Q.beta with hβ
  set κ₁ := W.constDist ε with hκ₁
  have hεI : ε ∈ Icc (0:ℝ) 1 := ⟨hε.1.le, hε.2.le⟩
  have hmv : v * d = 2 * m := regular_handshake H hreg
  have hrow := Q.ae_row_el H hmax
  have hN := hrow
  rw [ae_iff] at hN
  obtain ⟨xs, hxsN, hxs⟩ := exists_notMem_null_le_integral (W.integrable_rowDist hεI) hN
  rw [W.integral_rowDist ε] at hxs
  have hxsEL : ∀ᵐ y ∂unitμ, W.toFun xs y ∈ Ioo (0:ℝ) 1 ∧
      dS0 (W.toFun xs y) = α + β * W.gammaW H xs y := by
    simpa only [Set.mem_ofPred_eq, not_not] using hxsN
  set ws := W.rowVal m d α β ε xs with hws
  have hwsI : ws ∈ Icc (0:ℝ) 1 := ⟨(W.rowVal_mem m d α β ε xs).1.le, (W.rowVal_mem m d α β ε xs).2.le⟩
  have hwsε : |ws - ε| ≤ (|β| * (m : ℝ) ^ 2 + 1) * κ₁ := by
    have h1 := W.abs_degFun_sub_le_integral xs ws
    have h2 := W.integral_abs_sub_rowVal_le H hreg hεI hxsEL
    have h3 := W.abs_degFun_sub_le_rowDist ε xs
    have e : ws - ε = -(W.degFun xs - ws) + (W.degFun xs - ε) := by ring
    rw [e]
    calc |-(W.degFun xs - ws) + (W.degFun xs - ε)| ≤ |W.degFun xs - ws| + |W.degFun xs - ε| := by
          have := abs_add_le (-(W.degFun xs - ws)) (W.degFun xs - ε)
          rwa [abs_neg] at this
      _ ≤ |β| * (m : ℝ) ^ 2 * κ₁ + κ₁ := by linarith
      _ = (|β| * (m : ℝ) ^ 2 + 1) * κ₁ := by ring
  have hgs : gapFun d ε ws ≤ 4 / η * ((|β| * (m : ℝ) ^ 2 + 1) * κ₁) ^ 2 := by
    have h1 := gapFun_le_sq hd hε hεr hη hη1 hεη (le_trans hwsε hsmall)
    have h2 : (ws - ε) ^ 2 ≤ ((|β| * (m : ℝ) ^ 2 + 1) * κ₁) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hwsε 2
    have h3 : 4 / η * (ws - ε) ^ 2 ≤ 4 / η * ((|β| * (m : ℝ) ^ 2 + 1) * κ₁) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hΦs := W.abs_balFun_sub_phiFun_le H hreg hεI hxsEL
  have hbal := Q.ae_balFun_ge H hmax xs
  filter_upwards [hrow, hbal] with x hx hxb
  have hΦx := W.abs_balFun_sub_phiFun_le H hreg hεI hx
  set wx := W.rowVal m d α β ε x with hwx
  have hwxI : wx ∈ Icc (0:ℝ) 1 := ⟨(W.rowVal_mem m d α β ε x).1.le, (W.rowVal_mem m d α β ε x).2.le⟩
  have hpx := abs_phiFun_sub_le m d v (α := α) (β := β) (α₀ := alpha₀ m d ε) (β₀ := beta₀ m d ε)
    hεI hwxI
  have hps := abs_phiFun_sub_le m d v (α := α) (β := β) (α₀ := alpha₀ m d ε) (β₀ := beta₀ m d ε)
    hεI hwsI
  have hlx := phiFun_limit_eq hd hmv hm hε hεr wx
  have hls := phiFun_limit_eq hd hmv hm hε hεr ws
  have hΦx' := (abs_le.mp hΦx)
  have hΦs' := (abs_le.mp hΦs)
  have hpx' := (abs_le.mp hpx)
  have hps' := (abs_le.mp hps)
  have hB : balErr m v d α β * κ₁
      = ((2 * (|α| + |β| * m) + 2 * |α| + |β| * (v * d)) * (|β| * (m : ℝ) ^ 2) + |β| * (v * m)) * κ₁ :=
    rfl
  rw [hB]
  linarith [hΦx'.1, hΦx'.2, hΦs'.1, hΦs'.2, hpx'.1, hpx'.2, hps'.1, hps'.2, hlx, hls, hxb, hgs]

end UpperTailOptimizers
