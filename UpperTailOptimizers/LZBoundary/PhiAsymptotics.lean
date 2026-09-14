import UpperTailOptimizers.LZBoundary.PhiConvex
import UpperTailOptimizers.LZBoundary.PhiDeriv

/-!
# Asymptotic and joint-limit analysis of `φ_{p,d}` for `lem:contact-point-limits` of `paper/paper.tex`

Supporting lemmas for `lz_boundary_endpoint_limits` (`lem:contact-point-limits`): joint (in `p`
and `x`)
continuity and `±∞` limits of `φ_{p,d}'`, strict convexity of `φ_{p,d}` for `p ≥ p_*`, the
`p↓0` blow-up of `h_{p,d}`, and the generic subsequence/cluster-point lemma used to
turn "every joint subsequential limit is the same point" into convergence.
-/

open UpperTailOptimizers Real Filter Topology Set

namespace UpperTailOptimizers

/-- **Subsequence/cluster engine.**  If `f, g` eventually land in compact intervals
along a countably-generated `NeBot` filter `l`, and along *every* sequence `u → l`
any common subsequential limit `(α, β)` of `(f∘u, g∘u)` equals `(a₀, b₀)`, then
`f → a₀` and `g → b₀` along `l`.  (Reduce to sequences via `tendsto_iff_seq_tendsto`;
for each sequence, `tendsto_of_subseq_tendsto` + Bolzano–Weierstrass on the compacts.) -/
theorem tendsto_pair_of_subseq {l : Filter ℝ} [l.NeBot] [l.IsCountablyGenerated]
    {f g : ℝ → ℝ} {a b A B a₀ b₀ : ℝ}
    (hf : ∀ᶠ x in l, f x ∈ Set.Icc a b) (hg : ∀ᶠ x in l, g x ∈ Set.Icc A B)
    (hlim : ∀ (u : ℕ → ℝ) (α β : ℝ), Filter.Tendsto u Filter.atTop l →
        Filter.Tendsto (fun n => f (u n)) Filter.atTop (𝓝 α) →
        Filter.Tendsto (fun n => g (u n)) Filter.atTop (𝓝 β) → α = a₀ ∧ β = b₀) :
    Filter.Tendsto f l (𝓝 a₀) ∧ Filter.Tendsto g l (𝓝 b₀) := by
  have key : ∀ (u : ℕ → ℝ), Tendsto u atTop l →
      Tendsto (fun n => f (u n)) atTop (𝓝 a₀) ∧ Tendsto (fun n => g (u n)) atTop (𝓝 b₀) := by
    intro u hu
    have hfu : ∀ᶠ n in atTop, f (u n) ∈ Set.Icc a b := hu.eventually hf
    have hgu : ∀ᶠ n in atTop, g (u n) ∈ Set.Icc A B := hu.eventually hg
    constructor
    · apply tendsto_of_subseq_tendsto
      intro ns hns
      have hfreq : ∃ᶠ n in atTop, f (u (ns n)) ∈ Set.Icc a b :=
        (hns.eventually hfu).frequently
      obtain ⟨α, _hα, ψ, hψ, hαlim⟩ :=
        (isCompact_Icc (a := a) (b := b)).tendsto_subseq' hfreq
      have hgfreq : ∃ᶠ n in atTop, g (u (ns (ψ n))) ∈ Set.Icc A B := by
        have : ∀ᶠ n in atTop, g (u (ns (ψ n))) ∈ Set.Icc A B :=
          (((hns.comp hψ.tendsto_atTop).eventually hgu))
        exact this.frequently
      obtain ⟨β, _hβ, η, hη, hβlim⟩ :=
        (isCompact_Icc (a := A) (b := B)).tendsto_subseq' hgfreq
      set φ : ℕ → ℕ := fun n => ns (ψ (η n))
      have hφtt : Tendsto φ atTop atTop := hns.comp (hψ.comp hη).tendsto_atTop
      have hφl : Tendsto (fun n => u (φ n)) atTop l := hu.comp hφtt
      have hfφ : Tendsto (fun n => f (u (φ n))) atTop (𝓝 α) :=
        hαlim.comp hη.tendsto_atTop
      have hgφ : Tendsto (fun n => g (u (φ n))) atTop (𝓝 β) := hβlim
      obtain ⟨hαa₀, _hβb₀⟩ := hlim (fun n => u (φ n)) α β hφl hfφ hgφ
      subst hαa₀
      exact ⟨ψ ∘ η, hfφ⟩
    · apply tendsto_of_subseq_tendsto
      intro ns hns
      have hgfreq : ∃ᶠ n in atTop, g (u (ns n)) ∈ Set.Icc A B :=
        (hns.eventually hgu).frequently
      obtain ⟨β, _hβ, ψ, hψ, hβlim⟩ :=
        (isCompact_Icc (a := A) (b := B)).tendsto_subseq' hgfreq
      have hffreq : ∃ᶠ n in atTop, f (u (ns (ψ n))) ∈ Set.Icc a b := by
        have : ∀ᶠ n in atTop, f (u (ns (ψ n))) ∈ Set.Icc a b :=
          (((hns.comp hψ.tendsto_atTop).eventually hfu))
        exact this.frequently
      obtain ⟨α, _hα, η, hη, hαlim⟩ :=
        (isCompact_Icc (a := a) (b := b)).tendsto_subseq' hffreq
      set φ : ℕ → ℕ := fun n => ns (ψ (η n))
      have hφtt : Tendsto φ atTop atTop := hns.comp (hψ.comp hη).tendsto_atTop
      have hφl : Tendsto (fun n => u (φ n)) atTop l := hu.comp hφtt
      have hfφ : Tendsto (fun n => f (u (φ n))) atTop (𝓝 α) := hαlim
      have hgφ : Tendsto (fun n => g (u (φ n))) atTop (𝓝 β) :=
        hβlim.comp hη.tendsto_atTop
      obtain ⟨_hαa₀, hβb₀⟩ := hlim (fun n => u (φ n)) α β hφl hfφ hgφ
      subst hβb₀
      exact ⟨ψ ∘ η, hgφ⟩
  refine ⟨?_, ?_⟩
  · rw [tendsto_iff_seq_tendsto]
    intro u hu
    exact (key u hu).1
  · rw [tendsto_iff_seq_tendsto]
    intro u hu
    exact (key u hu).2

/-- **Joint continuity of `φ'`.**  `deriv (phi p d) x` is jointly continuous at
interior points `(p₀, x₀) ∈ (0,1)×(0,1)` (sequential form). -/
theorem phi_deriv_jointContinuous {d : ℕ} (hd : 2 ≤ d) {p₀ x₀ : ℝ}
    (hp₀0 : 0 < p₀) (hp₀1 : p₀ < 1) (hx₀0 : 0 < x₀) (hx₀1 : x₀ < 1)
    {pn xn : ℕ → ℝ}
    (hp : Filter.Tendsto pn Filter.atTop (𝓝 p₀)) (hx : Filter.Tendsto xn Filter.atTop (𝓝 x₀))
    (hpn : ∀ᶠ n in Filter.atTop, 0 < pn n ∧ pn n < 1)
    (hxn : ∀ᶠ n in Filter.atTop, 0 < xn n ∧ xn n < 1) :
    Filter.Tendsto (fun n => deriv (phi (pn n) d) (xn n)) Filter.atTop
      (𝓝 (deriv (phi p₀ d) x₀)) := by
  set c : ℝ := 1 / (d : ℝ) with hc
  have hu₀0 : 0 < Real.rpow x₀ c := Real.rpow_pos_of_pos hx₀0 c
  have hcpos : 0 < c := by rw [hc]; positivity
  have hu₀1 : Real.rpow x₀ c < 1 := Real.rpow_lt_one (le_of_lt hx₀0) hx₀1 hcpos
  have hderiv₀ : deriv (phi p₀ d) x₀ =
      Jp' p₀ (Real.rpow x₀ c) * (c * Real.rpow x₀ (c - 1)) :=
    (hasDerivAt_phi hd hp₀0 hp₀1 hx₀0 hx₀1).deriv
  rw [hderiv₀]
  have heq : (fun n => deriv (phi (pn n) d) (xn n)) =ᶠ[atTop]
      (fun n => Jp' (pn n) (Real.rpow (xn n) c) * (c * Real.rpow (xn n) (c - 1))) := by
    filter_upwards [hpn, hxn] with n hpnn hxnn
    exact (hasDerivAt_phi hd hpnn.1 hpnn.2 hxnn.1 hxnn.2).deriv
  refine Filter.Tendsto.congr' heq.symm ?_
  have hrpow_c : Filter.Tendsto (fun n => Real.rpow (xn n) c) atTop (𝓝 (Real.rpow x₀ c)) :=
    ((Real.continuousAt_rpow_const x₀ c (Or.inl (ne_of_gt hx₀0))).tendsto).comp hx
  have hrpow_c1 : Filter.Tendsto (fun n => Real.rpow (xn n) (c - 1)) atTop
      (𝓝 (Real.rpow x₀ (c - 1))) :=
    ((Real.continuousAt_rpow_const x₀ (c - 1) (Or.inl (ne_of_gt hx₀0))).tendsto).comp hx
  set arg₀ : ℝ := Real.rpow x₀ c * (1 - p₀) / ((1 - Real.rpow x₀ c) * p₀) with harg₀
  have h1mp₀ : (0:ℝ) < 1 - p₀ := by linarith
  have h1mu₀ : (0:ℝ) < 1 - Real.rpow x₀ c := by linarith
  have harg₀pos : 0 < arg₀ := by rw [harg₀]; positivity
  have harg : Filter.Tendsto
      (fun n => Real.rpow (xn n) c * (1 - pn n) / ((1 - Real.rpow (xn n) c) * pn n))
      atTop (𝓝 arg₀) := by
    rw [harg₀]
    apply Filter.Tendsto.div
    · exact hrpow_c.mul ((tendsto_const_nhds).sub hp)
    · exact ((tendsto_const_nhds).sub hrpow_c).mul hp
    · exact ne_of_gt (by positivity)
  have hJp' : Filter.Tendsto (fun n => Jp' (pn n) (Real.rpow (xn n) c)) atTop
      (𝓝 (Jp' p₀ (Real.rpow x₀ c))) := by
    have hlog : Filter.Tendsto
        (fun n => Real.log (Real.rpow (xn n) c * (1 - pn n) / ((1 - Real.rpow (xn n) c) * pn n)))
        atTop (𝓝 (Real.log arg₀)) :=
      ((Real.continuousAt_log (ne_of_gt harg₀pos)).tendsto).comp harg
    convert hlog using 2
    all_goals try rfl
  exact hJp'.mul (tendsto_const_nhds.mul hrpow_c1)

/-- **`φ' → -∞` jointly.**  When `xₙ → 0⁺` and `pₙ → p₀ ∈ (0,1)`,
`deriv (phi pₙ d) xₙ → -∞`. -/
theorem phi_deriv_tendsto_atBot_joint {d : ℕ} (hd : 2 ≤ d) {p₀ : ℝ}
    (hp₀0 : 0 < p₀) (_hp₀1 : p₀ < 1)
    {pn xn : ℕ → ℝ}
    (hp : Filter.Tendsto pn Filter.atTop (𝓝 p₀)) (hx : Filter.Tendsto xn Filter.atTop (𝓝 0))
    (hpn : ∀ᶠ n in Filter.atTop, 0 < pn n ∧ pn n < 1)
    (hxn : ∀ᶠ n in Filter.atTop, 0 < xn n ∧ xn n < 1) :
    Filter.Tendsto (fun n => deriv (phi (pn n) d) (xn n)) Filter.atTop Filter.atBot := by
  have hdpos := dpos hd
  have hde : (0:ℝ) < 1/(d:ℝ) := by positivity
  have hposexp : (0:ℝ) < 1 - 1/(d:ℝ) := by
    have : (1:ℝ)/(d:ℝ) < 1 := by rw [div_lt_one hdpos]; have := one_lt_d hd; linarith
    linarith
  set un : ℕ → ℝ := fun n => Real.rpow (xn n) (1/(d:ℝ))
  have heq : (fun n => deriv (phi (pn n) d) (xn n)) =ᶠ[atTop]
      (fun n => Jp' (pn n) (un n) * ((1/(d:ℝ)) * Real.rpow (xn n) (1/(d:ℝ) - 1))) := by
    filter_upwards [hpn, hxn] with n hpnn hxnn
    exact (hasDerivAt_phi hd hpnn.1 hpnn.2 hxnn.1 hxnn.2).deriv
  rw [Filter.tendsto_congr' heq]
  have hun0 : Tendsto un atTop (𝓝 0) := by
    have hc : Tendsto (fun y : ℝ => Real.rpow y (1/(d:ℝ))) (𝓝 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (1/(d:ℝ)) (Or.inr hde.le)).tendsto
      rwa [Real.zero_rpow (ne_of_gt hde)] at this
    exact hc.comp hx
  have hun_mem : ∀ᶠ n in atTop, 0 < un n ∧ un n < 1 := by
    filter_upwards [hxn] with n hxnn
    refine ⟨Real.rpow_pos_of_pos hxnn.1 _, ?_⟩
    have h := Real.rpow_lt_rpow hxnn.1.le hxnn.2 hde
    rwa [Real.one_rpow] at h
  set arg : ℕ → ℝ := fun n => un n * (1 - pn n) / ((1 - un n) * pn n) with harg_def
  have harg_nhds : Tendsto arg atTop (𝓝 0) := by
    have hnum : Tendsto (fun n => un n * (1 - pn n)) atTop (𝓝 (0 * (1 - p₀))) :=
      hun0.mul (Filter.Tendsto.const_sub 1 hp)
    have hden : Tendsto (fun n => (1 - un n) * pn n) atTop (𝓝 ((1 - 0) * p₀)) :=
      (Filter.Tendsto.const_sub 1 hun0).mul hp
    have hp0ne : ((1:ℝ) - 0) * p₀ ≠ 0 := by simp; exact ne_of_gt hp₀0
    have := hnum.div hden hp0ne
    simpa [Pi.div_def] using this
  have harg_pos : ∀ᶠ n in atTop, 0 < arg n := by
    filter_upwards [hpn, hun_mem] with n hpnn hunn
    have hp1' : (0:ℝ) < 1 - pn n := by linarith [hpnn.2]
    have h1u : (0:ℝ) < 1 - un n := by linarith [hunn.2]
    exact div_pos (mul_pos hunn.1 hp1') (mul_pos h1u hpnn.1)
  have harg_GT : Tendsto arg atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨harg_nhds, by filter_upwards [harg_pos] with n hn using Set.mem_Ioi.mpr hn⟩
  have hlog : Tendsto (fun n => Jp' (pn n) (un n)) atTop atBot := by
    have h := tendsto_log_nhdsGT_zero.comp harg_GT
    have hcongr : (Real.log ∘ arg) =ᶠ[atTop] (fun n => Jp' (pn n) (un n)) := by
      filter_upwards with n
      simp only [Function.comp_apply, Jp', harg_def]
    exact h.congr' hcongr
  have hbase : Tendsto (fun n => Real.rpow (xn n) (1 - 1/(d:ℝ))) atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Tendsto (fun y : ℝ => Real.rpow y (1 - 1/(d:ℝ))) (𝓝 0) (𝓝 0) := by
        have := (Real.continuousAt_rpow_const 0 (1 - 1/(d:ℝ)) (Or.inr hposexp.le)).tendsto
        rwa [Real.zero_rpow (ne_of_gt hposexp)] at this
      exact hc.comp hx
    · filter_upwards [hxn] with n hxnn
      exact Set.mem_Ioi.mpr (Real.rpow_pos_of_pos hxnn.1 _)
  have hinv : Tendsto (fun n => (Real.rpow (xn n) (1 - 1/(d:ℝ)))⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hbase
  have hrpow : Tendsto (fun n => Real.rpow (xn n) (1/(d:ℝ) - 1)) atTop atTop := by
    refine hinv.congr' ?_
    filter_upwards [hxn] with n hxnn
    have h := Real.rpow_neg hxnn.1.le (1 - 1/(d:ℝ))
    rw [show (1:ℝ)/(d:ℝ) - 1 = -(1 - 1/(d:ℝ)) from by ring]
    exact h.symm
  have hc : Tendsto (fun n => (1/(d:ℝ)) * Real.rpow (xn n) (1/(d:ℝ) - 1)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hrpow
  exact hlog.atBot_mul_atTop₀ hc

/-- **`φ' → +∞` jointly.**  When `xₙ → 1⁻` and `pₙ → p₀ ∈ (0,1)`,
`deriv (phi pₙ d) xₙ → +∞`. -/
theorem phi_deriv_tendsto_atTop_joint {d : ℕ} (hd : 2 ≤ d) {p₀ : ℝ}
    (hp₀0 : 0 < p₀) (hp₀1 : p₀ < 1)
    {pn xn : ℕ → ℝ}
    (hp : Filter.Tendsto pn Filter.atTop (𝓝 p₀)) (hx : Filter.Tendsto xn Filter.atTop (𝓝 1))
    (hpn : ∀ᶠ n in Filter.atTop, 0 < pn n ∧ pn n < 1)
    (hxn : ∀ᶠ n in Filter.atTop, 0 < xn n ∧ xn n < 1) :
    Filter.Tendsto (fun n => deriv (phi (pn n) d) (xn n)) Filter.atTop Filter.atTop := by
  have hdpos := dpos hd
  have hde : (0:ℝ) < 1/(d:ℝ) := by positivity
  set un : ℕ → ℝ := fun n => Real.rpow (xn n) (1/(d:ℝ))
  have heq : (fun n => deriv (phi (pn n) d) (xn n)) =ᶠ[atTop]
      (fun n => Jp' (pn n) (un n) * ((1/(d:ℝ)) * Real.rpow (xn n) (1/(d:ℝ) - 1))) := by
    filter_upwards [hpn, hxn] with n hpnn hxnn
    exact (hasDerivAt_phi hd hpnn.1 hpnn.2 hxnn.1 hxnn.2).deriv
  rw [Filter.tendsto_congr' heq]
  have hun1 : Tendsto un atTop (𝓝 1) := by
    have hc : Tendsto (fun y : ℝ => Real.rpow y (1/(d:ℝ))) (𝓝 1) (𝓝 1) := by
      have := (Real.continuousAt_rpow_const 1 (1/(d:ℝ)) (Or.inl one_ne_zero)).tendsto
      rwa [Real.one_rpow] at this
    exact hc.comp hx
  have hun_mem : ∀ᶠ n in atTop, 0 < un n ∧ un n < 1 := by
    filter_upwards [hxn] with n hxnn
    refine ⟨Real.rpow_pos_of_pos hxnn.1 _, ?_⟩
    exact Real.rpow_lt_one hxnn.1.le hxnn.2 hde
  set arg : ℕ → ℝ := fun n => un n * (1 - pn n) / ((1 - un n) * pn n) with harg_def
  have hnum : Tendsto (fun n => un n * (1 - pn n)) atTop (𝓝 (1 * (1 - p₀))) :=
    hun1.mul (Filter.Tendsto.const_sub 1 hp)
  have h1u_GT : Tendsto (fun n => 1 - un n) atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := Filter.Tendsto.const_sub (1:ℝ) hun1
      simpa using this
    · filter_upwards [hun_mem] with n hunn
      exact Set.mem_Ioi.mpr (by linarith [hunn.2])
  have hinv1u : Tendsto (fun n => (1 - un n)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp h1u_GT
  have hnumdiv : Tendsto (fun n => un n * (1 - pn n) / pn n) atTop (𝓝 ((1 * (1 - p₀)) / p₀)) :=
    hnum.div hp (ne_of_gt hp₀0)
  have hnumdiv_pos : (0:ℝ) < (1 * (1 - p₀)) / p₀ := by
    have := sub_pos.mpr hp₀1; positivity
  have harg_top : Tendsto arg atTop atTop := by
    refine (hinv1u.atTop_mul_pos hnumdiv_pos hnumdiv).congr' ?_
    filter_upwards [hpn, hun_mem] with n hpnn hunn
    have hune : (1:ℝ) - un n ≠ 0 := ne_of_gt (by linarith [hunn.2])
    have hpne : pn n ≠ 0 := ne_of_gt hpnn.1
    simp only [harg_def]
    field_simp
  have hlog : Tendsto (fun n => Jp' (pn n) (un n)) atTop atTop := by
    have h := tendsto_log_atTop.comp harg_top
    have hcongr : (Real.log ∘ arg) =ᶠ[atTop] (fun n => Jp' (pn n) (un n)) := by
      filter_upwards with n
      simp only [Function.comp_apply, Jp', harg_def]
    exact h.congr' hcongr
  have hc : Tendsto (fun n => (1/(d:ℝ)) * Real.rpow (xn n) (1/(d:ℝ) - 1)) atTop (𝓝 (1/(d:ℝ))) := by
    have hca : Tendsto (fun y : ℝ => (1/(d:ℝ)) * Real.rpow y (1/(d:ℝ) - 1)) (𝓝 1) (𝓝 (1/(d:ℝ))) := by
      have hcc : Tendsto (fun y : ℝ => Real.rpow y (1/(d:ℝ) - 1)) (𝓝 1) (𝓝 1) := by
        have := (Real.continuousAt_rpow_const 1 (1/(d:ℝ) - 1) (Or.inl one_ne_zero)).tendsto
        rwa [Real.one_rpow] at this
      have := hcc.const_mul (1/(d:ℝ))
      simpa using this
    exact hca.comp hx
  exact hlog.atTop_mul_pos (by positivity) hc

/-- **(D1)** At `p = p_*`, `h_{p_*,d}(u) > 0` for every `u ∈ (0,1)` with `u ≠ r_*`. -/
theorem hpd_pStar_pos {d : ℕ} (hd : 2 ≤ d) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (hne : u ≠ rStar d) :
    0 < hpd (pStar d) d u := by
  have hp0 : 0 < pStar d := pStar_pos hd
  have hp1 : pStar d < 1 := pStar_lt_one hd
  have hus0 := rStar_pos hd
  have hus1 := rStar_lt_one hd
  have hzero : hpd (pStar d) d (rStar d) = 0 :=
    (hpd_rStar_eq_zero_iff hd hp0 hp1).mpr rfl
  have hcwUStar : ContinuousWithinAt (hpd (pStar d) d) (Set.Ioo 0 1) (rStar d) :=
    hpd_continuousOn hd hp0 hp1 (rStar d) ⟨hus0, hus1⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hanti := hpd_strictAntiOn hd hp0 hp1
    set m := (u + rStar d) / 2 with hm
    have hum : u < m := by rw [hm]; linarith
    have hmus : m < rStar d := by rw [hm]; linarith
    have hm0 : 0 < m := lt_trans hu0 hum
    have h1 : hpd (pStar d) d m < hpd (pStar d) d u :=
      hanti ⟨hu0, hlt⟩ ⟨hm0, hmus⟩ hum
    have hge : hpd (pStar d) d (rStar d) ≤ hpd (pStar d) d m := by
      have hmemIoo : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (rStar d) :=
        mem_nhdsWithin.mpr ⟨Set.Ioi 0, isOpen_Ioi, hus0, by
          rintro x ⟨hx0, hx1⟩; exact ⟨hx0, lt_trans hx1 hus1⟩⟩
      have hlim : Tendsto (hpd (pStar d) d) (𝓝[<] (rStar d)) (𝓝 (hpd (pStar d) d (rStar d))) :=
        hcwUStar.mono_of_mem_nhdsWithin hmemIoo
      have hev : ∀ᶠ x in 𝓝[<] (rStar d), hpd (pStar d) d x ≤ hpd (pStar d) d m := by
        have hmem : Set.Ioo m (rStar d) ∈ 𝓝[<] (rStar d) :=
          mem_nhdsWithin.mpr ⟨Set.Ioi m, isOpen_Ioi, hmus, by
            rintro x ⟨hx0, hx1⟩; exact ⟨hx0, hx1⟩⟩
        filter_upwards [hmem] with x hx
        exact le_of_lt (hanti ⟨hm0, hmus⟩ ⟨lt_trans hm0 hx.1, hx.2⟩ hx.1)
      have : (𝓝[<] (rStar d)).NeBot := nhdsWithin_Iio_neBot (le_refl _)
      exact le_of_tendsto hlim hev
    linarith
  · have hmono := hpd_strictMonoOn hd hp0 hp1
    set m := (rStar d + u) / 2 with hm
    have hum : m < u := by rw [hm]; linarith
    have hmus : rStar d < m := by rw [hm]; linarith
    have hm1 : m < 1 := lt_trans hum hu1
    have h1 : hpd (pStar d) d m < hpd (pStar d) d u :=
      hmono ⟨hmus, hm1⟩ ⟨hgt, hu1⟩ hum
    have hge : hpd (pStar d) d (rStar d) ≤ hpd (pStar d) d m := by
      have hmemIoo : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (rStar d) :=
        mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, hus1, by
          rintro x ⟨hx1, hx0⟩; exact ⟨lt_trans hus0 hx0, hx1⟩⟩
      have hlim : Tendsto (hpd (pStar d) d) (𝓝[>] (rStar d)) (𝓝 (hpd (pStar d) d (rStar d))) :=
        hcwUStar.mono_of_mem_nhdsWithin hmemIoo
      have hev : ∀ᶠ x in 𝓝[>] (rStar d), hpd (pStar d) d x ≤ hpd (pStar d) d m := by
        have hmem : Set.Ioo (rStar d) m ∈ 𝓝[>] (rStar d) :=
          mem_nhdsWithin.mpr ⟨Set.Iio m, isOpen_Iio, hmus, by
            rintro x ⟨hx1, hx0⟩; exact ⟨hx0, hx1⟩⟩
        filter_upwards [hmem] with x hx
        exact le_of_lt (hmono ⟨hx.1, lt_trans hx.2 hm1⟩ ⟨hmus, hm1⟩ hx.2)
      have : (𝓝[>] (rStar d)).NeBot := nhdsWithin_Ioi_neBot (le_refl _)
      exact le_of_tendsto hlim hev
    linarith

/-- **`h_{p,d}` is monotone in `p`.**  Only the `-(d-1) J_p'(u)` term of
`h_{p,d}(u) = u J''(u) - (d-1) J_p'(u)` depends on `p`, and
`J_p'(u) = log(u(1-p)/((1-u)p))` decreases as `p` grows. -/
theorem hpd_mono_p {d : ℕ} (hd : 2 ≤ d) {p q u : ℝ} (hp0 : 0 < p) (hpq : p ≤ q) (hq1 : q < 1)
    (hu0 : 0 < u) (hu1 : u < 1) : hpd p d u ≤ hpd q d u := by
  have hq0 : 0 < q := lt_of_lt_of_le hp0 hpq
  have hp1 : p < 1 := lt_of_le_of_lt hpq hq1
  have hd1 : (0:ℝ) < (d:ℝ) - 1 := by have := one_lt_d hd; linarith
  have h1u : (0:ℝ) < 1 - u := by linarith
  have hJ : Jp' q u ≤ Jp' p u := by
    unfold Jp'
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hid : u * (1 - p) * ((1 - u) * q) - u * (1 - q) * ((1 - u) * p)
        = u * (1 - u) * (q - p) := by ring
    have hnn : 0 ≤ u * (1 - u) * (q - p) :=
      mul_nonneg (mul_nonneg hu0.le h1u.le) (sub_nonneg.mpr hpq)
    linarith
  unfold hpd
  nlinarith [mul_nonneg hd1.le (sub_nonneg.mpr hJ)]

/-- **(D1) above `p_*`.**  For `p_* ≤ p < 1` the convexity defect is strictly positive at every
`u ∈ (0,1)` with `u ≠ r_*`: it is so at `p = p_*` (`hpd_pStar_pos`), and `h_{p,d}(u)` only
grows with `p` (`hpd_mono_p`). -/
theorem hpd_pos_of_pStar_le {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hps : pStar d ≤ p) (hp1 : p < 1)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hne : u ≠ rStar d) : 0 < hpd p d u :=
  lt_of_lt_of_le (hpd_pStar_pos hd hu0 hu1 hne)
    (hpd_mono_p hd (pStar_pos hd) hps hp1 hu0 hu1)

/-- Helper for (D2): for `p_* ≤ p < 1`, `φ''_{p,d}(x) > 0` for `x ∈ (0,1)` with
`x ≠ (r_*)^d`. -/
theorem phi''_pos_of_pStar_le {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hps : pStar d ≤ p) (hp1 : p < 1)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hxm : x ≠ (rStar d) ^ d) : 0 < phi'' p d x := by
  have hu0 : 0 < Real.rpow x (1 / (d:ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hu1 : Real.rpow x (1 / (d:ℝ)) < 1 := by
    have : Real.rpow x (1 / (d:ℝ)) < Real.rpow 1 (1 / (d:ℝ)) :=
      Real.rpow_lt_rpow hx0.le hx1 (by positivity)
    simpa using this
  have hune : Real.rpow x (1 / (d:ℝ)) ≠ rStar d := by
    intro hcontra
    apply hxm
    have hpow : (Real.rpow x (1 / (d:ℝ))) ^ d = x := by
      rw [one_div]; exact Real.rpow_inv_natCast_pow hx0.le (by omega)
    rw [← hpow, hcontra]
  rw [phi''_pos_iff hd hx0]
  exact hpd_pos_of_pStar_le hd hps hp1 hu0 hu1 hune

/-- Helper for (D2): at `p = p_*`, `φ''_{p_*,d}(x) > 0` for `x ∈ (0,1)` with `x ≠ (r_*)^d`. -/
theorem phi''_pStar_pos {d : ℕ} (hd : 2 ≤ d) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hxm : x ≠ (rStar d) ^ d) : 0 < phi'' (pStar d) d x :=
  phi''_pos_of_pStar_le hd le_rfl (pStar_lt_one hd) hx0 hx1 hxm

/-- **(D2)** For `p_* ≤ p < 1`, `deriv (phi p d)` is strictly increasing on `(0,1)`
(i.e. `φ_{p,d}` is strictly convex).  `φ''_{p,d}` is positive on `(0,1)` except possibly at
`(r_*)^d`, so strict monotonicity holds on `(0,(r_*)^d]` and on `[(r_*)^d,1)` and glues.
NOTE: the same statement about `deriv` on `Icc 0 1` is *false*, because `deriv` returns the
junk value `0` at the non-differentiable endpoint `0` while `deriv → -∞` as `x → 0⁺`. -/
theorem phi_deriv_strictMonoOn_of_pStar_le {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hps : pStar d ≤ p)
    (hp1 : p < 1) : StrictMonoOn (deriv (phi p d)) (Set.Ioo (0:ℝ) 1) := by
  have hp0 : 0 < p := lt_of_lt_of_le (pStar_pos hd) hps
  have hus0 := rStar_pos hd
  have hus1 := rStar_lt_one hd
  set f := deriv (phi p d)
  set m : ℝ := (rStar d) ^ d with hm
  have hm0 : 0 < m := by rw [hm]; positivity
  have hm1 : m < 1 := by
    rw [hm]
    calc (rStar d) ^ d < 1 ^ d := by apply pow_lt_pow_left₀ hus1 hus0.le; omega
      _ = 1 := one_pow d
  have hcont : ContinuousOn f (Set.Ioo (0:ℝ) 1) := by
    intro x hx
    exact (hasDerivAt_phi'' hd hp0 hp1 hx.1 hx.2).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) 1, deriv f x = phi'' p d x := fun x hx =>
    (hasDerivAt_phi'' hd hp0 hp1 hx.1 hx.2).deriv
  have hL : StrictMonoOn f (Set.Ioc 0 m) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc _ _)
      (hcont.mono (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hm1⟩))
    intro x hx
    rw [interior_Ioc] at hx
    have hxin : x ∈ Set.Ioo (0:ℝ) 1 := ⟨hx.1, lt_trans hx.2 hm1⟩
    rw [hderiv x hxin]
    exact phi''_pos_of_pStar_le hd hps hp1 hxin.1 hxin.2 (ne_of_lt hx.2)
  have hR : StrictMonoOn f (Set.Ico m 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico _ _)
      (hcont.mono (fun x hx => ⟨lt_of_lt_of_le hm0 hx.1, hx.2⟩))
    intro x hx
    rw [interior_Ico] at hx
    have hxin : x ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_trans hm0 hx.1, hx.2⟩
    rw [hderiv x hxin]
    exact phi''_pos_of_pStar_le hd hps hp1 hxin.1 hxin.2 (ne_of_gt hx.1)
  have hunion : StrictMonoOn f (Set.Ioc 0 m ∪ Set.Ico m 1) :=
    hL.union hR (isGreatest_Ioc hm0) (isLeast_Ico hm1)
  have hset : Set.Ioc (0:ℝ) m ∪ Set.Ico m 1 = Set.Ioo (0:ℝ) 1 := by
    ext x
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, lt_of_le_of_lt h2 hm1⟩
      · exact ⟨lt_of_lt_of_le hm0 h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases le_or_gt x m with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h.le, h2⟩
  rw [hset] at hunion
  exact hunion

/-- **(D2)** at `p = p_*`: `deriv (phi (pStar d) d)` is strictly increasing on `(0,1)`. -/
theorem phi_deriv_pStar_strictMonoOn {d : ℕ} (hd : 2 ≤ d) :
    StrictMonoOn (deriv (phi (pStar d) d)) (Set.Ioo (0:ℝ) 1) :=
  phi_deriv_strictMonoOn_of_pStar_le hd le_rfl (pStar_lt_one hd)

/-- **Strict convexity of `φ_{p,d}` on `[0,1]` for `p_* ≤ p < 1`.**  `deriv (phi p d)` is
strictly increasing on `interior (Icc 0 1) = (0,1)`, which is all that
`StrictMonoOn.strictConvexOn_of_deriv` asks for: it does not require differentiability at the
endpoints, where `deriv` is the junk value `0`.  This is the strict form of
`convexOn_phi_of_pStar_le`, and it is what supplies the strict supporting line at `r^d` — hence
uniqueness of the constant optimizer — for every `p` above `p_*`. -/
theorem strictConvexOn_phi_of_pStar_le {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hps : pStar d ≤ p)
    (hp1 : p < 1) : StrictConvexOn ℝ (Set.Icc 0 1) (phi p d) := by
  have hp0 : 0 < p := lt_of_lt_of_le (pStar_pos hd) hps
  refine StrictMonoOn.strictConvexOn_of_deriv (convex_Icc 0 1)
    (phi_continuousOn_Icc hd hp0 hp1) ?_
  rw [interior_Icc]
  exact phi_deriv_strictMonoOn_of_pStar_le hd hps hp1

/-- **(D3)** For `p ↓ 0` and `uₙ → γ ∈ (0,1)`: `h_{pₙ,d}(uₙ) → -∞`. -/
theorem hpd_tendsto_atBot_p_zero {d : ℕ} (hd : 2 ≤ d) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {pn un : ℕ → ℝ}
    (hp : Filter.Tendsto pn Filter.atTop (𝓝[>] (0:ℝ)))
    (hu : Filter.Tendsto un Filter.atTop (𝓝 γ))
    (hun : ∀ᶠ n in Filter.atTop, 0 < un n ∧ un n < 1) :
    Filter.Tendsto (fun n => hpd (pn n) d (un n)) Filter.atTop Filter.atBot := by
  have hd1 : (0:ℝ) < (d:ℝ) - 1 := by have := one_lt_d hd; linarith
  have hp0 : Filter.Tendsto pn Filter.atTop (𝓝 (0:ℝ)) := hp.mono_right nhdsWithin_le_nhds
  have hppos : ∀ᶠ n in Filter.atTop, 0 < pn n := by
    have := hp.eventually (eventually_mem_nhdsWithin (a := (0:ℝ)) (s := Set.Ioi 0))
    filter_upwards [this] with n hn
    exact hn
  have hnum : Filter.Tendsto (fun n => un n * (1 - pn n)) Filter.atTop (𝓝 (γ * (1 - 0))) :=
    hu.mul ((tendsto_const_nhds).sub hp0)
  have hnum' : Filter.Tendsto (fun n => un n * (1 - pn n)) Filter.atTop (𝓝 γ) := by
    simpa using hnum
  have h1u : Filter.Tendsto (fun n => 1 - un n) Filter.atTop (𝓝 (1 - γ)) :=
    (tendsto_const_nhds).sub hu
  have hdenom : Filter.Tendsto (fun n => (1 - un n) * pn n) Filter.atTop (𝓝 (0:ℝ)) := by
    have := h1u.mul hp0
    simpa using this
  have hdenpos : ∀ᶠ n in Filter.atTop, 0 < (1 - un n) * pn n := by
    filter_upwards [hun, hppos] with n hn hpn
    exact mul_pos (by linarith [hn.2]) hpn
  have hdenAtBot : Filter.Tendsto (fun n => (1 - un n) * pn n) Filter.atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hdenom, hdenpos⟩
  have hinv : Filter.Tendsto (fun n => ((1 - un n) * pn n)⁻¹) Filter.atTop Filter.atTop := by
    have := tendsto_inv_nhdsGT_zero.comp hdenAtBot
    simpa [Function.comp_def] using this
  have harg : Filter.Tendsto
      (fun n => un n * (1 - pn n) / ((1 - un n) * pn n)) Filter.atTop Filter.atTop := by
    have hmul : Filter.Tendsto
        (fun n => un n * (1 - pn n) * ((1 - un n) * pn n)⁻¹) Filter.atTop Filter.atTop :=
      hnum'.pos_mul_atTop hγ0 hinv
    refine hmul.congr (fun n => ?_)
    rw [div_eq_mul_inv]
  have hlog : Filter.Tendsto (fun n => Jp' (pn n) (un n)) Filter.atTop Filter.atTop := by
    have := Real.tendsto_log_atTop.comp harg
    unfold Jp'
    simpa [Function.comp_def] using this
  have hscaled : Filter.Tendsto (fun n => ((d:ℝ) - 1) * Jp' (pn n) (un n)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hd1 hlog
  have hfin : Filter.Tendsto (fun n => (1 - un n)⁻¹) Filter.atTop (𝓝 ((1 - γ)⁻¹)) := by
    have h1γ : (1 - γ) ≠ 0 := ne_of_gt (by linarith)
    exact (h1u.inv₀ h1γ)
  have hcongr : (fun n => hpd (pn n) d (un n)) =ᶠ[Filter.atTop]
      (fun n => (1 - un n)⁻¹ - ((d:ℝ) - 1) * Jp' (pn n) (un n)) := by
    filter_upwards [hun] with n hn
    exact hpd_eq hn.1 hn.2
  rw [Filter.tendsto_congr' hcongr]
  have hneg : Filter.Tendsto (fun n => -(((d:ℝ) - 1) * Jp' (pn n) (un n))) Filter.atTop Filter.atBot :=
    tendsto_neg_atTop_atBot.comp hscaled
  have hres : Filter.Tendsto
      (fun n => (1 - un n)⁻¹ + -(((d:ℝ) - 1) * Jp' (pn n) (un n))) Filter.atTop Filter.atBot :=
    hfin.add_atBot hneg
  simpa [sub_eq_add_neg] using hres

end UpperTailOptimizers
