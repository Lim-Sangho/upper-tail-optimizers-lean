import UpperTailOptimizers.Bipodality.QualRegions

/-!
# Multipliers of the maximizers near the analytic family

For `ε` near `ε₀` and small `ϑ > 0`, every entropy maximizer at `(ε, ε^m + ϑ)` admits qualifying
directions whose Euler–Lagrange multipliers are arbitrarily close to

  `β₀(ε) = (S₀'(ζ) - S₀'(ε)) / (γ(ζ) - γ(ε))`,   `α₀(ε) = S₀'(ε) - β₀(ε) γ(ε)`,

where `γ(u) = m ε^{m-d} u^{d-1}` and `ζ = ζ_d(ε)` (draft `kb:prop:multipliers`).
-/

namespace UpperTailOptimizers

open MeasureTheory Set Filter Topology

/-- `γ(u) = m ε^{m-d} u^{d-1}`, the value of `Γ_W` on a row of degree `u` against a row of degree
`ε`. -/
noncomputable def gammaVal (m d : ℕ) (ε u : ℝ) : ℝ := m * (ε ^ (m - d) * u ^ (d - 1))

/-- The limiting multiplier of the `H`-density constraint. -/
noncomputable def beta₀ (m d : ℕ) (ε : ℝ) : ℝ :=
  (dS0 (zetaFun d ε) - dS0 ε) / (gammaVal m d ε (zetaFun d ε) - gammaVal m d ε ε)

/-- The limiting multiplier of the edge constraint. -/
noncomputable def alpha₀ (m d : ℕ) (ε : ℝ) : ℝ := dS0 ε - beta₀ m d ε * gammaVal m d ε ε

theorem continuousAt_dS0 {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) : ContinuousAt dS0 u :=
  (hasDerivAt_dS0 hu.1.ne' (ne_of_lt hu.2)).continuousAt

/-- **Uniform constants for the multipliers near `ε₀`.** -/
theorem exists_uniform_constants_mult {d m : ℕ} (hd : 2 ≤ d) (hm0 : 0 < m) {ε₀ : ℝ}
    (hε₀ : ε₀ ∈ Ioo (0:ℝ) 1) (hε₀r : ε₀ ≠ rStar d) :
    ∃ η a g N : ℝ, 0 < η ∧ 0 < a ∧ a ≤ 1 / 4 ∧ 0 < g ∧ 0 ≤ N ∧ ∀ ε, |ε - ε₀| < η →
      ε ∈ Ioo (0:ℝ) 1 ∧ ε ≠ rStar d ∧ ε ∈ Icc (2 * a) (1 - 2 * a) ∧
      zetaFun d ε ∈ Icc (2 * a) (1 - 2 * a) ∧
      g ≤ |gammaVal m d ε (zetaFun d ε) - gammaVal m d ε ε| ∧
      |dS0 (zetaFun d ε) - dS0 ε| ≤ N := by
  obtain ⟨hζ₀m, hζ₀ne, -⟩ := zetaFun_crit hd hε₀.1 hε₀.2 hε₀r
  set ζ₀ := zetaFun d ε₀ with hζ₀
  have hzc := continuousAt_zetaFun hd hε₀
  set a : ℝ := min (min ε₀ (1 - ε₀)) (min ζ₀ (1 - ζ₀)) / 4 with ha
  have ha0 : 0 < a := by
    have : 0 < min (min ε₀ (1 - ε₀)) (min ζ₀ (1 - ζ₀)) :=
      lt_min (lt_min hε₀.1 (by linarith [hε₀.2])) (lt_min hζ₀m.1 (by linarith [hζ₀m.2]))
    positivity
  have ha4 : a ≤ 1 / 4 := by
    have h1 : min (min ε₀ (1 - ε₀)) (min ζ₀ (1 - ζ₀)) ≤ ε₀ :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 : min (min ε₀ (1 - ε₀)) (min ζ₀ (1 - ζ₀)) ≤ 1 - ε₀ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    rw [ha]; linarith
  have hε₀a : ε₀ ∈ Icc (4 * a) (1 - 4 * a) := by
    have h1 : min (min ε₀ (1 - ε₀)) (min ζ₀ (1 - ζ₀)) ≤ ε₀ :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 : min (min ε₀ (1 - ε₀)) (min ζ₀ (1 - ζ₀)) ≤ 1 - ε₀ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    rw [ha]; constructor <;> linarith
  have hζ₀a : ζ₀ ∈ Icc (4 * a) (1 - 4 * a) := by
    have h1 : min (min ε₀ (1 - ε₀)) (min ζ₀ (1 - ζ₀)) ≤ ζ₀ :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : min (min ε₀ (1 - ε₀)) (min ζ₀ (1 - ζ₀)) ≤ 1 - ζ₀ :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    rw [ha]; constructor <;> linarith
  -- the gap of `γ`
  set G : ℝ → ℝ := fun ε => gammaVal m d ε (zetaFun d ε) - gammaVal m d ε ε with hG
  have hGc : ContinuousAt G ε₀ := by
    simp only [hG, gammaVal]
    exact ((continuousAt_const.mul ((continuousAt_id.pow _).mul (hzc.pow _))).sub
      (continuousAt_const.mul ((continuousAt_id.pow _).mul (continuousAt_id.pow _))))
  have hG0 : G ε₀ ≠ 0 := by
    simp only [hG, gammaVal]
    rw [← mul_sub, ← mul_sub]
    refine mul_ne_zero (by exact_mod_cast hm0.ne') (mul_ne_zero (pow_ne_zero _ hε₀.1.ne') ?_)
    rw [sub_ne_zero]
    intro h
    have hinj := (pow_left_strictMonoOn₀ (M₀ := ℝ) (n := d - 1) (by omega)).injOn
    exact hζ₀ne (hinj (Set.mem_Ici.mpr hζ₀m.1.le) (Set.mem_Ici.mpr hε₀.1.le) h)
  have hGpos : 0 < |G ε₀| := abs_pos.mpr hG0
  -- the gap of `S₀'`
  set Nf : ℝ → ℝ := fun ε => dS0 (zetaFun d ε) - dS0 ε with hNf
  have hNc : ContinuousAt Nf ε₀ := by
    have h1 : ContinuousAt (fun ε => dS0 (zetaFun d ε)) ε₀ :=
      ContinuousAt.comp (g := dS0) (f := zetaFun d) (continuousAt_dS0 hζ₀m) hzc
    exact h1.sub (continuousAt_dS0 hε₀)
  -- neighbourhoods
  have ev₁ : ∀ᶠ ε in 𝓝 ε₀, ε ∈ Ioo (ε₀ - 2 * a) (ε₀ + 2 * a) :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have ev₂ : ∀ᶠ ε in 𝓝 ε₀, zetaFun d ε ∈ Ioo (ζ₀ - 2 * a) (ζ₀ + 2 * a) :=
    hzc.eventually_mem (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  have ev₃ : ∀ᶠ ε in 𝓝 ε₀, |G ε₀| / 2 < |G ε| :=
    (continuous_abs.continuousAt.comp hGc).eventually (Ioi_mem_nhds (half_lt_self hGpos))
  have ev₄ : ∀ᶠ ε in 𝓝 ε₀, |Nf ε| < |Nf ε₀| + 1 :=
    (continuous_abs.continuousAt.comp hNc).eventually (Iio_mem_nhds (lt_add_one _))
  have ev₅ : ∀ᶠ ε in 𝓝 ε₀, ε ≠ rStar d := continuousAt_id.eventually_ne hε₀r
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp (ev₁.and (ev₂.and (ev₃.and (ev₄.and ev₅))))
  refine ⟨η, a, |G ε₀| / 2, |Nf ε₀| + 1, hη, ha0, ha4, half_pos hGpos, by positivity,
    fun ε hε => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hball (show dist ε ε₀ < η by rwa [Real.dist_eq])
  have hεI : ε ∈ Icc (2 * a) (1 - 2 * a) := ⟨by linarith [h1.1, hε₀a.1], by linarith [h1.2, hε₀a.2]⟩
  refine ⟨⟨by linarith [hεI.1], by linarith [hεI.2]⟩, h5, hεI,
    ⟨by linarith [h2.1, hζ₀a.1], by linarith [h2.2, hζ₀a.2]⟩, h3.le, h4.le⟩

theorem gammaVal_mem {m d : ℕ} {ε u : ℝ} (hε : ε ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1) :
    gammaVal m d ε u ∈ Icc (0:ℝ) m := by
  unfold gammaVal
  have h1 : ε ^ (m - d) * u ^ (d - 1) ∈ Icc (0:ℝ) 1 :=
    ⟨mul_nonneg (pow_nonneg hε.1 _) (pow_nonneg hu.1 _),
      mul_le_one₀ (pow_le_one₀ hε.1 hε.2) (pow_nonneg hu.1 _) (pow_le_one₀ hu.1 hu.2)⟩
  exact ⟨mul_nonneg (Nat.cast_nonneg _) h1.1, by
    calc (m : ℝ) * (ε ^ (m - d) * u ^ (d - 1)) ≤ m * 1 :=
          mul_le_mul_of_nonneg_left h1.2 (Nat.cast_nonneg _)
      _ = m := mul_one _⟩

/-- The arithmetic of the smallness conditions of `Graphon.exists_regions`. -/
theorem regions_conditions_arith {K ϑ t ω τ iI Q₁ r2 : ℝ} (hK : 0 < K) (hϑ : 0 < ϑ) (ht : 0 < t)
    (hω : 0 < ω) (hτ : 0 < τ)
    (h1 : ϑ < ω ^ 2 / (4 * K)) (h2 : ϑ < τ ^ 2 / (64 * K)) (h3 : ϑ < ω / K)
    (h4 : ϑ < 1 / (16 * K)) (h5 : t ≤ ω ^ 2 / (4 * K ^ 2)) (h6 : t ≤ τ ^ 2 / (16 * K ^ 2))
    (hQ : Q₁ ^ 2 ≤ K * ϑ) (hIlow : ϑ / K ≤ iI) (hIup : iI ≤ K * ϑ) (hr : r2 ≤ K * ϑ * t) :
    Q₁ / ω ≤ 1 / 2 ∧ Q₁ / τ ≤ 1 / 8 ∧ Real.sqrt iI * Real.sqrt r2 / ω ≤ iI / 2 ∧
      r2 / τ ^ 2 ≤ iI / 16 ∧ iI ≤ 1 / 16 ∧ Q₁ ≤ ω ∧ iI ≤ ω ∧ 0 < iI := by
  have hKϑω : K * ϑ < ω ^ 2 / 4 := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < 4 * K)).mp h1
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 4)]; linarith
  have hKϑτ : K * ϑ < τ ^ 2 / 64 := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < 64 * K)).mp h2
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 64)]; linarith
  have hQ₁ω : Q₁ < ω / 2 := by
    have h : Q₁ ^ 2 < (ω / 2) ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h
  have hQ₁τ : Q₁ < τ / 8 := by
    have h : Q₁ ^ 2 < (τ / 8) ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h
  have hIpos : 0 < iI := lt_of_lt_of_le (by positivity) hIlow
  have hKϑ : K * ϑ < ω := by have := (lt_div_iff₀ hK).mp h3; linarith
  have hKϑ16 : K * ϑ < 1 / 16 := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < 16 * K)).mp h4
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 16)]; linarith
  have hϑI : ϑ ≤ K * iI := by have := (div_le_iff₀ hK).mp hIlow; linarith
  have hr2ω : r2 ≤ ω ^ 2 * iI / 4 := by
    calc r2 ≤ K * ϑ * t := hr
      _ ≤ K * (K * iI) * (ω ^ 2 / (4 * K ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hϑI hK.le) h5 ht.le (by positivity)
      _ = ω ^ 2 * iI / 4 := by field_simp
  have hr2τ : r2 ≤ τ ^ 2 * iI / 16 := by
    calc r2 ≤ K * ϑ * t := hr
      _ ≤ K * (K * iI) * (τ ^ 2 / (16 * K ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hϑI hK.le) h6 ht.le (by positivity)
      _ = τ ^ 2 * iI / 16 := by field_simp
  refine ⟨?_, ?_, ?_, ?_, by linarith, by linarith, by linarith, hIpos⟩
  · rw [div_le_iff₀ hω]; linarith
  · rw [div_le_iff₀ hτ]; linarith
  · have hs : Real.sqrt r2 ≤ ω * Real.sqrt iI / 2 := by
      have h2' : r2 ≤ (ω * Real.sqrt iI / 2) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hIpos.le]; linarith
      calc Real.sqrt r2 ≤ Real.sqrt ((ω * Real.sqrt iI / 2) ^ 2) := Real.sqrt_le_sqrt h2'
        _ = ω * Real.sqrt iI / 2 := Real.sqrt_sq (by positivity)
    rw [div_le_iff₀ hω]
    calc Real.sqrt iI * Real.sqrt r2 ≤ Real.sqrt iI * (ω * Real.sqrt iI / 2) :=
          mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
      _ = iI / 2 * ω := by
          have := Real.mul_self_sqrt hIpos.le
          nlinarith
  · rw [div_le_iff₀ (by positivity)]; linarith

/-- The final arithmetic of the multiplier bounds. -/
theorem qual_final_arith {δ g N mR ν₀ e Lτ Nd Dd γ₁a β β₀ α α₀ : ℝ} (hδ : 0 < δ) (hg : 0 < g)
    (hN : 0 ≤ N) (hmR : 0 ≤ mR) (hν₀ : 0 < ν₀) (he0 : 0 ≤ e)
    (he : e ≤ ν₀) (hLτ : Lτ ≤ ν₀) (hNd : Nd ≤ N) (hNd0 : 0 ≤ Nd) (hDd : Dd ≤ mR)
    (hDd0 : 0 ≤ Dd) (hγ₁ : γ₁a ≤ mR) (hγ₁0 : 0 ≤ γ₁a)
    (hν₁ : ν₀ ≤ δ / (4 * (N + mR) / g ^ 2 + 1))
    (hν₂ : ν₀ ≤ δ / (1 + (N / g + δ) + 4 * (N + mR) / g ^ 2 * mR))
    (hβ₀ : |β₀| ≤ N / g)
    (hβ : |β - β₀| ≤ 4 * max e Lτ * (Nd + Dd) / g ^ 2)
    (hα : |α - α₀| ≤ Lτ + |β| * e + 4 * max e Lτ * (Nd + Dd) / g ^ 2 * γ₁a) :
    |β - β₀| ≤ δ ∧ |α - α₀| ≤ δ := by
  set Cβ : ℝ := 4 * (N + mR) / g ^ 2 with hCβ
  have hCβ0 : 0 ≤ Cβ := by positivity
  have hmax : max e Lτ ≤ ν₀ := max_le he hLτ
  have hmax0 : 0 ≤ max e Lτ := le_trans he0 (le_max_left _ _)
  have hB : 4 * max e Lτ * (Nd + Dd) / g ^ 2 ≤ Cβ * ν₀ := by
    rw [hCβ, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
    have h1 : max e Lτ * (Nd + Dd) ≤ ν₀ * (N + mR) :=
      mul_le_mul hmax (add_le_add hNd hDd) (by positivity) hν₀.le
    nlinarith
  have hB0 : 0 ≤ 4 * max e Lτ * (Nd + Dd) / g ^ 2 := by positivity
  have hCν : Cβ * ν₀ ≤ δ := by
    have h1 := (le_div_iff₀ (by positivity : (0:ℝ) < Cβ + 1)).mp hν₁
    nlinarith
  have hβδ : |β - β₀| ≤ δ := le_trans hβ (le_trans hB hCν)
  refine ⟨hβδ, ?_⟩
  have hβabs : |β| ≤ N / g + δ := by
    have := abs_sub_abs_le_abs_sub β β₀
    linarith
  have h1 : |β| * e ≤ (N / g + δ) * ν₀ := mul_le_mul hβabs he he0 (by positivity)
  have h2 : 4 * max e Lτ * (Nd + Dd) / g ^ 2 * γ₁a ≤ Cβ * ν₀ * mR :=
    mul_le_mul hB hγ₁ hγ₁0 (by positivity)
  have h3 : (1 + (N / g + δ) + Cβ * mR) * ν₀ ≤ δ := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 1 + (N / g + δ) + Cβ * mR)).mp hν₂
    linarith
  have h4 : (1 + (N / g + δ) + Cβ * mR) * ν₀ = ν₀ + (N / g + δ) * ν₀ + Cβ * ν₀ * mR := by ring
  linarith

set_option maxHeartbeats 4000000 in
/-- **The multipliers of the maximizers** (draft `kb:prop:multipliers`): uniformly for `ε` near
`ε₀`, as `ϑ ↘ 0` every maximizer has qualifying directions with multipliers tending to
`(α₀(ε), β₀(ε))`. -/
theorem KRRSFamily.exists_qualDirs {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    [DecidableRel H.Adj] {d : ℕ} {ε₀ : ℝ} (F : KRRSFamily H d ε₀) (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card) (hε₀ : ε₀ ∈ Ioo (0:ℝ) 1)
    (hε₀r : ε₀ ≠ rStar d) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ δ : ℝ, 0 < δ → ∃ Δ : ℝ, 0 < Δ ∧ ∀ (ε ϑ : ℝ) (W : Graphon),
      |ε - ε₀| < η₁ → 0 < ϑ → ϑ < Δ → IsMaximizer H W ε (ε ^ H.edgeFinset.card + ϑ) →
      ε ∈ F.U ∧ ϑ < F.Δ ∧
      ∃ Q : QualDirs H W, |Q.beta - beta₀ H.edgeFinset.card d ε| ≤ δ ∧
        |Q.alpha - alpha₀ H.edgeFinset.card d ε| ≤ δ := by
  classical
  set m : ℕ := H.edgeFinset.card with hmdef
  obtain ⟨ηS₀, ΔS₀, K, hηS₀, hΔS₀, hK, hstruct⟩ := F.exists_competitor_structure hd hreg hm hε₀ hε₀r
  obtain ⟨ηE, ΔE, KE, hηE, hΔE, -, hfam⟩ := KRRSFamily.exists_entropy_gap_le H F hd hreg hm hε₀ hε₀r
  obtain ⟨ηU, a, g, N, hηU, ha, ha4, hg, hN, hunif⟩ :=
    exists_uniform_constants_mult (m := m) hd (by omega) hε₀ hε₀r
  refine ⟨min (min ηS₀ ηE) ηU, lt_min (lt_min hηS₀ hηE) hηU, fun δ hδ => ?_⟩
  set mR : ℝ := (m : ℝ) with hmR
  have hmR0 : 0 ≤ mR := Nat.cast_nonneg _
  set dR : ℝ := (d : ℝ) with hdR
  have hdR1 : 1 ≤ dR := by rw [hdR]; exact_mod_cast (by omega : 1 ≤ d)
  set L : ℝ := 1 / a with hL
  have hL0 : 0 < L := by positivity
  set ν₀ : ℝ := min (g / 4) (min (δ / (4 * (N + mR) / g ^ 2 + 1))
    (δ / (1 + (N / g + δ) + 4 * (N + mR) / g ^ 2 * mR))) with hν₀
  have hν₀pos : 0 < ν₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  set τ : ℝ := min a (ν₀ / (L + 1)) with hτ
  have hτpos : 0 < τ := lt_min ha (by positivity)
  have hτa : τ ≤ a := min_le_left _ _
  have hLτ : L * τ ≤ ν₀ := by
    have h1 : τ ≤ ν₀ / (L + 1) := min_le_right _ _
    have h2 : L * τ ≤ L * (ν₀ / (L + 1)) := mul_le_mul_of_nonneg_left h1 hL0.le
    have h3 : L * (ν₀ / (L + 1)) ≤ ν₀ := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith
  set Cω : ℝ := 2 * mR ^ 2 + 2 * mR * dR + 1 with hCω
  have hCω0 : 0 < Cω := by positivity
  set ω : ℝ := ν₀ / Cω with hω
  have hωpos : 0 < ω := by positivity
  set t₁ : ℝ := min (ω ^ 2 / (4 * K ^ 2)) (τ ^ 2 / (16 * K ^ 2)) with ht₁
  have ht₁pos : 0 < t₁ := lt_min (by positivity) (by positivity)
  set Δ : ℝ := min (min ΔS₀ ΔE) (min (t₁ ^ 3) (min (1 / (16 * K)) (min (ω / K)
    (min (ω ^ 2 / (4 * K)) (τ ^ 2 / (64 * K)))))) with hΔ
  have hΔpos : 0 < Δ := by
    refine lt_min (lt_min hΔS₀ hΔE) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))
  refine ⟨Δ, hΔpos, fun ε ϑ W hε hϑ0 hϑΔ hmax => ?_⟩
  have hεS₀ : |ε - ε₀| < ηS₀ := lt_of_lt_of_le hε (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεE : |ε - ε₀| < ηE := lt_of_lt_of_le hε (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεU : |ε - ε₀| < ηU := lt_of_lt_of_le hε (min_le_right _ _)
  have hϑS₀ : ϑ < ΔS₀ := lt_of_lt_of_le hϑΔ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hϑE : ϑ < ΔE := lt_of_lt_of_le hϑΔ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hΔr : Δ ≤ min (t₁ ^ 3) (min (1 / (16 * K)) (min (ω / K)
      (min (ω ^ 2 / (4 * K)) (τ ^ 2 / (64 * K))))) := min_le_right _ _
  have hϑt : ϑ < t₁ ^ 3 := lt_of_lt_of_le hϑΔ (le_trans hΔr (min_le_left _ _))
  have hϑ16 : ϑ < 1 / (16 * K) :=
    lt_of_lt_of_le hϑΔ (le_trans hΔr (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hϑω : ϑ < ω / K := lt_of_lt_of_le hϑΔ (le_trans hΔr (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hϑω2 : ϑ < ω ^ 2 / (4 * K) := lt_of_lt_of_le hϑΔ (le_trans hΔr (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hϑτ : ϑ < τ ^ 2 / (64 * K) := lt_of_lt_of_le hϑΔ (le_trans hΔr (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))))
  obtain ⟨hεI, hεr, hεa, hζa, hgγ, hNε⟩ := hunif ε hεU
  set ζ : ℝ := zetaFun d ε with hζ
  have hεIcc : ε ∈ Icc (0:ℝ) 1 := ⟨hεI.1.le, hεI.2.le⟩
  have hζIcc : ζ ∈ Icc (0:ℝ) 1 := ⟨by linarith [hζa.1], by linarith [hζa.2]⟩
  obtain ⟨he, ht, hopt⟩ := hmax
  obtain ⟨hεUF, hϑF, -⟩ := hfam ε ϑ hεE hϑ0 hϑE
  have hcomp : (F.graphon ε ϑ).entropy ≤ W.entropy := by
    obtain ⟨-, -, -, -, -, hge, hgt⟩ := F.graphon_spec hεUF hϑ0 hϑF
    exact hopt _ hge hgt
  obtain ⟨-, -, hL2, -, I, hIm, -, hIlow, hIup, hcross⟩ :=
    hstruct ε ϑ W hεS₀ hϑ0 hϑS₀ he ht hcomp
  refine ⟨hεUF, hϑF, ?_⟩
  -- the small quantities
  set t : ℝ := ϑ ^ ((1:ℝ) / 3) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hϑ0 _
  have ht3 : t ^ 3 = ϑ := cube_rpow_third hϑ0.le
  have htt₁ : t ≤ t₁ := by
    by_contra h; push Not at h
    have := pow_lt_pow_left₀ h ht₁pos.le (by norm_num : (3:ℕ) ≠ 0)
    rw [ht3] at this; exact absurd hϑt (not_lt.mpr this.le)
  have hQ₁sq : (W.constDist ε) ^ 2 ≤ K * ϑ := by
    have h1 := W.constDist_le_sqrt ε
    have h0 : 0 ≤ ∫ p : ℝ × ℝ, (W.toFun p.1 p.2 - ε) ^ 2 ∂gμ := integral_nonneg fun _ => sq_nonneg _
    calc (W.constDist ε) ^ 2 ≤ Real.sqrt (∫ p : ℝ × ℝ, (W.toFun p.1 p.2 - ε) ^ 2 ∂gμ) ^ 2 :=
          pow_le_pow_left₀ (W.constDist_nonneg ε) h1 2
      _ = ∫ p : ℝ × ℝ, (W.toFun p.1 p.2 - ε) ^ 2 ∂gμ := Real.sq_sqrt h0
      _ ≤ K * ϑ := hL2
  have hr2bound : ∫ p : ℝ × ℝ, (W.toFun p.1 p.2 - crossProfile ε ζ I p) ^ 2 ∂gμ ≤ K * ϑ * t := by
    have e1 : K * (ϑ * ϑ ^ ((1:ℝ) / 3)) = K * ϑ * t := by rw [htdef]; ring
    rw [← e1]; exact hcross
  obtain ⟨hc1, hc2, hc3, hc4, hI16, hQω, hIω, hIpos⟩ := regions_conditions_arith hK hϑ0 ht0 hωpos
    hτpos hϑω2 hϑτ hϑω hϑ16
    (le_trans htt₁ (min_le_left _ _)) (le_trans htt₁ (min_le_right _ _)) hQ₁sq hIlow hIup hr2bound
  obtain ⟨E₁, E₂, hE₁m, hE₂m, hE₁s, hE₂s, hE₁pos, hE₂pos, hW₁, hW₂, hΓ₁, hΓ₂⟩ :=
    W.exists_regions H hd hreg hεIcc hζIcc hωpos hτpos hIm hIpos hc1 hc2 hc3 hc4 hI16
  -- the multipliers
  set e : ℝ := mR * (mR * (ω + W.constDist ε)) + mR * (dR - 1) * (ω + (unitμ I).toReal) with he_def
  have hdR0 : 0 ≤ dR - 1 := by linarith
  have he0 : 0 ≤ e := by
    have := W.constDist_nonneg ε
    have : 0 ≤ (unitμ I).toReal := ENNReal.toReal_nonneg
    positivity
  have heν : e ≤ ν₀ := by
    have h1 : mR * (mR * (ω + W.constDist ε)) ≤ mR * (mR * (2 * ω)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith only [hQω]) hmR0) hmR0
    have h2 : mR * (dR - 1) * (ω + (unitμ I).toReal) ≤ mR * dR * (2 * ω) := by
      have h21 : mR * (dR - 1) ≤ mR * dR := mul_le_mul_of_nonneg_left (by linarith only) hmR0
      have h22 : ω + (unitμ I).toReal ≤ 2 * ω := by linarith only [hIω]
      exact mul_le_mul h21 h22 (by positivity) (by positivity)
    have h3 : ν₀ = Cω * ω := by rw [hω]; field_simp
    have h4 : mR * (mR * (2 * ω)) + mR * dR * (2 * ω) ≤ Cω * ω := by
      have : Cω * ω = mR * (mR * (2 * ω)) + mR * dR * (2 * ω) + ω := by rw [hCω]; ring
      linarith only [this, hωpos]
    rw [he_def]
    linarith only [h1, h2, h3, h4]
  have hin₁ : ∀ p ∈ E₁, W.toFun p.1 p.2 ∈ Icc a (1 - a) := fun p hp => by
    have := abs_le.mp (hW₁ p hp)
    constructor <;> linarith only [this.1, this.2, hεa.1, hεa.2, hτa]
  have hin₂ : ∀ p ∈ E₂, W.toFun p.1 p.2 ∈ Icc a (1 - a) := fun p hp => by
    have := abs_le.mp (hW₂ p hp)
    constructor <;> linarith only [this.1, this.2, hζa.1, hζa.2, hτa]
  have hLip : ∀ w ∈ Icc a (1 - a), ∀ w' ∈ Icc a (1 - a), |dS0 w - dS0 w'| ≤ L * |w - w'| :=
    fun w hw w' hw' => abs_dS0_sub_le ha (by linarith only [ha4]) hw hw'
  have hg4 : ν₀ ≤ g / 4 := min_le_left _ _
  obtain ⟨Q, hβ, hα⟩ := W.exists_qualDirs_of_regions H hE₁m hE₂m hE₁s hE₂s (η := a)
    (c₁ := ε) (c₂ := ζ) (γ₁ := gammaVal m d ε ε) (γ₂ := gammaVal m d ε ζ) (τ := τ) (e := e)
    (L := L) (g := g) ha (by linarith only [ha4]) hE₁pos hE₂pos hW₁ hW₂ hin₁ hin₂
    ⟨by linarith only [hεa.1, ha], by linarith only [hεa.2, ha]⟩
    ⟨by linarith only [hζa.1, ha], by linarith only [hζa.2, ha]⟩
    hΓ₁ hΓ₂ hLip hg hgγ he0 hL0.le (le_trans heν hg4) (le_trans hLτ hg4)
  refine ⟨Q, ?_⟩
  have hD₀ : |gammaVal m d ε ζ - gammaVal m d ε ε| ≤ mR := by
    have h1 := gammaVal_mem (m := m) (d := d) hεIcc hζIcc
    have h2 := gammaVal_mem (m := m) (d := d) hεIcc hεIcc
    rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  have hβ₀ : |beta₀ m d ε| ≤ N / g := by
    unfold beta₀
    rw [abs_div, div_le_div_iff₀ (lt_of_lt_of_le hg hgγ) hg]
    exact mul_le_mul hNε hgγ hg.le hN
  have hγ₁ : |gammaVal m d ε ε| ≤ mR := by
    have h2 := gammaVal_mem (m := m) (d := d) hεIcc hεIcc
    rw [abs_of_nonneg h2.1]; exact h2.2
  have hαeq : alpha₀ m d ε = dS0 ε - (dS0 ζ - dS0 ε) / (gammaVal m d ε ζ - gammaVal m d ε ε)
      * gammaVal m d ε ε := rfl
  rw [hαeq]
  exact qual_final_arith hδ hg hN hmR0 hν₀pos he0 heν hLτ hNε (abs_nonneg _) hD₀
    (abs_nonneg _) hγ₁ (abs_nonneg _) (le_trans (min_le_right _ _) (min_le_left _ _))
    (le_trans (min_le_right _ _) (min_le_right _ _)) hβ₀ hβ hα

end UpperTailOptimizers
