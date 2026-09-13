import UpperTailOptimizers.Bipodality.Bipodal

/-!
# Uniform bipodality of maximizers

The hypotheses of `QualDirs.bipodal_of_bounds` hold uniformly for `ε` near a nonexceptional
`ε₀` and all small surpluses `ϑ`.  The contraction constants are controlled by the identity

  `2c(1-c) |β₀| m(d-1) c^{d-2} ε^{m-d} = 1 - c(1-c) Γ^gap''(c)`,   `c ∈ {ε, ζ_d(ε)}`,

whose right side is `< 1` because both zeros of `Γ^gap` are nondegenerate (`gapCurv_pos`).

## Contents

* `contraction_limit_eq` — the identity above;
* `exists_bipodal_constants` — uniform constants near `ε₀`;
* `KRRSFamily.exists_bipodal` — every maximizer is bipodal with parameters near the boundary.
-/

set_option linter.unusedSectionVars false

namespace UpperTailOptimizers

open MeasureTheory Set SingularEndpoint Filter Topology

/-- **The contraction constant at the limiting multiplier.** -/
theorem contraction_limit_eq {d m v : ℕ} (hd : 2 ≤ d) (hmv : v * d = 2 * m) (hm : 0 < m) {ε c : ℝ}
    (hε : ε ∈ Ioo (0:ℝ) 1) (hεr : ε ≠ rStar d) (hc : c ∈ Ioo (0:ℝ) 1) :
    2 * (c * (1 - c)) * (-beta₀ m d ε) * ((m : ℝ) * (d - 1 : ℕ)) * (c ^ (d - 2) * ε ^ (m - d))
      = 1 - c * (1 - c) * gapCurv d (ε, c) := by
  have hψ := beta₀_mul_eq_psiStar hd hmv hm hε hεr
  have hmvR : (v : ℝ) * d = 2 * m := by exact_mod_cast hmv
  have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  have hK : c * (1 - c) ≠ 0 := mul_ne_zero hc.1.ne' (by linarith [hc.2])
  have hC : c ^ (d - 2) ≠ 0 := pow_ne_zero _ hc.1.ne'
  have hD : ((d : ℝ) * ((d : ℝ) - 1)) ≠ 0 := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    exact mul_ne_zero (by linarith) (by linarith)
  have hgc : gapCurv d (ε, c) = ((d:ℝ) * ((d:ℝ) - 1) * c ^ (d - 2))
      * (psiStar d ε - (-1 / (c * (1 - c))) / ((d:ℝ) * ((d:ℝ) - 1) * c ^ (d - 2))) := rfl
  have hX : ((d:ℝ) * ((d:ℝ) - 1) * c ^ (d - 2))
      * ((-1 / (c * (1 - c))) / ((d:ℝ) * ((d:ℝ) - 1) * c ^ (d - 2))) = -1 / (c * (1 - c)) :=
    mul_div_cancel₀ _ (mul_ne_zero hD hC)
  have hY : c * (1 - c) * (-1 / (c * (1 - c))) = -1 := by
    rw [mul_div_assoc', mul_neg_one, neg_div, div_self hK]
  have e : c * (1 - c) * gapCurv d (ε, c)
      = c * (1 - c) * ((d:ℝ) * ((d:ℝ) - 1) * c ^ (d - 2)) * psiStar d ε + 1 := by
    have h1 := mul_sub ((d:ℝ) * ((d:ℝ) - 1) * c ^ (d - 2)) (psiStar d ε)
      ((-1 / (c * (1 - c))) / ((d:ℝ) * ((d:ℝ) - 1) * c ^ (d - 2)))
    rw [hgc, h1, hX]
    have h2 := mul_sub (c * (1 - c)) ((d:ℝ) * ((d:ℝ) - 1) * c ^ (d - 2) * psiStar d ε)
      (-1 / (c * (1 - c)))
    rw [h2, hY]; ring
  rw [e, hd1, ← hψ]
  linear_combination (c * (1 - c)) * ((d:ℝ) - 1) * c ^ (d - 2) * beta₀ m d ε * ε ^ (m - d) * hmvR

theorem beta₀_neg {d m v : ℕ} (hd : 2 ≤ d) (hmv : v * d = 2 * m) (hm : 0 < m) {ε : ℝ}
    (hε : ε ∈ Ioo (0:ℝ) 1) (hεr : ε ≠ rStar d) : beta₀ m d ε < 0 := by
  have hψ := beta₀_mul_eq_psiStar hd hmv hm hε hεr
  have hneg := psiStar_neg hd hε hεr
  have hv : (0:ℝ) < v := by
    have : 0 < v * d := by rw [hmv]; omega
    exact_mod_cast Nat.pos_of_mul_pos_right this
  have hpos : (0:ℝ) < (v : ℝ) * ε ^ (m - d) := mul_pos hv (pow_pos hε.1 _)
  by_contra h
  push Not at h
  have := mul_nonneg h hpos.le
  linarith

/-- `|γ(ζ) - γ(ε)| ≤ m(d-1)|ζ - ε|` on `[0,1]`. -/
theorem abs_gammaVal_sub_le {m d : ℕ} {ε u w : ℝ} (hε : ε ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1)
    (hw : w ∈ Icc (0:ℝ) 1) :
    |gammaVal m d ε u - gammaVal m d ε w| ≤ (m : ℝ) * (d - 1 : ℕ) * |u - w| := by
  unfold gammaVal
  have e : (m : ℝ) * (ε ^ (m - d) * u ^ (d - 1)) - m * (ε ^ (m - d) * w ^ (d - 1))
      = m * ε ^ (m - d) * (u ^ (d - 1) - w ^ (d - 1)) := by ring
  rw [e, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (pow_nonneg hε.1 _)]
  have h1 := abs_pow_sub_pow_le_of_mem hu hw (d - 1)
  have h2 : ε ^ (m - d) ≤ 1 := pow_le_one₀ hε.1 hε.2
  calc (m : ℝ) * ε ^ (m - d) * |u ^ (d - 1) - w ^ (d - 1)| ≤ m * 1 * ((d - 1 : ℕ) * |u - w|) := by
        gcongr
    _ = _ := by ring

set_option maxHeartbeats 2000000 in
/-- **Uniform constants for bipodality near `ε₀`.** -/
theorem exists_bipodal_constants {d m v : ℕ} (hd : 2 ≤ d) (hmv : v * d = 2 * m) (hm : 0 < m)
    {ε₀ : ℝ} (hε₀ : ε₀ ∈ Ioo (0:ℝ) 1) (hε₀r : ε₀ ≠ rStar d) :
    ∃ η₀ κg η sep μ A Bβ : ℝ, 0 < η₀ ∧ 0 < κg ∧ 0 < η ∧ η ≤ 1 / 2 ∧ 0 < sep ∧ 0 < μ ∧
      0 ≤ A ∧ 0 ≤ Bβ ∧ ∀ ε, |ε - ε₀| < η₀ →
        ε ∈ Ioo (0:ℝ) 1 ∧ ε ≠ rStar d ∧ ε ∈ Icc η (1 - η) ∧
        (∀ u ∈ Icc (0:ℝ) 1, κg * min ((u - ε) ^ 2) ((u - zetaFun d ε) ^ 2) ≤ gapFun d ε u) ∧
        sep ≤ |zetaFun d ε - ε| ∧ |alpha₀ m d ε| ≤ A ∧ |beta₀ m d ε| ≤ Bβ ∧
        2 * (ε * (1 - ε)) * |beta₀ m d ε| * ((m : ℝ) * (d - 1 : ℕ)) * (ε ^ (d - 2) * ε ^ (m - d))
          ≤ 1 - μ ∧
        2 * (zetaFun d ε * (1 - zetaFun d ε)) * |beta₀ m d ε| * ((m : ℝ) * (d - 1 : ℕ))
          * (zetaFun d ε ^ (d - 2) * ε ^ (m - d)) ≤ 1 - μ := by
  obtain ⟨κg, hκg, ηg, hηg, hgap⟩ := gap_quadratic_lower hd hε₀ hε₀r
  obtain ⟨ηu, a, g, N, hηu, ha, ha4, hg, hN, hunif⟩ :=
    exists_uniform_constants_mult (m := m) hd hm hε₀ hε₀r
  obtain ⟨L, hL⟩ := exists_abs_dS0_le (η := 2 * a) (by linarith)
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hL (2 * a) ⟨le_rfl, by linarith⟩)
  obtain ⟨hζ₀m, -, -⟩ := zetaFun_crit hd hε₀.1 hε₀.2 hε₀r
  obtain ⟨hG1, hG2⟩ := gapCurv_pos hd hε₀ hε₀r
  set f₁ : ℝ → ℝ := fun ε => ε * (1 - ε) * gapCurv d (ε, ε) with hf₁
  set f₂ : ℝ → ℝ := fun ε => zetaFun d ε * (1 - zetaFun d ε) * gapCurv d (ε, zetaFun d ε) with hf₂
  have hf₁c : ContinuousAt f₁ ε₀ := by
    have h := ContinuousAt.comp_of_eq (continuousAt_gapCurv hd hε₀ hε₀r hε₀)
      (continuousAt_id.prodMk continuousAt_id) rfl
    exact (continuousAt_id.mul (continuousAt_const.sub continuousAt_id)).mul h
  have hzc := continuousAt_zetaFun hd hε₀
  have hf₂c : ContinuousAt f₂ ε₀ := by
    have h := ContinuousAt.comp_of_eq (continuousAt_gapCurv hd hε₀ hε₀r hζ₀m)
      (continuousAt_id.prodMk hzc) rfl
    exact (hzc.mul (continuousAt_const.sub hzc)).mul h
  have hf₁0 : 0 < f₁ ε₀ := mul_pos (mul_pos hε₀.1 (by linarith [hε₀.2])) hG1
  have hf₂0 : 0 < f₂ ε₀ := mul_pos (mul_pos hζ₀m.1 (by linarith [hζ₀m.2])) hG2
  set μ : ℝ := min (f₁ ε₀) (f₂ ε₀) / 2 with hμ
  have hμ0 : 0 < μ := by positivity
  have ev₁ : ∀ᶠ ε in 𝓝 ε₀, μ < f₁ ε :=
    hf₁c.eventually (lt_mem_nhds (by rw [hμ]; linarith [min_le_left (f₁ ε₀) (f₂ ε₀)]))
  have ev₂ : ∀ᶠ ε in 𝓝 ε₀, μ < f₂ ε :=
    hf₂c.eventually (lt_mem_nhds (by rw [hμ]; linarith [min_le_right (f₁ ε₀) (f₂ ε₀)]))
  obtain ⟨ηc, hηc, hball⟩ := Metric.eventually_nhds_iff.mp (ev₁.and ev₂)
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hd1R : (0:ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d - 1)
  refine ⟨min (min ηg ηu) ηc, κg, 2 * a, g / ((m : ℝ) * (d - 1 : ℕ)), μ, L + N / g * m, N / g,
    lt_min (lt_min hηg hηu) hηc, hκg, by linarith, by linarith, by positivity, hμ0, by positivity,
    by positivity, fun ε hε => ?_⟩
  have hεg : |ε - ε₀| < ηg := lt_of_lt_of_le hε (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεu : |ε - ε₀| < ηu := lt_of_lt_of_le hε (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεc : |ε - ε₀| < ηc := lt_of_lt_of_le hε (min_le_right _ _)
  obtain ⟨hεI, hεr, hgapε⟩ := hgap ε hεg
  obtain ⟨-, -, hεa, hζa, hgε, hNε⟩ := hunif ε hεu
  obtain ⟨hμ₁, hμ₂⟩ := hball (show dist ε ε₀ < ηc by rwa [Real.dist_eq])
  have hmv' := hmv
  have hβneg := beta₀_neg hd hmv hm hεI hεr
  have hζm : zetaFun d ε ∈ Ioo (0:ℝ) 1 := zetaFun_mem hd hεI
  have hεI' : ε ∈ Icc (0:ℝ) 1 := ⟨hεI.1.le, hεI.2.le⟩
  have hζI' : zetaFun d ε ∈ Icc (0:ℝ) 1 := ⟨hζm.1.le, hζm.2.le⟩
  have hgpos : 0 < |gammaVal m d ε (zetaFun d ε) - gammaVal m d ε ε| := lt_of_lt_of_le hg hgε
  have hβbound : |beta₀ m d ε| ≤ N / g := by
    unfold beta₀
    rw [abs_div, div_le_div_iff₀ hgpos hg]
    calc |dS0 (zetaFun d ε) - dS0 ε| * g ≤ N * g := by gcongr
      _ ≤ N * |gammaVal m d ε (zetaFun d ε) - gammaVal m d ε ε| := by gcongr
  refine ⟨hεI, hεr, hεa, hgapε, ?_, ?_, hβbound, ?_, ?_⟩
  · have h1 := abs_gammaVal_sub_le (m := m) (d := d) hεI' hζI' hεI'
    rw [div_le_iff₀ (by positivity)]
    calc g ≤ |gammaVal m d ε (zetaFun d ε) - gammaVal m d ε ε| := hgε
      _ ≤ (m : ℝ) * (d - 1 : ℕ) * |zetaFun d ε - ε| := h1
      _ = |zetaFun d ε - ε| * ((m : ℝ) * (d - 1 : ℕ)) := by ring
  · unfold alpha₀
    have hdS : |dS0 ε| ≤ L := hL ε hεa
    have hγ := gammaVal_mem (m := m) (d := d) hεI' hεI'
    calc |dS0 ε - beta₀ m d ε * gammaVal m d ε ε| ≤ |dS0 ε| + |beta₀ m d ε * gammaVal m d ε ε| :=
          abs_sub _ _
      _ = |dS0 ε| + |beta₀ m d ε| * gammaVal m d ε ε := by rw [abs_mul, abs_of_nonneg hγ.1]
      _ ≤ L + N / g * m := add_le_add hdS (mul_le_mul hβbound hγ.2 hγ.1 (by positivity))
  · rw [abs_of_neg hβneg, contraction_limit_eq hd hmv hm hεI hεr hεI]
    have : μ < ε * (1 - ε) * gapCurv d (ε, ε) := hμ₁
    linarith
  · rw [abs_of_neg hβneg, contraction_limit_eq hd hmv hm hεI hεr hζm]
    have : μ < zetaFun d ε * (1 - zetaFun d ε) * gapCurv d (ε, zetaFun d ε) := hμ₂
    linarith

/-! ### Monotone bounds for the error constants -/

theorem contrCoef_le {m d : ℕ} {β β₀ c ε R κ₁ δ B₁ : ℝ} (hc : c ∈ Icc (0:ℝ) 1)
    (hε : ε ∈ Icc (0:ℝ) 1) (hR : 0 ≤ R) (hκ : 0 ≤ κ₁) (hδ : |β - β₀| ≤ δ) (hB : |β| ≤ B₁) :
    contrCoef m d β c ε R κ₁
      ≤ 2 * (c * (1 - c)) * |β₀| * ((m : ℝ) * (d - 1 : ℕ)) * (c ^ (d - 2) * ε ^ (m - d))
        + δ * ((m : ℝ) * (d - 1 : ℕ)) / 2
        + (2 * B₁ ^ 2 * ((m : ℝ) * (d - 1 : ℕ)) ^ 2 * m * (R + R + 2 * κ₁)
          + 2 * B₁ * ((m : ℝ) * (d - 1 : ℕ)) * (R + R)) := by
  unfold contrCoef
  set M₁ : ℝ := (m : ℝ) * (d - 1 : ℕ) with hM₁
  have hM₁0 : 0 ≤ M₁ := by positivity
  have hK0 : 0 ≤ c * (1 - c) := mul_nonneg hc.1 (by linarith [hc.2])
  have hK4 : c * (1 - c) ≤ 1 / 4 := by nlinarith [sq_nonneg (c - 1 / 2)]
  have hBc0 : 0 ≤ c ^ (d - 2) * ε ^ (m - d) := mul_nonneg (pow_nonneg hc.1 _) (pow_nonneg hε.1 _)
  have hBc1 : c ^ (d - 2) * ε ^ (m - d) ≤ 1 :=
    mul_le_one₀ (pow_le_one₀ hc.1 hc.2) (pow_nonneg hε.1 _) (pow_le_one₀ hε.1 hε.2)
  have hβ : |β| ≤ |β₀| + δ := by
    have := abs_sub_abs_le_abs_sub β β₀; linarith
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hδ
  have h1 : 2 * (c * (1 - c)) * |β| * M₁ * (c ^ (d - 2) * ε ^ (m - d))
      ≤ 2 * (c * (1 - c)) * |β₀| * M₁ * (c ^ (d - 2) * ε ^ (m - d)) + δ * M₁ / 2 := by
    have e : 2 * (c * (1 - c)) * |β| * M₁ * (c ^ (d - 2) * ε ^ (m - d))
        ≤ 2 * (c * (1 - c)) * (|β₀| + δ) * M₁ * (c ^ (d - 2) * ε ^ (m - d)) := by gcongr
    have e2 : 2 * (c * (1 - c)) * δ * M₁ * (c ^ (d - 2) * ε ^ (m - d)) ≤ δ * M₁ / 2 := by
      have : (c * (1 - c)) * (c ^ (d - 2) * ε ^ (m - d)) ≤ 1 / 4 :=
        le_trans (mul_le_of_le_one_right hK0 hBc1) hK4
      nlinarith [mul_nonneg hδ0 hM₁0]
    nlinarith
  have h2 : 2 * |β| ^ 2 * M₁ ^ 2 * m * (R + R + 2 * κ₁) ≤ 2 * B₁ ^ 2 * M₁ ^ 2 * m * (R + R + 2 * κ₁) := by
    gcongr
  have h3 : 2 * |β| * M₁ * (R + R) ≤ 2 * B₁ * M₁ * (R + R) := by gcongr
  linarith

theorem balErr_le {m v d : ℕ} {α β A₁ B₁ : ℝ} (hA : |α| ≤ A₁) (hB : |β| ≤ B₁) :
    balErr m v d α β
      ≤ (2 * (A₁ + B₁ * m) + 2 * A₁ + B₁ * (v * d)) * (B₁ * (m : ℝ) ^ 2) + B₁ * (v * m) := by
  unfold balErr
  have hA0 : 0 ≤ |α| := abs_nonneg _
  have hB0 : 0 ≤ |β| := abs_nonneg _
  have hA1 : 0 ≤ A₁ := le_trans hA0 hA
  have hB1 : 0 ≤ B₁ := le_trans hB0 hB
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hv : (0:ℝ) ≤ v := Nat.cast_nonneg _
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have hX : 2 * (|α| + |β| * m) + 2 * |α| + |β| * (v * d) ≤ 2 * (A₁ + B₁ * m) + 2 * A₁ + B₁ * (v * d) := by
    have h1 : |β| * m ≤ B₁ * m := mul_le_mul_of_nonneg_right hB hm
    have h2 : |β| * (v * d) ≤ B₁ * (v * d) := mul_le_mul_of_nonneg_right hB (mul_nonneg hv hd)
    linarith
  have hY : |β| * (m : ℝ) ^ 2 ≤ B₁ * (m : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hB (sq_nonneg _)
  have hZ : |β| * (v * m) ≤ B₁ * (v * m) := mul_le_mul_of_nonneg_right hB (mul_nonneg hv hm)
  have hX0 : 0 ≤ 2 * (A₁ + B₁ * m) + 2 * A₁ + B₁ * (v * d) := by positivity
  have := mul_le_mul hX hY (mul_nonneg hB0 (sq_nonneg _)) hX0
  linarith


set_option maxHeartbeats 1000000 in
/-- The real arithmetic behind `KRRSFamily.exists_bipodal`. -/
theorem bipodal_arith {τ sep μ κg η B₁ M₁ mR vR CB Rt δ κ₁ : ℝ} (_hτ : 0 < τ) (hsep : 0 < sep)
    (hμ : 0 < μ) (hκg : 0 < κg) (hη : 0 < η) (hB₁ : 0 < B₁) (hM₁ : 0 ≤ M₁) (hmR : 0 < mR)
    (hvR : 0 ≤ vR) (hCB : 0 ≤ CB) (hRt0 : 0 < Rt) (_hRtτ : Rt ≤ τ / 2) (_hRtsep : Rt ≤ sep / 2)
    (hRtμ : Rt ≤ μ / (32 * B₁ ^ 2 * M₁ ^ 2 * mR + 16 * B₁ * M₁ + 1))
    (hδ0 : 0 < δ) (hδμ : δ ≤ μ / (4 * M₁ + 1)) (hδκ : δ ≤ κg * Rt ^ 2 / (16 * (2 + vR)))
    (hκ0 : 0 ≤ κ₁) (hκη : κ₁ ≤ η / (2 * (B₁ * mR ^ 2 + 1)))
    (hκRt2 : κ₁ ≤ Rt / (2 * (B₁ * mR ^ 2 + 1))) (hκRt : κ₁ ≤ Rt) (hκ1 : κ₁ ≤ 1)
    (hκk : κ₁ ≤ κg * Rt ^ 2 / (8 * (4 / η * (B₁ * mR ^ 2 + 1) ^ 2 + 2 * CB) + 1))
    (hκsep : κ₁ ≤ sep / 4) (hκτ : κ₁ ≤ τ * sep / 2) :
    (B₁ * mR ^ 2 + 1) * κ₁ ≤ η / 2 ∧
    B₁ * mR ^ 2 * κ₁ ≤ Rt / 2 ∧
    Real.sqrt ((4 / η * ((B₁ * mR ^ 2 + 1) * κ₁) ^ 2 + 2 * (CB * κ₁) + 2 * (2 * δ + vR * δ)) / κg)
      ≤ Rt / 2 ∧
    2 * κ₁ / sep ≤ 1 / 2 ∧ 2 * κ₁ / sep ≤ τ ∧
    δ * M₁ / 2 + (2 * B₁ ^ 2 * M₁ ^ 2 * mR * (Rt + Rt + 2 * κ₁) + 2 * B₁ * M₁ * (Rt + Rt))
      ≤ μ / 2 := by
  have hB1m : 0 < B₁ * mR ^ 2 + 1 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * (B₁ * mR ^ 2 + 1))).mp hκη
    linarith
  · have h := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * (B₁ * mR ^ 2 + 1))).mp hκRt2
    have e : κ₁ * (2 * (B₁ * mR ^ 2 + 1)) = 2 * (B₁ * mR ^ 2 * κ₁) + 2 * κ₁ := by ring
    linarith
  · set X : ℝ := 4 / η * (B₁ * mR ^ 2 + 1) ^ 2 + 2 * CB with hX
    have hX0 : 0 ≤ X := by positivity
    have hsq : κ₁ ^ 2 ≤ κ₁ := pow_le_of_le_one hκ0 hκ1 (by norm_num)
    have h1 : 4 / η * ((B₁ * mR ^ 2 + 1) * κ₁) ^ 2 + 2 * (CB * κ₁) ≤ X * κ₁ := by
      have e : 4 / η * ((B₁ * mR ^ 2 + 1) * κ₁) ^ 2 = 4 / η * (B₁ * mR ^ 2 + 1) ^ 2 * κ₁ ^ 2 := by
        ring
      rw [e, hX]
      have : 4 / η * (B₁ * mR ^ 2 + 1) ^ 2 * κ₁ ^ 2 ≤ 4 / η * (B₁ * mR ^ 2 + 1) ^ 2 * κ₁ :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      linarith
    have h2 : X * κ₁ ≤ κg * Rt ^ 2 / 8 := by
      have h := (le_div_iff₀ (by positivity : (0:ℝ) < 8 * X + 1)).mp hκk
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 8)]
      have e : κ₁ * (8 * X + 1) = X * κ₁ * 8 + κ₁ := by ring
      linarith
    have h3 : 2 * (2 * δ + vR * δ) ≤ κg * Rt ^ 2 / 8 := by
      have h := (le_div_iff₀ (by positivity : (0:ℝ) < 16 * (2 + vR))).mp hδκ
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 8)]
      have e : δ * (16 * (2 + vR)) = 2 * (2 * δ + vR * δ) * 8 := by ring
      linarith
    have hG : (4 / η * ((B₁ * mR ^ 2 + 1) * κ₁) ^ 2 + 2 * (CB * κ₁) + 2 * (2 * δ + vR * δ)) / κg
        ≤ (Rt / 2) ^ 2 := by
      rw [div_le_iff₀ hκg]
      have e : (Rt / 2) ^ 2 * κg = κg * Rt ^ 2 / 8 + κg * Rt ^ 2 / 8 := by ring
      linarith
    calc Real.sqrt ((4 / η * ((B₁ * mR ^ 2 + 1) * κ₁) ^ 2 + 2 * (CB * κ₁)
          + 2 * (2 * δ + vR * δ)) / κg)
        ≤ Real.sqrt ((Rt / 2) ^ 2) := Real.sqrt_le_sqrt hG
      _ = Rt / 2 := Real.sqrt_sq (by positivity)
  · rw [div_le_iff₀ hsep]; linarith
  · rw [div_le_iff₀ hsep]; linarith
  · have h1 : δ * M₁ / 2 ≤ μ / 8 := by
      have h := (le_div_iff₀ (by positivity : (0:ℝ) < 4 * M₁ + 1)).mp hδμ
      have e : δ * (4 * M₁ + 1) = 4 * (δ * M₁) + δ := by ring
      linarith
    have h2 : 2 * B₁ ^ 2 * M₁ ^ 2 * mR * (Rt + Rt + 2 * κ₁) + 2 * B₁ * M₁ * (Rt + Rt)
        ≤ (8 * B₁ ^ 2 * M₁ ^ 2 * mR + 4 * B₁ * M₁) * Rt := by
      have hc : 0 ≤ 2 * B₁ ^ 2 * M₁ ^ 2 * mR := by positivity
      have : 2 * B₁ ^ 2 * M₁ ^ 2 * mR * (Rt + Rt + 2 * κ₁) ≤ 2 * B₁ ^ 2 * M₁ ^ 2 * mR * (4 * Rt) :=
        mul_le_mul_of_nonneg_left (by linarith) hc
      have e : 2 * B₁ ^ 2 * M₁ ^ 2 * mR * (4 * Rt) + 2 * B₁ * M₁ * (Rt + Rt)
          = (8 * B₁ ^ 2 * M₁ ^ 2 * mR + 4 * B₁ * M₁) * Rt := by ring
      linarith
    have h3 : (8 * B₁ ^ 2 * M₁ ^ 2 * mR + 4 * B₁ * M₁) * Rt ≤ μ / 4 := by
      have h := (le_div_iff₀ (by positivity : (0:ℝ) < 32 * B₁ ^ 2 * M₁ ^ 2 * mR + 16 * B₁ * M₁ + 1)).mp hRtμ
      have e : Rt * (32 * B₁ ^ 2 * M₁ ^ 2 * mR + 16 * B₁ * M₁ + 1)
          = 4 * ((8 * B₁ ^ 2 * M₁ ^ 2 * mR + 4 * B₁ * M₁) * Rt) + Rt := by ring
      linarith
    linarith

set_option maxHeartbeats 8000000 in
/-- **Every maximizer near the degenerate boundary is bipodal**, with parameters close to
`(·, ζ_d(ε), ε)` and a small first pode. -/
theorem KRRSFamily.exists_bipodal {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    [DecidableRel H.Adj] {d : ℕ} {ε₀ : ℝ} (F : KRRSFamily H d ε₀) (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card) (hε₀ : ε₀ ∈ Ioo (0:ℝ) 1)
    (hε₀r : ε₀ ≠ rStar d) :
    ∃ η₂ P₀ : ℝ, 0 < η₂ ∧ ∀ τ : ℝ, 0 < τ → ∃ Δ : ℝ, 0 < Δ ∧ ∀ (ε ϑ : ℝ) (W : Graphon),
      |ε - ε₀| < η₂ → 0 < ϑ → ϑ < Δ → IsMaximizer H W ε (ε ^ H.edgeFinset.card + ϑ) →
      ε ∈ F.U ∧ ϑ < F.Δ ∧ ∃ (J : Set ℝ) (a b q : ℝ), MeasurableSet J ∧ J ⊆ Icc 0 1 ∧
        (volume J).toReal ≤ τ ∧ a ∈ Ioo (0:ℝ) 1 ∧ |dS0 a| ≤ P₀ ∧
        b ∈ Ioo (0:ℝ) 1 ∧ |b - zetaFun d ε| ≤ τ ∧ q ∈ Ioo (0:ℝ) 1 ∧ |q - ε| ≤ τ ∧
        ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = bipodalValue J a b q z := by
  classical
  set m := H.edgeFinset.card with hmdef
  set v := Fintype.card V with hvdef
  have hm0 : 0 < m := by omega
  have hmv : v * d = 2 * m := regular_handshake H hreg
  obtain ⟨η₁, hη₁, hqual⟩ := F.exists_qualDirs hd hreg hm hε₀ hε₀r
  obtain ⟨ηS, ΔS, K, hηS, hΔS, hK, hstruct⟩ := F.exists_competitor_structure hd hreg hm hε₀ hε₀r
  obtain ⟨ηc, κg, η, sep, μ, A, Bβ, hηc, hκg, hη, hη1, hsep, hμ, hA, hBβ, hconst⟩ :=
    exists_bipodal_constants hd hmv hm0 hε₀ hε₀r
  set A₁ : ℝ := A + 1 with hA₁
  set B₁ : ℝ := Bβ + 1 with hB₁
  have hA₁0 : 0 < A₁ := by positivity
  have hB₁0 : 0 < B₁ := by positivity
  have hmR0 : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hvR0 : (0:ℝ) ≤ (v : ℝ) := Nat.cast_nonneg _
  have hM₁0 : (0:ℝ) ≤ (m : ℝ) * (d - 1 : ℕ) := by positivity
  set CB : ℝ := (2 * (A₁ + B₁ * (m : ℝ)) + 2 * A₁ + B₁ * ((v : ℝ) * d)) * (B₁ * (m : ℝ) ^ 2) + B₁ * ((v : ℝ) * (m : ℝ))
    with hCB
  have hCB0 : 0 ≤ CB := by positivity
  refine ⟨min (min η₁ ηS) ηc, A₁ + B₁ * (m : ℝ), lt_min (lt_min hη₁ hηS) hηc, fun τ hτ => ?_⟩
  -- the target accuracy for rows and pode size
  set Rt : ℝ := min (τ / 2) (min (sep / 2) (μ / (32 * B₁ ^ 2 * ((m : ℝ) * (d - 1 : ℕ)) ^ 2 * (m : ℝ) + 16 * B₁ * ((m : ℝ) * (d - 1 : ℕ)) + 1)))
    with hRt
  have hRt0 : 0 < Rt := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hRtτ : Rt ≤ τ / 2 := min_le_left _ _
  have hRtsep : Rt ≤ sep / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hRtμ : Rt ≤ μ / (32 * B₁ ^ 2 * ((m : ℝ) * (d - 1 : ℕ)) ^ 2 * (m : ℝ) + 16 * B₁ * ((m : ℝ) * (d - 1 : ℕ)) + 1) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  set δ : ℝ := min 1 (min (μ / (4 * ((m : ℝ) * (d - 1 : ℕ)) + 1)) (κg * Rt ^ 2 / (16 * (2 + (v : ℝ))))) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδμ : δ ≤ μ / (4 * ((m : ℝ) * (d - 1 : ℕ)) + 1) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδκ : δ ≤ κg * Rt ^ 2 / (16 * (2 + (v : ℝ))) := le_trans (min_le_right _ _) (min_le_right _ _)
  set k₁ : ℝ := min 1 (κg * Rt ^ 2 / (8 * (4 / η * (B₁ * (m : ℝ) ^ 2 + 1) ^ 2 + 2 * CB) + 1)) with hk₁
  have hk₁0 : 0 < k₁ := lt_min one_pos (by positivity)
  set k₀ : ℝ := min (min (η / (2 * (B₁ * (m : ℝ) ^ 2 + 1))) (Rt / (2 * (B₁ * (m : ℝ) ^ 2 + 1))))
    (min (min Rt k₁) (min (sep / 4) (τ * sep / 2))) with hk₀
  have hk₀0 : 0 < k₀ := lt_min (lt_min (by positivity) (by positivity))
    (lt_min (lt_min hRt0 hk₁0) (lt_min (by positivity) (by positivity)))
  obtain ⟨Δ₁, hΔ₁, hqualδ⟩ := hqual δ hδ0
  refine ⟨min (min Δ₁ ΔS) (k₀ ^ 2 / K), lt_min (lt_min hΔ₁ hΔS) (by positivity),
    fun ε ϑ W hε hϑ0 hϑΔ hmax => ?_⟩
  have hεq : |ε - ε₀| < η₁ := lt_of_lt_of_le hε (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεS : |ε - ε₀| < ηS := lt_of_lt_of_le hε (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεc : |ε - ε₀| < ηc := lt_of_lt_of_le hε (min_le_right _ _)
  have hϑ₁ : ϑ < Δ₁ := lt_of_lt_of_le hϑΔ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hϑS : ϑ < ΔS := lt_of_lt_of_le hϑΔ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hϑk : ϑ < k₀ ^ 2 / K := lt_of_lt_of_le hϑΔ (min_le_right _ _)
  obtain ⟨hεU, hϑF, Q, hQβ, hQα⟩ := hqualδ ε ϑ W hεq hϑ0 hϑ₁ hmax
  obtain ⟨hεI, hεr, hεη, hgap, hsepε, hAε, hBε, hθε₀, hθζ₀⟩ := hconst ε hεc
  -- the `L²` localization
  obtain ⟨hWe, hWt, hWmax⟩ := hmax
  obtain ⟨-, -, -, -, -, hGe, hGt⟩ := F.graphon_spec hεU hϑ0 hϑF
  have hent : (F.graphon ε ϑ).entropy ≤ W.entropy := hWmax _ hGe hGt
  obtain ⟨-, -, hL2, -⟩ := hstruct ε ϑ W hεS hϑ0 hϑS hWe hWt hent
  set κ₁ : ℝ := W.constDist ε with hκ₁
  have hκ₁0 : 0 ≤ κ₁ := W.constDist_nonneg ε
  have hκ₁k : κ₁ ≤ k₀ := by
    have h1 := W.constDist_le_sqrt ε
    have h2 : ∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ ≤ k₀ ^ 2 := by
      have := (lt_div_iff₀ hK).mp hϑk
      linarith [mul_comm K ϑ]
    calc κ₁ ≤ Real.sqrt (∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ) := h1
      _ ≤ Real.sqrt (k₀ ^ 2) := Real.sqrt_le_sqrt h2
      _ = k₀ := Real.sqrt_sq hk₀0.le
  have hκη : κ₁ ≤ η / (2 * (B₁ * (m : ℝ) ^ 2 + 1)) :=
    le_trans hκ₁k (le_trans (min_le_left _ _) (min_le_left _ _))
  have hκRt2 : κ₁ ≤ Rt / (2 * (B₁ * (m : ℝ) ^ 2 + 1)) :=
    le_trans hκ₁k (le_trans (min_le_left _ _) (min_le_right _ _))
  have hκRt : κ₁ ≤ Rt := le_trans hκ₁k (le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
    (min_le_left _ _)))
  have hκk₁ : κ₁ ≤ k₁ := le_trans hκ₁k (le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
    (min_le_right _ _)))
  have hκsep : κ₁ ≤ sep / 4 := le_trans hκ₁k (le_trans (min_le_right _ _) (le_trans
    (min_le_right _ _) (min_le_left _ _)))
  have hκτ : κ₁ ≤ τ * sep / 2 := le_trans hκ₁k (le_trans (min_le_right _ _) (le_trans
    (min_le_right _ _) (min_le_right _ _)))
  -- the multipliers
  have hβB : |Q.beta| ≤ B₁ := by
    have := abs_sub_abs_le_abs_sub Q.beta (beta₀ m d ε); rw [hB₁]; linarith
  have hαA : |Q.alpha| ≤ A₁ := by
    have := abs_sub_abs_le_abs_sub Q.alpha (alpha₀ m d ε); rw [hA₁]; linarith
  have hbal := balErr_le (m := m) (v := v) (d := d) hαA hβB
  -- the arithmetic
  obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6⟩ := bipodal_arith hτ hsep hμ hκg hη hB₁0 hM₁0 hmR0 hvR0 hCB0
    hRt0 hRtτ hRtsep hRtμ hδ0 hδμ hδκ hκ₁0 hκη hκRt2 hκRt (le_trans hκk₁ (min_le_left _ _))
    (le_trans hκk₁ (min_le_right _ _)) hκsep hκτ
  set e₁ : ℝ := B₁ * (m : ℝ) ^ 2 * κ₁ with he₁
  set r : ℝ := Real.sqrt ((4 / η * ((B₁ * (m : ℝ) ^ 2 + 1) * κ₁) ^ 2 + 2 * (CB * κ₁)
    + 2 * (2 * δ + (v : ℝ) * δ)) / κg) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have he₁0 : 0 ≤ e₁ := by positivity
  have hζε : sep ≤ |zetaFun d ε - ε| := hsepε
  -- the hypotheses of `bipodal_of_bounds`
  have hsmall : (|Q.beta| * (m : ℝ) ^ 2 + 1) * κ₁ ≤ η / 2 := by
    have : |Q.beta| * (m : ℝ) ^ 2 ≤ B₁ * (m : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hβB (sq_nonneg _)
    nlinarith
  have he₁' : |Q.beta| * (m : ℝ) ^ 2 * κ₁ ≤ e₁ := by
    have : |Q.beta| * (m : ℝ) ^ 2 ≤ B₁ * (m : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hβB (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right this hκ₁0
  have hrG : (4 / η * ((|Q.beta| * (m : ℝ) ^ 2 + 1) * κ₁) ^ 2
      + 2 * (balErr m v d Q.alpha Q.beta * κ₁)
      + 2 * (2 * |Q.alpha - alpha₀ m d ε| + v * |Q.beta - beta₀ m d ε|)) / κg ≤ r ^ 2 := by
    rw [hr, Real.sq_sqrt (by positivity)]
    apply div_le_div_of_nonneg_right _ hκg.le
    have h1 : ((|Q.beta| * (m : ℝ) ^ 2 + 1) * κ₁) ^ 2 ≤ ((B₁ * (m : ℝ) ^ 2 + 1) * κ₁) ^ 2 := by
      have : |Q.beta| * (m : ℝ) ^ 2 ≤ B₁ * (m : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hβB (sq_nonneg _)
      have h0 : 0 ≤ (|Q.beta| * (m : ℝ) ^ 2 + 1) * κ₁ := by positivity
      exact pow_le_pow_left₀ h0 (mul_le_mul_of_nonneg_right (by linarith) hκ₁0) 2
    have h2 : balErr m v d Q.alpha Q.beta * κ₁ ≤ CB * κ₁ := mul_le_mul_of_nonneg_right hbal hκ₁0
    have h3 : 2 * |Q.alpha - alpha₀ m d ε| + (v : ℝ) * |Q.beta - beta₀ m d ε| ≤ 2 * δ + (v : ℝ) * δ := by
      have := mul_le_mul_of_nonneg_left hQβ hvR0
      linarith
    have h4 : 4 / η * ((|Q.beta| * (m : ℝ) ^ 2 + 1) * κ₁) ^ 2 ≤ 4 / η * ((B₁ * (m : ℝ) ^ 2 + 1) * κ₁) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hsep' : r + e₁ ≤ |zetaFun d ε - ε| / 2 := by linarith
  have hJ' : 2 * κ₁ / |zetaFun d ε - ε| ≤ 1 / 2 :=
    le_trans (div_le_div_of_nonneg_left (by positivity) hsep hζε) hA4
  have hcoef : ∀ c ∈ Icc (0:ℝ) 1,
      2 * (c * (1 - c)) * |beta₀ m d ε| * ((m : ℝ) * (d - 1 : ℕ)) * (c ^ (d - 2) * ε ^ (m - d))
        ≤ 1 - μ → contrCoef m d Q.beta c ε (e₁ + r) κ₁ < 1 := by
    intro c hc hbase
    have h1 := contrCoef_le (m := m) (d := d) (β₀ := beta₀ m d ε) (δ := δ) (B₁ := B₁)
      (R := e₁ + r) hc ⟨hεI.1.le, hεI.2.le⟩ (add_nonneg he₁0 hr0) hκ₁0 hQβ hβB
    have hR : e₁ + r ≤ Rt := by linarith
    have h2 : 2 * B₁ ^ 2 * ((m : ℝ) * (d - 1 : ℕ)) ^ 2 * (m : ℝ) * ((e₁ + r) + (e₁ + r) + 2 * κ₁) + 2 * B₁ * ((m : ℝ) * (d - 1 : ℕ)) * ((e₁ + r) + (e₁ + r))
        ≤ 2 * B₁ ^ 2 * ((m : ℝ) * (d - 1 : ℕ)) ^ 2 * (m : ℝ) * (Rt + Rt + 2 * κ₁) + 2 * B₁ * ((m : ℝ) * (d - 1 : ℕ)) * (Rt + Rt) := by
      have hc1 : 0 ≤ 2 * B₁ ^ 2 * ((m : ℝ) * (d - 1 : ℕ)) ^ 2 * (m : ℝ) := by positivity
      have hc2 : 0 ≤ 2 * B₁ * ((m : ℝ) * (d - 1 : ℕ)) := by positivity
      have := mul_le_mul_of_nonneg_left (show (e₁ + r) + (e₁ + r) + 2 * κ₁ ≤ Rt + Rt + 2 * κ₁ by linarith) hc1
      have := mul_le_mul_of_nonneg_left (show (e₁ + r) + (e₁ + r) ≤ Rt + Rt by linarith) hc2
      linarith
    linarith
  have hθε := hcoef ε ⟨hεI.1.le, hεI.2.le⟩ hθε₀
  have hθζ := hcoef (zetaFun d ε) ⟨(zetaFun_mem hd hεI).1.le, (zetaFun_mem hd hεI).2.le⟩ hθζ₀
  obtain ⟨J, a, b, q, hJm, hJsub, hJvol, ha, hda, hb, hbζ, hq, hqε, hae⟩ :=
    Q.bipodal_of_bounds H ⟨hWe, hWt, hWmax⟩ hd hreg hm0 hεI hεr hκg hgap hη hη1 hεη hsmall he₁' hr0
      hrG hsep' hJ' hθε hθζ
  refine ⟨hεU, hϑF, J, a, b, q, hJm, hJsub, ?_, ha, ?_, hb, ?_, hq, ?_, hae⟩
  · exact le_trans hJvol (le_trans (div_le_div_of_nonneg_left (by positivity) hsep hζε) hA5)
  · have : |Q.alpha| + |Q.beta| * m ≤ A₁ + B₁ * (m : ℝ) :=
      add_le_add hαA (mul_le_mul_of_nonneg_right hβB (Nat.cast_nonneg _))
    linarith
  · linarith
  · linarith

end UpperTailOptimizers
