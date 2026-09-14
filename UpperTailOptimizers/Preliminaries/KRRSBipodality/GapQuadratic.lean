import UpperTailOptimizers.Preliminaries.KRRSBipodality.Efficiency
import UpperTailOptimizers.LZBoundary.Existence

/-!
# The gap function vanishes quadratically, and only at `ε` and `ζ_d(ε)`

`kb:lem:gap` of the bipodality draft.  Near a nonexceptional `ε₀` there are `κ > 0` and a
window in `ε` on which

  `Γ_ε(u) ≥ κ · min((u-ε)², (u-ζ_d(ε))²)`   for all `u ∈ [0,1]`.

Both zeros are double: `Γ_ε' = ψ_*𝒟_ε' - 𝒩_ε'` vanishes at `ε` trivially and at `ζ_d(ε)` by the
critical-point equation, and `Γ_ε'' = 𝒟''(ψ_* - R_d)` is positive at both because
`R_d(ε), R_d(ζ) < ψ_*` (`Rfun_lt_Aavg_of_crit`).

## Contents

* `continuousAt_zetaFun` — `ζ_d` is continuous (a strictly monotone involution of `(0,1)`);
* `continuousAt_psiStar`.
-/

namespace UpperTailOptimizers

open Real Set Filter Topology

theorem image_zetaFun_Ioo {d : ℕ} (hd : 2 ≤ d) :
    zetaFun d '' Ioo (0:ℝ) 1 = Ioo (0:ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact zetaFun_mem hd hx
  · intro hy
    exact ⟨zetaFun d y, zetaFun_mem hd hy, zetaFun_involutive hd hy⟩

/-- **`ζ_d` is continuous** on `(0,1)`. -/
theorem continuousAt_zetaFun {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (zetaFun d) ε := by
  have hmono : MonotoneOn (fun x => -zetaFun d x) (Ioo (0:ℝ) 1) := by
    intro a ha b hb hab
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · have := zetaFun_strictAntiOn hd ha hb h
      simp only [neg_le_neg_iff]; exact this.le
  have himg : (fun x => -zetaFun d x) '' Ioo (0:ℝ) 1 = Ioo (-1:ℝ) 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := zetaFun_mem hd hx
      exact ⟨by linarith [this.2], by linarith [this.1]⟩
    · intro hy
      have hy' : -y ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
      refine ⟨zetaFun d (-y), zetaFun_mem hd hy', ?_⟩
      simp only [zetaFun_involutive hd hy', neg_neg]
  have hzm := zetaFun_mem hd hε
  have hc : ContinuousAt (fun x => -zetaFun d x) ε := by
    refine continuousAt_of_monotoneOn_of_image_mem_nhds hmono (isOpen_Ioo.mem_nhds hε) ?_
    rw [himg]
    exact isOpen_Ioo.mem_nhds ⟨by linarith [hzm.2], by linarith [hzm.1]⟩
  have h2 : ContinuousAt (fun x => -(-zetaFun d x)) ε := hc.neg
  simpa only [neg_neg] using h2

theorem continuousAt_Nfun_prod {ε z : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (fun p : ℝ × ℝ => Nfun p.1 p.2) (ε, z) := by
  unfold Nfun
  have hS : Continuous S0 := continuous_S0
  have hdS : ContinuousAt dS0 ε := (analyticAt_dS0 hε.1 hε.2).continuousAt
  have h1 : ContinuousAt (fun p : ℝ × ℝ => dS0 p.1) (ε, z) :=
    ContinuousAt.comp_of_eq hdS continuous_fst.continuousAt rfl
  exact ((((hS.comp continuous_snd).continuousAt).sub ((hS.comp continuous_fst).continuousAt)).sub
    (h1.mul (continuous_snd.continuousAt.sub continuous_fst.continuousAt))).const_mul 2

theorem continuousAt_psiStar {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (hεr : ε ≠ rStar d) : ContinuousAt (psiStar d) ε := by
  obtain ⟨hzm, hzne, -⟩ := zetaFun_crit hd hε.1 hε.2 hεr
  have hzc := continuousAt_zetaFun hd hε
  have hpair : ContinuousAt (fun x => (x, zetaFun d x)) ε := continuousAt_id.prodMk hzc
  have hN : ContinuousAt (fun x => Nfun x (zetaFun d x)) ε :=
    ContinuousAt.comp (g := fun p : ℝ × ℝ => Nfun p.1 p.2) (f := fun x => (x, zetaFun d x))
      (x := ε) (continuousAt_Nfun_prod hε) hpair
  have hD : ContinuousAt (fun x => Dfun d x (zetaFun d x)) ε := by
    unfold Dfun
    exact ((hzc.pow d).sub (continuousAt_id.pow d)).sub
      ((continuousAt_const.mul (continuousAt_id.pow (d - 1))).mul (hzc.sub continuousAt_id))
  have hD0 : Dfun d ε (zetaFun d ε) ≠ 0 := ne_of_gt (Dfun_pos hd hε.1 hzm.1.le hzne)
  exact hN.div hD hD0

/-! ### Monotonicity of `𝒟_ε` and the factored form of `Γ` -/

theorem Dfun_monotoneOn_right {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε0 : 0 < ε) :
    MonotoneOn (Dfun d ε) (Ici ε) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici ε)
    (fun u _ => (hasDerivAt_Dfun d ε u).continuousAt.continuousWithinAt)
    (fun u _ => (hasDerivAt_Dfun d ε u).differentiableAt.differentiableWithinAt)
    (fun u hu => ?_)
  rw [interior_Ici] at hu
  rw [(hasDerivAt_Dfun d ε u).deriv]
  exact (dD_pos hd hε0 hu).le

theorem Dfun_antitoneOn_left {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} :
    AntitoneOn (Dfun d ε) (Icc 0 ε) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc 0 ε)
    (fun u _ => (hasDerivAt_Dfun d ε u).continuousAt.continuousWithinAt)
    (fun u _ => (hasDerivAt_Dfun d ε u).differentiableAt.differentiableWithinAt)
    (fun u hu => ?_)
  rw [interior_Icc] at hu
  rw [(hasDerivAt_Dfun d ε u).deriv]
  have h := dD_pos hd hu.1 hu.2
  rw [dD_swap] at h
  linarith

/-- `Γ = 𝒟_ε·(ψ_* - ψ_d(ε,·))` off the diagonal. -/
theorem gapFun_eq_mul {d : ℕ} (hd : 2 ≤ d) {ε u : ℝ} (hε0 : 0 < ε) (hu0 : 0 ≤ u)
    (hne : u ≠ ε) : gapFun d ε u = Dfun d ε u * (psiStar d ε - psiD d ε u) := by
  have hD : Dfun d ε u ≠ 0 := ne_of_gt (Dfun_pos hd hε0 hu0 hne)
  unfold gapFun psiD
  field_simp

/-- Extending a lower bound from an open interval to its closure, by continuity of `Γ`. -/
theorem gapFun_ge_of_Ioo {d : ℕ} {ε a b c : ℝ} (hab : a < b)
    (h : ∀ u ∈ Ioo a b, c ≤ gapFun d ε u) : ∀ u ∈ Icc a b, c ≤ gapFun d ε u := by
  have hsub : Icc a b ⊆ {w | c ≤ gapFun d ε w} := by
    rw [← closure_Ioo (ne_of_lt hab)]
    exact closure_minimal h (isClosed_le continuous_const (continuous_gapFun d ε))
  exact fun u hu => hsub hu

/-! ### Lower bounds away from the zeros -/

private theorem psiD_le_of_monoOn {d : ℕ} (hd : 2 ≤ d) {ε a b : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (ha0 : 0 < a) (hb1 : b < 1) (hab : a ≤ b) (hne : ∀ x ∈ Icc a b, x ≠ ε)
    (hpos : ∀ x ∈ Ioo a b, 0 < Wr d ε x) : psiD d ε a ≤ psiD d ε b := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · exact (psiD_strictMonoOn hd hε.1 ha0 hb1 hne hpos (left_mem_Icc.mpr hab)
      (right_mem_Icc.mpr hab) h).le

private theorem psiD_ge_of_antiOn {d : ℕ} (hd : 2 ≤ d) {ε a b : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (ha0 : 0 < a) (hb1 : b < 1) (hab : a ≤ b) (hne : ∀ x ∈ Icc a b, x ≠ ε)
    (hneg : ∀ x ∈ Ioo a b, Wr d ε x < 0) : psiD d ε b ≤ psiD d ε a := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · exact (psiD_strictAntiOn hd hε.1 ha0 hb1 hne hneg (left_mem_Icc.mpr hab)
      (right_mem_Icc.mpr hab) h).le

theorem psiD_le_psiStar {d : ℕ} (hd : 2 ≤ d) {ε u : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (hu : u ∈ Ioo (0:ℝ) 1) (hne : u ≠ ε) : psiD d ε u ≤ psiStar d ε :=
  zetaFun_isMax hd hε u hu hne

/-- **Away from the zeros, `ε < ζ_d(ε)`.** -/
theorem gapFun_ge_far_of_lt {d : ℕ} (hd : 2 ≤ d) {ε δ : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (hδ : 0 < δ) (hδε : δ < ε) (hδ1 : zetaFun d ε + δ < 1)
    (hδsep : ε + δ < zetaFun d ε - δ) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hfar : u ≤ ε - δ ∨ (ε + δ ≤ u ∧ u ≤ zetaFun d ε - δ) ∨ zetaFun d ε + δ ≤ u) :
    min (gapFun d ε (ε - δ)) (min (gapFun d ε (zetaFun d ε + δ))
      (Dfun d ε (ε + δ) * gapFun d ε (zetaFun d ε - δ) / Dfun d ε (zetaFun d ε - δ)))
      ≤ gapFun d ε u := by
  set ζ := zetaFun d ε with hζ
  have hζ1 : ζ < 1 := (zetaFun_mem hd hε).2
  rcases hfar with h1 | ⟨h2a, h2b⟩ | h3
  · -- left of `ε`
    refine le_trans (min_le_left _ _) ?_
    have hbound : ∀ w ∈ Ioo 0 (ε - δ), gapFun d ε (ε - δ) ≤ gapFun d ε w := by
      intro w hw
      have hwε : w < ε := by linarith [hw.2]
      have hψ := psiD_le_of_monoOn hd hε hw.1 (by linarith) hw.2.le
        (fun x hx => ne_of_lt (by linarith [hx.2])) (fun x hx => Wr_pos_of_lt_zeta hd hε
          ⟨by linarith [hw.1, hx.1], by linarith [hx.2]⟩ (ne_of_lt (by linarith [hx.2]))
          (by linarith [hx.2]))
      have hstar := psiD_le_psiStar hd hε ⟨by linarith, by linarith⟩ (ne_of_lt (by linarith) :
        ε - δ ≠ ε)
      have hD := Dfun_antitoneOn_left hd ⟨hw.1.le, hwε.le⟩ ⟨by linarith, by linarith⟩ hw.2.le
      have hD0 : 0 ≤ Dfun d ε (ε - δ) := (Dfun_pos hd hε.1 (by linarith) (by linarith)).le
      rw [gapFun_eq_mul hd hε.1 hw.1.le (ne_of_lt hwε),
        gapFun_eq_mul hd hε.1 (by linarith) (by linarith)]
      nlinarith [hψ, hstar, hD, hD0]
    exact gapFun_ge_of_Ioo (by linarith) hbound u ⟨hu.1, h1⟩
  · -- between `ε` and `ζ`
    refine le_trans (min_le_right _ _) (le_trans (min_le_right _ _) ?_)
    have hu0 : 0 < u := by linarith
    have huε : ε < u := by linarith
    have hψ := psiD_le_of_monoOn hd hε hu0 (by linarith) h2b
      (fun x hx => ne_of_gt (by linarith [hx.1])) (fun x hx => Wr_pos_of_lt_zeta hd hε
        ⟨by linarith [hx.1], by linarith [hx.2]⟩ (ne_of_gt (by linarith [hx.1]))
        (by linarith [hx.2]))
    have hstar := psiD_le_psiStar hd hε ⟨by linarith, by linarith⟩
      (ne_of_gt (by linarith) : ζ - δ ≠ ε)
    have hDu := Dfun_monotoneOn_right hd hε.1 (show ε ≤ ε + δ by linarith) huε.le h2a
    have hDζ : 0 < Dfun d ε (ζ - δ) := Dfun_pos hd hε.1 (by linarith) (by linarith)
    have hDe : 0 ≤ Dfun d ε (ε + δ) := (Dfun_pos hd hε.1 (by linarith) (by linarith)).le
    rw [gapFun_eq_mul hd hε.1 hu0.le (ne_of_gt huε),
      gapFun_eq_mul hd hε.1 (by linarith) (by linarith : ζ - δ ≠ ε), mul_div_assoc,
      mul_div_cancel_left₀ _ (ne_of_gt hDζ)]
    have h4 : 0 ≤ psiStar d ε - psiD d ε (ζ - δ) := by linarith
    nlinarith [hψ, hDu, hDe, h4]
  · -- right of `ζ`
    refine le_trans (min_le_right _ _) (le_trans (min_le_left _ _) ?_)
    have hbound : ∀ w ∈ Ioo (ζ + δ) 1, gapFun d ε (ζ + δ) ≤ gapFun d ε w := by
      intro w hw
      have hwε : ε < w := by linarith [hw.1]
      have hψ := psiD_ge_of_antiOn hd hε (by linarith) hw.2 hw.1.le
        (fun x hx => ne_of_gt (by linarith [hx.1])) (fun x hx => Wr_neg_of_zeta_lt hd hε
          ⟨by linarith [hx.1], by linarith [hx.2, hw.2]⟩ (ne_of_gt (by linarith [hx.1]))
          (by linarith [hx.1]))
      have hstar := psiD_le_psiStar hd hε ⟨by linarith, by linarith⟩
        (ne_of_gt (by linarith) : ζ + δ ≠ ε)
      have hD := Dfun_monotoneOn_right hd hε.1 (show ε ≤ ζ + δ by linarith) hwε.le hw.1.le
      have hD0 : 0 ≤ Dfun d ε (ζ + δ) := (Dfun_pos hd hε.1 (by linarith) (by linarith)).le
      rw [gapFun_eq_mul hd hε.1 (by linarith) (ne_of_gt hwε),
        gapFun_eq_mul hd hε.1 (by linarith) (by linarith : ζ + δ ≠ ε)]
      nlinarith [hψ, hstar, hD, hD0]
    exact gapFun_ge_of_Ioo (by linarith) hbound u ⟨h3, hu.2⟩

/-- **Away from the zeros, `ζ_d(ε) < ε`.** -/
theorem gapFun_ge_far_of_gt {d : ℕ} (hd : 2 ≤ d) {ε δ : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (hδ : 0 < δ) (hδζ : δ < zetaFun d ε) (hδ1 : ε + δ < 1)
    (hδsep : zetaFun d ε + δ < ε - δ) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hfar : u ≤ zetaFun d ε - δ ∨ (zetaFun d ε + δ ≤ u ∧ u ≤ ε - δ) ∨ ε + δ ≤ u) :
    min (gapFun d ε (zetaFun d ε - δ)) (min (gapFun d ε (ε + δ))
      (Dfun d ε (ε - δ) * gapFun d ε (zetaFun d ε + δ) / Dfun d ε (zetaFun d ε + δ)))
      ≤ gapFun d ε u := by
  set ζ := zetaFun d ε with hζ
  have hζ0 : 0 < ζ := (zetaFun_mem hd hε).1
  rcases hfar with h1 | ⟨h2a, h2b⟩ | h3
  · -- left of `ζ`
    refine le_trans (min_le_left _ _) ?_
    have hbound : ∀ w ∈ Ioo 0 (ζ - δ), gapFun d ε (ζ - δ) ≤ gapFun d ε w := by
      intro w hw
      have hwε : w < ε := by linarith [hw.2]
      have hψ := psiD_le_of_monoOn hd hε hw.1 (by linarith) hw.2.le
        (fun x hx => ne_of_lt (by linarith [hx.2])) (fun x hx => Wr_pos_of_lt_zeta hd hε
          ⟨by linarith [hw.1, hx.1], by linarith [hx.2]⟩ (ne_of_lt (by linarith [hx.2]))
          (by linarith [hx.2]))
      have hstar := psiD_le_psiStar hd hε ⟨by linarith, by linarith⟩
        (ne_of_lt (by linarith) : ζ - δ ≠ ε)
      have hD := Dfun_antitoneOn_left hd ⟨hw.1.le, hwε.le⟩ ⟨by linarith, by linarith⟩ hw.2.le
      have hD0 : 0 ≤ Dfun d ε (ζ - δ) := (Dfun_pos hd hε.1 (by linarith) (by linarith)).le
      rw [gapFun_eq_mul hd hε.1 hw.1.le (ne_of_lt hwε),
        gapFun_eq_mul hd hε.1 (by linarith) (by linarith : ζ - δ ≠ ε)]
      nlinarith [hψ, hstar, hD, hD0]
    exact gapFun_ge_of_Ioo (by linarith) hbound u ⟨hu.1, h1⟩
  · -- between `ζ` and `ε`
    refine le_trans (min_le_right _ _) (le_trans (min_le_right _ _) ?_)
    have hu0 : 0 < u := by linarith
    have huε : u < ε := by linarith
    have hψ := psiD_ge_of_antiOn hd hε (by linarith) (by linarith) h2a
      (fun x hx => ne_of_lt (by linarith [hx.2])) (fun x hx => Wr_neg_of_zeta_lt hd hε
        ⟨by linarith [hx.1], by linarith [hx.2]⟩ (ne_of_lt (by linarith [hx.2]))
        (by linarith [hx.1]))
    have hstar := psiD_le_psiStar hd hε ⟨by linarith, by linarith⟩
      (ne_of_lt (by linarith) : ζ + δ ≠ ε)
    have hDu := Dfun_antitoneOn_left hd ⟨hu0.le, huε.le⟩ ⟨by linarith, by linarith⟩ h2b
    have hDζ : 0 < Dfun d ε (ζ + δ) := Dfun_pos hd hε.1 (by linarith) (by linarith)
    have hDe : 0 ≤ Dfun d ε (ε - δ) := (Dfun_pos hd hε.1 (by linarith) (by linarith)).le
    rw [gapFun_eq_mul hd hε.1 hu0.le (ne_of_lt huε),
      gapFun_eq_mul hd hε.1 (by linarith) (by linarith : ζ + δ ≠ ε), mul_div_assoc,
      mul_div_cancel_left₀ _ (ne_of_gt hDζ)]
    have h4 : 0 ≤ psiStar d ε - psiD d ε (ζ + δ) := by linarith
    nlinarith [hψ, hDu, hDe, h4]
  · -- right of `ε`
    refine le_trans (min_le_right _ _) (le_trans (min_le_left _ _) ?_)
    have hbound : ∀ w ∈ Ioo (ε + δ) 1, gapFun d ε (ε + δ) ≤ gapFun d ε w := by
      intro w hw
      have hwε : ε < w := by linarith [hw.1]
      have hψ := psiD_ge_of_antiOn hd hε (by linarith) hw.2 hw.1.le
        (fun x hx => ne_of_gt (by linarith [hx.1])) (fun x hx => Wr_neg_of_zeta_lt hd hε
          ⟨by linarith [hx.1], by linarith [hx.2, hw.2]⟩ (ne_of_gt (by linarith [hx.1]))
          (by linarith [hx.1]))
      have hstar := psiD_le_psiStar hd hε ⟨by linarith, by linarith⟩
        (ne_of_gt (by linarith) : ε + δ ≠ ε)
      have hD := Dfun_monotoneOn_right hd hε.1 (show ε ≤ ε + δ by linarith) hwε.le hw.1.le
      have hD0 : 0 ≤ Dfun d ε (ε + δ) := (Dfun_pos hd hε.1 (by linarith) (by linarith)).le
      rw [gapFun_eq_mul hd hε.1 (by linarith) (ne_of_gt hwε),
        gapFun_eq_mul hd hε.1 (by linarith) (by linarith : ε + δ ≠ ε)]
      nlinarith [hψ, hstar, hD, hD0]
    exact gapFun_ge_of_Ioo (by linarith) hbound u ⟨h3, hu.2⟩

/-! ### Strict inequality, and the double zeros -/

/-- `ψ_d(ε,u) < ψ_*` for `u ∉ {ε, ζ_d(ε)}`: an interior maximizer is a critical point. -/
theorem psiD_lt_psiStar {d : ℕ} (hd : 2 ≤ d) {ε u : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (hu : u ∈ Ioo (0:ℝ) 1) (hne : u ≠ ε) (hnz : u ≠ zetaFun d ε) :
    psiD d ε u < psiStar d ε := by
  refine lt_of_le_of_ne (psiD_le_psiStar hd hε hu hne) (fun heq => hnz ?_)
  have hmax : IsLocalMax (fun w => psiD d ε w) u := by
    have hnb : ∀ᶠ w in 𝓝 u, w ∈ Ioo (0:ℝ) 1 ∧ w ≠ ε :=
      Filter.Eventually.and (isOpen_Ioo.mem_nhds hu) (isOpen_ne.mem_nhds hne)
    filter_upwards [hnb] with w hw
    rw [heq]; exact psiD_le_psiStar hd hε hw.1 hw.2
  have hder := hasDerivAt_psiD hd hε.1 hu.1 hu.2 hne
  have h0 := hmax.hasDerivAt_eq_zero hder
  have hD : Dfun d ε u ≠ 0 := ne_of_gt (Dfun_pos hd hε.1 hu.1.le hne)
  have hW : Wr d ε u = 0 := by
    rcases div_eq_zero_iff.mp h0 with h | h
    · exact h
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hD
  exact zetaFun_eq_of_crit hd hε hu hne hW

theorem gapFun_pos {d : ℕ} (hd : 2 ≤ d) {ε u : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (hu : u ∈ Ioo (0:ℝ) 1) (hne : u ≠ ε) (hnz : u ≠ zetaFun d ε) : 0 < gapFun d ε u := by
  rw [gapFun_eq_mul hd hε.1 hu.1.le hne]
  exact mul_pos (Dfun_pos hd hε.1 hu.1.le hne)
    (sub_pos.mpr (psiD_lt_psiStar hd hε hu hne hnz))

theorem hasDerivAt_gapFun {d : ℕ} (ε : ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (gapFun d ε) (-Kfun d (psiStar d ε) ε u) u := by
  have h := ((hasDerivAt_Dfun d ε u).const_mul (psiStar d ε)).sub
    (hasDerivAt_Nfun ε (ne_of_gt hu0) (ne_of_lt hu1))
  have hval : psiStar d ε * dD d ε u - dN ε u = -Kfun d (psiStar d ε) ε u := by
    unfold Kfun; ring
  rw [hval] at h
  exact h

theorem hasDerivAt_neg_Kfun {d : ℕ} (hd : 2 ≤ d) (c ε : ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (fun x => -Kfun d c ε x) (d2D d u * (c - Rfun d u)) u := by
  have h := (hasDerivAt_Kfun hd c ε hu0 hu1).neg
  have hval : -(d2D d u * (Rfun d u - c)) = d2D d u * (c - Rfun d u) := by ring
  rw [hval] at h
  exact h

theorem gapFun_self (d : ℕ) (ε : ℝ) : gapFun d ε ε = 0 := by
  unfold gapFun Dfun Nfun; ring

theorem gapFun_zeta {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1) (hεr : ε ≠ rStar d) :
    gapFun d ε (zetaFun d ε) = 0 := by
  obtain ⟨hzm, hzne, -⟩ := zetaFun_crit hd hε.1 hε.2 hεr
  have hD : Dfun d ε (zetaFun d ε) ≠ 0 := ne_of_gt (Dfun_pos hd hε.1 hzm.1.le hzne)
  unfold gapFun psiStar psiD
  field_simp
  ring

theorem Kfun_zeta {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1) (hεr : ε ≠ rStar d) :
    Kfun d (psiStar d ε) ε (zetaFun d ε) = 0 := by
  obtain ⟨hzm, hzne, hW⟩ := zetaFun_crit hd hε.1 hε.2 hεr
  have hD : Dfun d ε (zetaFun d ε) ≠ 0 := ne_of_gt (Dfun_pos hd hε.1 hzm.1.le hzne)
  unfold Kfun psiStar psiD
  unfold Wr at hW
  field_simp
  linarith

/-- **Quadratic growth at a double zero**, for `c = ε` or `c = ζ_d(ε)`. -/
theorem gapFun_quadratic_near {d : ℕ} (hd : 2 ≤ d) {ε c δ m : ℝ} (hc0 : 0 < c - δ)
    (hc1 : c + δ < 1) (hδ : 0 ≤ δ) (hfc : gapFun d ε c = 0)
    (hf'c : Kfun d (psiStar d ε) ε c = 0)
    (hm : ∀ x ∈ Icc (c - δ) (c + δ), m ≤ d2D d x * (psiStar d ε - Rfun d x)) :
    ∀ u ∈ Icc (c - δ) (c + δ), m / 2 * (u - c) ^ 2 ≤ gapFun d ε u := by
  have hmem : ∀ x ∈ Icc (c - δ) (c + δ), 0 < x ∧ x < 1 := fun x hx =>
    ⟨lt_of_lt_of_le hc0 hx.1, lt_of_le_of_lt hx.2 hc1⟩
  refine quadratic_lower_of_deriv2_ge (f' := fun x => -Kfun d (psiStar d ε) ε x)
    (f'' := fun x => d2D d x * (psiStar d ε - Rfun d x)) (by linarith) (by linarith)
    (fun x hx => hasDerivAt_gapFun ε (hmem x hx).1 (hmem x hx).2)
    (fun x hx => hasDerivAt_neg_Kfun hd _ ε (hmem x hx).1 (hmem x hx).2) hm hfc ?_
  simp [hf'c]

/-! ### Continuity in `(ε, u)` and positivity of the curvature -/

theorem continuousAt_gapFun_prod {d : ℕ} (hd : 2 ≤ d) {ε u : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (hεr : ε ≠ rStar d) : ContinuousAt (fun p : ℝ × ℝ => gapFun d p.1 p.2) (ε, u) := by
  unfold gapFun
  have hps : ContinuousAt (fun p : ℝ × ℝ => psiStar d p.1) (ε, u) :=
    ContinuousAt.comp_of_eq (continuousAt_psiStar hd hε hεr) continuous_fst.continuousAt rfl
  have hD : ContinuousAt (fun p : ℝ × ℝ => Dfun d p.1 p.2) (ε, u) := by
    unfold Dfun; fun_prop
  exact (hps.mul hD).sub (continuousAt_Nfun_prod hε)

theorem continuousAt_Rfun {d : ℕ} (hd : 2 ≤ d) {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (Rfun d) u := by
  have hN : ContinuousAt d2N u := (hasDerivAt_d2N (ne_of_gt hu.1) (ne_of_lt hu.2)).continuousAt
  have hD : ContinuousAt (d2D d) u := (hasDerivAt_d2D hd u).continuousAt
  exact hN.div hD (ne_of_gt (d2D_pos hd hu.1))

/-- The curvature `Γ'' = 𝒟''·(ψ_* - R_d)` as a function of `(ε, u)`. -/
noncomputable def gapCurv (d : ℕ) (p : ℝ × ℝ) : ℝ := d2D d p.2 * (psiStar d p.1 - Rfun d p.2)

theorem continuousAt_gapCurv {d : ℕ} (hd : 2 ≤ d) {ε u : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (hεr : ε ≠ rStar d) (hu : u ∈ Ioo (0:ℝ) 1) : ContinuousAt (gapCurv d) (ε, u) := by
  unfold gapCurv
  have h1 : ContinuousAt (fun p : ℝ × ℝ => d2D d p.2) (ε, u) := by
    unfold d2D; fun_prop
  have h2 : ContinuousAt (fun p : ℝ × ℝ => psiStar d p.1) (ε, u) :=
    ContinuousAt.comp_of_eq (continuousAt_psiStar hd hε hεr) continuous_fst.continuousAt rfl
  have h3 : ContinuousAt (fun p : ℝ × ℝ => Rfun d p.2) (ε, u) :=
    ContinuousAt.comp_of_eq (continuousAt_Rfun hd hu) continuous_snd.continuousAt rfl
  exact h1.mul (h2.sub h3)

theorem Aavg_zeta_eq_psiStar {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (hεr : ε ≠ rStar d) : Aavg d ε (zetaFun d ε) = psiStar d ε := by
  obtain ⟨hzm, hzne, hW⟩ := zetaFun_crit hd hε.1 hε.2 hεr
  have hD : Dfun d ε (zetaFun d ε) ≠ 0 := ne_of_gt (Dfun_pos hd hε.1 hzm.1.le hzne)
  have hdD : dD d ε (zetaFun d ε) ≠ 0 := dD_ne_zero hd hε.1 hzm.1 hzne
  unfold Aavg psiStar psiD
  unfold Wr at hW
  rw [div_eq_div_iff hdD hD]
  linarith

theorem gapCurv_pos {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1) (hεr : ε ≠ rStar d) :
    0 < gapCurv d (ε, ε) ∧ 0 < gapCurv d (ε, zetaFun d ε) := by
  obtain ⟨hzm, hzne, hW⟩ := zetaFun_crit hd hε.1 hε.2 hεr
  have hA := Aavg_zeta_eq_psiStar hd hε hεr
  have hR : Rfun d ε < psiStar d ε ∧ Rfun d (zetaFun d ε) < psiStar d ε := by
    rcases lt_or_gt_of_ne hzne with hlt | hgt
    · have h := Rfun_lt_Aavg_of_crit hd hzm.1 hε.2 hlt (Wr_eq_zero_swap hW)
      rw [Aavg_symm, hA] at h
      exact ⟨h.2, h.1⟩
    · have h := Rfun_lt_Aavg_of_crit hd hε.1 hzm.2 hgt hW
      rw [hA] at h
      exact h
  unfold gapCurv
  exact ⟨mul_pos (d2D_pos hd hε.1) (sub_pos.mpr hR.1),
    mul_pos (d2D_pos hd hzm.1) (sub_pos.mpr hR.2)⟩

/-! ### The uniform quadratic lower bound -/

/-- A neighbourhood version of positivity of a continuous function. -/
private theorem eventually_gt_half {f : ℝ → ℝ} {x₀ : ℝ} (hf : ContinuousAt f x₀) (h : 0 < f x₀) :
    ∃ η : ℝ, 0 < η ∧ ∀ x, |x - x₀| < η → f x₀ / 2 < f x := by
  have hev := hf.eventually (lt_mem_nhds (show f x₀ / 2 < f x₀ by linarith))
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨η, hη, fun x hx => hball (by rwa [Real.dist_eq])⟩

private theorem eventually_gt_half₂ {f : ℝ × ℝ → ℝ} {p₀ : ℝ × ℝ} (hf : ContinuousAt f p₀)
    (h : 0 < f p₀) : ∃ r : ℝ, 0 < r ∧ ∀ p, dist p p₀ < r → f p₀ / 2 < f p := by
  have hev := hf.eventually (lt_mem_nhds (show f p₀ / 2 < f p₀ by linarith))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨r, hr, fun p hp => hball hp⟩

private theorem min_sq_le_one {u a b : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (ha : a ∈ Icc (0:ℝ) 1) :
    min ((u - a) ^ 2) ((u - b) ^ 2) ≤ 1 := by
  refine le_trans (min_le_left _ _) ?_
  have h1 : -1 ≤ u - a := by linarith [hu.1, ha.2]
  have h2 : u - a ≤ 1 := by linarith [hu.2, ha.1]
  nlinarith

/-- **`kb:lem:gap`, uniform form.** -/
theorem gap_quadratic_lower {d : ℕ} (hd : 2 ≤ d) {ε₀ : ℝ} (hε₀ : ε₀ ∈ Ioo (0:ℝ) 1)
    (hε₀r : ε₀ ≠ rStar d) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ ∀ ε, |ε - ε₀| < η →
      ε ∈ Ioo (0:ℝ) 1 ∧ ε ≠ rStar d ∧
      ∀ u ∈ Icc (0:ℝ) 1, κ * min ((u - ε) ^ 2) ((u - zetaFun d ε) ^ 2) ≤ gapFun d ε u := by
  obtain ⟨hζ₀m, hζ₀ne, -⟩ := zetaFun_crit hd hε₀.1 hε₀.2 hε₀r
  set ζ₀ := zetaFun d ε₀ with hζ₀
  obtain ⟨hG1, hG2⟩ := gapCurv_pos hd hε₀ hε₀r
  obtain ⟨r₁, hr₁, hball₁⟩ := eventually_gt_half₂ (continuousAt_gapCurv hd hε₀ hε₀r hε₀) hG1
  obtain ⟨r₂, hr₂, hball₂⟩ := eventually_gt_half₂ (continuousAt_gapCurv hd hε₀ hε₀r hζ₀m) hG2
  set c₀ : ℝ := min (gapCurv d (ε₀, ε₀) / 2) (gapCurv d (ε₀, ζ₀) / 2) with hc₀
  have hc₀pos : 0 < c₀ := lt_min (by linarith) (by linarith)
  set sep : ℝ := |ζ₀ - ε₀| with hsep
  have hsep0 : 0 < sep := abs_pos.mpr (sub_ne_zero.mpr hζ₀ne)
  set m₀ : ℝ := min (min ε₀ (1 - ε₀)) (min ζ₀ (1 - ζ₀)) with hm₀
  have hm₀pos : 0 < m₀ := lt_min (lt_min hε₀.1 (by linarith [hε₀.2]))
    (lt_min hζ₀m.1 (by linarith [hζ₀m.2]))
  set δ : ℝ := min (min (sep / 8) (m₀ / 4)) (min r₁ r₂ / 2) with hδ
  have hδpos : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (by
    have := lt_min hr₁ hr₂; linarith)
  have hδsep : δ ≤ sep / 8 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδm : δ ≤ m₀ / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδr₁ : δ ≤ r₁ / 2 := le_trans (min_le_right _ _) (by
    have := min_le_left r₁ r₂; linarith)
  have hδr₂ : δ ≤ r₂ / 2 := le_trans (min_le_right _ _) (by
    have := min_le_right r₁ r₂; linarith)
  have hm₀ε : m₀ ≤ ε₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hm₀ε1 : m₀ ≤ 1 - ε₀ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hm₀ζ : m₀ ≤ ζ₀ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hm₀ζ1 : m₀ ≤ 1 - ζ₀ := le_trans (min_le_right _ _) (min_le_right _ _)
  -- continuity of `ζ_d`
  obtain ⟨ηζ, hηζ, hζball⟩ : ∃ η : ℝ, 0 < η ∧ ∀ x, |x - ε₀| < η → |zetaFun d x - ζ₀| < δ := by
    have hev := (continuousAt_zetaFun hd hε₀).eventually (Metric.ball_mem_nhds ζ₀ hδpos)
    obtain ⟨η, hη, h⟩ := Metric.eventually_nhds_iff.mp hev
    exact ⟨η, hη, fun x hx => by
      have := h (show dist x ε₀ < η by rwa [Real.dist_eq])
      rwa [Real.dist_eq] at this⟩
  set ηr : ℝ := |ε₀ - rStar d| with hηr
  have hηr0 : 0 < ηr := abs_pos.mpr (sub_ne_zero.mpr hε₀r)
  -- the two quadratic windows
  have hnearε : ∀ ε, |ε - ε₀| < δ → ε ∈ Ioo (0:ℝ) 1 → ∀ u ∈ Icc (ε - δ) (ε + δ),
      c₀ / 2 * (u - ε) ^ 2 ≤ gapFun d ε u := by
    intro ε hε hεI
    refine gapFun_quadratic_near hd (by linarith [abs_lt.mp hε]) (by linarith [abs_lt.mp hε])
      hδpos.le (gapFun_self d ε) (Kfun_self d _ ε) (fun x hx => ?_)
    have hdist : dist ((ε, x) : ℝ × ℝ) (ε₀, ε₀) < r₁ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      refine max_lt (by linarith [abs_lt.mp hε]) ?_
      rw [abs_lt]; constructor <;> linarith [abs_lt.mp hε, hx.1, hx.2]
    have := hball₁ _ hdist
    exact le_trans (min_le_left _ _) this.le
  have hnearζ : ∀ ε, |ε - ε₀| < min δ ηr → |zetaFun d ε - ζ₀| < δ → ε ∈ Ioo (0:ℝ) 1 →
      ∀ u ∈ Icc (zetaFun d ε - δ) (zetaFun d ε + δ),
      c₀ / 2 * (u - zetaFun d ε) ^ 2 ≤ gapFun d ε u := by
    intro ε hε hζε hεI
    have hεr : ε ≠ rStar d := by
      intro h
      have := lt_of_lt_of_le hε (min_le_right _ _)
      rw [h, abs_sub_comm] at this
      exact lt_irrefl _ this
    refine gapFun_quadratic_near hd (by linarith [abs_lt.mp hζε]) (by linarith [abs_lt.mp hζε])
      hδpos.le (gapFun_zeta hd hεI hεr) (Kfun_zeta hd hεI hεr) (fun x hx => ?_)
    have hε' := lt_of_lt_of_le hε (min_le_left _ _)
    have hdist : dist ((ε, x) : ℝ × ℝ) (ε₀, ζ₀) < r₂ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      refine max_lt (by linarith [abs_lt.mp hε']) ?_
      rw [abs_lt]; constructor <;> linarith [abs_lt.mp hζε, hx.1, hx.2]
    have := hball₂ _ hdist
    exact le_trans (min_le_right _ _) this.le
  have hεgood : ∀ ε, |ε - ε₀| < min δ ηr → ε ∈ Ioo (0:ℝ) 1 ∧ ε ≠ rStar d := by
    intro ε hε
    have h1 := lt_of_lt_of_le hε (min_le_left _ _)
    have h2 := lt_of_lt_of_le hε (min_le_right _ _)
    refine ⟨⟨by linarith [abs_lt.mp h1], by linarith [abs_lt.mp h1]⟩, fun h => ?_⟩
    rw [h, abs_sub_comm] at h2
    exact lt_irrefl _ h2
  -- joint continuity of the far bounds
  have hcomp : ∀ g : ℝ → ℝ, ContinuousAt g ε₀ →
      ContinuousAt (fun x => gapFun d x (g x)) ε₀ := fun g hg =>
    ContinuousAt.comp (g := fun p : ℝ × ℝ => gapFun d p.1 p.2) (f := fun x => (x, g x))
      (x := ε₀) (continuousAt_gapFun_prod hd hε₀ hε₀r) (continuousAt_id.prodMk hg)
  have hDcomp : ∀ g : ℝ → ℝ, ContinuousAt g ε₀ → ContinuousAt (fun x => Dfun d x (g x)) ε₀ := by
    intro g hg; unfold Dfun; fun_prop
  have hζc := continuousAt_zetaFun hd hε₀
  rcases lt_or_gt_of_ne hζ₀ne with hgt | hlt
  · -- `ζ₀ < ε₀`
    have hsepv : sep = ε₀ - ζ₀ := by rw [hsep, abs_sub_comm, abs_of_pos (by linarith)]
    set L : ℝ → ℝ := fun x => min (gapFun d x (zetaFun d x - δ)) (min (gapFun d x (x + δ))
      (Dfun d x (x - δ) * gapFun d x (zetaFun d x + δ) / Dfun d x (zetaFun d x + δ))) with hL
    have hLc : ContinuousAt L ε₀ := by
      refine (hcomp _ (hζc.sub continuousAt_const)).min ((hcomp _ (continuousAt_id.add
        continuousAt_const)).min (((hDcomp _ (continuousAt_id.sub continuousAt_const)).mul
        (hcomp _ (hζc.add continuousAt_const))).div (hDcomp _ (hζc.add continuousAt_const)) ?_))
      exact ne_of_gt (Dfun_pos hd hε₀.1 (by linarith) (by linarith))
    have hL0 : 0 < L ε₀ := by
      have p1 := gapFun_pos hd hε₀ (u := ζ₀ - δ) ⟨by linarith, by linarith⟩ (by linarith)
        (by linarith)
      have p2 := gapFun_pos hd hε₀ (u := ε₀ + δ) ⟨by linarith, by linarith⟩ (by linarith)
        (by linarith)
      have p3 := gapFun_pos hd hε₀ (u := ζ₀ + δ) ⟨by linarith, by linarith⟩ (by linarith)
        (by linarith)
      have q1 := Dfun_pos hd hε₀.1 (z := ε₀ - δ) (by linarith) (by linarith)
      have q2 := Dfun_pos hd hε₀.1 (z := ζ₀ + δ) (by linarith) (by linarith)
      exact lt_min p1 (lt_min p2 (div_pos (mul_pos q1 p3) q2))
    obtain ⟨ηL, hηL, hLball⟩ := eventually_gt_half hLc hL0
    refine ⟨min (c₀ / 2) (L ε₀ / 2), lt_min (by linarith) (by linarith),
      min (min δ ηr) (min ηζ ηL), lt_min (lt_min hδpos hηr0) (lt_min hηζ hηL), ?_⟩
    intro ε hε
    have hε1 := lt_of_lt_of_le hε (min_le_left _ _)
    have hεδ := lt_of_lt_of_le hε1 (min_le_left _ _)
    have hεζ := hζball ε (lt_of_lt_of_le hε (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hεL := hLball ε (lt_of_lt_of_le hε (le_trans (min_le_right _ _) (min_le_right _ _)))
    obtain ⟨hεI, hεr⟩ := hεgood ε hε1
    refine ⟨hεI, hεr, fun u hu => ?_⟩
    set ζ := zetaFun d ε with hζdef
    have hmin1 := min_sq_le_one (b := ζ) hu ⟨hεI.1.le, hεI.2.le⟩
    have hmin0 : 0 ≤ min ((u - ε) ^ 2) ((u - ζ) ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    by_cases h1 : |u - ε| ≤ δ
    · have := hnearε ε hεδ hεI u ⟨by linarith [abs_le.mp h1], by linarith [abs_le.mp h1]⟩
      have hk : min (c₀ / 2) (L ε₀ / 2) * min ((u - ε) ^ 2) ((u - ζ) ^ 2)
          ≤ c₀ / 2 * (u - ε) ^ 2 :=
        mul_le_mul (min_le_left _ _) (min_le_left _ _) hmin0 (by linarith)
      linarith
    by_cases h2 : |u - ζ| ≤ δ
    · have := hnearζ ε hε1 hεζ hεI u ⟨by linarith [abs_le.mp h2], by linarith [abs_le.mp h2]⟩
      have hk : min (c₀ / 2) (L ε₀ / 2) * min ((u - ε) ^ 2) ((u - ζ) ^ 2)
          ≤ c₀ / 2 * (u - ζ) ^ 2 :=
        mul_le_mul (min_le_left _ _) (min_le_right _ _) hmin0 (by linarith)
      linarith
    push Not at h1 h2
    have hfar : u ≤ ζ - δ ∨ (ζ + δ ≤ u ∧ u ≤ ε - δ) ∨ ε + δ ≤ u := by
      rcases lt_abs.mp h1 with h1 | h1 <;> rcases lt_abs.mp h2 with h2 | h2
      · right; right; linarith
      · exfalso; linarith [abs_lt.mp hεζ, abs_lt.mp hεδ]
      · right; left; constructor <;> linarith
      · left; linarith
    have hfarb := gapFun_ge_far_of_gt hd hεI hδpos (by linarith [abs_lt.mp hεζ])
      (by linarith [abs_lt.mp hεδ]) (by linarith [abs_lt.mp hεζ, abs_lt.mp hεδ]) hu hfar
    have hk : min (c₀ / 2) (L ε₀ / 2) * min ((u - ε) ^ 2) ((u - ζ) ^ 2) ≤ L ε₀ / 2 := by
      calc min (c₀ / 2) (L ε₀ / 2) * min ((u - ε) ^ 2) ((u - ζ) ^ 2)
          ≤ L ε₀ / 2 * 1 := mul_le_mul (min_le_right _ _) hmin1 hmin0 (by linarith)
        _ = L ε₀ / 2 := mul_one _
    have : L ε₀ / 2 < L ε := hεL
    linarith
  · -- `ε₀ < ζ₀`
    have hsepv : sep = ζ₀ - ε₀ := by rw [hsep, abs_of_pos (by linarith)]
    set L : ℝ → ℝ := fun x => min (gapFun d x (x - δ)) (min (gapFun d x (zetaFun d x + δ))
      (Dfun d x (x + δ) * gapFun d x (zetaFun d x - δ) / Dfun d x (zetaFun d x - δ))) with hL
    have hLc : ContinuousAt L ε₀ := by
      refine (hcomp _ (continuousAt_id.sub continuousAt_const)).min ((hcomp _ (hζc.add
        continuousAt_const)).min (((hDcomp _ (continuousAt_id.add continuousAt_const)).mul
        (hcomp _ (hζc.sub continuousAt_const))).div (hDcomp _ (hζc.sub continuousAt_const)) ?_))
      exact ne_of_gt (Dfun_pos hd hε₀.1 (by linarith) (by linarith))
    have hL0 : 0 < L ε₀ := by
      have p1 := gapFun_pos hd hε₀ (u := ε₀ - δ) ⟨by linarith, by linarith⟩ (by linarith)
        (by linarith)
      have p2 := gapFun_pos hd hε₀ (u := ζ₀ + δ) ⟨by linarith, by linarith⟩ (by linarith)
        (by linarith)
      have p3 := gapFun_pos hd hε₀ (u := ζ₀ - δ) ⟨by linarith, by linarith⟩ (by linarith)
        (by linarith)
      have q1 := Dfun_pos hd hε₀.1 (z := ε₀ + δ) (by linarith) (by linarith)
      have q2 := Dfun_pos hd hε₀.1 (z := ζ₀ - δ) (by linarith) (by linarith)
      exact lt_min p1 (lt_min p2 (div_pos (mul_pos q1 p3) q2))
    obtain ⟨ηL, hηL, hLball⟩ := eventually_gt_half hLc hL0
    refine ⟨min (c₀ / 2) (L ε₀ / 2), lt_min (by linarith) (by linarith),
      min (min δ ηr) (min ηζ ηL), lt_min (lt_min hδpos hηr0) (lt_min hηζ hηL), ?_⟩
    intro ε hε
    have hε1 := lt_of_lt_of_le hε (min_le_left _ _)
    have hεδ := lt_of_lt_of_le hε1 (min_le_left _ _)
    have hεζ := hζball ε (lt_of_lt_of_le hε (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hεL := hLball ε (lt_of_lt_of_le hε (le_trans (min_le_right _ _) (min_le_right _ _)))
    obtain ⟨hεI, hεr⟩ := hεgood ε hε1
    refine ⟨hεI, hεr, fun u hu => ?_⟩
    set ζ := zetaFun d ε with hζdef
    have hmin1 := min_sq_le_one (b := ζ) hu ⟨hεI.1.le, hεI.2.le⟩
    have hmin0 : 0 ≤ min ((u - ε) ^ 2) ((u - ζ) ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    by_cases h1 : |u - ε| ≤ δ
    · have := hnearε ε hεδ hεI u ⟨by linarith [abs_le.mp h1], by linarith [abs_le.mp h1]⟩
      have hk : min (c₀ / 2) (L ε₀ / 2) * min ((u - ε) ^ 2) ((u - ζ) ^ 2)
          ≤ c₀ / 2 * (u - ε) ^ 2 :=
        mul_le_mul (min_le_left _ _) (min_le_left _ _) hmin0 (by linarith)
      linarith
    by_cases h2 : |u - ζ| ≤ δ
    · have := hnearζ ε hε1 hεζ hεI u ⟨by linarith [abs_le.mp h2], by linarith [abs_le.mp h2]⟩
      have hk : min (c₀ / 2) (L ε₀ / 2) * min ((u - ε) ^ 2) ((u - ζ) ^ 2)
          ≤ c₀ / 2 * (u - ζ) ^ 2 :=
        mul_le_mul (min_le_left _ _) (min_le_right _ _) hmin0 (by linarith)
      linarith
    push Not at h1 h2
    have hfar : u ≤ ε - δ ∨ (ε + δ ≤ u ∧ u ≤ ζ - δ) ∨ ζ + δ ≤ u := by
      rcases lt_abs.mp h1 with h1 | h1 <;> rcases lt_abs.mp h2 with h2 | h2
      · right; right; linarith
      · right; left; constructor <;> linarith
      · exfalso; linarith [abs_lt.mp hεζ, abs_lt.mp hεδ]
      · left; linarith
    have hfarb := gapFun_ge_far_of_lt hd hεI hδpos (by linarith [abs_lt.mp hεδ])
      (by linarith [abs_lt.mp hεζ]) (by linarith [abs_lt.mp hεζ, abs_lt.mp hεδ]) hu hfar
    have hk : min (c₀ / 2) (L ε₀ / 2) * min ((u - ε) ^ 2) ((u - ζ) ^ 2) ≤ L ε₀ / 2 := by
      calc min (c₀ / 2) (L ε₀ / 2) * min ((u - ε) ^ 2) ((u - ζ) ^ 2)
          ≤ L ε₀ / 2 * 1 := mul_le_mul (min_le_right _ _) hmin1 hmin0 (by linarith)
        _ = L ε₀ / 2 := mul_one _
    have : L ε₀ / 2 < L ε := hεL
    linarith

end UpperTailOptimizers
