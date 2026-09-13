import UpperTailOptimizers.KRRS.PsiCritical

/-!
# Comparing `ψ_d` with the ratio `R_d`, and the sign of `∂_zψ_d` off the exceptional density

Two things are still missing before Kenyon–Radin–Ren–Sadun's `ζ_d` can be *constructed* rather
than assumed: a way to bound the values of `ψ_d` by values of `R_d`, and the sign of the
derivative on the two intervals where `R_d` is monotone.  Both come from one test function.

For a constant `c`, put

  `K_c(s) := 𝒩'_ε(s) - c·𝒟'_ε(s)`,

so that `K_c(ε) = 0`, `K_c' = 𝒟''·(R_d - c)` and `∫_ε^z K_c = 𝒩_ε(z) - c·𝒟_ε(z)`.  If `R_d < c`
throughout the interval joining `ε` and `z`, then `K_c` decreases through its zero at `ε`, so
`∫_ε^z K_c < 0` *in either orientation*, and `𝒟_ε(z) > 0` turns that into `ψ_d(ε,z) < c`.  With
`c = 0` (where `R_d < 0` always) this already gives `ψ_d < 0`; with `c = R_d(ε)` it says that
`ψ_d(ε,·)` sits below `R_d(ε)` on the side of `ε` where `R_d` is smaller, and above it on the
other side.

The same test function, at `c = R_d` of an endpoint, bounds the mean `A(ε,z)` of
`KRRS/PsiIntegral.lean` by that endpoint value, which is exactly the hypothesis of the two
sign lemmas `Hfun_nonpos_right` and `Hfun_nonneg_left` proved in `KRRS/PsiCritical.lean`.
Feeding them the identity

  `W(a,b) = -𝒟'_a(b)·∫_a^b H`

gives `W > 0` below the exceptional density and `W < 0` above it — the two facts that locate
the critical point in `KRRS/PsiExists.lean`.

## Contents

* `Kfun`, `hasDerivAt_Kfun`, `integral_Kfun` — the test function;
* `Nfun_sub_neg`, `psiD_lt_of_Rfun_lt` and their duals — `ψ_d` against a constant;
* `psiD_neg` — `ψ_d < 0` off the diagonal;
* `Aavg_le_of_forall_le`, `le_Aavg_of_forall_le` — the mean against a constant;
* `Wr_pos_of_le_rStar`, `Wr_neg_of_rStar_le` — the sign of `∂_zψ_d` on each monotone side.
-/

namespace UpperTailOptimizers

open Real Set intervalIntegral

/-! ### The test function `K_c` -/

/-- `K_c(s) = 𝒩'_ε(s) - c·𝒟'_ε(s)`; the `H` of `KRRS/PsiIntegral.lean` is the case
`c = A(ε,z)`. -/
noncomputable def Kfun (d : ℕ) (c ε s : ℝ) : ℝ := dN ε s - c * dD d ε s

theorem Kfun_self (d : ℕ) (c ε : ℝ) : Kfun d c ε ε = 0 := by
  unfold Kfun dN dD; ring

/-- `K_c'(s) = 𝒟''(s)·(R_d(s) - c)`. -/
theorem hasDerivAt_Kfun {d : ℕ} (hd : 2 ≤ d) (c ε : ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt (Kfun d c ε) (d2D d s * (Rfun d s - c)) s := by
  have h1 : HasDerivAt (fun x => dN ε x) (d2N s) s :=
    hasDerivAt_dN ε (ne_of_gt hs0) (ne_of_lt hs1)
  have h2 : HasDerivAt (fun x => dD d ε x) (d2D d s) s := hasDerivAt_dD hd ε s
  have h := h1.fun_sub (h2.const_mul c)
  have hval : d2N s - c * d2D d s = d2D d s * (Rfun d s - c) := by
    have hpos : 0 < d2D d s := d2D_pos hd hs0
    unfold Rfun
    field_simp
  rw [hval] at h
  exact h

theorem intervalIntegrable_Kfun {d : ℕ} (hd : 2 ≤ d) (c : ℝ) {ε z : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hz0 : 0 < z) (hz1 : z < 1) : IntervalIntegrable (Kfun d c ε) MeasureTheory.volume ε z := by
  have hsub := uIcc_subset_Ioo hε0 hε1 hz0 hz1
  refine ContinuousOn.intervalIntegrable (fun s hs => ?_)
  have h := hsub hs
  exact (hasDerivAt_Kfun hd c ε h.1 h.2).continuousAt.continuousWithinAt

theorem integral_Kfun {d : ℕ} (hd : 2 ≤ d) (c : ℝ) {ε z : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hz0 : 0 < z) (hz1 : z < 1) :
    ∫ s in ε..z, Kfun d c ε s = Nfun ε z - c * Dfun d ε z := by
  have hsub := uIcc_subset_Ioo hε0 hε1 hz0 hz1
  have hintN : IntervalIntegrable (fun s => dN ε s) MeasureTheory.volume ε z := by
    refine ContinuousOn.intervalIntegrable (fun s hs => ?_)
    have h := hsub hs
    exact ((hasDerivAt_dN ε (ne_of_gt h.1) (ne_of_lt h.2)).continuousAt).continuousWithinAt
  have hintD : IntervalIntegrable (fun s => dD d ε s) MeasureTheory.volume ε z :=
    ContinuousOn.intervalIntegrable
      (fun s _ => ((hasDerivAt_dD hd ε s).continuousAt).continuousWithinAt)
  unfold Kfun
  rw [integral_sub hintN (hintD.const_mul _), integral_const_mul,
    integral_dN hε0 hε1 hz0 hz1, integral_dD hd ε z]

/-! ### `R_d < 0`, and `𝒟'` off the diagonal -/

theorem Rfun_neg {d : ℕ} (hd : 2 ≤ d) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : Rfun d t < 0 := by
  have hd1 : (1 : ℝ) < (d : ℝ) := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hg : 0 < gfun d t := gfun_pos h0 h1
  have hden : 0 < (d : ℝ) * ((d : ℝ) - 1) * gfun d t := by
    have : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
    positivity
  rw [Rfun_eq hd h0 h1]
  exact div_neg_of_neg_of_pos (by norm_num) hden

/-- `𝒟'_a(b) = d(b^{d-1} - a^{d-1}) > 0` for `0 < a < b`. -/
theorem dD_pos {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha0 : 0 < a) (hab : a < b) : 0 < dD d a b := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  have hdne : d - 1 ≠ 0 := by omega
  have hpow : a ^ (d - 1) < b ^ (d - 1) := pow_lt_pow_left₀ hab ha0.le hdne
  unfold dD
  nlinarith [hpow, hd0]

/-! ### `ψ_d` against a constant -/

private theorem Kfun_strictAntiOn {d : ℕ} (hd : 2 ≤ d) {c ε a b : ℝ} (ha0 : 0 < a) (hb1 : b < 1)
    (h : ∀ s ∈ Set.Ioo a b, Rfun d s < c) : StrictAntiOn (Kfun d c ε) (Set.Icc a b) := by
  have hmem : ∀ s ∈ Set.Icc a b, 0 < s ∧ s < 1 := fun s hs =>
    ⟨lt_of_lt_of_le ha0 hs.1, lt_of_le_of_lt hs.2 hb1⟩
  refine strictAntiOn_of_deriv_neg (convex_Icc a b)
    (fun s hs =>
      (hasDerivAt_Kfun hd c ε (hmem s hs).1 (hmem s hs).2).continuousAt.continuousWithinAt)
    (fun x hx => ?_)
  rw [interior_Icc] at hx
  have hxmem : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
  rw [(hasDerivAt_Kfun hd c ε (hmem x hxmem).1 (hmem x hxmem).2).deriv]
  have hpos : 0 < d2D d x := d2D_pos hd (hmem x hxmem).1
  nlinarith [h x hx]

private theorem Kfun_strictMonoOn {d : ℕ} (hd : 2 ≤ d) {c ε a b : ℝ} (ha0 : 0 < a) (hb1 : b < 1)
    (h : ∀ s ∈ Set.Ioo a b, c < Rfun d s) : StrictMonoOn (Kfun d c ε) (Set.Icc a b) := by
  have hmem : ∀ s ∈ Set.Icc a b, 0 < s ∧ s < 1 := fun s hs =>
    ⟨lt_of_lt_of_le ha0 hs.1, lt_of_le_of_lt hs.2 hb1⟩
  refine strictMonoOn_of_deriv_pos (convex_Icc a b)
    (fun s hs =>
      (hasDerivAt_Kfun hd c ε (hmem s hs).1 (hmem s hs).2).continuousAt.continuousWithinAt)
    (fun x hx => ?_)
  rw [interior_Icc] at hx
  have hxmem : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
  rw [(hasDerivAt_Kfun hd c ε (hmem x hxmem).1 (hmem x hxmem).2).deriv]
  have hpos : 0 < d2D d x := d2D_pos hd (hmem x hxmem).1
  nlinarith [h x hx]

/-- **`R_d < c` between `ε` and `z` forces `𝒩 - c𝒟 < 0`.**  `K_c` vanishes at `ε` and strictly
decreases, so it is negative to the right of `ε` and positive to the left; either way the
oriented integral `∫_ε^z K_c` is negative. -/
theorem Nfun_sub_neg {d : ℕ} (hd : 2 ≤ d) {c ε z : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hz0 : 0 < z) (hz1 : z < 1) (hne : z ≠ ε)
    (h : ∀ s ∈ Set.Ioo (min ε z) (max ε z), Rfun d s < c) :
    Nfun ε z - c * Dfun d ε z < 0 := by
  rw [← integral_Kfun hd c hε0 hε1 hz0 hz1]
  have hint := intervalIntegrable_Kfun hd c hε0 hε1 hz0 hz1
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [min_eq_right hlt.le, max_eq_left hlt.le] at h
    have hanti := Kfun_strictAntiOn (ε := ε) hd hz0 hε1 h
    have hpos : ∀ x ∈ Set.Ioo z ε, 0 < Kfun d c ε x := by
      intro x hx
      have := hanti ⟨hx.1.le, hx.2.le⟩ (Set.right_mem_Icc.mpr hlt.le) hx.2
      rwa [Kfun_self] at this
    have hIp := intervalIntegral_pos_of_pos_on hint.symm hpos hlt
    rw [integral_symm z ε]
    linarith
  · rw [min_eq_left hgt.le, max_eq_right hgt.le] at h
    have hanti := Kfun_strictAntiOn (ε := ε) hd hε0 hz1 h
    have hpos : ∀ x ∈ Set.Ioo ε z, 0 < -Kfun d c ε x := by
      intro x hx
      have := hanti (Set.left_mem_Icc.mpr hgt.le) ⟨hx.1.le, hx.2.le⟩ hx.1
      rw [Kfun_self] at this
      linarith
    have hIp := intervalIntegral_pos_of_pos_on hint.neg hpos hgt
    simp only [Pi.neg_apply, integral_neg] at hIp
    linarith

/-- The dual of `Nfun_sub_neg`. -/
theorem Nfun_sub_pos {d : ℕ} (hd : 2 ≤ d) {c ε z : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hz0 : 0 < z) (hz1 : z < 1) (hne : z ≠ ε)
    (h : ∀ s ∈ Set.Ioo (min ε z) (max ε z), c < Rfun d s) :
    0 < Nfun ε z - c * Dfun d ε z := by
  rw [← integral_Kfun hd c hε0 hε1 hz0 hz1]
  have hint := intervalIntegrable_Kfun hd c hε0 hε1 hz0 hz1
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [min_eq_right hlt.le, max_eq_left hlt.le] at h
    have hmono := Kfun_strictMonoOn (ε := ε) hd hz0 hε1 h
    have hpos : ∀ x ∈ Set.Ioo z ε, 0 < -Kfun d c ε x := by
      intro x hx
      have := hmono ⟨hx.1.le, hx.2.le⟩ (Set.right_mem_Icc.mpr hlt.le) hx.2
      rw [Kfun_self] at this
      linarith
    have hIp := intervalIntegral_pos_of_pos_on hint.symm.neg hpos hlt
    simp only [Pi.neg_apply, integral_neg] at hIp
    rw [integral_symm z ε]
    linarith
  · rw [min_eq_left hgt.le, max_eq_right hgt.le] at h
    have hmono := Kfun_strictMonoOn (ε := ε) hd hε0 hz1 h
    have hpos : ∀ x ∈ Set.Ioo ε z, 0 < Kfun d c ε x := by
      intro x hx
      have := hmono (Set.left_mem_Icc.mpr hgt.le) ⟨hx.1.le, hx.2.le⟩ hx.1
      rwa [Kfun_self] at this
    exact intervalIntegral_pos_of_pos_on hint hpos hgt

theorem psiD_lt_of_Rfun_lt {d : ℕ} (hd : 2 ≤ d) {c ε z : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hz0 : 0 < z) (hz1 : z < 1) (hne : z ≠ ε)
    (h : ∀ s ∈ Set.Ioo (min ε z) (max ε z), Rfun d s < c) : psiD d ε z < c := by
  have hD : 0 < Dfun d ε z := Dfun_pos hd hε0 hz0.le hne
  have := Nfun_sub_neg hd hε0 hε1 hz0 hz1 hne h
  unfold psiD
  rw [div_lt_iff₀ hD]
  linarith

theorem lt_psiD_of_lt_Rfun {d : ℕ} (hd : 2 ≤ d) {c ε z : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hz0 : 0 < z) (hz1 : z < 1) (hne : z ≠ ε)
    (h : ∀ s ∈ Set.Ioo (min ε z) (max ε z), c < Rfun d s) : c < psiD d ε z := by
  have hD : 0 < Dfun d ε z := Dfun_pos hd hε0 hz0.le hne
  have := Nfun_sub_pos hd hε0 hε1 hz0 hz1 hne h
  unfold psiD
  rw [lt_div_iff₀ hD]
  linarith

/-- **`ψ_d < 0` off the diagonal**: the case `c = 0` of `psiD_lt_of_Rfun_lt`, since `R_d < 0`
throughout `(0,1)`.  This is strict concavity of `S₀` against strict convexity of `u ↦ u^d`. -/
theorem psiD_neg {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hz0 : 0 < z) (hz1 : z < 1) (hne : z ≠ ε) : psiD d ε z < 0 := by
  refine psiD_lt_of_Rfun_lt hd hε0 hε1 hz0 hz1 hne (fun s hs => ?_)
  have hs0 : 0 < s := lt_of_le_of_lt (le_min hε0.le hz0.le) hs.1
  have hs1 : s < 1 := lt_of_lt_of_le hs.2 (max_le hε1.le hz1.le)
  exact Rfun_neg hd hs0 hs1

/-! ### The mean `A` against a constant -/

/-- If `R_d ≤ c` throughout `[a,b]`, then so is its `𝒟''`-weighted mean `A(a,b)`. -/
theorem Aavg_le_of_forall_le {d : ℕ} (hd : 2 ≤ d) {a b c : ℝ} (ha0 : 0 < a) (hb1 : b < 1)
    (hab : a < b) (h : ∀ s ∈ Set.Ioo a b, Rfun d s < c) : Aavg d a b ≤ c := by
  have hDpos : 0 < dD d a b := dD_pos hd ha0 hab
  have hanti := Kfun_strictAntiOn (ε := a) hd ha0 hb1 h
  have hKb : Kfun d c a b < 0 := by
    have := hanti (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le) hab
    rwa [Kfun_self] at this
  have : dN a b - c * dD d a b < 0 := hKb
  unfold Aavg
  rw [div_le_iff₀ hDpos]
  linarith

/-! ### The sign of `W` on each monotone side of the exceptional density -/

/-- `W(a,b) = -𝒟'_a(b)·∫_a^b H`: the criticality functional is the oriented integral of the
test function of `KRRS/PsiIntegral.lean`, scaled by `𝒟'`. -/
theorem Wr_eq_neg_dD_mul_integral {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) (hne : b ≠ a) :
    Wr d a b = -(dD d a b * ∫ s in a..b, Hfun d a b s) := by
  rw [integral_Hfun hd ha0 ha1 hb0 hb1]
  have hDne : dD d a b ≠ 0 := dD_ne_zero hd ha0 hb0 hne
  unfold Aavg Wr
  field_simp
  ring

/-- The integral of `H` is nonzero at a non-critical configuration: if it vanished, `H` would
vanish identically on the interior and `R_d` would be constant there. -/
private theorem integral_Hfun_ne_zero_of_le_right {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha0 : 0 < a)
    (hb1 : b < 1) (hab : a < b) (hA : Aavg d a b ≤ Rfun d b) :
    (∫ s in a..b, Hfun d a b s) < 0 := by
  have hb0 : 0 < b := lt_trans ha0 hab
  have hne : b ≠ a := ne_of_gt hab
  have hsubIoo : ∀ s ∈ Set.Icc a b, 0 < s ∧ s < 1 := fun s hs =>
    ⟨lt_of_lt_of_le ha0 hs.1, lt_of_le_of_lt hs.2 hb1⟩
  have hderiv : ∀ s ∈ Set.Icc a b,
      HasDerivAt (Hfun d a b) (d2D d s * (Rfun d s - Aavg d a b)) s := fun s hs =>
    hasDerivAt_Hfun hd a b (hsubIoo s hs).1 (hsubIoo s hs).2
  have hcontAll : ContinuousOn (Hfun d a b) (Set.Icc a b) := fun s hs =>
    (hderiv s hs).continuousAt.continuousWithinAt
  have hnonpos := Hfun_nonpos_right hd ha0 hb1 hab hne hA
  have hint : IntervalIntegrable (Hfun d a b) MeasureTheory.volume a b := by
    refine ContinuousOn.intervalIntegrable (hcontAll.mono ?_)
    rw [Set.uIcc_of_le hab.le]
  have hle : (∫ s in a..b, Hfun d a b s) ≤ 0 := by
    have hnn : ∀ u ∈ Set.Icc a b, 0 ≤ -Hfun d a b u := fun u hu => by
      have := hnonpos u hu; linarith
    have h := integral_nonneg (μ := MeasureTheory.volume) (f := fun u => -Hfun d a b u) hab.le hnn
    simp only [integral_neg] at h
    linarith
  refine lt_of_le_of_ne hle (fun heq => ?_)
  have hz := eq_zero_of_nonpos_of_integral_zero hab hcontAll hnonpos heq
  refine not_Rfun_const hd ha0 hb1 hab (A := Aavg d a b) (fun s hs => ?_)
  have hev : Hfun d a b =ᶠ[nhds s] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht using hz t ht
  have h0 : HasDerivAt (Hfun d a b) 0 s :=
    (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hev
  have h1 := hderiv s ⟨hs.1.le, hs.2.le⟩
  have hzero : (0 : ℝ) = d2D d s * (Rfun d s - Aavg d a b) := h0.unique h1
  have hpos : 0 < d2D d s := d2D_pos hd (hsubIoo s ⟨hs.1.le, hs.2.le⟩).1
  rcases mul_eq_zero.mp hzero.symm with h' | h'
  · exact absurd h' (ne_of_gt hpos)
  · linarith

private theorem integral_Hfun_pos_of_le_left {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha0 : 0 < a)
    (hb1 : b < 1) (hab : a < b) (hA : Aavg d a b ≤ Rfun d a) :
    0 < ∫ s in a..b, Hfun d a b s := by
  have hb0 : 0 < b := lt_trans ha0 hab
  have hne : b ≠ a := ne_of_gt hab
  have hsubIoo : ∀ s ∈ Set.Icc a b, 0 < s ∧ s < 1 := fun s hs =>
    ⟨lt_of_lt_of_le ha0 hs.1, lt_of_le_of_lt hs.2 hb1⟩
  have hderiv : ∀ s ∈ Set.Icc a b,
      HasDerivAt (Hfun d a b) (d2D d s * (Rfun d s - Aavg d a b)) s := fun s hs =>
    hasDerivAt_Hfun hd a b (hsubIoo s hs).1 (hsubIoo s hs).2
  have hcontAll : ContinuousOn (Hfun d a b) (Set.Icc a b) := fun s hs =>
    (hderiv s hs).continuousAt.continuousWithinAt
  have hnonneg := Hfun_nonneg_left hd ha0 hb1 hab hne hA
  have hge : 0 ≤ ∫ s in a..b, Hfun d a b s :=
    integral_nonneg (μ := MeasureTheory.volume) hab.le hnonneg
  refine lt_of_le_of_ne hge (fun heq => ?_)
  have hz := eq_zero_of_nonneg_of_integral_zero hab hcontAll hnonneg heq.symm
  refine not_Rfun_const hd ha0 hb1 hab (A := Aavg d a b) (fun s hs => ?_)
  have hev : Hfun d a b =ᶠ[nhds s] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht using hz t ht
  have h0 : HasDerivAt (Hfun d a b) 0 s :=
    (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hev
  have h1 := hderiv s ⟨hs.1.le, hs.2.le⟩
  have hzero : (0 : ℝ) = d2D d s * (Rfun d s - Aavg d a b) := h0.unique h1
  have hpos : 0 < d2D d s := d2D_pos hd (hsubIoo s ⟨hs.1.le, hs.2.le⟩).1
  rcases mul_eq_zero.mp hzero.symm with h' | h'
  · exact absurd h' (ne_of_gt hpos)
  · linarith

/-- **Below the exceptional density `∂_zψ_d > 0`.**  On `(0,r_*]` the ratio `R_d` is strictly
increasing, so its mean over `[a,b]` is below `R_d(b)`, `H ≤ 0` throughout, and `∫ H < 0`. -/
theorem Wr_pos_of_le_rStar {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha0 : 0 < a) (hab : a < b)
    (hbr : b ≤ rStar d) : 0 < Wr d a b := by
  have hr1 : rStar d < 1 := rStar_lt_one hd
  have hb1 : b < 1 := lt_of_le_of_lt hbr hr1
  have ha1 : a < 1 := lt_trans hab hb1
  have hb0 : 0 < b := lt_trans ha0 hab
  have hmono : ∀ s ∈ Set.Ioo a b, Rfun d s < Rfun d b := fun s hs =>
    Rfun_strictMonoOn hd ⟨lt_trans ha0 hs.1, le_trans hs.2.le hbr⟩ ⟨hb0, hbr⟩ hs.2
  have hA : Aavg d a b ≤ Rfun d b := Aavg_le_of_forall_le hd ha0 hb1 hab hmono
  have hI := integral_Hfun_ne_zero_of_le_right hd ha0 hb1 hab hA
  have hD := dD_pos hd ha0 hab
  rw [Wr_eq_neg_dD_mul_integral hd ha0 ha1 hb0 hb1 (ne_of_gt hab)]
  have : dD d a b * (∫ s in a..b, Hfun d a b s) < 0 := mul_neg_of_pos_of_neg hD hI
  linarith

/-- **Above the exceptional density `∂_zψ_d < 0`.**  The mirror of `Wr_pos_of_le_rStar`, with
`R_d` strictly decreasing on `[r_*,1)`. -/
theorem Wr_neg_of_rStar_le {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (hra : rStar d ≤ a) (hab : a < b)
    (hb1 : b < 1) : Wr d a b < 0 := by
  have hr0 : 0 < rStar d := rStar_pos hd
  have ha0 : 0 < a := lt_of_lt_of_le hr0 hra
  have ha1 : a < 1 := lt_trans hab hb1
  have hb0 : 0 < b := lt_trans ha0 hab
  have hanti : ∀ s ∈ Set.Ioo a b, Rfun d s < Rfun d a := fun s hs =>
    Rfun_strictAntiOn hd ⟨hra, ha1⟩ ⟨le_trans hra hs.1.le, lt_trans hs.2 hb1⟩ hs.1
  have hA : Aavg d a b ≤ Rfun d a := Aavg_le_of_forall_le hd ha0 hb1 hab hanti
  have hI := integral_Hfun_pos_of_le_left hd ha0 hb1 hab hA
  have hD := dD_pos hd ha0 hab
  rw [Wr_eq_neg_dD_mul_integral hd ha0 ha1 hb0 hb1 (ne_of_gt hab)]
  have : 0 < dD d a b * (∫ s in a..b, Hfun d a b s) := mul_pos hD hI
  linarith

end UpperTailOptimizers
