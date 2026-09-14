import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.PsiRatio

/-!
# The averaged form of the critical-point equation

Writing `P(t) = 2S₀'(t)` and `Q(t) = d t^{d-1}`, so that `N'(ε,s) = P(s) - P(ε)` is `dN` and
`D'(ε,s) = Q(s) - Q(ε)` is `dD`, the fundamental theorem of calculus turns the two Taylor
remainders into

  `N(ε,z) = ∫_ε^z N'(ε,s)ds`,   `D(ε,z) = ∫_ε^z D'(ε,s)ds`.

Set `A(ε,z) := N'(ε,z)/D'(ε,z)` — the `Q'`-weighted mean of `R_d` over the interval — and

  `H(s) := N'(ε,s) - A·D'(ε,s)`.

Then `H(ε) = 0` always, `H(z) = 0` by the definition of `A`, and `∫_ε^z H = N - A·D`, which
vanishes exactly when `(ε,z)` is a critical point of `ψ_d`.  Finally `H' = D''·(R_d - A)`, so
the sign of `H'` is the sign of `R_d - A`, which `Preliminaries/KRRSAnalyticExtension/PsiRatio.lean` controls.

## Contents

* `Aavg`, `Aavg_symm`, `Hfun` — the mean and the test function;
* `integral_dN`, `integral_dD` — the two fundamental-theorem identities;
* `Hfun_left`, `Hfun_right`, `hasDerivAt_Hfun`, `integral_Hfun` — the four facts above;
* `integral_Hfun_eq_zero_of_Wr` — criticality is `∫_ε^z H = 0`.
-/

namespace UpperTailOptimizers

open Real Set intervalIntegral

/-! ### The interval stays inside `(0,1)` -/

theorem uIcc_subset_Ioo {ε z : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    Set.uIcc ε z ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro s hs
  exact ⟨lt_of_lt_of_le (lt_min hε0 hz0) hs.1, lt_of_le_of_lt hs.2 (max_lt hε1 hz1)⟩

/-! ### The two fundamental-theorem identities -/

theorem integral_dN {ε z : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    ∫ s in ε..z, dN ε s = Nfun ε z := by
  have hsub := uIcc_subset_Ioo hε0 hε1 hz0 hz1
  have hderiv : ∀ s ∈ Set.uIcc ε z, HasDerivAt (fun x => Nfun ε x) (dN ε s) s := by
    intro s hs
    have h := hsub hs
    exact hasDerivAt_Nfun ε (ne_of_gt h.1) (ne_of_lt h.2)
  have hcont : ContinuousOn (fun s => dN ε s) (Set.uIcc ε z) := by
    intro s hs
    have h := hsub hs
    exact ((hasDerivAt_dN ε (ne_of_gt h.1) (ne_of_lt h.2)).continuousAt).continuousWithinAt
  have hint : IntervalIntegrable (fun s => dN ε s) MeasureTheory.volume ε z :=
    hcont.intervalIntegrable
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have hzero : Nfun ε ε = 0 := by unfold Nfun; ring
  rw [hzero, sub_zero]

theorem integral_dD {d : ℕ} (hd : 2 ≤ d) (ε z : ℝ) :
    ∫ s in ε..z, dD d ε s = Dfun d ε z := by
  have hderiv : ∀ s ∈ Set.uIcc ε z, HasDerivAt (fun x => Dfun d ε x) (dD d ε s) s :=
    fun s _ => hasDerivAt_Dfun d ε s
  have hcont : ContinuousOn (fun s => dD d ε s) (Set.uIcc ε z) :=
    fun s _ => ((hasDerivAt_dD hd ε s).continuousAt).continuousWithinAt
  have hint : IntervalIntegrable (fun s => dD d ε s) MeasureTheory.volume ε z :=
    hcont.intervalIntegrable
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have hzero : Dfun d ε ε = 0 := by unfold Dfun; ring
  rw [hzero, sub_zero]

/-! ### The mean `A` and the test function `H` -/

/-- `A(ε,z) = N'(ε,z)/D'(ε,z)`, the `Q'`-weighted mean of `R_d` over the interval. -/
noncomputable def Aavg (d : ℕ) (ε z : ℝ) : ℝ := dN ε z / dD d ε z

/-- `A` is symmetric: both `N'` and `D'` are odd under exchanging the arguments. -/
theorem Aavg_symm (d : ℕ) (ε z : ℝ) : Aavg d z ε = Aavg d ε z := by
  unfold Aavg
  rw [dN_swap, dD_swap, neg_div_neg_eq]

/-- `D'(ε,z) ≠ 0` off the diagonal: `t ↦ t^{d-1}` is injective on the nonnegatives. -/
theorem dD_ne_zero {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε0 : 0 < ε) (hz0 : 0 < z) (hne : z ≠ ε) :
    dD d ε z ≠ 0 := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  have hdne : d - 1 ≠ 0 := by omega
  have hpow : z ^ (d - 1) ≠ ε ^ (d - 1) := by
    rcases lt_trichotomy z ε with h | h | h
    · exact ne_of_lt (pow_lt_pow_left₀ h hz0.le hdne)
    · exact absurd h hne
    · exact ne_of_gt (pow_lt_pow_left₀ h hε0.le hdne)
  unfold dD
  intro h
  apply hpow
  have : (d : ℝ) * (z ^ (d - 1) - ε ^ (d - 1)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' (ne_of_gt hd0)
  · linarith

/-- `H(s) = N'(ε,s) - A(ε,z)·D'(ε,s)`. -/
noncomputable def Hfun (d : ℕ) (ε z s : ℝ) : ℝ := dN ε s - Aavg d ε z * dD d ε s

theorem Hfun_left (d : ℕ) (ε z : ℝ) : Hfun d ε z ε = 0 := by
  unfold Hfun dN dD; ring

theorem Hfun_right {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε0 : 0 < ε) (hz0 : 0 < z) (hne : z ≠ ε) :
    Hfun d ε z z = 0 := by
  unfold Hfun Aavg
  field_simp [dD_ne_zero hd hε0 hz0 hne]
  ring

/-- `H'(s) = D''(s)·(R_d(s) - A)`. -/
theorem hasDerivAt_Hfun {d : ℕ} (hd : 2 ≤ d) (ε z : ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt (Hfun d ε z) (d2D d s * (Rfun d s - Aavg d ε z)) s := by
  have h1 : HasDerivAt (fun x => dN ε x) (d2N s) s :=
    hasDerivAt_dN ε (ne_of_gt hs0) (ne_of_lt hs1)
  have h2 : HasDerivAt (fun x => dD d ε x) (d2D d s) s := hasDerivAt_dD hd ε s
  have h := h1.fun_sub (h2.const_mul (Aavg d ε z))
  have hval : d2N s - Aavg d ε z * d2D d s = d2D d s * (Rfun d s - Aavg d ε z) := by
    have hpos : 0 < d2D d s := d2D_pos hd hs0
    unfold Rfun
    field_simp
  rw [hval] at h
  exact h

theorem integral_Hfun {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hz0 : 0 < z) (hz1 : z < 1) :
    ∫ s in ε..z, Hfun d ε z s = Nfun ε z - Aavg d ε z * Dfun d ε z := by
  have hsub := uIcc_subset_Ioo hε0 hε1 hz0 hz1
  have hintN : IntervalIntegrable (fun s => dN ε s) MeasureTheory.volume ε z := by
    refine ContinuousOn.intervalIntegrable (fun s hs => ?_)
    have h := hsub hs
    exact ((hasDerivAt_dN ε (ne_of_gt h.1) (ne_of_lt h.2)).continuousAt).continuousWithinAt
  have hintD : IntervalIntegrable (fun s => dD d ε s) MeasureTheory.volume ε z :=
    ContinuousOn.intervalIntegrable
      (fun s _ => ((hasDerivAt_dD hd ε s).continuousAt).continuousWithinAt)
  unfold Hfun
  rw [integral_sub hintN (hintD.const_mul _), integral_const_mul,
    integral_dN hε0 hε1 hz0 hz1, integral_dD hd ε z]

/-- **Criticality is `∫_ε^z H = 0`.** -/
theorem integral_Hfun_eq_zero_of_Wr {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hz0 : 0 < z) (hz1 : z < 1) (hne : z ≠ ε) (hcrit : Wr d ε z = 0) :
    ∫ s in ε..z, Hfun d ε z s = 0 := by
  have hDne := dD_ne_zero hd hε0 hz0 hne
  rw [integral_Hfun hd hε0 hε1 hz0 hz1]
  unfold Aavg
  have hW : dN ε z * Dfun d ε z - Nfun ε z * dD d ε z = 0 := hcrit
  field_simp
  linarith [hW]

end UpperTailOptimizers
