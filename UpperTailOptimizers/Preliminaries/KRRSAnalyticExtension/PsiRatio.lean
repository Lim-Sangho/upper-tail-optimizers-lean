import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.PsiSymmetry

/-!
# The ratio `R_d = N''/D''` and its unimodality

Steps 2 and 4 of Kenyon–Radin–Ren–Sadun, Theorem 3.3 both turn on the shape of one scalar
function.  Writing `P(t) = 2S₀'(t)` and `Q(t) = d t^{d-1}`, the two Taylor remainders of
`eq:krrs-entropy-remainder` and `eq:krrs-moment-remainder` are `N(ε,z) = ∫_ε^z (P(s) - P(ε))ds`
and `D(ε,z) = ∫_ε^z (Q(s) - Q(ε))ds`, so `ψ_d(ε,·)` is a weighted average of

  `R_d(t) := N''(t)/D''(t) = P'(t)/Q'(t) = -1/(d(d-1)·t^{d-1}(1-t))`.

The source's Step 2 uses exactly this: its integrands carry the factor
`ε̃^{k-1}(1-ε̃) - x^{k-1}(1-x)`, and its sign is controlled because "the function `x^{k-1}(1-x)`
has a single maximum at `x = (k-1)/k`".  That is `gfun` below, and `R_d` is a strictly
increasing function of it, so `R_d` rises on `(0,r_*]` and falls on `[r_*,1)`.

## Contents

* `gfun`, `hasDerivAt_gfun`, `gfun_pos` — `g_d(t) = t^{d-1}(1-t)` and its derivative
  `t^{d-2}((d-1) - dt)`;
* `gfun_strictMonoOn`, `gfun_strictAntiOn` — the single maximum at `r_* = (d-1)/d`;
* `Rfun`, `Rfun_eq`, `Rfun_strictMonoOn`, `Rfun_strictAntiOn` — the same shape for `R_d`.
-/

namespace UpperTailOptimizers

open Real Set

/-! ### `g_d(t) = t^{d-1}(1-t)` -/

/-- The source's `x^{k-1}(1-x)`, whose single maximum at `(k-1)/k` controls every sign in
Steps 2 and 4. -/
noncomputable def gfun (d : ℕ) (t : ℝ) : ℝ := t ^ (d - 1) * (1 - t)

theorem gfun_pos {d : ℕ} {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 0 < gfun d t := by
  have h2 : (0 : ℝ) < 1 - t := by linarith
  exact mul_pos (pow_pos h0 _) h2

/-- `g_d'(t) = t^{d-2}((d-1) - dt)`. -/
theorem hasDerivAt_gfun {d : ℕ} (hd : 2 ≤ d) (t : ℝ) :
    HasDerivAt (gfun d) (t ^ (d - 2) * (((d : ℝ) - 1) - (d : ℝ) * t)) t := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ (d - 1)) (((d - 1 : ℕ) : ℝ) * t ^ (d - 1 - 1)) t :=
    hasDerivAt_pow (d - 1) t
  have hlin : HasDerivAt (fun x : ℝ => 1 - x) (0 - 1) t :=
    (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)
  have h : HasDerivAt (fun x : ℝ => x ^ (d - 1) * (1 - x))
      (((d - 1 : ℕ) : ℝ) * t ^ (d - 1 - 1) * (1 - t) + t ^ (d - 1) * (0 - 1)) t :=
    hpow.fun_mul hlin
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ d := by omega
    push_cast [Nat.cast_sub h1]; ring
  have hidx : d - 1 - 1 = d - 2 := by omega
  have hmul : t ^ (d - 1) = t ^ (d - 2) * t := by
    rw [← pow_succ]; congr 1; omega
  have hval : ((d - 1 : ℕ) : ℝ) * t ^ (d - 1 - 1) * (1 - t) + t ^ (d - 1) * (0 - 1)
      = t ^ (d - 2) * (((d : ℝ) - 1) - (d : ℝ) * t) := by
    rw [hcast, hidx, hmul]; ring
  rw [hval] at h
  exact h

theorem gfun_strictMonoOn {d : ℕ} (hd : 2 ≤ d) :
    StrictMonoOn (gfun d) (Icc 0 (rStar d)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 (rStar d))
    (fun x _ => (hasDerivAt_gfun hd x).continuousAt.continuousWithinAt) ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_gfun hd x).deriv]
  have hx0 : 0 < x := hx.1
  have hlt : x < rStar d := hx.2
  have hfac : 0 < ((d : ℝ) - 1) - (d : ℝ) * x := by
    rw [rStar] at hlt
    have hx := (lt_div_iff₀ hd0).mp hlt
    linarith [hx]
  positivity

theorem gfun_strictAntiOn {d : ℕ} (hd : 2 ≤ d) :
    StrictAntiOn (gfun d) (Icc (rStar d) 1) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  have hr0 : 0 < rStar d := rStar_pos hd
  refine strictAntiOn_of_deriv_neg (convex_Icc (rStar d) 1)
    (fun x _ => (hasDerivAt_gfun hd x).continuousAt.continuousWithinAt) ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_gfun hd x).deriv]
  have hx0 : 0 < x := lt_trans hr0 hx.1
  have hgt : rStar d < x := hx.1
  have hfac : ((d : ℝ) - 1) - (d : ℝ) * x < 0 := by
    rw [rStar] at hgt
    have hx := (div_lt_iff₀ hd0).mp hgt
    linarith [hx]
  have hpow : 0 < x ^ (d - 2) := pow_pos hx0 _
  exact mul_neg_of_pos_of_neg hpow hfac

/-! ### `R_d = N''/D''` -/

/-- `R_d(t) = N''(t)/D''(t)`, the ratio whose weighted averages are the values of `ψ_d`. -/
noncomputable def Rfun (d : ℕ) (t : ℝ) : ℝ := d2N t / d2D d t

/-- `R_d(t) = -1/(d(d-1)g_d(t))`. -/
theorem Rfun_eq {d : ℕ} (hd : 2 ≤ d) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    Rfun d t = -1 / ((d : ℝ) * ((d : ℝ) - 1) * gfun d t) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  have hd1 : (1 : ℝ) < (d : ℝ) := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hpow : t ^ (d - 1) = t ^ (d - 2) * t := by
    rw [← pow_succ]; congr 1; omega
  have hp2 : (0 : ℝ) < t ^ (d - 2) := pow_pos h0 _
  unfold Rfun d2N d2D gfun
  rw [hpow]
  field_simp

/-- `D''_d(t) > 0` on the interior. -/
theorem d2D_pos {d : ℕ} (hd : 2 ≤ d) {t : ℝ} (h0 : 0 < t) : 0 < d2D d t := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  have hd1 : (1 : ℝ) < (d : ℝ) := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  unfold d2D
  have : (0 : ℝ) < t ^ (d - 2) := pow_pos h0 _
  have hsub : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  positivity

/-- Comparing values of `R_d` is comparing values of `g_d`: both are strictly increasing in
the other, since `R_d = -1/(d(d-1)g_d)` and `g_d > 0`. -/
theorem Rfun_lt_Rfun_iff {d : ℕ} (hd : 2 ≤ d) {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1) : Rfun d s < Rfun d t ↔ gfun d s < gfun d t := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  have hd1 : (1 : ℝ) < (d : ℝ) := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hgs : 0 < gfun d s := gfun_pos hs0 hs1
  have hgt : 0 < gfun d t := gfun_pos ht0 ht1
  have hc : (0 : ℝ) < (d : ℝ) * ((d : ℝ) - 1) := by nlinarith
  rw [Rfun_eq hd hs0 hs1, Rfun_eq hd ht0 ht1]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

theorem Rfun_strictMonoOn {d : ℕ} (hd : 2 ≤ d) :
    StrictMonoOn (Rfun d) (Ioc 0 (rStar d)) := by
  intro s hs t ht hst
  have hr1 : rStar d < 1 := rStar_lt_one hd
  rw [Rfun_lt_Rfun_iff hd hs.1 (lt_of_le_of_lt hs.2 hr1) ht.1 (lt_of_le_of_lt ht.2 hr1)]
  exact gfun_strictMonoOn hd ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩ hst

theorem Rfun_strictAntiOn {d : ℕ} (hd : 2 ≤ d) :
    StrictAntiOn (Rfun d) (Ico (rStar d) 1) := by
  intro s hs t ht hst
  have hr0 : 0 < rStar d := rStar_pos hd
  rw [Rfun_lt_Rfun_iff hd (lt_of_lt_of_le hr0 ht.1) ht.2 (lt_of_lt_of_le hr0 hs.1) hs.2]
  exact gfun_strictAntiOn hd ⟨hs.1, hs.2.le⟩ ⟨ht.1, ht.2.le⟩ hst

end UpperTailOptimizers
