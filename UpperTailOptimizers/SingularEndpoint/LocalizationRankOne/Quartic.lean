import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.Gap
import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.PowBounds
import UpperTailOptimizers.LZBoundary.Existence

/-!
# The quartic localization bounds (Section 5, `paper/sections/singular.tex`)

This file proves the two quantitative estimates of `sec:localization-rank-one` that turn the
qualitative statement `eq:endpoint-gap-positivity` (`Γ_d ≥ 0`, with equality only at `r_*`)
into a usable localization tool:

```
Γ_d(z) ≥ c_d |z - r_*|^4          (eq:endpoint-gap-quartic-bound)
R_d(z)^2 ≤ C_d Γ_d(z)             (the unnumbered `R_d² ≤ C_dΓ_d`)
```

both for `0 ≤ u ≤ 1`.  The first is the quantitative form of the statement that `Γ_d` has a
zero of *exact* order four at `r_*`: the contact identities
`eq:endpoint-entropy-derivatives` kill `Γ_d, Γ_d', Γ_d'', Γ_d'''` at `r_*`, while
`Lstar3_rStar` gives `Γ_d^{(4)}(r_*) = d^5/(d-1)^2 > 0`.  Near `r_*` the bound therefore
comes from a fourth-order Taylor argument, and away from `r_*` from compactness.  The second
estimate then follows from the first, because the convexity defect `R_d` vanishes to order
two at `r_*` (`pow_taylor_abs_le` supplies the explicit constant).

## Contents

* `quartic_lower_of_deriv4_ge` — the generic fourth-order analogue of
  `quadratic_lower_of_deriv2_ge`: a function whose first four Taylor coefficients at `c`
  vanish and whose fourth derivative is `≥ m` satisfies `f x ≥ (m/24)(x-c)^4`;
* `exists_gam_quartic_lower` — `eq:endpoint-gap-quartic-bound`;
* `exists_rd_sq_le_gam` — `R_d² ≤ C_dΓ_d`.
-/

namespace UpperTailOptimizers

/-! ## A generic quartic lower bound -/

/-- **Fourth-order Taylor lower bound.**  If `f` is four times differentiable on `[a,b]`,
its fourth derivative is bounded below by `m`, and `f` together with its first three
derivatives vanishes at an interior point `c`, then `f x ≥ (m/24)(x-c)^4` on `[a,b]`.

This is the fourth-order analogue of `quadratic_lower_of_deriv2_ge`, and is applied to the
singular endpoint supporting gap `Γ_d` of `sec:localization-rank-one`, whose first four Taylor
coefficients at `r_*` vanish by `eq:endpoint-entropy-derivatives`. -/
theorem quartic_lower_of_deriv4_ge {f f1 f2 f3 f4 : ℝ → ℝ} {c m a b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x ∈ Set.Icc a b, HasDerivAt f1 (f2 x) x)
    (hf2 : ∀ x ∈ Set.Icc a b, HasDerivAt f2 (f3 x) x)
    (hf3 : ∀ x ∈ Set.Icc a b, HasDerivAt f3 (f4 x) x)
    (hge : ∀ x ∈ Set.Icc a b, m ≤ f4 x)
    (hfc : f c = 0) (h1c : f1 c = 0) (h2c : f2 c = 0) (h3c : f3 c = 0) :
    ∀ x ∈ Set.Icc a b, m / 24 * (x - c) ^ 4 ≤ f x := by
  have hp4 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (y - c) ^ 4) (4 * (x - c) ^ 3) x := by
    intro x
    simpa using ((hasDerivAt_id x).sub_const c).fun_pow 4
  have hp3 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (y - c) ^ 3) (3 * (x - c) ^ 2) x := by
    intro x
    simpa using ((hasDerivAt_id x).sub_const c).fun_pow 3
  -- the second derivative is already controlled by the quadratic bound
  have hquad : ∀ x ∈ Set.Icc a b, m / 2 * (x - c) ^ 2 ≤ f2 x :=
    quadratic_lower_of_deriv2_ge hac hcb hf2 hf3 hge h2c h3c
  -- apply the quadratic bound a second time, to `g = f - (m/24)(x-c)^4`, with `m := 0`
  have key : ∀ x ∈ Set.Icc a b, (0 : ℝ) / 2 * (x - c) ^ 2 ≤ f x - m / 24 * (x - c) ^ 4 := by
    refine quadratic_lower_of_deriv2_ge (f := fun y => f y - m / 24 * (y - c) ^ 4)
      (f' := fun y => f1 y - m / 6 * (y - c) ^ 3)
      (f'' := fun y => f2 y - m / 2 * (y - c) ^ 2) hac hcb ?_ ?_ ?_ ?_ ?_
    · intro y hy
      have h2 : HasDerivAt (fun z : ℝ => m / 24 * (z - c) ^ 4) (m / 6 * (y - c) ^ 3) y := by
        have h := (hp4 y).const_mul (m / 24)
        convert h using 1
        all_goals try rfl
        ring
      exact (hf y hy).sub h2
    · intro y hy
      have h2 : HasDerivAt (fun z : ℝ => m / 6 * (z - c) ^ 3) (m / 2 * (y - c) ^ 2) y := by
        have h := (hp3 y).const_mul (m / 6)
        convert h using 1
        all_goals try rfl
        ring
      exact (hf1 y hy).sub h2
    · intro y hy
      have h := hquad y hy
      linarith
    · show f c - m / 24 * (c - c) ^ 4 = 0
      rw [hfc]; ring
    · show f1 c - m / 6 * (c - c) ^ 3 = 0
      rw [h1c]; ring
  intro x hx
  have h := key x hx
  simp only [zero_div, zero_mul] at h
  linarith

namespace SingularEndpoint

open Real

variable {d : ℕ}

/-! ## Preliminaries -/

/-- `𝓛_*'''` is continuous on `(0,1)`: it is `J_p^{(4)}(z) = 2/z^3 + 2/(1-z)^3` minus a
constant multiple of a power. -/
private theorem continuousAt_Lstar3 (d : ℕ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    ContinuousAt (Lstar3 d) z := by
  have hzne : z ≠ 0 := ne_of_gt hz0
  have h1ne : (1 : ℝ) - z ≠ 0 := ne_of_gt (by linarith)
  have hJ : ContinuousAt (fun y : ℝ => 2 / y ^ 3 + 2 / (1 - y) ^ 3) z :=
    (continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero 3 hzne)).add
      (continuousAt_const.div ((continuousAt_const.sub continuousAt_id).pow 3)
        (pow_ne_zero 3 h1ne))
  have hpow : ContinuousAt (fun y : ℝ =>
      gammaStar d * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d - 3 : ℕ) : ℝ) * y ^ (d - 4)) z :=
    continuousAt_const.mul (continuousAt_id.pow _)
  exact hJ.sub hpow

/-- A window `[r_* - δ, r_* + δ] ⊆ (0,1)` on which `𝓛_*''' = Γ_d^{(4)}` stays above half of
its value `d^5/(d-1)^2` at `r_*` (`Lstar3_rStar`). -/
private theorem exists_lstar3_window (hd : 2 ≤ d) :
    ∃ δ : ℝ, 0 < δ ∧ 0 < rStar d - δ ∧ rStar d + δ < 1 ∧
      ∀ x ∈ Set.Icc (rStar d - δ) (rStar d + δ),
        (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 2 ≤ Lstar3 d x := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hr0 := rStar_pos hd
  have hr1 := rStar_lt_one hd
  have hApos : 0 < (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 :=
    div_pos (pow_pos (by linarith) 5) (pow_pos (by linarith) 2)
  have hcont : ContinuousAt (Lstar3 d) (rStar d) := continuousAt_Lstar3 d hr0 hr1
  have hgt : (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 2 < Lstar3 d (rStar d) := by
    rw [Lstar3_rStar hd]; linarith
  have hev : ∀ᶠ z in nhds (rStar d),
      0 < z ∧ z < 1 ∧ (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 2 ≤ Lstar3 d z := by
    have hA := hcont.eventually (eventually_ge_nhds hgt)
    have hI : ∀ᶠ z in nhds (rStar d), z ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhds hr0 hr1
    filter_upwards [hA, hI] with z hz1 hz2 using ⟨hz2.1, hz2.2, hz1⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hkey : ∀ x ∈ Set.Icc (rStar d - ε / 2) (rStar d + ε / 2),
      0 < x ∧ x < 1 ∧ (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 2 ≤ Lstar3 d x := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    refine hball ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  exact ⟨ε / 2, by linarith, (hkey _ ⟨le_rfl, by linarith⟩).1,
    (hkey _ ⟨by linarith, le_rfl⟩).2.1, fun x hx => (hkey x hx).2.2⟩

/-! ## `eq:endpoint-gap-quartic-bound` -/

/-- **`eq:endpoint-gap-quartic-bound`.**  There is `c_d > 0` with
`Γ_d(z) ≥ c_d |z - r_*|^4` for `0 ≤ z ≤ 1`.

Near `r_*` this is the fourth-order Taylor bound `quartic_lower_of_deriv4_ge` applied to
`Γ_d`, whose first four Taylor coefficients vanish (`Gam_rStar`, `Lstar_rStar`,
`Lstar1_rStar`, `Lstar2_rStar`) and whose fourth derivative is close to
`Γ_d^{(4)}(r_*) = d^5/(d-1)^2 > 0`.  Away from `r_*` the set is compact and `Γ_d` is
continuous and strictly positive there (`Gam_pos_of_ne`), so it has a positive minimum. -/
theorem exists_gam_quartic_lower (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ u ∈ Set.Icc (0 : ℝ) 1, c * |u - rStar d| ^ 4 ≤ Gam d u := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hr0 := rStar_pos hd
  have hr1 := rStar_lt_one hd
  have hApos : 0 < (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 :=
    div_pos (pow_pos (by linarith) 5) (pow_pos (by linarith) 2)
  obtain ⟨δ, hδ, hlo, hhi, hL3⟩ := exists_lstar3_window hd
  have hmem : ∀ x ∈ Set.Icc (rStar d - δ) (rStar d + δ), 0 < x ∧ x < 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- the local quartic bound on the window
  have hlocal : ∀ x ∈ Set.Icc (rStar d - δ) (rStar d + δ),
      (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 48 * (x - rStar d) ^ 4 ≤ Gam d x := by
    have hq := quartic_lower_of_deriv4_ge (f := Gam d) (f1 := Lstar d) (f2 := Lstar1 d)
      (f3 := Lstar2 d) (f4 := Lstar3 d) (c := rStar d)
      (m := (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 2)
      (by linarith) (by linarith)
      (fun x hx => hasDerivAt_Gam hd (hmem x hx).1 (hmem x hx).2)
      (fun x hx => hasDerivAt_Lstar hd (hmem x hx).1 (hmem x hx).2)
      (fun x hx => hasDerivAt_Lstar1 hd (hmem x hx).1 (hmem x hx).2)
      (fun x hx => hasDerivAt_Lstar2 hd (hmem x hx).1 (hmem x hx).2)
      hL3 (Gam_rStar hd) (Lstar_rStar hd) (Lstar1_rStar hd) (Lstar2_rStar hd)
    intro x hx
    have h := hq x hx
    calc (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 48 * (x - rStar d) ^ 4
        = (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 2 / 24 * (x - rStar d) ^ 4 := by ring
      _ ≤ Gam d x := h
  -- on `[0,1]` the distance to `r_*` is at most `1`
  have hle1 : ∀ u ∈ Set.Icc (0 : ℝ) 1, (u - rStar d) ^ 4 ≤ 1 := by
    intro u hu
    have habs : |u - rStar d| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    calc (u - rStar d) ^ 4 = |u - rStar d| ^ 4 := (Even.pow_abs (n := 4) (by norm_num) _).symm
      _ ≤ 1 ^ 4 := pow_le_pow_left₀ (abs_nonneg _) habs 4
      _ = 1 := one_pow 4
  by_cases hKne : (Set.Icc (0 : ℝ) 1 \ Set.Ioo (rStar d - δ) (rStar d + δ)).Nonempty
  · obtain ⟨u0, hu0, hmin⟩ := (isCompact_Icc.diff isOpen_Ioo).exists_isMinOn hKne
      ((continuousOn_Gam hd).mono Set.sdiff_subset)
    have hu0pos : 0 < Gam d u0 := by
      refine Gam_pos_of_ne hd hu0.1.1 hu0.1.2 ?_
      intro h
      exact hu0.2 (by rw [h]; exact ⟨by linarith, by linarith⟩)
    refine ⟨min ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 48) (Gam d u0),
      lt_min (by linarith) hu0pos, ?_⟩
    intro u hu
    rw [Even.pow_abs (n := 4) (by norm_num)]
    by_cases hin : u ∈ Set.Ioo (rStar d - δ) (rStar d + δ)
    · refine le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)) ?_
      exact hlocal u ⟨hin.1.le, hin.2.le⟩
    · have hmle : Gam d u0 ≤ Gam d u := hmin ⟨hu, hin⟩
      have hmpos : 0 ≤ min ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 48) (Gam d u0) :=
        le_of_lt (lt_min (by linarith) hu0pos)
      have hb := mul_le_mul_of_nonneg_left (hle1 u hu) hmpos
      have hr := min_le_right ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 48) (Gam d u0)
      linarith
  · refine ⟨(d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 48, by linarith, ?_⟩
    intro u hu
    rw [Even.pow_abs (n := 4) (by norm_num)]
    have hin : u ∈ Set.Ioo (rStar d - δ) (rStar d + δ) := by
      by_contra hcon
      exact hKne ⟨u, hu, hcon⟩
    exact hlocal u ⟨hin.1.le, hin.2.le⟩

/-! ## `R_d² ≤ C_dΓ_d` -/

/-- **`R_d² ≤ C_dΓ_d`.**  There is `C_d < ∞` with `R_d(u)^2 ≤ C_d Γ_d(u)` for
`0 ≤ u ≤ 1`.

The convexity defect `R_d` is the first-order Taylor remainder of `u ↦ u^d` at `r_*`
divided by `d r_*^{d-1}`, so `pow_taylor_abs_le` gives `|R_d(u)| ≤ L (u - r_*)^2` with the
explicit constant `L = d^2/(d r_*^{d-1})`.  Squaring and feeding in
`eq:endpoint-gap-quartic-bound` produces `C_d = L^2/c_d`. -/
theorem exists_rd_sq_le_gam (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Set.Icc (0 : ℝ) 1, Rd d u ^ 2 ≤ C * Gam d u := by
  obtain ⟨c, hc, hcbound⟩ := exists_gam_quartic_lower hd
  have hr0 := rStar_pos hd
  have hr1 := rStar_lt_one hd
  have hD : 0 < (d : ℝ) * rStar d ^ (d - 1) := mul_pos (dpos hd) (pow_pos hr0 _)
  have hLpos : 0 < (d : ℝ) ^ 2 / ((d : ℝ) * rStar d ^ (d - 1)) :=
    div_pos (pow_pos (dpos hd) 2) hD
  refine ⟨((d : ℝ) ^ 2 / ((d : ℝ) * rStar d ^ (d - 1))) ^ 2 / c,
    div_pos (pow_pos hLpos 2) hc, ?_⟩
  intro u hu
  have hrmem : rStar d ∈ Set.Icc (0 : ℝ) 1 := ⟨hr0.le, hr1.le⟩
  have htay := pow_taylor_abs_le hu hrmem d
  have hLD : (d : ℝ) ^ 2 / ((d : ℝ) * rStar d ^ (d - 1)) * ((d : ℝ) * rStar d ^ (d - 1))
      = (d : ℝ) ^ 2 := by
    field_simp
  have hRabs : |Rd d u| ≤ (d : ℝ) ^ 2 / ((d : ℝ) * rStar d ^ (d - 1)) * (u - rStar d) ^ 2 := by
    rw [Rd, abs_div, abs_of_pos hD, div_le_iff₀ hD]
    calc |u ^ d - rStar d ^ d - (d : ℝ) * rStar d ^ (d - 1) * (u - rStar d)|
        ≤ (d : ℝ) ^ 2 * (u - rStar d) ^ 2 := htay
      _ = (d : ℝ) ^ 2 / ((d : ℝ) * rStar d ^ (d - 1)) * (u - rStar d) ^ 2
            * ((d : ℝ) * rStar d ^ (d - 1)) := by
          have hswap : (d : ℝ) ^ 2 / ((d : ℝ) * rStar d ^ (d - 1)) * (u - rStar d) ^ 2
                * ((d : ℝ) * rStar d ^ (d - 1))
              = (d : ℝ) ^ 2 / ((d : ℝ) * rStar d ^ (d - 1)) * ((d : ℝ) * rStar d ^ (d - 1))
                * (u - rStar d) ^ 2 := by ring
          rw [hswap, hLD]
  have hsq : Rd d u ^ 2
      ≤ ((d : ℝ) ^ 2 / ((d : ℝ) * rStar d ^ (d - 1))) ^ 2 * (u - rStar d) ^ 4 := by
    calc Rd d u ^ 2 = |Rd d u| ^ 2 := (sq_abs _).symm
      _ ≤ ((d : ℝ) ^ 2 / ((d : ℝ) * rStar d ^ (d - 1)) * (u - rStar d) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hRabs 2
      _ = ((d : ℝ) ^ 2 / ((d : ℝ) * rStar d ^ (d - 1))) ^ 2 * (u - rStar d) ^ 4 := by ring
  have hg := hcbound u hu
  rw [Even.pow_abs (n := 4) (by norm_num)] at hg
  have h4 : (u - rStar d) ^ 4 ≤ Gam d u / c := by
    rw [le_div_iff₀ hc]; linarith
  calc Rd d u ^ 2
      ≤ ((d : ℝ) ^ 2 / ((d : ℝ) * rStar d ^ (d - 1))) ^ 2 * (u - rStar d) ^ 4 := hsq
    _ ≤ ((d : ℝ) ^ 2 / ((d : ℝ) * rStar d ^ (d - 1))) ^ 2 * (Gam d u / c) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = ((d : ℝ) ^ 2 / ((d : ℝ) * rStar d ^ (d - 1))) ^ 2 / c * Gam d u := by ring

end SingularEndpoint

end UpperTailOptimizers
