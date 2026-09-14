import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.FamilyQuadratic
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.LstarTaylor

/-!
# The family expansions at quadratic order (Section 5, `paper/sections/singular.tex`)

The proof of `lem:rank-one-parameter-expansions` (its outline, and
`app:rank-one-parameter-expansions`) computes the quadratic Taylor coefficients `U₂`, `G₂`, `L₂`
of the rank-one KKT family,

  `u_h = u_* + \frac{5-3d}{6u_*}h² + O_d(h⁴)`,
  `γ_h = γ_* + \frac{2d^{d+2}}{3(d-1)^d}h² + O_d(h⁴)`,
  `ℓ(p_h) = ℓ_* + \frac{2d³}{3(d-1)}h² + O_d(h⁴)`;

the first and the last, written as `Λ_h = ℓ(p_h) - ℓ_*`, are entries of
`eq:rank-one-parameter-expansions`.  This file proves the three coefficients; the `O_d(h⁴)`
remainders are added in `SingularEndpoint/ConstantGraphonComparison/ParameterRemainders.lean`.  Nothing here needs the implicit function theorem a
second time: the coefficients are read off the **three KKT equations themselves**, by
dividing each by the right power of `h` and passing to the limit.

## The mechanism

Write `Λ_h = ℓ(p_h) - ℓ_*` and `Δ_h = γ_h - γ_*`.  Because `J_p'` depends on `p` only through
`ℓ(p)`, the rank-one KKT function splits exactly (`Fkkt_eq_Lstar_add`):

  `F_{p_h,γ_h}(z) = 𝓛_*(z) + Λ_h - Δ_h z^{d-1}`,

so the three equations `eq:three-value-kkt` become three equations in `𝓛_*` alone.
Into them we feed the Taylor expansion of `𝓛_*` at `r_*`, which by
`eq:endpoint-entropy-derivatives` starts at the cube,

  `𝓛_*(z) = \frac{k₃}{6}(z-r_*)³ + (z-r_*)⁴ S(z)`,   `k₃ = d⁵/(d-1)²`, `S(r_*) = k₄/24`,

(`Lstar_expand`, from `SingularEndpoint/ConstantGraphonComparison/TaylorTail.lean`).  Here and in the files that build on
this one, `k₃ = 𝓛_*'''(r_*)` and `k₄ = 𝓛_*^{(4)}(r_*)` are derivatives; the constants `k_3`,
`k_4` of `app:rank-one-kkt-family` and `app:rank-one-parameter-expansions` are `k₃/6` and
`k₄/24`.  Dividing the three equations by `h²`, `h³`, `h⁴`
respectively gives three linear equations for the three coefficients:

* the **cross** equation, at `h²`: `L₂ = G₂ r_*^{d-1}`;
* the **difference** of the outer equations, at `h³`: `G₂(d-1)r_*^{d-2} = \frac{2k₃r_*}{3}`;
* the **second difference**, at `h⁴`: `2k₃r_*(4u_*U₂+2) + \frac{4k₄r_*²}{3}
  = 4(d-1)·G₂(d-1)r_*^{d-2}`.

The middle node contributes nothing to the first two because `s_h t_h - r_* = O(h²)`, so
`𝓛_*(s_h t_h) = O(h⁶)`; the quartic tail `S` contributes only to the third, because the two
outer nodes enter it with the same sign.  The three then solve in closed form, and the powers
`r_*^{d-1}`, `r_*^{d-2}` are eliminated by `γ_* r_*^d = 1`.

Two polynomial identities carry the algebra with no estimate at all:
`t^{2(d-1)} - s^{2(d-1)} = 2h·∑` and `(t²)^{d-1} + (s²)^{d-1} - 2(st)^{d-1} = (t^{d-1}-s^{d-1})²`.

## Contents

* `rStar_mem_Ioo`, `LstarTail`, `Lstar_expand`, `LstarTail_rStar`, `continuousAt_LstarTail`,
  `tendsto_LstarTail_comp` — the cubic-plus-quartic expansion;
* `Fkkt_eq_Lstar_add` and `kkt_residual_*` — the equations in `𝓛_*` form;
* `family_eq_cross`, `family_eq_diff`, `family_eq_second` — the three limit equations;
* `Gcoeff_eq`, `Lcoeff_eq`, `Ucoeff_eq` — the three quadratic coefficients `G₂`, `L₂`, `U₂`;
* `eventually_window`, `tendsto_pow_punctured` — the two filter conveniences, the second
  shared with `SingularEndpoint/ConstantGraphonComparison/IncrementSum.lean`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology Finset

variable {d : ℕ}

/-! ## The expansion of `𝓛_*` at `r_*` -/

/-- The **quartic tail** `S` of `𝓛_*` at `r_*`: the analytic function with

  `𝓛_*(z) = \frac{𝓛_*'''(r_*)}{6}(z - r_*)³ + (z - r_*)⁴ S(z)`,  `S(r_*) = 𝓛_*^{(4)}(r_*)/24`.

The two coefficients are the contact constants `k₃` and `k₄` used below. -/
noncomputable def LstarTail (d : ℕ) : ℝ → ℝ := taylorTail (Lstar d) (rStar d) 4

theorem rStar_mem_Ioo (hd : 2 ≤ d) : rStar d ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨rStar_pos hd, rStar_lt_one hd⟩

/-- **The cubic-plus-quartic expansion of `𝓛_*`.**  The first three Taylor coefficients of
`𝓛_*` at `r_*` vanish `eq:endpoint-entropy-derivatives`, so the expansion of
`SingularEndpoint/ConstantGraphonComparison/TaylorTail.lean` starts at the cube, with the exact non-degenerate coefficient
`k₃/6 = d⁵/(6(d-1)²)` of `Lstar3_rStar`. -/
theorem Lstar_expand (hd : 2 ≤ d) (z : ℝ) :
    Lstar d z = ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 6) * (z - rStar d) ^ 3
      + (z - rStar d) ^ 4 * LstarTail d z := by
  have hana : AnalyticAt ℝ (Lstar d) (rStar d) :=
    analyticAt_Lstar hd (rStar_pos hd) (rStar_lt_one hd)
  have hvan : ∀ k, k < 3 → iteratedDeriv k (Lstar d) (rStar d) = 0 := by
    intro k hk
    interval_cases k
    · rw [iteratedDeriv_zero]; exact Lstar_rStar hd
    · exact iteratedDeriv_one_Lstar hd
    · exact iteratedDeriv_two_Lstar hd
  have h := taylorTail_expand_of_iteratedDeriv_eq_zero hana hvan z
  rw [iteratedDeriv_three_Lstar hd] at h
  simpa [LstarTail, Nat.factorial] using h

/-- `S(r_*) = k₄/24 = 5d⁶(d-2)/(24(d-1)³)`. -/
theorem LstarTail_rStar (hd : 2 ≤ d) :
    LstarTail d (rStar d) = 5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 24 := by
  have hana : AnalyticAt ℝ (Lstar d) (rStar d) :=
    analyticAt_Lstar hd (rStar_pos hd) (rStar_lt_one hd)
  have h := taylorTail_apply_self hana 4
  rw [iteratedDeriv_four_Lstar hd] at h
  simpa [LstarTail, Nat.factorial] using h

theorem continuousAt_LstarTail (hd : 2 ≤ d) : ContinuousAt (LstarTail d) (rStar d) :=
  (analyticOnNhd_taylorTail (analyticOnNhd_Lstar hd) (rStar_mem_Ioo hd) 4 _
    (rStar_mem_Ioo hd)).continuousAt

/-- The tail evaluated along any family of nodes collapsing to `r_*`. -/
theorem tendsto_LstarTail_comp (hd : 2 ≤ d) {f : ℝ → ℝ}
    (hf : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 (rStar d))) :
    Tendsto (fun h : ℝ => LstarTail d (f h)) (𝓝[≠] (0 : ℝ))
      (𝓝 (5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 24)) := by
  have h := ((continuousAt_LstarTail hd).tendsto).comp hf
  rwa [LstarTail_rStar hd] at h

/-! ## The KKT equations in `𝓛_*` form -/

variable (B : KKTFamily d)

/-- **The exact splitting of the rank-one KKT function.**  `J_p'(z) = ℓ(p) - ℓ(z)` is affine
in `ℓ(p)`, so moving from `(p_*, γ_*)` to `(p_h, γ_h)` shifts `F` by the constant `Λ_h` and
the monomial `-Δ_h z^{d-1}`:

  `F_{p_h,γ_h}(z) = 𝓛_*(z) + Λ_h - Δ_h z^{d-1}`. -/
theorem Fkkt_eq_Lstar_add (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) {z : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1) :
    Fkkt d (B.p h) (B.gam h) z
      = Lstar d z + (ell (B.p h) - ell (pStar d))
        - (B.gam h - gammaStar d) * z ^ (d - 1) := by
  have hp := B.p_mem h hh
  rw [Fkkt, Lstar, Fkkt, Jp'_eq_ell_sub hp.1 hp.2 hz0 hz1,
    Jp'_eq_ell_sub (pStar_pos hd) (pStar_lt_one hd) hz0 hz1]
  ring

private theorem sq_sVal_pos {h : ℝ} (hh : |h| < B.h₀) : 0 < B.sVal h ^ 2 :=
  pow_pos (KKTFamily.sVal_pos hh) 2

private theorem sq_sVal_lt_one {h : ℝ} (hh : |h| < B.h₀) : B.sVal h ^ 2 < 1 := by
  nlinarith [KKTFamily.sVal_pos hh, KKTFamily.sVal_lt_one hh]

private theorem sq_tVal_pos {h : ℝ} (hh : |h| < B.h₀) : 0 < B.tVal h ^ 2 :=
  pow_pos (KKTFamily.tVal_pos hh) 2

private theorem sq_tVal_lt_one {h : ℝ} (hh : |h| < B.h₀) : B.tVal h ^ 2 < 1 := by
  nlinarith [KKTFamily.tVal_pos hh, KKTFamily.tVal_lt_one hh]

private theorem cross_pos {h : ℝ} (hh : |h| < B.h₀) : 0 < B.sVal h * B.tVal h :=
  mul_pos (KKTFamily.sVal_pos hh) (KKTFamily.tVal_pos hh)

private theorem cross_lt_one {h : ℝ} (hh : |h| < B.h₀) : B.sVal h * B.tVal h < 1 := by
  nlinarith [KKTFamily.sVal_pos hh, KKTFamily.sVal_lt_one hh,
    KKTFamily.tVal_pos hh, KKTFamily.tVal_lt_one hh]

/-- The lower KKT equation in `𝓛_*` form. -/
theorem kkt_residual_ss (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) :
    Lstar d (B.sVal h ^ 2) + (ell (B.p h) - ell (pStar d))
      - (B.gam h - gammaStar d) * (B.sVal h ^ 2) ^ (d - 1) = 0 := by
  rw [← Fkkt_eq_Lstar_add B hd hh (sq_sVal_pos B hh) (sq_sVal_lt_one B hh)]
  exact B.kkt_ss h hh

/-- The cross KKT equation in `𝓛_*` form. -/
theorem kkt_residual_st (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) :
    Lstar d (B.sVal h * B.tVal h) + (ell (B.p h) - ell (pStar d))
      - (B.gam h - gammaStar d) * (B.sVal h * B.tVal h) ^ (d - 1) = 0 := by
  rw [← Fkkt_eq_Lstar_add B hd hh (cross_pos B hh) (cross_lt_one B hh)]
  exact B.kkt_st h hh

/-- The upper KKT equation in `𝓛_*` form. -/
theorem kkt_residual_tt (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) :
    Lstar d (B.tVal h ^ 2) + (ell (B.p h) - ell (pStar d))
      - (B.gam h - gammaStar d) * (B.tVal h ^ 2) ^ (d - 1) = 0 := by
  rw [← Fkkt_eq_Lstar_add B hd hh (sq_tVal_pos B hh) (sq_tVal_lt_one B hh)]
  exact B.kkt_tt h hh

/-- The parameter window is an eventual condition along the punctured neighbourhood. -/
theorem eventually_window : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < B.h₀ := by
  have hmem : Set.Ioo (-B.h₀) B.h₀ ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [B.h₀_pos]) B.h₀_pos
  filter_upwards [nhdsWithin_le_nhds hmem] with h hh
  exact abs_lt.mpr ⟨hh.1, hh.2⟩

/-! ## The three limit equations -/

/-- `h^n → 0` along the punctured neighbourhood of `0`, for `n ≠ 0`. -/
theorem tendsto_pow_punctured {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun h : ℝ => h ^ n) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have h : Tendsto (fun h : ℝ => h ^ n) (𝓝[≠] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ n)) :=
    tendsto_self_punctured.pow n
  rwa [zero_pow hn] at h

/-- **The cross equation, at order `h²`.**  The middle node moves only at second order, so
`𝓛_*(s_h t_h) = O(h⁶)` drops out and the equation `F_{p_h,γ_h}(s_h t_h) = 0` divided by `h²`
gives `L₂ = G₂ r_*^{d-1}` in the limit. -/
theorem family_eq_cross (hd : 2 ≤ d) : Lcoeff B = Gcoeff B * rStar d ^ (d - 1) := by
  have hc := tendsto_cross_rate2 B hd
  have hS := tendsto_LstarTail_comp hd (tendsto_cross B hd)
  set C : ℝ := 2 * uStar d * Ucoeff B - 1 with hC
  set K₄ : ℝ := 5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 24 with hK₄
  -- the `𝓛_*` term is negligible
  have hL0 : Tendsto (fun h : ℝ => Lstar d (B.sVal h * B.tVal h) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by
    have hA := ((hc.pow 3).mul (tendsto_pow_punctured (n := 4) (by norm_num))).const_mul
      ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 6)
    have hB := ((hc.pow 4).mul (tendsto_pow_punctured (n := 6) (by norm_num))).mul hS
    have hsum := hA.add hB
    rw [show (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 6 * (C ^ 3 * 0) + C ^ 4 * 0 * K₄ = 0 from
      by ring] at hsum
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ≠ 0 := hh
    rw [Lstar_expand hd]
    field_simp
  -- the whole residual, divided by `h²`
  have hlim := (hL0.add (tendsto_ell_coeff B hd).2).sub
    ((tendsto_gam_coeff B).mul ((tendsto_cross B hd).pow (d - 1)))
  have hzero : Tendsto (fun h : ℝ =>
      Lstar d (B.sVal h * B.tVal h) / h ^ 2 + (ell (B.p h) - ell (pStar d)) / h ^ 2
        - ((B.gam h - gammaStar d) / h ^ 2) * (B.sVal h * B.tVal h) ^ (d - 1))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))
    filter_upwards [self_mem_nhdsWithin, eventually_window B] with h hh hw
    have hne : h ≠ 0 := hh
    have hk := kkt_residual_st B hd hw
    have hsplit : Lstar d (B.sVal h * B.tVal h) / h ^ 2
        + (ell (B.p h) - ell (pStar d)) / h ^ 2
        - ((B.gam h - gammaStar d) / h ^ 2) * (B.sVal h * B.tVal h) ^ (d - 1)
        = (Lstar d (B.sVal h * B.tVal h) + (ell (B.p h) - ell (pStar d))
            - (B.gam h - gammaStar d) * (B.sVal h * B.tVal h) ^ (d - 1)) / h ^ 2 := by
      field_simp
    rw [hsplit, hk, zero_div]
  have := tendsto_nhds_unique hlim hzero
  linarith [this]

/-- **The difference equation, at order `h³`.**  Subtracting the two outer KKT equations
eliminates `Λ_h`, and the exact factorisation `t^{2(d-1)} - s^{2(d-1)} = 2h·∑` divides by `h`
with no remainder.  In the limit `G₂(d-1)r_*^{d-2} = 2k₃r_*/3` with `k₃ = d⁵/(d-1)²`. -/
theorem family_eq_diff (hd : 2 ≤ d) :
    Gcoeff B * ((d : ℝ) - 1) * rStar d ^ (d - 2)
      = 2 * ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2) * rStar d / 3 := by
  have hd1 : (1 : ℕ) ≤ d := by omega
  have hu := uStar_pos hd
  have hs := tendsto_sVal_sq_rate hd B
  have ht := tendsto_tVal_sq_rate hd B
  have hSs := tendsto_LstarTail_comp hd (tendsto_sVal_sq B hd)
  have hSt := tendsto_LstarTail_comp hd (tendsto_tVal_sq B hd)
  set K₄ : ℝ := 5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 24 with hK₄
  set k₃ : ℝ := (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 with hk₃
  -- the `𝓛_*` difference
  have hLdiff : Tendsto
      (fun h : ℝ => (Lstar d (B.tVal h ^ 2) - Lstar d (B.sVal h ^ 2)) / h ^ 3)
      (𝓝[≠] (0 : ℝ)) (𝓝 (k₃ / 6 * (16 * uStar d ^ 3))) := by
    have hA := ((ht.pow 3).sub (hs.pow 3)).const_mul (k₃ / 6)
    have hB := (tendsto_pow_punctured (n := 1) (by norm_num)).mul
      (((ht.pow 4).mul hSt).sub ((hs.pow 4).mul hSs))
    have hsum := hA.add hB
    rw [show k₃ / 6 * ((2 * uStar d) ^ 3 - (-(2 * uStar d)) ^ 3)
        + 0 * ((2 * uStar d) ^ 4 * K₄ - (-(2 * uStar d)) ^ 4 * K₄)
        = k₃ / 6 * (16 * uStar d ^ 3) from by ring] at hsum
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ≠ 0 := hh
    rw [Lstar_expand hd (B.tVal h ^ 2), Lstar_expand hd (B.sVal h ^ 2)]
    field_simp
    ring
  -- the polynomial difference
  have hpoly := tendsto_pow_diff_rate B (2 * (d - 1))
  have hlim := hLdiff.sub ((tendsto_gam_coeff B).mul hpoly)
  have hzero : Tendsto (fun h : ℝ =>
      (Lstar d (B.tVal h ^ 2) - Lstar d (B.sVal h ^ 2)) / h ^ 3
        - ((B.gam h - gammaStar d) / h ^ 2)
          * ((B.tVal h ^ (2 * (d - 1)) - B.sVal h ^ (2 * (d - 1))) / h))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))
    filter_upwards [self_mem_nhdsWithin, eventually_window B] with h hh hw
    have hne : h ≠ 0 := hh
    have hk1 := kkt_residual_tt B hd hw
    have hk2 := kkt_residual_ss B hd hw
    have hpow : ∀ x : ℝ, (x ^ 2) ^ (d - 1) = x ^ (2 * (d - 1)) := fun x => by
      rw [← pow_mul]
    have hcomb : Lstar d (B.tVal h ^ 2) - Lstar d (B.sVal h ^ 2)
        - (B.gam h - gammaStar d)
          * (B.tVal h ^ (2 * (d - 1)) - B.sVal h ^ (2 * (d - 1))) = 0 := by
      rw [← hpow, ← hpow]
      linear_combination hk1 - hk2
    have hsplit : (Lstar d (B.tVal h ^ 2) - Lstar d (B.sVal h ^ 2)) / h ^ 3
        - ((B.gam h - gammaStar d) / h ^ 2)
          * ((B.tVal h ^ (2 * (d - 1)) - B.sVal h ^ (2 * (d - 1))) / h)
        = (Lstar d (B.tVal h ^ 2) - Lstar d (B.sVal h ^ 2)
            - (B.gam h - gammaStar d)
              * (B.tVal h ^ (2 * (d - 1)) - B.sVal h ^ (2 * (d - 1)))) / h ^ 3 := by
      field_simp
    rw [hsplit, hcomb, zero_div]
  have heq := tendsto_nhds_unique hlim hzero
  -- convert the powers of `u_*` into powers of `r_*`
  have hcast : ((2 * (d - 1) : ℕ) : ℝ) = 2 * ((d : ℝ) - 1) := by
    push_cast [Nat.cast_sub hd1]
    ring
  have hexp : uStar d ^ (2 * (d - 1) - 1) = uStar d * rStar d ^ (d - 2) := by
    rw [show 2 * (d - 1) - 1 = 2 * (d - 2) + 1 from by omega, pow_succ, pow_mul, uStar_sq hd]
    ring
  have hcube : uStar d ^ 3 = uStar d * rStar d := by
    rw [← uStar_sq hd]; ring
  rw [hcast, hexp, hcube] at heq
  have hune : uStar d ≠ 0 := ne_of_gt hu
  have hkey : uStar d * (Gcoeff B * ((d : ℝ) - 1) * rStar d ^ (d - 2))
      = uStar d * (2 * k₃ * rStar d / 3) := by linear_combination (-(1 : ℝ) / 4) * heq
  exact mul_left_cancel₀ hune hkey

/-- **The second-difference equation, at order `h⁴`.**  The combination
`F(t_h²) + F(s_h²) - 2F(s_h t_h)` kills `Λ_h` as well, and its polynomial part is the exact
square `(t^{d-1} - s^{d-1})²`.  This is the only equation the quartic tail `S` reaches, and
the only one in which `U₂` appears. -/
theorem family_eq_second (hd : 2 ≤ d) :
    2 * ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2) * rStar d * (4 * uStar d * Ucoeff B + 2)
        + 4 * (5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3) * rStar d ^ 2 / 3
      = 4 * ((d : ℝ) - 1) * (Gcoeff B * ((d : ℝ) - 1) * rStar d ^ (d - 2)) := by
  have hd1 : (1 : ℕ) ≤ d := by omega
  have hs := tendsto_sVal_sq_rate hd B
  have ht := tendsto_tVal_sq_rate hd B
  have hc := tendsto_cross_rate2 B hd
  have houter := tendsto_outer_sum_rate2 B hd
  have hSs := tendsto_LstarTail_comp hd (tendsto_sVal_sq B hd)
  have hSt := tendsto_LstarTail_comp hd (tendsto_tVal_sq B hd)
  have hSc := tendsto_LstarTail_comp hd (tendsto_cross B hd)
  set C : ℝ := 2 * uStar d * Ucoeff B - 1 with hC
  set K₄ : ℝ := 5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 24 with hK₄
  set k₃ : ℝ := (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 with hk₃
  -- the `𝓛_*` second difference
  have hLsec : Tendsto
      (fun h : ℝ =>
        (Lstar d (B.tVal h ^ 2) + Lstar d (B.sVal h ^ 2)
          - 2 * Lstar d (B.sVal h * B.tVal h)) / h ^ 4)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (k₃ / 6 * ((4 * uStar d * Ucoeff B + 2) * (12 * uStar d ^ 2))
        + (16 * uStar d ^ 4 * K₄ + 16 * uStar d ^ 4 * K₄))) := by
    have hcubes := houter.mul (((ht.pow 2).sub (ht.mul hs)).add (hs.pow 2))
    have hmid := (hc.pow 3).mul (tendsto_pow_punctured (n := 2) (by norm_num))
    have hA := (hcubes.sub (hmid.const_mul (2 : ℝ))).const_mul (k₃ / 6)
    have hB := (((ht.pow 4).mul hSt).add ((hs.pow 4).mul hSs)).sub
      ((((hc.pow 4).mul (tendsto_pow_punctured (n := 4) (by norm_num))).mul hSc).const_mul
        (2 : ℝ))
    have hsum := hA.add hB
    rw [show k₃ / 6 * ((4 * uStar d * Ucoeff B + 2)
            * ((2 * uStar d) ^ 2 - 2 * uStar d * -(2 * uStar d) + (-(2 * uStar d)) ^ 2)
          - 2 * (C ^ 3 * 0))
        + ((2 * uStar d) ^ 4 * K₄ + (-(2 * uStar d)) ^ 4 * K₄ - 2 * (C ^ 4 * 0 * K₄))
        = k₃ / 6 * ((4 * uStar d * Ucoeff B + 2) * (12 * uStar d ^ 2))
          + (16 * uStar d ^ 4 * K₄ + 16 * uStar d ^ 4 * K₄) from by ring] at hsum
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ≠ 0 := hh
    rw [Lstar_expand hd (B.tVal h ^ 2), Lstar_expand hd (B.sVal h ^ 2),
      Lstar_expand hd (B.sVal h * B.tVal h)]
    field_simp
    ring
  have hpoly := (tendsto_pow_diff_rate B (d - 1)).pow 2
  have hlim := hLsec.sub ((tendsto_gam_coeff B).mul hpoly)
  have hzero : Tendsto (fun h : ℝ =>
      (Lstar d (B.tVal h ^ 2) + Lstar d (B.sVal h ^ 2)
        - 2 * Lstar d (B.sVal h * B.tVal h)) / h ^ 4
        - ((B.gam h - gammaStar d) / h ^ 2)
          * ((B.tVal h ^ (d - 1) - B.sVal h ^ (d - 1)) / h) ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))
    filter_upwards [self_mem_nhdsWithin, eventually_window B] with h hh hw
    have hne : h ≠ 0 := hh
    have hk1 := kkt_residual_tt B hd hw
    have hk2 := kkt_residual_ss B hd hw
    have hk3 := kkt_residual_st B hd hw
    have hsq : (B.tVal h ^ 2) ^ (d - 1) + (B.sVal h ^ 2) ^ (d - 1)
        - 2 * (B.sVal h * B.tVal h) ^ (d - 1)
        = (B.tVal h ^ (d - 1) - B.sVal h ^ (d - 1)) ^ 2 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 (d - 1), pow_mul, pow_mul]
      ring
    have hcomb : Lstar d (B.tVal h ^ 2) + Lstar d (B.sVal h ^ 2)
        - 2 * Lstar d (B.sVal h * B.tVal h)
        - (B.gam h - gammaStar d) * (B.tVal h ^ (d - 1) - B.sVal h ^ (d - 1)) ^ 2 = 0 := by
      rw [← hsq]
      linear_combination hk1 + hk2 - 2 * hk3
    have hsplit : (Lstar d (B.tVal h ^ 2) + Lstar d (B.sVal h ^ 2)
          - 2 * Lstar d (B.sVal h * B.tVal h)) / h ^ 4
        - ((B.gam h - gammaStar d) / h ^ 2)
          * ((B.tVal h ^ (d - 1) - B.sVal h ^ (d - 1)) / h) ^ 2
        = (Lstar d (B.tVal h ^ 2) + Lstar d (B.sVal h ^ 2)
            - 2 * Lstar d (B.sVal h * B.tVal h)
            - (B.gam h - gammaStar d)
              * (B.tVal h ^ (d - 1) - B.sVal h ^ (d - 1)) ^ 2) / h ^ 4 := by
      field_simp
    rw [hsplit, hcomb, zero_div]
  have heq := tendsto_nhds_unique hlim hzero
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    push_cast [Nat.cast_sub hd1]; ring
  have hexp : (uStar d ^ (d - 1 - 1)) ^ 2 = rStar d ^ (d - 2) := by
    rw [show d - 1 - 1 = d - 2 from by omega, ← pow_mul, mul_comm, pow_mul, uStar_sq hd]
  have hsq2 : uStar d ^ 2 = rStar d := uStar_sq hd
  have hsq4 : uStar d ^ 4 = rStar d ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, uStar_sq hd]
  rw [hcast] at heq
  rw [show (2 * ((d : ℝ) - 1) * uStar d ^ (d - 1 - 1)) ^ 2
      = 4 * ((d : ℝ) - 1) ^ 2 * (uStar d ^ (d - 1 - 1)) ^ 2 from by ring, hexp] at heq
  rw [hsq2, hsq4] at heq
  rw [hk₃, hK₄] at heq
  linarith [heq]

/-! ## The coefficients themselves

The three limit equations are now solved.  The only arithmetic input is that `γ_*` inverts
the powers of `r_*`: `γ_* r_*^d = 1`, hence `γ_* r_*^{d-1} = d/(d-1)` and
`γ_* r_*^{d-2} r_*^2 = 1`.  Multiplying `family_eq_diff` by `γ_* r_*^2` and
`family_eq_cross` by `γ_*` removes the symbolic exponents entirely. -/

private theorem gammaStar_mul_rStar_pow_sub_two (hd : 2 ≤ d) :
    gammaStar d * rStar d ^ (d - 2) * rStar d ^ 2 = 1 := by
  rw [mul_assoc, ← pow_add, show d - 2 + 2 = d from by omega]
  exact gammaStar_mul_rStar_pow hd

/-- **The coefficient `G₂` of `γ_h`** (`app:rank-one-parameter-expansions`):

  `γ_h = γ_* + \frac{2d^{d+2}}{3(d-1)^d}h² + o(h²)`. -/
theorem Gcoeff_eq (hd : 2 ≤ d) :
    Gcoeff B = 2 * (d : ℝ) ^ (d + 2) / (3 * ((d : ℝ) - 1) ^ d) := by
  have hD : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hdd : ((d : ℝ) - 1) ^ d ≠ 0 := pow_ne_zero _ hd1
  have hII := family_eq_diff B hd
  have key : Gcoeff B * ((d : ℝ) - 1)
      = 2 * ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2) * rStar d / 3
        * (gammaStar d * rStar d ^ 2) := by
    calc Gcoeff B * ((d : ℝ) - 1)
        = Gcoeff B * ((d : ℝ) - 1) * (gammaStar d * rStar d ^ (d - 2) * rStar d ^ 2) := by
          rw [gammaStar_mul_rStar_pow_sub_two hd, mul_one]
      _ = Gcoeff B * ((d : ℝ) - 1) * rStar d ^ (d - 2) * (gammaStar d * rStar d ^ 2) := by
          ring
      _ = _ := by rw [hII]
  rw [eq_div_of_mul_eq hd1 key, rStar_eq, gammaStar, div_pow, pow_add]
  field_simp

/-- **The coefficient `L₂` of `ℓ(p_h)`**, which gives the `Λ_h` entry of
`eq:rank-one-parameter-expansions`:

  `Λ_h = ℓ(p_h) - ℓ_* = \frac{2d³}{3(d-1)}h² + o(h²)`. -/
theorem Lcoeff_eq (hd : 2 ≤ d) : Lcoeff B = 2 * (d : ℝ) ^ 3 / (3 * ((d : ℝ) - 1)) := by
  have hD : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hdd : ((d : ℝ) - 1) ^ d ≠ 0 := pow_ne_zero _ hd1
  have hddd : (d : ℝ) ^ d ≠ 0 := pow_ne_zero _ hd0
  have hgpos : gammaStar d ≠ 0 := ne_of_gt (gammaStar_pos hd)
  have key : Lcoeff B * gammaStar d = Gcoeff B * ((d : ℝ) / ((d : ℝ) - 1)) := by
    rw [family_eq_cross B hd, ← gammaStar_mul_rStar_pow_pred hd]; ring
  rw [Gcoeff_eq B hd] at key
  rw [eq_div_of_mul_eq hgpos key, gammaStar, div_pow, pow_add]
  field_simp

/-- **The coefficient `U₂` of `u_h`**, the `u_h` entry of `eq:rank-one-parameter-expansions`:

  `u_h = u_* + \frac{5-3d}{6u_*}h² + o(h²)`.

This is the one coefficient in which the fifth-order contact constant
`k₄ = Γ_d^{(5)}(r_*) = 5d⁶(d-2)/(d-1)³` appears, through the identity
`k₄ r_* = 5(d-2) k₃`. -/
theorem Ucoeff_eq (hd : 2 ≤ d) : Ucoeff B = (5 - 3 * (d : ℝ)) / (6 * uStar d) := by
  have hD : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hu : (0 : ℝ) < uStar d := uStar_pos hd
  have hrpos : (0 : ℝ) < rStar d := rStar_pos hd
  have hII := family_eq_diff B hd
  have hIII := family_eq_second B hd
  rw [hII] at hIII
  -- `k₄ r_* = 5(d-2) k₃`, the only relation between the two contact constants used
  have hkr : 5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 * rStar d
      = 5 * ((d : ℝ) - 2) * ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2) := by
    rw [rStar_eq]; field_simp
  have hne : (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 * rStar d ≠ 0 := by positivity
  have hprod : ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 * rStar d)
      * (24 * (uStar d * Ucoeff B) + 12 * (d : ℝ) - 20) = 0 := by
    linear_combination 3 * hIII - 4 * rStar d * hkr
  have h24 : 24 * (uStar d * Ucoeff B) + 12 * (d : ℝ) - 20 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hne
  have h6 : (6 : ℝ) * uStar d ≠ 0 := by positivity
  rw [eq_div_iff h6]
  linarith [h24]

end SingularEndpoint

end UpperTailOptimizers
