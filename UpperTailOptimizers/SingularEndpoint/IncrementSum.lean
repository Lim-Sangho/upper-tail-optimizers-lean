import UpperTailOptimizers.SingularEndpoint.GamTaylor

/-!
# The sum of increments at the contacts at order `h⁴` (Section 7, `paper/singular_endpoint.tex`)

`SingularEndpoint/Order4.lean` and `SingularEndpoint/Order4Right.lean` prove the `h⁴` order of the two
increments at the contacts

  `A_h = 𝓜_h(s_h²) - 𝓜_h(s_h t_h)`,   `B_h = 𝓜_h(t_h²) - 𝓜_h(s_h t_h)`,

separately, by a Lagrange-remainder sandwich over the shrinking node interval.  Their **sum**
`A_h + B_h`, which is the denominator of the block-weight formula
`eq:block-proportion-formula`, is much easier, and this file computes it by pure algebra:
both polynomial combinations that occur are exact squares,

  `t² + s² - 2st = (t-s)² = 4h²`,   `t^{2d} + s^{2d} - 2(st)^d = (t^d - s^d)²`,

so nothing has to be estimated.  The result `(A_h + B_h)/h⁴ → -4d³/3` agrees with the two
separate `-2d³/3`, and is what `SingularEndpoint/Order5.lean` divides the `h⁵` numerator by.

The tool is the **displacement identity** `Mfun_sub_eq`.  `J_p` depends on `p` only through
the affine term `ℓ(p)·z` `eq:entropy-parameter-shift`, and `𝓜_{p,γ}(z) = J_p(z) - (γ/d)z^d`, so

  `𝓜_h(z) - 𝓜_h(z') = (Γ_d(z) - Γ_d(z')) + Λ_h(z - z') - \frac{Δ_h}{d}(z^d - z'^d)`,

with `Λ_h = ℓ_h - ℓ_*` and `Δ_h = γ_h - γ_*`.  All the `h`-dependence outside `Γ_d` is now in
two scalars whose `h²` rates `SingularEndpoint/Expansions.lean` has pinned.

## Contents

* `Mfun_sub_eq` — the displacement identity for increments of `𝓜`;
* `sq_sVal_mem'`, `sq_tVal_mem'`, `cross_mem'` — the three edge values in the *open* interval
  `(0,1)`, as the entropy displacement needs them;
* `tendsto_outer_gap_rate` — `(t_h² - s_h²)/h = 4u_h → 4u_*`, exact;
* `tendsto_increment_sum` — `(A_h + B_h)/h⁴ → -4d³/3`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology Finset

variable {d : ℕ}

/-! ## The displacement identity for increments of `𝓜` -/

/-- **Increments of `𝓜_{p,γ}` in terms of `Γ_d`.**  Combining `eq:entropy-parameter-shift`
(`Jp_eq_Jp_pStar_add`) with `eq:endpoint-supporting-gap` (`Jp_pStar_eq_gam`),

  `𝓜_{p,γ}(z) - 𝓜_{p,γ}(z') = (Γ_d(z) - Γ_d(z')) + (ℓ(p)-ℓ_*)(z - z')
      - \frac{γ - γ_*}{d}(z^d - z'^d)`.

The `z`-independent constants — `J_{p_*}(r_*)`, `β_d r_*^d` and the `p`-dependent additive
constant of `eq:entropy-parameter-shift` — cancel in the increment. -/
theorem Mfun_sub_eq (hd : 2 ≤ d) {p γ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {z z' : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hz0' : 0 ≤ z') (hz1' : z' ≤ 1) :
    Mfun d p γ z - Mfun d p γ z'
      = (Gam d z - Gam d z') + (ell p - ell (pStar d)) * (z - z')
        - ((γ - gammaStar d) / (d : ℝ)) * (z ^ d - z' ^ d) := by
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  have hb : betaD d = gammaStar d / (d : ℝ) := rfl
  rw [Mfun, Mfun, Jp_eq_Jp_pStar_add hd hp0 hp1 hz0 hz1,
    Jp_eq_Jp_pStar_add hd hp0 hp1 hz0' hz1', Jp_pStar_eq_gam d z, Jp_pStar_eq_gam d z', hb]
  field_simp
  ring

variable (B : KKTFamily d)

/-- The lower edge value lies in `[0,1]`, in the two-sided form `Mfun_sub_eq` consumes. -/
theorem sq_sVal_mem' {h : ℝ} (hh : |h| < B.h₀) :
    0 ≤ B.sVal h ^ 2 ∧ B.sVal h ^ 2 ≤ 1 :=
  ⟨(KKTFamily.sq_sVal_mem hh).1, (KKTFamily.sq_sVal_mem hh).2⟩

/-- The upper edge value lies in `[0,1]`. -/
theorem sq_tVal_mem' {h : ℝ} (hh : |h| < B.h₀) :
    0 ≤ B.tVal h ^ 2 ∧ B.tVal h ^ 2 ≤ 1 :=
  ⟨(KKTFamily.sq_tVal_mem hh).1, (KKTFamily.sq_tVal_mem hh).2⟩

/-- The cross edge value lies in `[0,1]`. -/
theorem cross_mem' {h : ℝ} (hh : |h| < B.h₀) :
    0 ≤ B.sVal h * B.tVal h ∧ B.sVal h * B.tVal h ≤ 1 :=
  ⟨(KKTFamily.cross_mem hh).1, (KKTFamily.cross_mem hh).2⟩

/-- `(t_h² - s_h²)/h = 4u_h → 4u_*`; the node gap is exactly `4u_h h`. -/
theorem tendsto_outer_gap_rate :
    Tendsto (fun h : ℝ => (B.tVal h ^ 2 - B.sVal h ^ 2) / h) (𝓝[≠] (0 : ℝ))
      (𝓝 (4 * uStar d)) := by
  have h := (tendsto_u_punctured B).const_mul (4 : ℝ)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := hh
  rw [KKTFamily.sVal, KKTFamily.tVal]
  field_simp
  ring

/-! ## The sum `A_h + B_h` at order `h⁴` -/

/-- **`(A_h + B_h)/h⁴ → -4d³/3`.**

Both polynomial combinations are exact squares, `t² + s² - 2st = (t-s)² = 4h²` and
`t^{2d} + s^{2d} - 2(st)^d = (t^d - s^d)²`, so the whole computation reduces to the `Γ_d`
average `(Γ_d(t²) + Γ_d(s²) - 2Γ_d(st))/h⁴ → \frac{4k₃u_*⁴}{3}` together with the two
already-known rates `Λ_h/h² → ℓ₂` and `Δ_h/h² → γ₂`.  The closed form uses
`family_eq_cross` (`ℓ₂ = γ₂ r_*^{d-1}`) and `Lcoeff_eq`. -/
theorem tendsto_increment_sum (hd : 2 ≤ d) :
    Tendsto (fun h : ℝ => (Mfun d (B.p h) (B.gam h) (B.sVal h ^ 2)
        + Mfun d (B.p h) (B.gam h) (B.tVal h ^ 2)
        - 2 * Mfun d (B.p h) (B.gam h) (B.sVal h * B.tVal h)) / h ^ 4)
      (𝓝[≠] (0 : ℝ)) (𝓝 (-(4 * (d : ℝ) ^ 3 / 3))) := by
  have hD : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  set k₃ : ℝ := (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 with hk₃
  set T₅ : ℝ := 5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 120 with hT₅
  have hs := tendsto_sVal_sq_rate hd B
  have ht := tendsto_tVal_sq_rate hd B
  have hc := tendsto_sVal_mul_tVal_rate hd B
  have hTs := tendsto_GamTail_comp hd (tendsto_sVal_sq B hd)
  have hTt := tendsto_GamTail_comp hd (tendsto_tVal_sq B hd)
  have hTc := tendsto_GamTail_comp hd (tendsto_cross B hd)
  -- the `Γ_d` average
  have hGam : Tendsto (fun h : ℝ => (Gam d (B.tVal h ^ 2) + Gam d (B.sVal h ^ 2)
      - 2 * Gam d (B.sVal h * B.tVal h)) / h ^ 4) (𝓝[≠] (0 : ℝ))
      (𝓝 (k₃ / 24 * (32 * uStar d ^ 4))) := by
    have hA := (((ht.pow 4).add (hs.pow 4)).sub ((hc.pow 4).const_mul (2 : ℝ))).const_mul
      (k₃ / 24)
    have hB := (tendsto_pow_punctured (n := 1) (by norm_num)).mul
      ((((ht.pow 5).mul hTt).add ((hs.pow 5).mul hTs)).sub
        (((hc.pow 5).mul hTc).const_mul (2 : ℝ)))
    have hsum := hA.add hB
    rw [show k₃ / 24 * ((2 * uStar d) ^ 4 + (-(2 * uStar d)) ^ 4 - 2 * (0 : ℝ) ^ 4)
        + 0 * (((2 * uStar d) ^ 5 * T₅ + (-(2 * uStar d)) ^ 5 * T₅) - 2 * ((0 : ℝ) ^ 5 * T₅))
        = k₃ / 24 * (32 * uStar d ^ 4) from by ring] at hsum
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ≠ 0 := hh
    rw [Gam_expand hd (B.tVal h ^ 2), Gam_expand hd (B.sVal h ^ 2),
      Gam_expand hd (B.sVal h * B.tVal h), hk₃]
    field_simp
    ring
  -- the polynomial part
  have hpoly := (tendsto_pow_diff_rate B d).pow 2
  have hlim := (hGam.add (((tendsto_ell_coeff B hd).2).const_mul (4 : ℝ))).sub
    ((tendsto_gam_coeff B).mul (hpoly.div_const (d : ℝ)))
  have hzero : Tendsto (fun h : ℝ =>
      (Gam d (B.tVal h ^ 2) + Gam d (B.sVal h ^ 2)
        - 2 * Gam d (B.sVal h * B.tVal h)) / h ^ 4
      + 4 * ((ell (B.p h) - ell (pStar d)) / h ^ 2)
      - ((B.gam h - gammaStar d) / h ^ 2)
        * (((B.tVal h ^ d - B.sVal h ^ d) / h) ^ 2 / (d : ℝ)))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (k₃ / 24 * (32 * uStar d ^ 4) + 4 * Lcoeff B
        - Gcoeff B * ((2 * (d : ℝ) * uStar d ^ (d - 1)) ^ 2 / (d : ℝ)))) := hlim
  have heq : Tendsto (fun h : ℝ => (Mfun d (B.p h) (B.gam h) (B.sVal h ^ 2)
      + Mfun d (B.p h) (B.gam h) (B.tVal h ^ 2)
      - 2 * Mfun d (B.p h) (B.gam h) (B.sVal h * B.tVal h)) / h ^ 4)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (k₃ / 24 * (32 * uStar d ^ 4) + 4 * Lcoeff B
        - Gcoeff B * ((2 * (d : ℝ) * uStar d ^ (d - 1)) ^ 2 / (d : ℝ)))) := by
    refine hzero.congr' ?_
    filter_upwards [self_mem_nhdsWithin, eventually_window B] with h hh hw
    have hne : h ≠ 0 := hh
    have hp := B.p_mem h hw
    have m1 := Mfun_sub_eq (γ := B.gam h) hd hp.1 hp.2 (sq_sVal_mem' B hw).1
      (sq_sVal_mem' B hw).2 (cross_mem' B hw).1 (cross_mem' B hw).2
    have m2 := Mfun_sub_eq (γ := B.gam h) hd hp.1 hp.2 (sq_tVal_mem' B hw).1
      (sq_tVal_mem' B hw).2 (cross_mem' B hw).1 (cross_mem' B hw).2
    have hid1 : B.tVal h ^ 2 + B.sVal h ^ 2 - 2 * (B.sVal h * B.tVal h) = 4 * h ^ 2 := by
      rw [KKTFamily.sVal, KKTFamily.tVal]; ring
    have hid2 : (B.tVal h ^ 2) ^ d + (B.sVal h ^ 2) ^ d - 2 * (B.sVal h * B.tVal h) ^ d
        = (B.tVal h ^ d - B.sVal h ^ d) ^ 2 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 d, pow_mul, pow_mul]
      ring
    have hcomb : Mfun d (B.p h) (B.gam h) (B.sVal h ^ 2)
        + Mfun d (B.p h) (B.gam h) (B.tVal h ^ 2)
        - 2 * Mfun d (B.p h) (B.gam h) (B.sVal h * B.tVal h)
        = (Gam d (B.tVal h ^ 2) + Gam d (B.sVal h ^ 2)
            - 2 * Gam d (B.sVal h * B.tVal h))
          + (ell (B.p h) - ell (pStar d)) * (4 * h ^ 2)
          - ((B.gam h - gammaStar d) / (d : ℝ)) * (B.tVal h ^ d - B.sVal h ^ d) ^ 2 := by
      rw [← hid1, ← hid2]
      linear_combination m1 + m2
    rw [hcomb]
    field_simp
  -- the closed form of the limit
  have hpow : (uStar d ^ (d - 1)) ^ 2 = rStar d ^ (d - 1) := by
    rw [← pow_mul, mul_comm, pow_mul, uStar_sq hd]
  have hexpand : (2 * (d : ℝ) * uStar d ^ (d - 1)) ^ 2 = 4 * (d : ℝ) ^ 2 * rStar d ^ (d - 1) := by
    rw [mul_pow, mul_pow, hpow]; ring
  have hsq4 : uStar d ^ 4 = rStar d ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, uStar_sq hd]
  have hval : k₃ / 24 * (32 * uStar d ^ 4) + 4 * Lcoeff B
      - Gcoeff B * ((2 * (d : ℝ) * uStar d ^ (d - 1)) ^ 2 / (d : ℝ))
      = -(4 * (d : ℝ) ^ 3 / 3) := by
    rw [hexpand, hsq4, hk₃]
    have hstep : Gcoeff B * (4 * (d : ℝ) ^ 2 * rStar d ^ (d - 1) / (d : ℝ))
        = 4 * (d : ℝ) * Lcoeff B := by
      rw [family_eq_cross B hd]; field_simp
    rw [hstep, Lcoeff_eq B hd, rStar_eq]
    field_simp
    ring
  rwa [hval] at heq


end SingularEndpoint

end UpperTailOptimizers
