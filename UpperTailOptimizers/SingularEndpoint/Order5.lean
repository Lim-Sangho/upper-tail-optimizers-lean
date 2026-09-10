import UpperTailOptimizers.SingularEndpoint.IncrementSum
import UpperTailOptimizers.SingularEndpoint.RowSign
import UpperTailOptimizers.SingularEndpoint.Trapezoid

/-!
# The `h⁵` increment at the contacts and the block-weight slope (Section 7)

The block weight of `lem:rank-one-kkt-family` solves `eq:block-proportion-formula`,
`α_h = B_h/(A_h + B_h)`, so

  `α_h - 1/2 = \frac{B_h - A_h}{2(A_h + B_h)}`,   `B_h - A_h = 𝓜_h(t_h²) - 𝓜_h(s_h²)`.

The denominator is `Θ(h⁴)` (`tendsto_increment_sum`) and the numerator `O(h⁵)`, so the slope
`a₁ = α'(0)` is the ratio of the `h⁵` coefficient of `B_h - A_h` to twice the `h⁴` coefficient
of `A_h + B_h`.  This file computes the first, and hence

  **`α_h = 1/2 + \frac{2d²u_*}{3(d-1)}h + o(h)`**,

the fourth line of `eq:rank-one-parameter-expansions`.

## How the `h⁵` order is reached without a Weierstrass division

`FORMALISATION.md` records that the `h⁵` coefficient cannot come from the Lagrange remainder used
at `h⁴`: there the third derivative is evaluated at an unlocated `ξ`, and at `h⁵` the answer
depends on *where* in the node interval it is evaluated.  The route here avoids the paper's
analytic Weierstrass division altogether.  Three exact algebraic reductions do the work.

1. **The displacement identity** `Mfun_sub_eq` (`SingularEndpoint/IncrementSum.lean`) writes the
   increment as a `Γ_d` increment plus `Λ_h(x-y) - \frac{Δ_h}{d}(x^d - y^d)`, where
   `x = t_h²`, `y = s_h²`.

2. **Eliminating `Λ_h`.**  The two *outer* KKT equations give
   `Λ_h = Δ_h\frac{x^{d-1}+y^{d-1}}{2} - \frac{𝓛_*(x)+𝓛_*(y)}{2}`.  Substituting turns the
   two `Θ(h³)` terms into

     `Δ_h·Θ(x,y) - \frac{(𝓛_*(x)+𝓛_*(y))(x-y)}{2}`,

   where `Θ` is the **trapezoid-rule error** for `∫_y^x z^{d-1}dz`.  The symmetric average is
   essential: `𝓛_*(x)` alone is `Θ(h³)`, so `𝓛_*(x)/h⁴` diverges, while the *sum* is `Θ(h⁴)`
   because the cubes cancel (`tendsto_Lstar_outer_sum`).

3. **The trapezoid error factors an exact cube.**  `trapezoid_error_eq` writes
   `Θ = \frac{(x-y)³}{2d}·D(x,y)` with `D` a double geometric sum, and `x - y = 4u_h h`
   exactly, so the division by `h³` is exact and `D` may simply be evaluated in the limit
   (`tendsto_trapezoid_sum`).

Everything else is the `Γ_d` expansion of `SingularEndpoint/GamTaylor.lean`.  The fifth-order contact
constant `k₄ = Γ_d^{(5)}(r_*)` enters through `contact_const_rel`, `k₄ r_* = 5(d-2)k₃`, and
vanishes at `d = 2` — where the whole `h⁵` coefficient still does not, being carried by `k₃`.

## Contents

* `contact_const_rel`, `gcoeff_trapezoid_term` — the two arithmetic reductions;
* `tendsto_increment_diff` — `(B_h - A_h)/h⁵ → -16d⁵u_*/(9(d-1))`;
* `tendsto_alph_slope` — `(α_h - 1/2)/h → 2d²u_*/(3(d-1))`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology Finset

variable {d : ℕ}

variable (B : KKTFamily d)

/-! ## The difference `B_h - A_h` at order `h⁵` -/

/-- The `Γ`-coefficient identity `k₄ r_* = 5(d-2) k₃` between the fourth and fifth contact
constants — the only relation between them that the `h⁵` coefficient uses.  Note it is an
identity, not an inequality: at `d = 2` both sides vanish. -/
theorem contact_const_rel (hd : 2 ≤ d) :
    5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 * rStar d
      = 5 * ((d : ℝ) - 2) * ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2) := by
  have hD : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  rw [rStar_eq]; field_simp

/-- **The trapezoid term in closed form.**  The `γ₂`-weighted trapezoid error contributes

  `γ₂ · \frac{16(d-1)(d-2)u_*³ r_*^{d-3}}{3} = \frac{32(d-2)u_* r_* k₃}{9}`,

by `family_eq_diff` divided by `r_*`.  At `d = 2` both sides vanish through the factor
`d - 2`, which is exactly the case in which `r_*^{d-3}` is not `r_*^{d-2}/r_*`. -/
theorem gcoeff_trapezoid_term (hd : 2 ≤ d) :
    Gcoeff B * (16 / 3 * ((d : ℝ) - 1) * ((d : ℝ) - 2) * uStar d ^ 3 * rStar d ^ (d - 3))
      = 32 * ((d : ℝ) - 2) * uStar d * rStar d * ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2) / 9 := by
  have hu3 : uStar d ^ 3 = uStar d * rStar d := by rw [← uStar_sq hd]; ring
  rcases eq_or_lt_of_le hd with hd2 | hd3
  · have hz : (d : ℝ) - 2 = 0 := by rw [← hd2]; norm_num
    rw [hz]; ring
  · have hd3' : 3 ≤ d := hd3
    have hrne : rStar d ≠ 0 := rStar_ne_zero hd
    have hsplit : rStar d ^ (d - 2) = rStar d ^ (d - 3) * rStar d := by
      rw [← pow_succ, show d - 3 + 1 = d - 2 from by omega]
    have hII := family_eq_diff B hd
    rw [hsplit] at hII
    have hII' : (Gcoeff B * ((d : ℝ) - 1) * rStar d ^ (d - 3)) * rStar d
        = (2 * ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2) / 3) * rStar d := by
      linear_combination hII
    have hIII := mul_right_cancel₀ hrne hII'
    rw [hu3]
    linear_combination (16 / 3 * ((d : ℝ) - 2) * uStar d * rStar d) * hIII

/-- **`(B_h - A_h)/h⁵ → -16d⁵u_*/(9(d-1))`**, the `h⁵` coefficient of the difference
between increments at the contacts.

The three contributions are the `Γ_d` difference, the `γ₂`-weighted trapezoid error of the
polynomial part, and the outer-node `𝓛_*` sum weighted by the node gap.  Their closed forms
use `Ucoeff_eq` through `4u_*U₂ + 2 = (16-6d)/3`, `family_eq_diff` through
`gcoeff_trapezoid_term`, and nothing else. -/
theorem tendsto_increment_diff (hd : 2 ≤ d) :
    Tendsto (fun h : ℝ => (Mfun d (B.p h) (B.gam h) (B.tVal h ^ 2)
        - Mfun d (B.p h) (B.gam h) (B.sVal h ^ 2)) / h ^ 5)
      (𝓝[≠] (0 : ℝ)) (𝓝 (-(16 * (d : ℝ) ^ 5 * uStar d / (9 * ((d : ℝ) - 1))))) := by
  have hD : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hune : uStar d ≠ 0 := ne_of_gt (uStar_pos hd)
  have hs := tendsto_sVal_sq_rate hd B
  have ht := tendsto_tVal_sq_rate hd B
  have hgap := tendsto_outer_gap_rate B
  have houter := tendsto_outer_sum_rate2 B hd
  have hTs := tendsto_GamTail_comp hd (tendsto_sVal_sq B hd)
  have hTt := tendsto_GamTail_comp hd (tendsto_tVal_sq B hd)
  have hLsum := tendsto_Lstar_outer_sum hd B
  have hDS := tendsto_trapezoid_sum (x := fun h : ℝ => B.tVal h ^ 2)
    (y := fun h : ℝ => B.sVal h ^ 2) d (tendsto_tVal_sq B hd) (tendsto_sVal_sq B hd)
  -- the `Γ_d` difference at order `h⁵`
  have hGam : Tendsto (fun h : ℝ =>
      (Gam d (B.tVal h ^ 2) - Gam d (B.sVal h ^ 2)) / h ^ 5) (𝓝[≠] (0 : ℝ))
      (𝓝 ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 24
            * (4 * uStar d * ((4 * uStar d * Ucoeff B + 2)
              * ((2 * uStar d) ^ 2 + (-(2 * uStar d)) ^ 2)))
          + ((2 * uStar d) ^ 5 * (5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 120)
            - (-(2 * uStar d)) ^ 5
              * (5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 120)))) := by
    have hA := (hgap.mul (houter.mul ((ht.pow 2).add (hs.pow 2)))).const_mul
      ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 24)
    have hB := ((ht.pow 5).mul hTt).sub ((hs.pow 5).mul hTs)
    refine (hA.add hB).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ≠ 0 := hh
    rw [Gam_expand hd (B.tVal h ^ 2), Gam_expand hd (B.sVal h ^ 2)]
    field_simp
    ring
  have hlim := (hGam.add ((tendsto_gam_coeff B).mul
      (((hgap.pow 3).div_const (2 * (d : ℝ))).mul hDS))).sub
    ((hLsum.div_const (2 : ℝ)).mul hgap)
  -- the closed form of the limit
  have hval : ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 24
        * (4 * uStar d * ((4 * uStar d * Ucoeff B + 2)
          * ((2 * uStar d) ^ 2 + (-(2 * uStar d)) ^ 2)))
      + ((2 * uStar d) ^ 5 * (5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 120)
        - (-(2 * uStar d)) ^ 5
          * (5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 120)))
      + Gcoeff B * ((4 * uStar d) ^ 3 / (2 * (d : ℝ))
          * ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) / 6 * rStar d ^ (d - 3)))
      - ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 6
            * ((4 * uStar d * Ucoeff B + 2) * (12 * uStar d ^ 2))
          + 32 * uStar d ^ 4
            * (5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 24)) / 2 * (4 * uStar d)
      = -(16 * (d : ℝ) ^ 5 * uStar d / (9 * ((d : ℝ) - 1))) := by
    have hU : 4 * uStar d * Ucoeff B + 2 = (16 - 6 * (d : ℝ)) / 3 := by
      rw [Ucoeff_eq B hd]; field_simp; ring
    have hstep : Gcoeff B * ((4 * uStar d) ^ 3 / (2 * (d : ℝ))
        * ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) / 6 * rStar d ^ (d - 3)))
        = 32 * ((d : ℝ) - 2) * uStar d * rStar d
          * ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2) / 9 := by
      rw [show (4 * uStar d) ^ 3 / (2 * (d : ℝ))
          * ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) / 6 * rStar d ^ (d - 3))
          = 16 / 3 * ((d : ℝ) - 1) * ((d : ℝ) - 2) * uStar d ^ 3 * rStar d ^ (d - 3) from by
        field_simp; ring]
      exact gcoeff_trapezoid_term B hd
    have h2 : uStar d ^ 2 = rStar d := uStar_sq hd
    have h4 : uStar d ^ 4 = rStar d ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2]
    have h5 : uStar d ^ 5 = uStar d * rStar d ^ 2 := by
      rw [show (5 : ℕ) = 1 + 2 * 2 from rfl, pow_add, pow_mul, h2, pow_one]
    rw [hU, hstep,
      show ((2 : ℝ) * uStar d) ^ 5 = 32 * uStar d ^ 5 from by ring,
      show (-((2 : ℝ) * uStar d)) ^ 5 = -(32 * uStar d ^ 5) from by ring,
      show ((2 : ℝ) * uStar d) ^ 2 = 4 * uStar d ^ 2 from by ring,
      show (-((2 : ℝ) * uStar d)) ^ 2 = 4 * uStar d ^ 2 from by ring,
      h5, h4, h2, rStar_eq]
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_window B] with h hh hw
  have hne : h ≠ 0 := hh
  have hp := B.p_mem h hw
  have hm := Mfun_sub_eq (γ := B.gam h) hd hp.1 hp.2 (sq_tVal_mem' B hw).1
    (sq_tVal_mem' B hw).2 (sq_sVal_mem' B hw).1 (sq_sVal_mem' B hw).2
  have hk1 := kkt_residual_tt B hd hw
  have hk2 := kkt_residual_ss B hd hw
  have htz := trapezoid_error_eq d (by omega) (B.tVal h ^ 2) (B.sVal h ^ 2)
  have hcomb : Mfun d (B.p h) (B.gam h) (B.tVal h ^ 2)
      - Mfun d (B.p h) (B.gam h) (B.sVal h ^ 2)
      = (Gam d (B.tVal h ^ 2) - Gam d (B.sVal h ^ 2))
        + (B.gam h - gammaStar d)
          * ((B.tVal h ^ 2 - B.sVal h ^ 2) ^ 3 / (2 * (d : ℝ))
            * ∑ j ∈ range d,
                (∑ i ∈ range j, (B.tVal h ^ 2) ^ i * (B.sVal h ^ 2) ^ (j - 1 - i))
                  * ∑ i ∈ range (d - 1 - j),
                      (B.tVal h ^ 2) ^ i * (B.sVal h ^ 2) ^ (d - 1 - j - 1 - i))
        - (Lstar d (B.tVal h ^ 2) + Lstar d (B.sVal h ^ 2)) / 2
          * (B.tVal h ^ 2 - B.sVal h ^ 2) := by
    rw [← htz]
    linear_combination hm + ((B.tVal h ^ 2 - B.sVal h ^ 2) / 2) * (hk1 + hk2)
  rw [hcomb]
  field_simp

/-! ## The block-weight slope -/

/-- **`eq:rank-one-parameter-expansions`, the block-weight line**:

  `α_h = \frac12 + \frac{2d²u_*}{3(d-1)}h + o(h)`.

`eq:block-proportion-balance` gives `α_h(A_h + B_h) = B_h`, i.e. `α_h - 1/2 = (B_h-A_h)/(2(A_h+B_h))`,
so the slope is the ratio of `tendsto_increment_diff` to twice `tendsto_increment_sum`. -/
theorem tendsto_alph_slope (hd : 2 ≤ d) :
    Tendsto (fun h : ℝ => (B.alph h - 1 / 2) / h) (𝓝[≠] (0 : ℝ))
      (𝓝 (2 * (d : ℝ) ^ 2 * uStar d / (3 * ((d : ℝ) - 1)))) := by
  have hD : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hnum := tendsto_increment_diff B hd
  have hden := tendsto_increment_sum B hd
  have hdenne : -(4 * (d : ℝ) ^ 3 / 3) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) ^ 3 := by positivity
    intro hc; nlinarith
  have hq := hnum.div hden hdenne
  have hval : -(16 * (d : ℝ) ^ 5 * uStar d / (9 * ((d : ℝ) - 1))) / -(4 * (d : ℝ) ^ 3 / 3) / 2
      = 2 * (d : ℝ) ^ 2 * uStar d / (3 * ((d : ℝ) - 1)) := by
    field_simp
    ring
  have hq2 := hq.div_const (2 : ℝ)
  rw [hval] at hq2
  refine hq2.congr' ?_
  have hne0 := hden.eventually_ne hdenne
  filter_upwards [self_mem_nhdsWithin, eventually_window B, hne0] with h hh hw hd0'
  have hne : h ≠ 0 := hh
  have hS : Mfun d (B.p h) (B.gam h) (B.sVal h ^ 2)
      + Mfun d (B.p h) (B.gam h) (B.tVal h ^ 2)
      - 2 * Mfun d (B.p h) (B.gam h) (B.sVal h * B.tVal h) ≠ 0 := by
    intro hc
    exact hd0' (by rw [hc, zero_div])
  have hrow : B.alph h * (Mfun d (B.p h) (B.gam h) (B.sVal h ^ 2)
        - Mfun d (B.p h) (B.gam h) (B.sVal h * B.tVal h))
      = (1 - B.alph h) * (Mfun d (B.p h) (B.gam h) (B.tVal h ^ 2)
        - Mfun d (B.p h) (B.gam h) (B.sVal h * B.tVal h)) := B.rowBalance h hw
  have halpha : B.alph h - 1 / 2
      = (Mfun d (B.p h) (B.gam h) (B.tVal h ^ 2)
          - Mfun d (B.p h) (B.gam h) (B.sVal h ^ 2))
        / (2 * (Mfun d (B.p h) (B.gam h) (B.sVal h ^ 2)
            + Mfun d (B.p h) (B.gam h) (B.tVal h ^ 2)
            - 2 * Mfun d (B.p h) (B.gam h) (B.sVal h * B.tVal h))) := by
    rw [eq_div_iff (by simpa using mul_ne_zero (two_ne_zero) hS)]
    linear_combination 2 * hrow
  simp only [Pi.div_apply]
  rw [halpha]
  field_simp

end SingularEndpoint

end UpperTailOptimizers
