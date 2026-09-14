import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.Expansions

/-!
# Quintic singular endpoint Taylor data (Section 5, `paper/sections/singular.tex`)

`SingularEndpoint/ConstantGraphonComparison/Expansions.lean` reads the `h²` coefficients `U₂`, `L₂`, `G₂` of the family
off the three KKT equations divided by `h²`, `h³`, `h⁴`.  The
one coefficient it cannot reach is the block weight slope

  `a₁ = α'(0) = \frac{2d²u_*}{3(d-1)}`,

because `α_h` enters the increment at the contacts `B_h - A_h = 𝓜_h(t_h²) - 𝓜_h(s_h²)` only at order
`h⁵`.  This file supplies the two pieces of Taylor data
that the `h⁵` bookkeeping consumes, each one order beyond what is already in the development.

## Contents

* `GamTail`, `Gam_expand`, `GamTail_rStar`, `continuousAt_GamTail`, `tendsto_GamTail_comp` —
  the quartic-plus-quintic expansion of the singular endpoint supporting gap,

    `Γ_d(z) = \frac{k₃}{24}(z-r_*)⁴ + (z-r_*)⁵ T(z)`,  `T(r_*) = k₄/120`,

  `k₃ = d⁵/(d-1)²`, `k₄ = 5d⁶(d-2)/(d-1)³`.  This is `eq:endpoint-gap-expansion`
  with its next term made explicit, and it is the exact mirror, one order up, of the `𝓛_*`
  block at the top of `SingularEndpoint/ConstantGraphonComparison/Expansions.lean`: `Γ_d' = 𝓛_*`, so the vanishing list runs
  over `0 ≤ j ≤ 3` instead of `0 ≤ j ≤ 2` and the tail index is `5` instead of `4`.
* `tendsto_Lstar_outer_sum` — the **sum** of `𝓛_*` over the two outer nodes at order `h⁴`.

The second is the companion of the second difference `𝓛_*(t_h²) + 𝓛_*(s_h²) - 2𝓛_*(s_h t_h)`
computed inside `family_eq_second`: the same expansion with the middle-node terms deleted.
Both halves of the cubic-plus-quartic expansion survive the deletion, because the two outer
nodes enter the quartic tail with the *same* sign — the mechanism that made the quartic tail
invisible in `family_eq_cross` and `family_eq_diff`.  The one algebraic step is the
factorisation of a sum of cubes, valid for `h ≠ 0`,

  `(w₃³ + w₁³)/h⁴ = \frac{w₃ + w₁}{h²}\left\{(w₃/h)² - (w₃/h)(w₁/h) + (w₁/h)²\right\}`,

with `w₃ = t_h² - r_*` and `w₁ = s_h² - r_*`; the three factors converge by
`tendsto_outer_sum_rate2`, `tendsto_tVal_sq_rate` and `tendsto_sVal_sq_rate`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

variable {d : ℕ}

/-! ## The expansion of `Γ_d` at `r_*` -/

/-- The **quintic Taylor tail** `T` of the singular endpoint supporting gap `Γ_d` at `r_*`: the
analytic function with

  `Γ_d(z) = \frac{Γ_d^{(4)}(r_*)}{24}(z - r_*)⁴ + (z - r_*)⁵ T(z)`,  `T(r_*) = Γ_d^{(5)}(r_*)/120`.

It stands to `Γ_d` exactly as `LstarTail` stands to `𝓛_* = Γ_d'`, one order higher. -/
noncomputable def GamTail (d : ℕ) : ℝ → ℝ := taylorTail (Gam d) (rStar d) 5

/-- **The quartic-plus-quintic expansion of `Γ_d`.**  The first four Taylor coefficients of
`Γ_d` at `r_*` vanish — `Γ_d^{(j)}(r_*) = 0` for `0 ≤ j ≤ 3`, the vanishing quoted before
`eq:endpoint-gap-expansion` — so the expansion of `SingularEndpoint/ConstantGraphonComparison/TaylorTail.lean` starts
at the fourth power, with the exact non-degenerate coefficient `k₃/24 = d⁵/(24(d-1)²)` of
`iteratedDeriv_four_Gam`. -/
theorem Gam_expand (hd : 2 ≤ d) (z : ℝ) :
    Gam d z = ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 24) * (z - rStar d) ^ 4
      + (z - rStar d) ^ 5 * GamTail d z := by
  have hana : AnalyticAt ℝ (Gam d) (rStar d) :=
    analyticAt_Gam hd (rStar_pos hd) (rStar_lt_one hd)
  have hvan : ∀ k, k < 4 → iteratedDeriv k (Gam d) (rStar d) = 0 := by
    intro k hk
    interval_cases k
    · rw [iteratedDeriv_zero]; exact Gam_rStar hd
    · exact iteratedDeriv_one_Gam hd
    · exact iteratedDeriv_two_Gam hd
    · exact iteratedDeriv_three_Gam hd
  have h := taylorTail_expand_of_iteratedDeriv_eq_zero hana hvan z
  rw [iteratedDeriv_four_Gam hd] at h
  simpa [GamTail, Nat.factorial] using h

/-- `T(r_*) = k₄/120 = 5d⁶(d-2)/(120(d-1)³)`, by `iteratedDeriv_five_Gam`. -/
theorem GamTail_rStar (hd : 2 ≤ d) :
    GamTail d (rStar d) = 5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 120 := by
  have hana : AnalyticAt ℝ (Gam d) (rStar d) :=
    analyticAt_Gam hd (rStar_pos hd) (rStar_lt_one hd)
  have h := taylorTail_apply_self hana 5
  rw [iteratedDeriv_five_Gam hd] at h
  simpa [GamTail, Nat.factorial] using h

/-- The tail is continuous at `r_*`: it is analytic on all of `(0,1)`. -/
theorem continuousAt_GamTail (hd : 2 ≤ d) : ContinuousAt (GamTail d) (rStar d) :=
  (analyticOnNhd_taylorTail (analyticOnNhd_Gam hd) (rStar_mem_Ioo hd) 5 _
    (rStar_mem_Ioo hd)).continuousAt

/-- The tail evaluated along any family of nodes collapsing to `r_*`. -/
theorem tendsto_GamTail_comp (hd : 2 ≤ d) {f : ℝ → ℝ}
    (hf : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 (rStar d))) :
    Tendsto (fun h : ℝ => GamTail d (f h)) (𝓝[≠] (0 : ℝ))
      (𝓝 (5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 120)) := by
  have h := ((continuousAt_GamTail hd).tendsto).comp hf
  rwa [GamTail_rStar hd] at h

/-! ## The outer-node sum for `𝓛_*` -/

/-- **The outer-node sum at order `h⁴`.**

  `\frac{𝓛_*(t_h²) + 𝓛_*(s_h²)}{h⁴} \to \frac{k₃}{6}(4u_*U₂+2)(12u_*²) + 32u_*⁴\frac{k₄}{24}`,

with `k₃ = d⁵/(d-1)²` and `k₄ = 5d⁶(d-2)/(d-1)³`.  This is the computation of `hLsec` inside
`family_eq_second` with the middle-node terms `-2𝓛_*(s_h t_h)` deleted; unlike there, the
quartic tail `S` is not cancelled by anything, and it contributes the second summand
`(2u_*)⁴S(r_*) + (-2u_*)⁴S(r_*) = 32u_*⁴S(r_*)`.

The cubic part is handled by writing `w₃³ + w₁³ = (w₃ + w₁)(w₃² - w₃w₁ + w₁²)` and dividing
the first factor by `h²` (`tendsto_outer_sum_rate2`) and the second by `h²` as a product of
two first-order rates (`tendsto_tVal_sq_rate`, `tendsto_sVal_sq_rate`), so that no
cancellation is left to the limit. -/
theorem tendsto_Lstar_outer_sum (hd : 2 ≤ d) (B : KKTFamily d) :
    Tendsto (fun h : ℝ => (Lstar d (B.tVal h ^ 2) + Lstar d (B.sVal h ^ 2)) / h ^ 4)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 6
            * ((4 * uStar d * Ucoeff B + 2) * (12 * uStar d ^ 2))
          + 32 * uStar d ^ 4
            * (5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 24))) := by
  have hs := tendsto_sVal_sq_rate hd B
  have ht := tendsto_tVal_sq_rate hd B
  have houter := tendsto_outer_sum_rate2 B hd
  have hSs := tendsto_LstarTail_comp hd (tendsto_sVal_sq B hd)
  have hSt := tendsto_LstarTail_comp hd (tendsto_tVal_sq B hd)
  set K₄ : ℝ := 5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 / 24 with hK₄
  set k₃ : ℝ := (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 with hk₃
  have hcubes := houter.mul (((ht.pow 2).sub (ht.mul hs)).add (hs.pow 2))
  have hA := hcubes.const_mul (k₃ / 6)
  have hB := ((ht.pow 4).mul hSt).add ((hs.pow 4).mul hSs)
  have hsum := hA.add hB
  rw [show k₃ / 6 * ((4 * uStar d * Ucoeff B + 2)
          * ((2 * uStar d) ^ 2 - 2 * uStar d * -(2 * uStar d) + (-(2 * uStar d)) ^ 2))
        + ((2 * uStar d) ^ 4 * K₄ + (-(2 * uStar d)) ^ 4 * K₄)
      = k₃ / 6 * ((4 * uStar d * Ucoeff B + 2) * (12 * uStar d ^ 2))
        + 32 * uStar d ^ 4 * K₄ from by ring] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := hh
  rw [Lstar_expand hd (B.tVal h ^ 2), Lstar_expand hd (B.sVal h ^ 2)]
  field_simp
  ring

end SingularEndpoint

end UpperTailOptimizers
