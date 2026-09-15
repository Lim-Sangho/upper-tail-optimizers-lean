import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.TaylorTail
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.FamilyRates
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilyAnalytic

/-!
# Quadratic-order rates along the family (Section 5, `paper/sections/singular.tex`)

`SingularEndpoint/ConstantGraphonComparison/FamilyRates.lean` records the **first**-order rates of the three edge values,
`(s_h² - r_*)/h → -2u_*`, `(t_h² - r_*)/h → 2u_*`, `(s_h t_h - r_*)/h → 0`, which is all the
`h⁴` order of `SingularEndpoint/ConstantGraphonComparison/GamAverage.lean` needs.  The expansions
`eq:rank-one-parameter-expansions` need one order more.

This file supplies that layer:

* the `h²` Taylor coefficient `coeff2 v = v''(0)/2` of an **even** analytic family function,
  together with the limit `(v_h - v_0)/h² → coeff2 v` (`tendsto_coeff2`, an instance of
  `tendsto_sub_self_div_pow`);
* the three family coefficients `Ucoeff`, `Lcoeff`, `Gcoeff` — the `U₂`, `L₂` and `G₂` of
  `app:rank-one-parameter-expansions`, the quadratic coefficients of `u_h`, `ℓ(p_h)` and
  `γ_h` — with their defining limits;
* the two second-order node rates the KKT equations are divided by,
  `(s_h t_h - r_*)/h² → 2u_*U₂ - 1` and `(t_h² + s_h² - 2r_*)/h² → 4u_*U₂ + 2`;
* `tendsto_pow_diff_rate` — `(t_h^m - s_h^m)/h → 2m u_*^{m-1}`, the factor that turns the
  polynomial half of `eq:three-value-kkt` into a limit.  It uses `t_h - s_h = 2h`
  exactly, so no cancellation is left to the limit.

Nothing here uses `𝓛_*`; the equations themselves are in `SingularEndpoint/ConstantGraphonComparison/Expansions.lean`.

## Contents

* `coeff2`, `tendsto_coeff2` — the `h²` Taylor coefficient of an even analytic function and
  the limit that pins it;
* `Ucoeff`, `Lcoeff`, `Gcoeff` — the three family coefficients, with their defining limits
  `tendsto_u_coeff`, `tendsto_ell_coeff`, `tendsto_gam_coeff` and the analyticity
  `analyticAt_ell_p` the middle one rests on;
* `tendsto_sVal`, `tendsto_tVal`, `tendsto_sVal_sq`,
  `tendsto_tVal_sq`, `tendsto_cross` — the plain limits of the family data at `h = 0`;
* `tendsto_cross_rate2`, `tendsto_outer_sum_rate2` — the two second-order node rates;
* `tendsto_geom_sum₂`, `tendsto_pow_diff_rate` — the geometric-sum factor.
-/

namespace UpperTailOptimizers

open Filter Topology Finset

variable {d : ℕ}

/-! ## The `h²` coefficient of an even analytic function -/

/-- The `h²` Taylor coefficient `v''(0)/2` of `v` at the origin.

For the family functions `u_h, ℓ(p_h), γ_h` — analytic and even in `h` — this is the coefficient
`U₂`, `L₂` or `G₂` of `app:rank-one-parameter-expansions`, and `tendsto_coeff2` is the limit
that pins it. -/
noncomputable def coeff2 (v : ℝ → ℝ) : ℝ := iteratedDeriv 2 v 0 / 2

/-- **The defining limit of `coeff2`.**  An even function analytic at `0` has vanishing
derivative there (`deriv_zero_of_even`), so its increment is `O(h²)` and

  `(v_h - v_0)/h² → v''(0)/2`. -/
theorem tendsto_coeff2 {v : ℝ → ℝ} (hv : AnalyticAt ℝ v 0) (hev : ∀ h : ℝ, v (-h) = v h) :
    Tendsto (fun h : ℝ => (v h - v 0) / h ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (coeff2 v)) := by
  have hderiv : deriv v 0 = 0 :=
    deriv_zero_of_even hev hv.differentiableAt.hasDerivAt
  have hvan : ∀ k, 1 ≤ k → k < 2 → iteratedDeriv k v 0 = 0 := by
    intro k hk1 hk2
    interval_cases k
    · rw [iteratedDeriv_one]; exact hderiv
  have h := tendsto_sub_self_div_pow (f := v) (a := (0 : ℝ)) (n := 2) (by norm_num) hv hvan
  simpa [coeff2, Nat.factorial] using h

/-! ## The three family coefficients -/

/-- `U₂`, the `h²` coefficient of the midpoint `u_h` `eq:rank-one-parameter-expansions`. -/
noncomputable def Ucoeff (B : KKTFamily d) : ℝ := coeff2 B.u

/-- The `h²` coefficient of the log-odds `ℓ(p_h)`, i.e. of `Λ_h := ℓ(p_h) - ℓ_*`.  The
paper introduces `Λ_h` without a label in Section 5.2, just before
`lem:rank-one-parameter-expansions`; its quadratic rate is the `Λ_h` entry of
`eq:rank-one-parameter-expansions`. -/
noncomputable def Lcoeff (B : KKTFamily d) : ℝ := coeff2 (fun h => ell (B.p h))

/-- The `h²` coefficient of the scalar multiplier `γ_h`. -/
noncomputable def Gcoeff (B : KKTFamily d) : ℝ := coeff2 B.gam

variable (B : KKTFamily d)

private theorem zero_mem_window : |(0 : ℝ)| < B.h₀ := by rw [abs_zero]; exact B.h₀_pos

theorem tendsto_u_coeff : Tendsto (fun h : ℝ => (B.u h - uStar d) / h ^ 2) (𝓝[≠] (0 : ℝ))
    (𝓝 (Ucoeff B)) := by
  have h := tendsto_coeff2 (B.analyticAt_u 0 (zero_mem_window B)) B.u_even
  rwa [B.u_zero] at h

theorem tendsto_gam_coeff : Tendsto (fun h : ℝ => (B.gam h - gammaStar d) / h ^ 2)
    (𝓝[≠] (0 : ℝ)) (𝓝 (Gcoeff B)) := by
  have h := tendsto_coeff2 (B.analyticAt_gam 0 (zero_mem_window B)) B.gam_even
  rwa [B.gam_zero] at h

/-- `h ↦ ℓ(p_h)` is analytic at the origin: `p_h` is, and `ℓ` is analytic on `(0,1)` ∋ `p_*`. -/
theorem analyticAt_ell_p (hd : 2 ≤ d) : AnalyticAt ℝ (fun h : ℝ => ell (B.p h)) 0 := by
  have hp : AnalyticAt ℝ ell (B.p 0) := by
    rw [B.p_zero]; exact analyticAt_ell (pStar_pos hd) (pStar_lt_one hd)
  exact hp.comp (B.analyticAt_p 0 (zero_mem_window B))

theorem tendsto_ell_coeff (hd : 2 ≤ d) :
    Tendsto (fun h : ℝ => ell (B.p h) - ell (pStar d)) (𝓝[≠] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun h : ℝ => (ell (B.p h) - ell (pStar d)) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (Lcoeff B)) := by
  have hev : ∀ h : ℝ, ell (B.p (-h)) = ell (B.p h) := fun h => by rw [B.p_even]
  have h2 := tendsto_coeff2 (analyticAt_ell_p B hd) hev
  rw [B.p_zero] at h2
  refine ⟨?_, h2⟩
  have hc : Tendsto (fun h : ℝ => ell (B.p h)) (𝓝[≠] (0 : ℝ)) (𝓝 (ell (B.p 0))) :=
    ((analyticAt_ell_p B hd).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  rw [B.p_zero] at hc
  have := hc.sub (tendsto_const_nhds (x := ell (pStar d)))
  rwa [sub_self] at this

/-! ## Convergence of the family data -/

theorem tendsto_sVal : Tendsto B.sVal (𝓝[≠] (0 : ℝ)) (𝓝 (uStar d)) := by
  have h := (tendsto_u_punctured B).sub (tendsto_id.mono_left nhdsWithin_le_nhds)
  rw [sub_zero] at h
  exact h.congr fun _ => rfl

theorem tendsto_tVal : Tendsto B.tVal (𝓝[≠] (0 : ℝ)) (𝓝 (uStar d)) := by
  have h := (tendsto_u_punctured B).add (tendsto_id.mono_left nhdsWithin_le_nhds)
  rw [add_zero] at h
  exact h.congr fun _ => rfl

theorem tendsto_sVal_sq (hd : 2 ≤ d) :
    Tendsto (fun h : ℝ => B.sVal h ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (rStar d)) := by
  have h := (tendsto_sVal B).pow 2
  rwa [uStar_sq hd] at h

theorem tendsto_tVal_sq (hd : 2 ≤ d) :
    Tendsto (fun h : ℝ => B.tVal h ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (rStar d)) := by
  have h := (tendsto_tVal B).pow 2
  rwa [uStar_sq hd] at h

theorem tendsto_cross (hd : 2 ≤ d) :
    Tendsto (fun h : ℝ => B.sVal h * B.tVal h) (𝓝[≠] (0 : ℝ)) (𝓝 (rStar d)) := by
  have h := (tendsto_sVal B).mul (tendsto_tVal B)
  rwa [show uStar d * uStar d = rStar d from by rw [← sq, uStar_sq hd]] at h

/-! ## The two second-order node rates -/

/-- **The cross node at second order**: `(s_h t_h - r_*)/h² → 2u_*U₂ - 1`.

Exactly `s_h t_h - r_* = (u_h - u_*)(u_h + u_*) - h²`, so the limit is
`U₂ · 2u_* - 1` with no remainder to estimate. -/
theorem tendsto_cross_rate2 (hd : 2 ≤ d) :
    Tendsto (fun h : ℝ => (B.sVal h * B.tVal h - rStar d) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (2 * uStar d * Ucoeff B - 1)) := by
  have hsum : Tendsto (fun h : ℝ => B.u h + uStar d) (𝓝[≠] (0 : ℝ)) (𝓝 (2 * uStar d)) := by
    have h := (tendsto_u_punctured B).add (tendsto_const_nhds (x := uStar d))
    rwa [show uStar d + uStar d = 2 * uStar d from by ring] at h
  have h := ((tendsto_u_coeff B).mul hsum).sub (tendsto_const_nhds (x := (1 : ℝ)))
  rw [show Ucoeff B * (2 * uStar d) - 1 = 2 * uStar d * Ucoeff B - 1 from by ring] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := hh
  rw [KKTFamily.sVal, KKTFamily.tVal, ← uStar_sq hd]
  field_simp
  ring

/-- **The outer nodes at second order**: `(t_h² + s_h² - 2r_*)/h² → 4u_*U₂ + 2`.

Exactly `t_h² + s_h² - 2r_* = 2(u_h - u_*)(u_h + u_*) + 2h²`. -/
theorem tendsto_outer_sum_rate2 (hd : 2 ≤ d) :
    Tendsto (fun h : ℝ => (B.tVal h ^ 2 + B.sVal h ^ 2 - 2 * rStar d) / h ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (4 * uStar d * Ucoeff B + 2)) := by
  have h := (tendsto_cross_rate2 B hd).const_mul (2 : ℝ)
  have h2 := h.add (tendsto_const_nhds (x := (4 : ℝ)))
  rw [show 2 * (2 * uStar d * Ucoeff B - 1) + 4 = 4 * uStar d * Ucoeff B + 2 from by ring] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := hh
  rw [KKTFamily.sVal, KKTFamily.tVal]
  field_simp
  ring

/-! ## Geometric sums -/

/-- If `f` and `g` share the limit `c`, the geometric sum `∑_{i<m} f^i g^{m-1-i}` tends to
`m c^{m-1}`. -/
theorem tendsto_geom_sum₂ {f g : ℝ → ℝ} {c : ℝ} (m : ℕ)
    (hf : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 c)) (hg : Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 c)) :
    Tendsto (fun h : ℝ => ∑ i ∈ range m, f h ^ i * g h ^ (m - 1 - i)) (𝓝[≠] (0 : ℝ))
      (𝓝 ((m : ℝ) * c ^ (m - 1))) := by
  have hterm : Tendsto (fun h : ℝ => ∑ i ∈ range m, f h ^ i * g h ^ (m - 1 - i))
      (𝓝[≠] (0 : ℝ)) (𝓝 (∑ _i ∈ range m, c ^ (m - 1))) := by
    refine tendsto_finsetSum _ fun i hi => ?_
    have hpow : c ^ i * c ^ (m - 1 - i) = c ^ (m - 1) := by
      rw [← pow_add]
      congr 1
      have : i < m := mem_range.mp hi
      omega
    have := (hf.pow i).mul (hg.pow (m - 1 - i))
    rwa [hpow] at this
  rwa [Finset.sum_const, card_range, nsmul_eq_mul] at hterm

/-- **The polynomial increment rate**: `(t_h^m - s_h^m)/h → 2m u_*^{m-1}`.

`t_h - s_h = 2h` exactly, so `t_h^m - s_h^m = 2h · ∑_{i<m} t_h^i s_h^{m-1-i}` and the
division by `h` is exact. -/
theorem tendsto_pow_diff_rate (m : ℕ) :
    Tendsto (fun h : ℝ => (B.tVal h ^ m - B.sVal h ^ m) / h) (𝓝[≠] (0 : ℝ))
      (𝓝 (2 * (m : ℝ) * uStar d ^ (m - 1))) := by
  have h := (tendsto_geom_sum₂ m (tendsto_tVal B) (tendsto_sVal B)).const_mul (2 : ℝ)
  rw [show (2 : ℝ) * ((m : ℝ) * uStar d ^ (m - 1)) = 2 * (m : ℝ) * uStar d ^ (m - 1) from
    by ring] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := hh
  have hgap : B.tVal h - B.sVal h = 2 * h := by
    rw [KKTFamily.sVal, KKTFamily.tVal]; ring
  have hfac := pow_sub_pow_eq (B.tVal h) (B.sVal h) m
  rw [hgap] at hfac
  rw [hfac]
  field_simp

end UpperTailOptimizers
