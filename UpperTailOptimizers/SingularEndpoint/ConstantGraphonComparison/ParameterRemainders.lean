import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilyContinuity
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.MuExpansion
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.ParityOrder

/-!
# `lem:rank-one-parameter-expansions` with the paper's remainders

`SingularEndpoint/ConstantGraphonComparison/FamilyQuadratic.lean`, `SingularEndpoint/ConstantGraphonComparison/Order5.lean`,
`SingularEndpoint/ConstantGraphonComparison/EdgeGap.lean` and `SingularEndpoint/ConstantGraphonComparison/MuExpansion.lean` prove the *rates* along
the rank-one KKT family: limits of difference quotients such as `(u_h - u_*)/h² → U₂`, which say
`u_h = u_* + U₂h² + o(h²)`.  `eq:rank-one-parameter-expansions` states one order more:

  `u_h = u_* + \frac{5-3d}{6u_*}h² + O_d(h⁴)`,   `Λ_h = \frac{2d³}{3(d-1)}h² + O_d(h⁴)`,
  `α_h = \frac12 + \frac{2d²u_*}{3(d-1)}h + O_d(h³)`,   `r_h = r_* - \frac{2(4d-1)}3h² + O_d(h⁴)`.

The paper's reason for the extra order is the parity recorded in `lem:rank-one-kkt-family`; the
proof of `lem:rank-one-parameter-expansions` opens: "The symmetries in `lem:rank-one-kkt-family`
show that `u_h,γ_h`, and `Λ_h` have expansions in even powers of `h`, while `α_h-1/2` has an
expansion in odd powers".  `SingularEndpoint/ConstantGraphonComparison/ParityOrder.lean` turns exactly that into the two-order gain,
and this file applies it to each parameter.

Every ingredient is already carried by `KKTFamily`: the four analyticity fields, the three
evenness fields `u_even`, `p_even`, `gam_even`, and the reflection `alph_reflect`.  The derived
scalars `q_h`, `r_h`, `μ_h` inherit evenness through `qVal_even`, `rVal_even` and `muVal_even`,
and analyticity through `analyticAt_qVal`, `analyticAt_rVal` and `analyticAt_muVal`.

## Contents

* `u_remainder`, `lambda_remainder`, `alph_remainder`, `rVal_remainder` — the four expansions
  of `eq:rank-one-parameter-expansions`: the leading coefficients explicitly, the remainders as
  `O` bounds on a window;
* `rank_one_parameter_expansions` — the four collected on one window with one constant, the
  form `lem:rank-one-parameter-expansions` states;
* `gam_remainder`, `qVal_remainder`, `muVal_remainder` — the same upgrade for the auxiliary
  scalars `γ_h`, `q_h`, `μ_h`;
* `muVal_even`, `analyticAt_muVal` — the two inputs `μ_h` needed.
-/

namespace UpperTailOptimizers

open Filter Topology

variable {d : ℕ}

/-! ## The two missing inputs for `μ_h` -/

/-- `μ_{-h} = μ_h`: both factors of `μ_h = γ_h/(m q_h^{v-2})` are even. -/
theorem muVal_even (B : KKTFamily d) (m h : ℝ) : B.muVal m (-h) = B.muVal m h := by
  simp only [KKTFamily.muVal, B.gam_even, KKTFamily.qVal_even]

/-- `μ_h` is analytic at `0`.  Same construction as `analyticAt_rVal`: the real power is
`exp (log q_h · (v-2))`, and `q_0 > 0`. -/
theorem analyticAt_muVal (B : KKTFamily d) {m : ℝ} (hm : 0 < m) :
    AnalyticAt ℝ (B.muVal m) 0 := by
  have hw := KKTFamily.zero_mem_window B
  have hq0 : 0 < B.qVal 0 := KKTFamily.qVal_pos hw
  have hpow : AnalyticAt ℝ (fun z : ℝ => B.qVal z ^ (2 * m / (d : ℝ) - 2)) 0 := by
    have hexp : AnalyticAt ℝ
        (fun z : ℝ => Real.exp (Real.log (B.qVal z) * (2 * m / (d : ℝ) - 2))) 0 :=
      (((KKTFamily.analyticAt_qVal hw).log (KKTFamily.qVal_pos hw)).mul analyticAt_const).rexp'
    refine hexp.congr ?_
    filter_upwards [KKTFamily.eventually_window_of_mem hw] with z hz
    exact (Real.rpow_def_of_pos (KKTFamily.qVal_pos hz) _).symm
  have hden0 : m * B.qVal 0 ^ (2 * m / (d : ℝ) - 2) ≠ 0 := by
    have : (0 : ℝ) < B.qVal 0 ^ (2 * m / (d : ℝ) - 2) := Real.rpow_pos_of_pos hq0 _
    positivity
  exact (B.analyticAt_gam 0 hw).div (analyticAt_const.mul hpow) hden0

/-! ## The four expansions of `eq:rank-one-parameter-expansions` -/

/-- **`u_h = u_* + \frac{5-3d}{6u_*}h² + O_d(h⁴)`.**  `u_h` is analytic and even, so the `h³`
term of its Taylor expansion is absent and the first omitted term is quartic. -/
theorem u_remainder (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      |B.u h - (uStar d + (5 - 3 * (d : ℝ)) / (6 * uStar d) * h ^ 2)| ≤ C * |h| ^ 4 := by
  have hlim : Tendsto (fun h : ℝ => (B.u h - B.u 0) / h ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (Ucoeff B)) := by
    rw [B.u_zero]; exact tendsto_u_coeff B
  obtain ⟨C, δ, hC, hδ, hb⟩ := exists_pow_bound_sub_quadratic
    (B.analyticAt_u 0 (KKTFamily.zero_mem_window B)) B.u_even hlim
  refine ⟨C, δ, hC, hδ, fun h hh => ?_⟩
  have h1 := hb h hh
  rw [B.u_zero, Ucoeff_eq B hd] at h1
  rw [show B.u h - (uStar d + (5 - 3 * (d : ℝ)) / (6 * uStar d) * h ^ 2)
      = B.u h - uStar d - (5 - 3 * (d : ℝ)) / (6 * uStar d) * h ^ 2 from by ring]
  exact h1

/-- **`Λ_h = \frac{2d³}{3(d-1)}h² + O_d(h⁴)`**, where `Λ_h = ℓ(p_h) - ℓ_*`.  `p_h` is even, so
`ℓ(p_h)` is. -/
theorem lambda_remainder (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      |ell (B.p h) - ell (pStar d) - 2 * (d : ℝ) ^ 3 / (3 * ((d : ℝ) - 1)) * h ^ 2|
        ≤ C * |h| ^ 4 := by
  have hev : ∀ h : ℝ, ell (B.p (-h)) = ell (B.p h) := fun h => by rw [B.p_even]
  have hlim : Tendsto (fun h : ℝ => (ell (B.p h) - ell (B.p 0)) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (Lcoeff B)) := by
    rw [B.p_zero]; exact (tendsto_ell_coeff B hd).2
  obtain ⟨C, δ, hC, hδ, hb⟩ := exists_pow_bound_sub_quadratic (analyticAt_ell_p B hd) hev hlim
  refine ⟨C, δ, hC, hδ, fun h hh => ?_⟩
  have h1 := hb h hh
  rw [B.p_zero, Lcoeff_eq B hd] at h1
  exact h1

/-- **`α_h = \frac12 + \frac{2d²u_*}{3(d-1)}h + O_d(h³)`.**  `alph_reflect` makes `α_h - 1/2`
odd, so the `h²` term is absent and the first omitted term is cubic. -/
theorem alph_remainder (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      |B.alph h - (1 / 2 + 2 * (d : ℝ) ^ 2 * uStar d / (3 * ((d : ℝ) - 1)) * h)|
        ≤ C * |h| ^ 3 := by
  have hana : AnalyticAt ℝ (fun h : ℝ => B.alph h - 1 / 2) 0 :=
    (B.analyticAt_alph 0 (KKTFamily.zero_mem_window B)).sub analyticAt_const
  have hodd : ∀ h : ℝ, (fun h : ℝ => B.alph h - 1 / 2) (-h)
      = -(fun h : ℝ => B.alph h - 1 / 2) h := by
    intro h; simp only [B.alph_reflect h]; ring
  obtain ⟨C, δ, hC, hδ, hb⟩ := exists_pow_bound_sub_linear hana hodd (tendsto_alph_slope B hd)
  refine ⟨C, δ, hC, hδ, fun h hh => ?_⟩
  have h1 := hb h hh
  rw [show B.alph h - (1 / 2 + 2 * (d : ℝ) ^ 2 * uStar d / (3 * ((d : ℝ) - 1)) * h)
      = B.alph h - 1 / 2 - 2 * (d : ℝ) ^ 2 * uStar d / (3 * ((d : ℝ) - 1)) * h from by ring]
  exact h1

/-- **`r_h = r_* - \frac{2(4d-1)}3h² + O_d(h⁴)`.**  `r_h = q_h^{2/d}` is even because `q_h` is
(`qVal_even`, which is where `alph_reflect` enters). -/
theorem rVal_remainder (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      |B.rVal h - (rStar d - 2 * (4 * (d : ℝ) - 1) / 3 * h ^ 2)| ≤ C * |h| ^ 4 := by
  have hlim : Tendsto (fun h : ℝ => (B.rVal h - B.rVal 0) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-(2 * (4 * (d : ℝ) - 1) / 3))) := by
    rw [KKTFamily.rVal_zero hd B]; exact tendsto_rVal_coeff B hd
  obtain ⟨C, δ, hC, hδ, hb⟩ := exists_pow_bound_sub_quadratic
    (KKTFamily.analyticAt_rVal (KKTFamily.zero_mem_window B)) (fun h => KKTFamily.rVal_even h) hlim
  refine ⟨C, δ, hC, hδ, fun h hh => ?_⟩
  have h1 := hb h hh
  rw [KKTFamily.rVal_zero hd B] at h1
  rw [show B.rVal h - (rStar d - 2 * (4 * (d : ℝ) - 1) / 3 * h ^ 2)
      = B.rVal h - rStar d - -(2 * (4 * (d : ℝ) - 1) / 3) * h ^ 2 from by ring]
  exact h1

/-! ## The auxiliary scalars -/

/-- The same upgrade for `γ_h`, which is analytic and even. -/
theorem gam_remainder (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      |B.gam h - gammaStar d
          - 2 * (d : ℝ) ^ (d + 2) / (3 * ((d : ℝ) - 1) ^ d) * h ^ 2| ≤ C * |h| ^ 4 := by
  have hlim : Tendsto (fun h : ℝ => (B.gam h - B.gam 0) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (Gcoeff B)) := by
    rw [B.gam_zero]; exact tendsto_gam_coeff B
  obtain ⟨C, δ, hC, hδ, hb⟩ := exists_pow_bound_sub_quadratic
    (B.analyticAt_gam 0 (KKTFamily.zero_mem_window B)) B.gam_even hlim
  refine ⟨C, δ, hC, hδ, fun h hh => ?_⟩
  have h1 := hb h hh
  rwa [B.gam_zero, Gcoeff_eq B hd] at h1

/-- The same upgrade for the rank-one moment `q_h`. -/
theorem qVal_remainder (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      |B.qVal h - uStar d ^ d
          - -((d : ℝ) * (4 * (d : ℝ) - 1) / 3 * uStar d ^ (d - 2)) * h ^ 2| ≤ C * |h| ^ 4 := by
  have hlim : Tendsto (fun h : ℝ => (B.qVal h - B.qVal 0) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-((d : ℝ) * (4 * (d : ℝ) - 1) / 3 * uStar d ^ (d - 2)))) := by
    rw [KKTFamily.qVal_zero B]; exact tendsto_qVal_coeff B hd
  obtain ⟨C, δ, hC, hδ, hb⟩ := exists_pow_bound_sub_quadratic
    (KKTFamily.analyticAt_qVal (KKTFamily.zero_mem_window B))
    (fun h => KKTFamily.qVal_even h) hlim
  refine ⟨C, δ, hC, hδ, fun h hh => ?_⟩
  have h1 := hb h hh
  rwa [KKTFamily.qVal_zero B] at h1

/-- The same upgrade for the Lagrange multiplier `μ_h`. -/
theorem muVal_remainder (hd : 2 ≤ d) (B : KKTFamily d) {m : ℝ} (hm : 0 < m) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      |B.muVal m h - 1 / (m * rStar d ^ m)
          - 1 / (m * rStar d ^ m) * ((d : ℝ) ^ 2 / 3)
            * (2 + (2 * m / (d : ℝ) - 2) * (4 * (d : ℝ) - 1) / ((d : ℝ) - 1)) * h ^ 2|
        ≤ C * |h| ^ 4 := by
  have hlim : Tendsto (fun h : ℝ => (B.muVal m h - B.muVal m 0) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (1 / (m * rStar d ^ m) * ((d : ℝ) ^ 2 / 3)
        * (2 + (2 * m / (d : ℝ) - 2) * (4 * (d : ℝ) - 1) / ((d : ℝ) - 1)))) := by
    rw [B.muVal_zero hd m]; exact tendsto_muVal_coeff_rStar B hd hm
  obtain ⟨C, δ, hC, hδ, hb⟩ := exists_pow_bound_sub_quadratic
    (analyticAt_muVal B hm) (fun h => muVal_even B m h) hlim
  refine ⟨C, δ, hC, hδ, fun h hh => ?_⟩
  have h1 := hb h hh
  rwa [B.muVal_zero hd m] at h1

/-! ## `lem:rank-one-parameter-expansions` -/

/-- **`lem:rank-one-parameter-expansions`.**  The four expansions of
`eq:rank-one-parameter-expansions`, on one window and with one constant:

  `u_h = u_* + \frac{5-3d}{6u_*}h² + O_d(h⁴)`,   `Λ_h = \frac{2d³}{3(d-1)}h² + O_d(h⁴)`,
  `α_h = \frac12 + \frac{2d²u_*}{3(d-1)}h + O_d(h³)`,   `r_h = r_* - \frac{2(4d-1)}3h² + O_d(h⁴)`.

The remainders are the paper's: two orders past the leading term, by the parity of the
family (`SingularEndpoint/ConstantGraphonComparison/ParityOrder.lean`). -/
theorem rank_one_parameter_expansions (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      |B.u h - (uStar d + (5 - 3 * (d : ℝ)) / (6 * uStar d) * h ^ 2)| ≤ C * |h| ^ 4 ∧
      |ell (B.p h) - ell (pStar d) - 2 * (d : ℝ) ^ 3 / (3 * ((d : ℝ) - 1)) * h ^ 2|
        ≤ C * |h| ^ 4 ∧
      |B.alph h - (1 / 2 + 2 * (d : ℝ) ^ 2 * uStar d / (3 * ((d : ℝ) - 1)) * h)|
        ≤ C * |h| ^ 3 ∧
      |B.rVal h - (rStar d - 2 * (4 * (d : ℝ) - 1) / 3 * h ^ 2)| ≤ C * |h| ^ 4 := by
  obtain ⟨C₁, δ₁, hC₁, hδ₁, h₁⟩ := u_remainder hd B
  obtain ⟨C₂, δ₂, hC₂, hδ₂, h₂⟩ := lambda_remainder hd B
  obtain ⟨C₃, δ₃, hC₃, hδ₃, h₃⟩ := alph_remainder hd B
  obtain ⟨C₄, δ₄, hC₄, hδ₄, h₄⟩ := rVal_remainder hd B
  refine ⟨max (max C₁ C₂) (max C₃ C₄), min (min δ₁ δ₂) (min δ₃ δ₄),
    lt_of_lt_of_le hC₁ (le_trans (le_max_left _ _) (le_max_left _ _)),
    lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ hδ₄), fun h hh => ?_⟩
  have hh1 : |h| < δ₁ := lt_of_lt_of_le hh (le_trans (min_le_left _ _) (min_le_left _ _))
  have hh2 : |h| < δ₂ := lt_of_lt_of_le hh (le_trans (min_le_left _ _) (min_le_right _ _))
  have hh3 : |h| < δ₃ := lt_of_lt_of_le hh (le_trans (min_le_right _ _) (min_le_left _ _))
  have hh4 : |h| < δ₄ := lt_of_lt_of_le hh (le_trans (min_le_right _ _) (min_le_right _ _))
  have hp3 : (0 : ℝ) ≤ |h| ^ 3 := by positivity
  have hp4 : (0 : ℝ) ≤ |h| ^ 4 := by positivity
  refine ⟨le_trans (h₁ h hh1) ?_, le_trans (h₂ h hh2) ?_, le_trans (h₃ h hh3) ?_,
    le_trans (h₄ h hh4) ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) hp4
  · exact mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _)) hp4
  · exact mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _)) hp3
  · exact mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) hp4

end UpperTailOptimizers
