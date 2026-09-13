import UpperTailOptimizers.SingularEndpoint.LagrangeBridge
import UpperTailOptimizers.SingularEndpoint.ContinuationKernelBounds
import UpperTailOptimizers.SingularEndpoint.ParameterRemainders

/-!
# The auxiliary Lagrangian of `sec:auxiliary-lagrangian` and the linear moment correction

`sec:auxiliary-lagrangian` (`paper/sections/singular_auxiliary_lagrangian.tex`) works with the
auxiliary Lagrangian

`𝓛_h(ξ) = 𝒥_h(ξ) - μ_h{m_d(ξ)^v - q_h^v}`,   `𝒥_h(ξ) = ∬ K_h dξ dξ`,   `m_d(ξ) = ∫ x^d dξ`,

for probability measures `ξ` on `[0,2]`.  The distribution-level estimates of the Lean
development subtract instead the linear moment term `η_h Δ_h(ξ)`, `Δ_h(ξ) = m_d(ξ) - q_h`,
with `η_h = 2γ_h q_h/d = μ_h v q_h^{v-1}` (`KKTFamily.etaVal_eq_muVal`).  The two differ by the
Taylor remainder `μ_h{(q_h + Δ)^v - q_h^v - v q_h^{v-1}Δ}`, which `abs_pow_sub_taylor_le`
bounds by `|μ_h| v² (2^d)^{2v} Δ²` because `m_d(ξ), q_h ∈ [0, 2^d]`.

## Contents

* `integral_pow_mem_Icc_of_support` — `m_d(ξ) ∈ [0, 2^d]` for `ξ` carried by `[0,2]`;
* `KKTFamily.auxLagrangian` — `𝓛_h`, with `auxLagrangian_distributionMeasure`
  (`𝓛_h(ν_h) = 𝒥_h(ν_h)`, since `m_d(ν_h) = q_h`);
* `KKTFamily.exists_abs_muVal_le` — `|μ_h|` is bounded near `h = 0`;
* `KKTFamily.nonlinear_correction_ge` — the scalar conversion with its explicit remainder;
* `KKTFamily.auxLagrangian_gap_ge` — `𝓛_h(ξ) - 𝓛_h(ν_h)` is at least the linear gap minus
  `|μ_h| v² (2^d)^{2v} Δ_h(ξ)²`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory Filter Topology

variable {d : ℕ}

/-- **`m_d(ξ) ∈ [0, 2^d]`** for a probability measure `ξ` carried by `[0,2]`. -/
theorem integral_pow_mem_Icc_of_support {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) (d : ℕ) :
    (∫ x, x ^ d ∂ν) ∈ Set.Icc (0 : ℝ) (2 ^ d) := by
  have hae : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 2 := by
    rw [ae_iff]
    exact hν
  have hbd : ∀ᵐ x ∂ν, ‖x ^ d‖ ≤ (2 : ℝ) ^ d := by
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1 d)]
    exact pow_le_pow_left₀ hx.1 hx.2 d
  have hint : Integrable (fun x : ℝ => x ^ d) ν :=
    (integrable_const ((2 : ℝ) ^ d)).mono' (continuous_pow d).aestronglyMeasurable hbd
  constructor
  · exact integral_nonneg_of_ae (hae.mono fun x hx => pow_nonneg hx.1 d)
  · have h := integral_mono_ae hint (integrable_const ((2 : ℝ) ^ d))
      (hae.mono fun x hx => pow_le_pow_left₀ hx.1 hx.2 d)
    simpa using h

namespace KKTFamily

/-- **The auxiliary Lagrangian** `𝓛_h(ξ) = 𝒥_h(ξ) - μ_h{m_d(ξ)^v - q_h^v}` of
`sec:auxiliary-lagrangian`, for `v = n` and `m` the number of edges. -/
noncomputable def auxLagrangian (B : KKTFamily d) (m : ℝ) (n : ℕ) (h : ℝ) (ν : Measure ℝ) : ℝ :=
  B.distributionJ h ν - B.muVal m h * ((∫ x, x ^ d ∂ν) ^ n - B.qVal h ^ n)

/-- `𝓛_h(ν_h) = 𝒥_h(ν_h)`: the constraint term vanishes at the candidate. -/
theorem auxLagrangian_distributionMeasure (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    (m : ℝ) (n : ℕ) :
    B.auxLagrangian m n h (B.distributionMeasure h) = B.distributionJ h (B.distributionMeasure h) := by
  rw [auxLagrangian, integral_pow_distributionMeasure B hh, sub_self, mul_zero, sub_zero]

/-- `|μ_h|` is bounded near `h = 0`: `μ_h` is analytic at `0`. -/
theorem exists_abs_muVal_le (B : KKTFamily d) {m : ℝ} (hm : 0 < m) :
    ∃ Cμ δ : ℝ, 0 < Cμ ∧ 0 < δ ∧ ∀ h : ℝ, |h| < δ → |B.muVal m h| ≤ Cμ := by
  have hc := (analyticAt_muVal B hm).continuousAt
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hc 1 one_pos
  refine ⟨|B.muVal m 0| + 1, δ, by positivity, hδ, fun h hh => ?_⟩
  have h1 := hball (show dist h 0 < δ by rwa [Real.dist_eq, sub_zero])
  rw [Real.dist_eq] at h1
  have h2 := abs_sub_abs_le_abs_sub (B.muVal m h) (B.muVal m 0)
  linarith

/-- **From the linear moment correction to the nonlinear Lagrangian correction.**  For
`a ∈ [0,2^d]`, `n ≥ 2` and `2m = nd`,

`G - μ_h(aⁿ - q_hⁿ) ≥ (G - η_h(a - q_h)) - |μ_h| n² (2^d)^{2n} (a - q_h)²`.

The remainder is `μ_h{aⁿ - q_hⁿ - n q_h^{n-1}(a - q_h)}`, bounded by `abs_pow_sub_taylor_le`,
and `η_h = μ_h n q_h^{n-1}` is `etaVal_eq_muVal`. -/
theorem nonlinear_correction_ge (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    {n : ℕ} {m : ℝ} (hm : 0 < m) (hn : 2 * m = (n : ℝ) * (d : ℝ)) (hn2 : 2 ≤ n)
    {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) (2 ^ d)) (G : ℝ) :
    (G - B.etaVal h * (a - B.qVal h))
        - |B.muVal m h| * ((n : ℝ) ^ 2 * (2 ^ d) ^ (2 * n) * (a - B.qVal h) ^ 2)
      ≤ G - B.muVal m h * (a ^ n - B.qVal h ^ n) := by
  have hq0 := qVal_pos hh
  have hq1 := qVal_lt_one hd hh
  have hM : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hT := abs_pow_sub_taylor_le hM ha.1 ha.2 hq0.le (by linarith) n
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have heta := etaVal_eq_muVal B hh hm hn hd0 hn2
  have hsplit : B.muVal m h * (a ^ n - B.qVal h ^ n)
      = B.etaVal h * (a - B.qVal h)
        + B.muVal m h * (a ^ n - B.qVal h ^ n - (n : ℝ) * B.qVal h ^ (n - 1) * (a - B.qVal h)) := by
    rw [heta]
    ring
  have hR : |B.muVal m h * (a ^ n - B.qVal h ^ n - (n : ℝ) * B.qVal h ^ (n - 1) * (a - B.qVal h))|
      ≤ |B.muVal m h| * ((n : ℝ) ^ 2 * (2 ^ d) ^ (2 * n) * (a - B.qVal h) ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hT (abs_nonneg _)
  have hneg := le_abs_self
    (B.muVal m h * (a ^ n - B.qVal h ^ n - (n : ℝ) * B.qVal h ^ (n - 1) * (a - B.qVal h)))
  rw [hsplit]
  linarith

/-- **`𝓛_h(ξ) - 𝓛_h(ν_h)` versus the linear moment gap.**  For a probability measure `ξ`
carried by `[0,2]`,

`𝓛_h(ξ) - 𝓛_h(ν_h) ≥ [𝒥_h(ξ) - 𝒥_h(ν_h) - η_hΔ_h(ξ)] - |μ_h| n² (2^d)^{2n} Δ_h(ξ)²`. -/
theorem auxLagrangian_gap_ge (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    {n : ℕ} {m : ℝ} (hm : 0 < m) (hn : 2 * m = (n : ℝ) * (d : ℝ)) (hn2 : 2 ≤ n)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) :
    (B.distributionJ h ν - B.distributionJ h (B.distributionMeasure h)
          - B.etaVal h * ((∫ x, x ^ d ∂ν) - B.qVal h))
        - |B.muVal m h| * ((n : ℝ) ^ 2 * (2 ^ d) ^ (2 * n) * ((∫ x, x ^ d ∂ν) - B.qVal h) ^ 2)
      ≤ B.auxLagrangian m n h ν - B.auxLagrangian m n h (B.distributionMeasure h) := by
  rw [auxLagrangian_distributionMeasure B hh, auxLagrangian]
  have h1 := nonlinear_correction_ge hd B hh hm hn hn2 (integral_pow_mem_Icc_of_support hν d)
    (B.distributionJ h ν - B.distributionJ h (B.distributionMeasure h))
  linarith

end KKTFamily

end SingularEndpoint

end UpperTailOptimizers
