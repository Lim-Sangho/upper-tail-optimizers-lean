import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.PsiTilde
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilyContinuity

/-!
# The scalar half of the tail-uniform two-point interpolation (Section 5)

A two-node route pairs the distribution integrand `φ(u) = J̃_{p_h}(x̃u)` against
`σ = ν - ν_h`, uniformly in the frozen tail variable `x̃`, through a two-node interpolation
lemma: interpolate `φ` at the two nodes
`s_h, t_h` in the basis `{1, u^d}` and estimate the resulting error `g` pointwise.  The
paper does not state that lemma — the corresponding step inside the proof of
`lem:auxiliary-lagrangian-bound` (the mixed terms) is argued by subtracting the value at the
single point `u_h` and applying the `1/2`-Hölder bound of `lem:continuation-kernel-bounds`, so
its bound carries no logarithmic factor.  The quantitative two-node route formalised here goes
beyond the paper.  Its proof splits into a
*scalar* half — the interpolation itself, the coefficient bounds, the pointwise `δ(u)^{3/4}`
estimate and the well inequality `δ(u)² ≤ |Q_h(u)|` — and a *measure* half, which pairs `g`
against `σ = ν - ν_h` by Hölder.  **This file is the scalar half only**; nothing here mentions
a measure.

Because `x̃ ∈ [0,2]` and `u ∈ [0,2]`, the entropy is evaluated at `x̃u ∈ [0,4]`, so the
*continued* entropy `J̃` is genuinely needed and every statement below is phrased with
`KKTFamily.JpTildeH` (`SingularEndpoint/AuxiliaryLagrangian/PsiTilde.lean`), never with `Jp`.  The dual potential
`Ψ_h` needs the continued entropy for the same reason (`SingularEndpoint/AuxiliaryLagrangian/PsiTilde.lean`).

## The route

The four steps are realised as follows.

* `exists_pow_mul_logMod_le` is the elementary absorption `τ^{1/4}(1 + log⁺(1/τ)) ≤ C` for
  `0 < τ ≤ 3`, rearranged as `τ(1 + log⁺(1/τ)) ≤ C τ^{3/4}`.  It is proved from
  `Real.log_le_sub_one_of_pos` applied to `τ^{-1/4}`, which gives `-log τ ≤ 4τ^{-1/4} - 4`
  and hence the bound with `C = 4`.
* `logMod_le_mul` is the scaling/monotonicity fact `τ ≤ Kσ ⟹ ω(τ) ≤ K ω(σ)` for
  `ω(τ) = τ(1 + log⁺(1/τ))`.  It makes explicit the monotonicity of `ω` that the route uses,
  and is again proved from `Real.log_le_sub_one_of_pos`, this time at `σ/τ`.
* `KKTFamily.exists_JpTildeH_modulus` transfers the logarithmic modulus
  (`exists_JpTilde_modulus`, `SingularEndpoint/AuxiliaryLagrangian/JpTilde.lean`) from `J̃_{p_*}` to `J̃_{p_h}`: the
  displacement `eq:entropy-parameter-shift` is affine with coefficients tending to `0`, and the extra
  `|Λ_h||z-z'|` is absorbed because `1 + log⁺(·) ≥ 1`.
* `KKTFamily.exists_pow_gap_lower` is the node separation `t_h^d - s_h^d ≥ c_d h`.
  It is exact rather than asymptotic: `pow_sub_pow_ge`
  (`NonexceptionalEndpoint/QuadraticGrowth/PowBounds.lean`) gives `s_h^{d-1}(t_h - s_h) ≤ t_h^d - s_h^d` and
  `t_h - s_h = 2h`, so `c_d = 2(u_*/2)^{d-1}` works once `h` is small enough that
  `s_h ≥ u_*/2`.  No degree count is ever performed: `d` is symbolic throughout.

## Contents

* `exists_pow_mul_logMod_le` — the `τ^{1/4}` absorption;
* `KKTFamily.exists_JpTildeH_modulus` — the logarithmic modulus for `J̃_{p_h}`;
* `KKTFamily.exists_pow_gap_lower` — the node separation `t_h^d - s_h^d ≥ c_d h`;
* `KKTFamily.gCoefB`, `.gCoefA`, `.gfun` — the two-node interpolation `B`, `A`, `g`,
  with `gfun_sVal` and `gfun_tVal`;
* `KKTFamily.exists_coef_bound` — `|A|, |B| ≤ C L_h` with `L_h = 1 + log(1/h)`;
* `KKTFamily.exists_gfun_bound` — the pointwise bound
  `|g(u)| ≤ C L_h δ(u)^{3/4}`, `δ(u) = min(|u - s_h|, |u - t_h|)`;
* `KKTFamily.sq_min_dist_le_abs_Qh` — the well inequality `δ(u)² ≤ |Q_h(u)|`;
* `abs_sub_le_add` — `|a - b| ≤ |a| + |b|`, shared with the `Law*` layer.

The measure half of the two-node route (the Hölder step against `ν` and the
`σ = ν - ν_h` decomposition) is not in this file.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

variable {d : ℕ}

/-! ## Two elementary facts about the modulus `ω(τ) = τ(1 + log⁺(1/τ))` -/

/-- **The `τ^{1/4}` absorption.**  There is `C > 0` with

`τ (1 + log⁺(1/τ)) ≤ C τ^{3/4}`   for `0 < τ ≤ 3`,

which is `τ^{1/4}(1 + log⁺(1/τ)) ≤ C` multiplied by `τ^{3/4}`.
`C = 4` works.

Only `0 < τ < 1` carries any content, since `log⁺(1/τ) = 0` for `τ ≥ 1`; both ranges are
covered at once by `Real.log_le_sub_one_of_pos` applied to `τ^{-1/4}`, which gives
`-log τ ≤ 4τ^{-1/4} - 4`, together with `log τ ≤ τ - 1 ≤ 2`. -/
theorem exists_pow_mul_logMod_le : ∃ C : ℝ, 0 < C ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ 3 → τ * (1 + max 0 (Real.log (1 / τ))) ≤ C * τ ^ (3 / 4 : ℝ) := by
  refine ⟨4, by norm_num, ?_⟩
  intro τ hτ0 hτ3
  have hq : (0 : ℝ) < τ ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hτ0 _
  have hlog1 : -(1 / 4 : ℝ) * Real.log τ ≤ τ ^ (-(1 / 4) : ℝ) - 1 := by
    have h := Real.log_le_sub_one_of_pos hq
    rwa [Real.log_rpow hτ0] at h
  have hlog2 : Real.log τ ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos hτ0
    linarith
  have hmax : max 0 (Real.log (1 / τ)) ≤ 3 - Real.log τ := by
    rw [one_div, Real.log_inv]
    exact max_le (by linarith) (by linarith)
  have hstep : 1 + max 0 (Real.log (1 / τ)) ≤ 4 * τ ^ (-(1 / 4) : ℝ) := by linarith
  have hmul : τ * τ ^ (-(1 / 4) : ℝ) = τ ^ (3 / 4 : ℝ) := by
    have h : τ ^ ((1 : ℝ) + -(1 / 4)) = τ ^ (1 : ℝ) * τ ^ (-(1 / 4) : ℝ) :=
      Real.rpow_add hτ0 _ _
    rw [Real.rpow_one] at h
    rw [← h]
    norm_num
  calc τ * (1 + max 0 (Real.log (1 / τ)))
      ≤ τ * (4 * τ ^ (-(1 / 4) : ℝ)) := mul_le_mul_of_nonneg_left hstep hτ0.le
    _ = 4 * (τ * τ ^ (-(1 / 4) : ℝ)) := by ring
    _ = 4 * τ ^ (3 / 4 : ℝ) := by rw [hmul]

/-- **Scaling and monotonicity of the modulus.**  If `0 ≤ τ ≤ Kσ` with `0 < σ` and `1 ≤ K`,
then `ω(τ) ≤ K ω(σ)` for `ω(τ) = τ(1 + log⁺(1/τ))`.

At `K = 1` this is monotonicity of `ω`, used to replace
`ω(2δ(u))` by `Cδ(u)(1 + log⁺(1/δ(u)))`.  Three cases: for `σ ≤ τ` the logarithm is
monotone; for `1 ≤ τ ≤ σ` the positive part vanishes; and for `0 < τ < 1` with `τ ≤ σ` one
splits `log(1/τ) = log(σ/τ) + log(1/σ)` and bounds `τ log(σ/τ) ≤ σ - τ` by
`Real.log_le_sub_one_of_pos`. -/
theorem logMod_le_mul {τ σ K : ℝ} (hτ : 0 ≤ τ) (hσ : 0 < σ) (hK : 1 ≤ K)
    (hle : τ ≤ K * σ) :
    τ * (1 + max 0 (Real.log (1 / τ)))
      ≤ K * (σ * (1 + max 0 (Real.log (1 / σ)))) := by
  have hM0 : (0 : ℝ) ≤ max 0 (Real.log (1 / σ)) := le_max_left _ _
  have hm0 : (0 : ℝ) ≤ max 0 (Real.log (1 / τ)) := le_max_left _ _
  have hσM : 0 ≤ σ * (1 + max 0 (Real.log (1 / σ))) := mul_nonneg hσ.le (by linarith)
  have hKrhs : σ * (1 + max 0 (Real.log (1 / σ)))
      ≤ K * (σ * (1 + max 0 (Real.log (1 / σ)))) := le_mul_of_one_le_left hσM hK
  rcases le_total σ τ with hst | hst
  · have hτ0 : 0 < τ := lt_of_lt_of_le hσ hst
    have hlog : max 0 (Real.log (1 / τ)) ≤ max 0 (Real.log (1 / σ)) :=
      max_le_max le_rfl
        (Real.log_le_log (div_pos zero_lt_one hτ0) (one_div_le_one_div_of_le hσ hst))
    nlinarith [mul_nonneg hτ (sub_nonneg.mpr hlog),
      mul_nonneg (sub_nonneg.mpr hle) (by linarith : (0 : ℝ) ≤ 1 + max 0 (Real.log (1 / σ)))]
  · rcases le_total 1 τ with h1 | h1
    · have hτ0 : 0 < τ := lt_of_lt_of_le zero_lt_one h1
      have hz : max 0 (Real.log (1 / τ)) = 0 :=
        max_eq_left (Real.log_nonpos (div_pos zero_lt_one hτ0).le
          (by rw [div_le_one hτ0]; linarith))
      rw [hz]
      have hσm : 0 ≤ σ * max 0 (Real.log (1 / σ)) := mul_nonneg hσ.le hM0
      nlinarith
    · rcases eq_or_lt_of_le hτ with h0 | hτ0
      · rw [← h0]
        simp only [zero_mul]
        linarith
      · have hlogτ : max 0 (Real.log (1 / τ)) = Real.log (1 / τ) :=
          max_eq_right (Real.log_nonneg (by rw [le_div_iff₀ hτ0]; linarith))
        have hsplit : Real.log (1 / τ) = Real.log (σ / τ) + Real.log (1 / σ) := by
          rw [← Real.log_mul (by positivity) (by positivity)]
          congr 1
          field_simp
        have hbound : Real.log (σ / τ) ≤ σ / τ - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have hmul : τ * Real.log (σ / τ) ≤ σ - τ := by
          have hstep := mul_le_mul_of_nonneg_left hbound hτ0.le
          have he : τ * (σ / τ - 1) = σ - τ := by field_simp
          linarith [he ▸ hstep]
        have hmul2 : τ * Real.log (1 / σ) ≤ σ * max 0 (Real.log (1 / σ)) := by
          have hle' : Real.log (1 / σ) ≤ max 0 (Real.log (1 / σ)) := le_max_right _ _
          nlinarith
        rw [hlogτ, hsplit]
        nlinarith

/-- `|a - b| ≤ |a| + |b|`, in the form used repeatedly below and in the `Law*` layer.
Mathlib's nearest form is `norm_sub_le`, which needs a `Real.norm_eq_abs` bridge. -/
theorem abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  rwa [← sub_eq_add_neg, abs_neg] at h

/-- `|x^d - y^d| ≤ d·2^d·2^d·|x - y|` on `[0,2]`: the factorisation `pow_sub_pow_eq` has `d`
terms, each of which is a product of two powers bounded by `2^d`.  The constant is not
optimal (`d 2^{d-1}` would do), but `d` is symbolic here, so no degree count is
performed and only the *existence* of a constant matters downstream. -/
theorem abs_pow_sub_pow_le_two (d : ℕ) {x y : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2)
    (hy0 : 0 ≤ y) (hy2 : y ≤ 2) :
    |x ^ d - y ^ d| ≤ (d : ℝ) * (2 ^ d * 2 ^ d) * |x - y| := by
  rw [pow_sub_pow_eq, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [abs_of_nonneg (geom_sum₂_nonneg hx0 hy0 d)]
  calc ∑ i ∈ Finset.range d, x ^ i * y ^ (d - 1 - i)
      ≤ ∑ _i ∈ Finset.range d, ((2 : ℝ) ^ d * 2 ^ d) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hxi : x ^ i ≤ (2 : ℝ) ^ d :=
          le_trans (pow_le_pow_left₀ hx0 hx2 i)
            (pow_le_pow_right₀ (by norm_num) (Finset.mem_range.mp hi).le)
        have hyi : y ^ (d - 1 - i) ≤ (2 : ℝ) ^ d :=
          le_trans (pow_le_pow_left₀ hy0 hy2 _)
            (pow_le_pow_right₀ (by norm_num) (by omega))
        exact mul_le_mul hxi hyi (pow_nonneg hy0 _) (by positivity)
    _ = (d : ℝ) * ((2 : ℝ) ^ d * 2 ^ d) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

namespace KKTFamily

/-! ## The displaced entropy: modulus and uniform bound

The two facts about `J̃_{p_h}` that the interpolation consumes.  Both need the affine
displacement of `eq:entropy-parameter-shift` to be small, which is continuity of `h ↦ p_h` at the
singular endpoint (`SingularEndpoint/RankOneStationaryFamily/FamilyContinuity.lean`). -/

/-- **The affine displacement of `eq:entropy-parameter-shift` is uniformly small near `h = 0`.** -/
private theorem exists_shift_small (hd : 2 ≤ d) (B : KKTFamily d) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      |ell (B.p h) - ell (pStar d)| ≤ ε ∧ |Jp (B.p h) 0 - Jp (pStar d) 0| ≤ ε := by
  have h1 : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), |ell (B.p h) - ell (pStar d)| < ε := by
    have h := Metric.tendsto_nhds.mp (ell_p_continuousAt hd B) ε hε
    simpa [Real.dist_eq, B.p_zero] using h
  have h2 : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), |Jp (B.p h) 0 - Jp (pStar d) 0| < ε := by
    have h := Metric.tendsto_nhds.mp (Jp_p_zero_continuousAt hd B) ε hε
    simpa [Real.dist_eq, B.p_zero] using h
  obtain ⟨δ, hδ, hprop⟩ := Metric.eventually_nhds_iff.mp (h1.and h2)
  refine ⟨δ, hδ, fun h hh => ?_⟩
  have hdist : dist h (0 : ℝ) < δ := by rwa [Real.dist_eq, sub_zero]
  exact ⟨(hprop hdist).1.le, (hprop hdist).2.le⟩

/-- **The logarithmic modulus for the displaced entropy.**  There are `C > 0` and
`δ > 0` such that, for `|h| < δ` inside the family window,

`|J̃_{p_h}(z) - J̃_{p_h}(z')| ≤ C |z - z'| (1 + log⁺(1/|z - z'|))`   for `z, z' ∈ [0,4]`.

The displacement `J̃_{p_h} = J̃_{p_*} + Λ_h · + C_h` is affine, so the increment differs from
that of `J̃_{p_*}` by `Λ_h(z - z')`; the constant `C_h` cancels and the linear term is
absorbed because `Λ_h → 0` and `1 + log⁺(·) ≥ 1`. -/
theorem exists_JpTildeH_modulus (hd : 2 ≤ d) (B : KKTFamily d) : ∃ C : ℝ, 0 < C ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → |h| < B.h₀ →
      ∀ z ∈ Set.Icc (0 : ℝ) 4, ∀ z' ∈ Set.Icc (0 : ℝ) 4,
        |B.JpTildeH h z - B.JpTildeH h z'|
          ≤ C * |z - z'| * (1 + max 0 (Real.log (1 / |z - z'|))) := by
  obtain ⟨C, hC, hmod⟩ := exists_JpTilde_modulus (d := d) hd
  obtain ⟨δ, hδ, hshift⟩ := exists_shift_small hd B (show (0 : ℝ) < 1 by norm_num)
  refine ⟨C + 1, by linarith, δ, hδ, ?_⟩
  intro h hhδ _ z hz z' hz'
  have hL := (hshift h hhδ).1
  have hbase := hmod z hz z' hz'
  have hsplit : B.JpTildeH h z - B.JpTildeH h z'
      = (JpTilde d z - JpTilde d z') + (ell (B.p h) - ell (pStar d)) * (z - z') := by
    simp only [JpTildeH]
    ring
  have hmpos : (0 : ℝ) ≤ max 0 (Real.log (1 / |z - z'|)) := le_max_left _ _
  have hterm : |(ell (B.p h) - ell (pStar d)) * (z - z')|
      ≤ 1 * |z - z'| * (1 + max 0 (Real.log (1 / |z - z'|))) := by
    rw [abs_mul, one_mul]
    calc |ell (B.p h) - ell (pStar d)| * |z - z'|
        ≤ 1 * |z - z'| := mul_le_mul_of_nonneg_right hL (abs_nonneg _)
      _ = |z - z'| := one_mul _
      _ ≤ |z - z'| * (1 + max 0 (Real.log (1 / |z - z'|))) := by
          nlinarith [abs_nonneg (z - z')]
  rw [hsplit]
  calc |(JpTilde d z - JpTilde d z') + (ell (B.p h) - ell (pStar d)) * (z - z')|
      ≤ |JpTilde d z - JpTilde d z'| + |(ell (B.p h) - ell (pStar d)) * (z - z')| :=
        abs_add_le _ _
    _ ≤ C * |z - z'| * (1 + max 0 (Real.log (1 / |z - z'|)))
        + 1 * |z - z'| * (1 + max 0 (Real.log (1 / |z - z'|))) := add_le_add hbase hterm
    _ = (C + 1) * |z - z'| * (1 + max 0 (Real.log (1 / |z - z'|))) := by ring

/-- `J̃_{p_*}` is bounded on the compact `[0,4]`. -/
private theorem exists_JpTilde_bound (hd : 2 ≤ d) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ Set.Icc (0 : ℝ) 4, |JpTilde d z| ≤ M := by
  obtain ⟨z₀, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 4)) (continuousOn_JpTilde hd).abs
  refine ⟨|JpTilde d z₀| + 1, by positivity, fun z hz => ?_⟩
  have h := isMaxOn_iff.mp hmax z hz
  linarith

/-- **A uniform sup bound for the displaced entropy on `[0,4]`**, needed for the constant
coefficient `A` of the interpolation. -/
private theorem exists_JpTildeH_bound (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      ∀ z ∈ Set.Icc (0 : ℝ) 4, |B.JpTildeH h z| ≤ M := by
  obtain ⟨M, hM, hbd⟩ := exists_JpTilde_bound (d := d) hd
  obtain ⟨δ, hδ, hshift⟩ := exists_shift_small hd B (show (0 : ℝ) < 1 by norm_num)
  refine ⟨M + 5, by linarith, δ, hδ, ?_⟩
  intro h hh z hz
  have h1 := hbd z hz
  have h2 := (hshift h hh).1
  have h3 := (hshift h hh).2
  have hz4 : |z| ≤ 4 := by
    rw [abs_of_nonneg hz.1]
    exact hz.2
  have hterm : |(ell (B.p h) - ell (pStar d)) * z| ≤ 4 := by
    rw [abs_mul]
    calc |ell (B.p h) - ell (pStar d)| * |z|
        ≤ 1 * 4 := mul_le_mul h2 hz4 (abs_nonneg z) zero_le_one
      _ = 4 := by norm_num
  have htri1 := abs_add_le (JpTilde d z + (ell (B.p h) - ell (pStar d)) * z)
    (Jp (B.p h) 0 - Jp (pStar d) 0)
  have htri2 := abs_add_le (JpTilde d z) ((ell (B.p h) - ell (pStar d)) * z)
  rw [JpTildeH]
  linarith

/-! ## The two-node interpolation -/

/-- **The `u^d` coefficient of the two-node tail interpolation**:
`B = (φ(t_h) - φ(s_h))/(t_h^d - s_h^d)` with `φ(u) = J̃_{p_h}(x̃u)`. -/
noncomputable def gCoefB (B : KKTFamily d) (h xt : ℝ) : ℝ :=
  (B.JpTildeH h (xt * B.tVal h) - B.JpTildeH h (xt * B.sVal h))
    / (B.tVal h ^ d - B.sVal h ^ d)

/-- **The constant coefficient of the two-node interpolation**:
`A = φ(s_h) - B s_h^d`. -/
noncomputable def gCoefA (B : KKTFamily d) (h xt : ℝ) : ℝ :=
  B.JpTildeH h (xt * B.sVal h) - B.gCoefB h xt * B.sVal h ^ d

/-- **The interpolation error** `g(u) = φ(u) - A - B u^d` of the two-node tail
interpolation, with `φ(u) = J̃_{p_h}(x̃u)`. -/
noncomputable def gfun (B : KKTFamily d) (h xt u : ℝ) : ℝ :=
  B.JpTildeH h (xt * u) - B.gCoefA h xt - B.gCoefB h xt * u ^ d

/-- `g` vanishes at the lower node.  This is the definition of `A` and needs no hypothesis. -/
theorem gfun_sVal (B : KKTFamily d) (h xt : ℝ) : B.gfun h xt (B.sVal h) = 0 := by
  simp only [gfun, gCoefA]
  ring

/-- `g` vanishes at the upper node.  Here the definition of `B` is used, so the two nodes
must be distinct: `t_h - s_h = 2h > 0` and `0 < s_h`, hence `s_h^d < t_h^d`. -/
theorem gfun_tVal (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hpos : 0 < h)
    (hh : |h| < B.h₀) (xt : ℝ) : B.gfun h xt (B.tVal h) = 0 := by
  have hs0 := sVal_pos hh
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hpos
  have hne : B.tVal h ^ d - B.sVal h ^ d ≠ 0 := by
    have h := pow_lt_pow_left₀ hst hs0.le (show d ≠ 0 by omega)
    intro hcontra
    linarith [sub_eq_zero.mp hcontra]
  have hkey : B.gCoefB h xt * (B.tVal h ^ d - B.sVal h ^ d)
      = B.JpTildeH h (xt * B.tVal h) - B.JpTildeH h (xt * B.sVal h) := by
    rw [gCoefB]
    field_simp
  simp only [gfun, gCoefA]
  linarith

/-! ## The node separation `t_h^d - s_h^d ≥ c_d h` -/

/-- **The node separation.**  There are `c > 0` and `δ > 0`
with `c h ≤ t_h^d - s_h^d` for `0 < h < δ` inside the family window.

Exact rather than asymptotic: `pow_sub_pow_ge` gives `s_h^{d-1}(t_h - s_h) ≤ t_h^d - s_h^d`,
`t_h - s_h = 2h`, and `s_h ≥ u_*/2` once `h` is small, so `c = 2(u_*/2)^{d-1}` works.  No
degree count occurs — `d` is symbolic. -/
theorem exists_pow_gap_lower (hd : 2 ≤ d) (B : KKTFamily d) : ∃ c : ℝ, 0 < c ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → |h| < B.h₀ →
      c * h ≤ B.tVal h ^ d - B.sVal h ^ d := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hcu : ContinuousAt B.u 0 := u_continuousAt B
  have hev : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), |B.u h - uStar d| < uStar d / 4 := by
    have h := Metric.tendsto_nhds.mp hcu (uStar d / 4) (by linarith)
    simpa [Real.dist_eq, B.u_zero] using h
  obtain ⟨δ₁, hδ₁, hprop⟩ := Metric.eventually_nhds_iff.mp hev
  have hcpos : 0 < 2 * (uStar d / 2) ^ (d - 1) := by
    have h := pow_pos (show (0 : ℝ) < uStar d / 2 by linarith) (d - 1)
    linarith
  refine ⟨2 * (uStar d / 2) ^ (d - 1), hcpos, min δ₁ (uStar d / 4),
    lt_min hδ₁ (by linarith), ?_⟩
  intro h hh0 hhδ hhb
  have hdist : dist h (0 : ℝ) < δ₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
    exact lt_of_lt_of_le hhδ (min_le_left _ _)
  have h2 : h < uStar d / 4 := lt_of_lt_of_le hhδ (min_le_right _ _)
  have hu := abs_lt.mp (hprop hdist)
  have hus : uStar d / 2 ≤ B.sVal h := by
    simp only [sVal]
    linarith [hu.1]
  have hs0 : (0 : ℝ) < B.sVal h := lt_of_lt_of_le (by linarith) hus
  have hgap : B.tVal h - B.sVal h = 2 * h := by
    simp only [sVal, tVal]
    ring
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hh0
  have hpowle : B.sVal h ^ d ≤ B.tVal h ^ d := pow_le_pow_left₀ hs0.le hst.le d
  have hkey := pow_sub_pow_ge (x := B.tVal h) (y := B.sVal h) (by linarith) hs0.le
    (show 1 ≤ d by omega)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ B.tVal h - B.sVal h),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ B.tVal h ^ d - B.sVal h ^ d), hgap] at hkey
  have hpw : (uStar d / 2) ^ (d - 1) ≤ B.sVal h ^ (d - 1) :=
    pow_le_pow_left₀ (by linarith) hus (d - 1)
  have hfin : (uStar d / 2) ^ (d - 1) * (2 * h) ≤ B.sVal h ^ (d - 1) * (2 * h) :=
    mul_le_mul_of_nonneg_right hpw (by linarith)
  linarith

/-! ## The coefficient bounds -/

/-- **`|A|, |B| ≤ C L_h`** with `L_h = 1 + log(1/h)`, the coefficient bound.

For `B` the modulus of `exists_JpTildeH_modulus` bounds the numerator by `ω(2x̃h) ≤ 4ω(h)`
(`logMod_le_mul`, with `x̃ ≤ 2`), and `exists_pow_gap_lower` bounds the denominator below by
`c h`; the `h` cancels and leaves `L_h`.  For `A` one adds `|φ(s_h)| ≤ M` from the uniform
sup bound and uses `s_h^d ≤ 1` together with `L_h ≥ 1`. -/
theorem exists_coef_bound (hd : 2 ≤ d) (B : KKTFamily d) : ∃ C : ℝ, 0 < C ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → |h| < B.h₀ →
      ∀ xt ∈ Set.Icc (0 : ℝ) 2,
        |B.gCoefA h xt| ≤ C * (1 + Real.log (1 / h)) ∧
          |B.gCoefB h xt| ≤ C * (1 + Real.log (1 / h)) := by
  obtain ⟨CJ, hCJ, δJ, hδJ, hmod⟩ := exists_JpTildeH_modulus hd B
  obtain ⟨c₀, hc₀, δg, hδg, hgap⟩ := exists_pow_gap_lower hd B
  obtain ⟨M, hM, δM, hδM, hMbd⟩ := exists_JpTildeH_bound hd B
  have hCB : 0 < 4 * CJ / c₀ := div_pos (by linarith) hc₀
  refine ⟨M + 4 * CJ / c₀, by linarith, min (min δJ δg) (min δM 1),
    lt_min (lt_min hδJ hδg) (lt_min hδM one_pos), ?_⟩
  intro h hh0 hhδ hhb xt hxt
  have hJ : |h| < δJ := by
    rw [abs_of_pos hh0]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hg : h < δg := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hMδ : |h| < δM := by
    rw [abs_of_pos hh0]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hh1 : h < 1 := lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hlog0 : 0 ≤ Real.log (1 / h) := by
    rw [one_div, Real.log_inv, neg_nonneg]
    exact Real.log_nonpos hh0.le hh1.le
  have hs0 := sVal_pos hhb
  have hs1 := sVal_lt_one hhb
  have ht0 := tVal_pos hhb
  have ht1 := tVal_lt_one hhb
  have hxt0 : (0 : ℝ) ≤ xt := hxt.1
  have hxt2 : xt ≤ 2 := hxt.2
  have hzt : xt * B.tVal h ∈ Set.Icc (0 : ℝ) 4 :=
    ⟨mul_nonneg hxt0 ht0.le, by nlinarith [mul_le_mul_of_nonneg_left ht1.le hxt0]⟩
  have hzs : xt * B.sVal h ∈ Set.Icc (0 : ℝ) 4 :=
    ⟨mul_nonneg hxt0 hs0.le, by nlinarith [mul_le_mul_of_nonneg_left hs1.le hxt0]⟩
  have hgp := hgap h hh0 hg hhb
  have hden : 0 < B.tVal h ^ d - B.sVal h ^ d := by nlinarith
  -- the numerator of `B`, through the modulus and the scaling `logMod_le_mul`
  have habsdiff : |xt * B.tVal h - xt * B.sVal h| = xt * (2 * h) := by
    have he : xt * B.tVal h - xt * B.sVal h = xt * (2 * h) := by
      simp only [sVal, tVal]
      ring
    rw [he, abs_of_nonneg (mul_nonneg hxt0 (by linarith))]
  have hmono := logMod_le_mul (τ := xt * (2 * h)) (σ := h) (K := 4)
    (mul_nonneg hxt0 (by linarith)) hh0 (by norm_num) (by nlinarith)
  have hmaxh : max 0 (Real.log (1 / h)) = Real.log (1 / h) := max_eq_right hlog0
  rw [hmaxh] at hmono
  have hnum : |B.JpTildeH h (xt * B.tVal h) - B.JpTildeH h (xt * B.sVal h)|
      ≤ 4 * CJ * (h * (1 + Real.log (1 / h))) := by
    have hbase := hmod h hJ hhb _ hzt _ hzs
    rw [habsdiff] at hbase
    have hstep : CJ * (xt * (2 * h) * (1 + max 0 (Real.log (1 / (xt * (2 * h))))))
        ≤ CJ * (4 * (h * (1 + Real.log (1 / h)))) :=
      mul_le_mul_of_nonneg_left hmono hCJ.le
    linarith
  -- the bound on `B`
  have hLnn : (0 : ℝ) ≤ 1 + Real.log (1 / h) := by linarith
  have hBbound : |B.gCoefB h xt| ≤ 4 * CJ / c₀ * (1 + Real.log (1 / h)) := by
    rw [gCoefB, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have hstep : 4 * CJ / c₀ * (1 + Real.log (1 / h)) * (c₀ * h)
        = 4 * CJ * (h * (1 + Real.log (1 / h))) := by
      field_simp
    calc |B.JpTildeH h (xt * B.tVal h) - B.JpTildeH h (xt * B.sVal h)|
        ≤ 4 * CJ * (h * (1 + Real.log (1 / h))) := hnum
      _ = 4 * CJ / c₀ * (1 + Real.log (1 / h)) * (c₀ * h) := hstep.symm
      _ ≤ 4 * CJ / c₀ * (1 + Real.log (1 / h)) * (B.tVal h ^ d - B.sVal h ^ d) :=
          mul_le_mul_of_nonneg_left hgp (mul_nonneg hCB.le hLnn)
  -- the bound on `A`
  have hsd : |B.sVal h ^ d| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hs0.le d)]
    exact pow_le_one₀ hs0.le hs1.le
  have hAbound : |B.gCoefA h xt| ≤ (M + 4 * CJ / c₀) * (1 + Real.log (1 / h)) := by
    have hφs : |B.JpTildeH h (xt * B.sVal h)| ≤ M := hMbd h hMδ _ hzs
    have hprod : |B.gCoefB h xt * B.sVal h ^ d| ≤ 4 * CJ / c₀ * (1 + Real.log (1 / h)) := by
      rw [abs_mul]
      calc |B.gCoefB h xt| * |B.sVal h ^ d|
          ≤ (4 * CJ / c₀ * (1 + Real.log (1 / h))) * 1 :=
            mul_le_mul hBbound hsd (abs_nonneg _) (mul_nonneg hCB.le hLnn)
        _ = 4 * CJ / c₀ * (1 + Real.log (1 / h)) := mul_one _
    have htri := abs_sub_le_add (B.JpTildeH h (xt * B.sVal h))
      (B.gCoefB h xt * B.sVal h ^ d)
    rw [gCoefA]
    nlinarith
  refine ⟨hAbound, ?_⟩
  nlinarith

/-! ## The pointwise bound on the interpolation error -/

/-- **The pointwise bound on the interpolation error.**  There are `C > 0` and
`δ > 0` such that, for `0 < h < δ` inside the family window, every `x̃ ∈ [0,2]` and every
`u ∈ [0,2]`,

`|g(u)| ≤ C (1 + log(1/h)) δ(u)^{3/4}`,  `δ(u) = min(|u - s_h|, |u - t_h|)`.

The route: `g` vanishes at both nodes, so `|g(u)| = |g(u) - g(u₀)|` for the
nearer node `u₀`; the entropy increment is controlled by the modulus at `x̃δ(u) ≤ 2δ(u)`
(`exists_JpTildeH_modulus` and `logMod_le_mul`), the polynomial increment by
`|u^d - u₀^d| ≤ C_d δ(u)` (`abs_pow_sub_pow_le_two`) times the coefficient bound
`exists_coef_bound`, and finally `exists_pow_mul_logMod_le` converts
`δ(1 + log⁺(1/δ))` into `Cδ^{3/4}` — legitimately, since `δ(u) ≤ 2 ≤ 3` because the nodes
lie in `(0,1)`. -/
theorem exists_gfun_bound (hd : 2 ≤ d) (B : KKTFamily d) : ∃ C : ℝ, 0 < C ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → |h| < B.h₀ →
      ∀ xt ∈ Set.Icc (0 : ℝ) 2, ∀ u ∈ Set.Icc (0 : ℝ) 2,
        |B.gfun h xt u|
          ≤ C * (1 + Real.log (1 / h))
              * (min |u - B.sVal h| |u - B.tVal h|) ^ (3 / 4 : ℝ) := by
  obtain ⟨C₁, hC₁, hpow⟩ := exists_pow_mul_logMod_le
  obtain ⟨CJ, hCJ, δJ, hδJ, hmod⟩ := exists_JpTildeH_modulus hd B
  obtain ⟨CC, hCC, δC, hδC, hcoef⟩ := exists_coef_bound hd B
  have hMd : (0 : ℝ) < (d : ℝ) * (2 ^ d * 2 ^ d) := by
    have : (0 : ℝ) < (d : ℝ) := dpos hd
    positivity
  have hCpos : 0 < 2 * CJ * C₁ + CC * ((d : ℝ) * (2 ^ d * 2 ^ d)) * C₁ := by
    have h1 : 0 < 2 * CJ * C₁ := by positivity
    have h2 : 0 < CC * ((d : ℝ) * (2 ^ d * 2 ^ d)) * C₁ := by positivity
    linarith
  refine ⟨2 * CJ * C₁ + CC * ((d : ℝ) * (2 ^ d * 2 ^ d)) * C₁, hCpos,
    min (min δJ δC) 1, lt_min (lt_min hδJ hδC) one_pos, ?_⟩
  intro h hh0 hhδ hhb xt hxt u hu
  have hJ : |h| < δJ := by
    rw [abs_of_pos hh0]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hC : h < δC := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hh1 : h < 1 := lt_of_lt_of_le hhδ (min_le_right _ _)
  have hlog0 : 0 ≤ Real.log (1 / h) := by
    rw [one_div, Real.log_inv, neg_nonneg]
    exact Real.log_nonpos hh0.le hh1.le
  have hs0 := sVal_pos hhb
  have hs1 := sVal_lt_one hhb
  have ht0 := tVal_pos hhb
  have ht1 := tVal_lt_one hhb
  have hcb := (hcoef h hh0 hC hhb xt hxt).2
  have hxt0 : (0 : ℝ) ≤ xt := hxt.1
  have hxt2 : xt ≤ 2 := hxt.2
  have hu0 : (0 : ℝ) ≤ u := hu.1
  have hu2 : u ≤ 2 := hu.2
  have hmz : xt * u ∈ Set.Icc (0 : ℝ) 4 :=
    ⟨mul_nonneg hxt0 hu0, by nlinarith [mul_le_mul hxt2 hu2 hu0 (by norm_num : (0 : ℝ) ≤ 2)]⟩
  -- the estimate at a node, stated for an arbitrary node so that both cases share it
  have key : ∀ u₀ : ℝ, 0 < u₀ → u₀ < 1 → B.gfun h xt u₀ = 0 →
      |B.gfun h xt u|
        ≤ (2 * CJ * C₁ + CC * ((d : ℝ) * (2 ^ d * 2 ^ d)) * C₁) * (1 + Real.log (1 / h))
            * |u - u₀| ^ (3 / 4 : ℝ) := by
    intro u₀ hu₀0 hu₀1 hzero
    have hmz₀ : xt * u₀ ∈ Set.Icc (0 : ℝ) 4 :=
      ⟨mul_nonneg hxt0 hu₀0.le,
        by nlinarith [mul_le_mul_of_nonneg_left hu₀1.le hxt0]⟩
    rcases eq_or_lt_of_le (abs_nonneg (u - u₀)) with hz0 | hzpos
    · have hueq : u = u₀ := by
        have h := abs_eq_zero.mp hz0.symm
        linarith
      have hgz : B.gfun h xt u = 0 := by rw [hueq]; exact hzero
      have hrz : |u - u₀| ^ (3 / 4 : ℝ) = 0 := by
        rw [hueq, sub_self, abs_zero, Real.zero_rpow (by norm_num)]
      rw [hgz, abs_zero, hrz, mul_zero]
    · have hsplit : B.gfun h xt u
          = (B.JpTildeH h (xt * u) - B.JpTildeH h (xt * u₀))
            - B.gCoefB h xt * (u ^ d - u₀ ^ d) := by
        simp only [gfun] at hzero ⊢
        linarith
      have hdle : |u - u₀| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hτ : |xt * u - xt * u₀| = xt * |u - u₀| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hxt0]
      have hτle : xt * |u - u₀| ≤ 2 * |u - u₀| :=
        mul_le_mul_of_nonneg_right hxt2 (abs_nonneg _)
      have hmono := logMod_le_mul (mul_nonneg hxt0 (abs_nonneg (u - u₀))) hzpos
        (by norm_num : (1 : ℝ) ≤ 2) hτle
      have hpw := hpow |u - u₀| hzpos (by linarith)
      have hX : (0 : ℝ) ≤ |u - u₀| ^ (3 / 4 : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
      -- the entropy increment
      have hbase' : |B.JpTildeH h (xt * u) - B.JpTildeH h (xt * u₀)|
          ≤ CJ * (xt * |u - u₀| * (1 + max 0 (Real.log (1 / (xt * |u - u₀|))))) := by
        have hb := hmod h hJ hhb _ hmz _ hmz₀
        rw [hτ] at hb
        linarith
      have hA : CJ * (xt * |u - u₀| * (1 + max 0 (Real.log (1 / (xt * |u - u₀|)))))
          ≤ CJ * (2 * (|u - u₀| * (1 + max 0 (Real.log (1 / |u - u₀|))))) :=
        mul_le_mul_of_nonneg_left hmono hCJ.le
      have hB2 : CJ * (2 * (|u - u₀| * (1 + max 0 (Real.log (1 / |u - u₀|)))))
          ≤ CJ * (2 * (C₁ * |u - u₀| ^ (3 / 4 : ℝ))) := by
        have h := mul_le_mul_of_nonneg_left hpw (by linarith : (0 : ℝ) ≤ 2 * CJ)
        linarith
      have hstep1 : |B.JpTildeH h (xt * u) - B.JpTildeH h (xt * u₀)|
          ≤ 2 * CJ * C₁ * |u - u₀| ^ (3 / 4 : ℝ) := by linarith
      -- the polynomial increment
      have hδle : |u - u₀| ≤ C₁ * |u - u₀| ^ (3 / 4 : ℝ) := by
        have hm : (0 : ℝ) ≤ max 0 (Real.log (1 / |u - u₀|)) := le_max_left _ _
        nlinarith [mul_nonneg (abs_nonneg (u - u₀)) hm]
      have hpowb : |u ^ d - u₀ ^ d| ≤ (d : ℝ) * (2 ^ d * 2 ^ d) * |u - u₀| :=
        abs_pow_sub_pow_le_two d hu0 hu2 hu₀0.le (by linarith)
      have hcoefb : |B.gCoefB h xt * (u ^ d - u₀ ^ d)|
          ≤ CC * ((d : ℝ) * (2 ^ d * 2 ^ d)) * C₁ * (1 + Real.log (1 / h))
              * |u - u₀| ^ (3 / 4 : ℝ) := by
        rw [abs_mul]
        calc |B.gCoefB h xt| * |u ^ d - u₀ ^ d|
            ≤ CC * (1 + Real.log (1 / h)) * ((d : ℝ) * (2 ^ d * 2 ^ d) * |u - u₀|) :=
              mul_le_mul hcb hpowb (abs_nonneg _)
                (mul_nonneg hCC.le (by linarith))
          _ ≤ CC * (1 + Real.log (1 / h))
                * ((d : ℝ) * (2 ^ d * 2 ^ d) * (C₁ * |u - u₀| ^ (3 / 4 : ℝ))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hδle hMd.le)
                (mul_nonneg hCC.le (by linarith))
          _ = CC * ((d : ℝ) * (2 ^ d * 2 ^ d)) * C₁ * (1 + Real.log (1 / h))
                * |u - u₀| ^ (3 / 4 : ℝ) := by ring
      rw [hsplit]
      have htri := abs_sub_le_add (B.JpTildeH h (xt * u) - B.JpTildeH h (xt * u₀))
        (B.gCoefB h xt * (u ^ d - u₀ ^ d))
      have hslack : (0 : ℝ) ≤ 2 * CJ * C₁ * |u - u₀| ^ (3 / 4 : ℝ) * Real.log (1 / h) :=
        mul_nonneg (mul_nonneg (by positivity) hX) hlog0
      linarith
  rcases le_total |u - B.sVal h| |u - B.tVal h| with hc | hc
  · rw [min_eq_left hc]
    exact key (B.sVal h) hs0 hs1 (B.gfun_sVal h xt)
  · rw [min_eq_right hc]
    exact key (B.tVal h) ht0 ht1 (gfun_tVal hd B hh0 hhb xt)

/-! ## The well inequality -/

/-- **The well inequality `δ(u)² ≤ |Q_h(u)|`**, where
`Q_h(u) = (u - s_h)(u - t_h)` and `δ(u) = min(|u - s_h|, |u - t_h|)`.

A case split on whether `u` lies between the nodes is
unnecessary, because `|Q_h(u)| = |u - s_h| · |u - t_h|` and the minimum of two nonnegative
reals has square at most their product.  Consequently the hypothesis `0 < h` — which a case
split would use through `t_h - s_h = 2h > 0` — is not consumed, and is kept only to
record the intended regime. -/
theorem sq_min_dist_le_abs_Qh (B : KKTFamily d) {h : ℝ} (_hpos : 0 < h) (u : ℝ) :
    (min |u - B.sVal h| |u - B.tVal h|) ^ 2 ≤ |B.Qh h u| := by
  have h1 : min |u - B.sVal h| |u - B.tVal h| ≤ |u - B.sVal h| := min_le_left _ _
  have h2 : min |u - B.sVal h| |u - B.tVal h| ≤ |u - B.tVal h| := min_le_right _ _
  have h0 : (0 : ℝ) ≤ min |u - B.sVal h| |u - B.tVal h| :=
    le_min (abs_nonneg _) (abs_nonneg _)
  rw [Qh, abs_mul, sq]
  exact mul_le_mul h1 h2 h0 (abs_nonneg _)

end KKTFamily

end SingularEndpoint

end UpperTailOptimizers
