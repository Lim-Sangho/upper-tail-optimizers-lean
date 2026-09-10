import UpperTailOptimizers.SingularEndpoint.RowWindow
import UpperTailOptimizers.SingularEndpoint.TailScalar

/-!
# Step 3 of `lem:graphon-lagrangian-bound`: the row collapse (Section 7, `paper/singular_endpoint.tex`)

Step 3 of the proof of `lem:graphon-lagrangian-bound` (Section 7.5) controls the part
of the entropy comparison that lives *outside* the central square `Ω_ρ(f)²`: the two mixed
rectangles `Ω_ρ(f)^c × Ω_ρ(f)` and the tail–tail square `(Ω_ρ(f)^c)²`.  Neither is asked to
produce a gain; both are only kept from costing more than a fixed fraction of the `b_ρ ε_ρ(ν)`
that `lem:auxiliary-lagrangian-bound` supplies at rank-one level.

The mixed rectangles are handled by **collapsing the row to a single average**.  For almost
every `x`, the Factor orthogonality `eq:rank-one-orthogonality`, `T_E(f^{d-1}) = 0`,
bounds the row integral of the residual,

`u_*^{d-1}|∫_{Ω_ρ(f)}E(x,y)dy| ≤ C_{d,m,ρ}h`,

so the row average `W̄_x = |Ω_ρ(f)|^{-1}∫_{Ω_ρ(f)}W(x,y)dy` is pinned to the rank-one value,
`|W̄_x - u_*f(x)| ≤ C_{d,m}h`.  Jensen's inequality then replaces the row by that single value,
and the common modulus of continuity `ω_d` of `J̃_{p_h}` absorbs both the pinning error and the
spread of `f` across `Ω_ρ(f)`, leaving

`∫_{Ω_ρ(f)}{J_{p_h}(W(x,y)) - J̃_{p_h}(f(x)f(y))}dy ≥ -ω_d(C_{d,m}h) - ω_d(2√h) - C_{d,m}h²`

uniformly in `x`.  Integrating over `x ∈ Ω_ρ(f)^c` gives the mixed-rectangle bound, whose right
side is `ε_ρ(ν)` times a quantity that vanishes with `h`; that is `rowJensen_exists_mixed`,
stated as "for every `β > 0` the loss is at most `β ε_ρ(ν)` once `h` is small".

The tail–tail square needs nothing but boundedness: both entropies are bounded on their compact
ranges and the square has measure `ε_ρ(ν)²`, which is `rowJensen_exists_tailSq`.

No *positive* gain is extracted from these rectangles.  The rank-one tail
`∫_{T_ρ}Ψ_h dν ≥ b_ρ ε_ρ(ν)` carries the whole positive `ε_ρ(ν)` term, and Step 3 only has to
stay below it.

## Contents

* `rowAvg` — the row average `W̄_x` over `Ω_ρ(f)`, with `rowAvg_mem_Icc`;
* `abs_setIntegral_resid_le` — the Factor bound on `∫_{Ω_ρ(f)}E(x,·)`;
* `abs_rowAvg_sub_le` — the pinning `|W̄_x - u_*f(x)| ≤ C h`;
* `setIntegral_Jp_ge_jensen` — Jensen's inequality on `Ω_ρ(f)`;
* `logMod_le_four` — the uniform bound `τ(1 + log⁺(1/τ)) ≤ 4` on `[0,4]`;
* `rowJensen_per_row` — the per-row bound, uniform in `x`;
* **`rowJensen_exists_mixed`** — the mixed rectangles;
* **`rowJensen_exists_tailSq`** — the tail–tail square.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ} {W : Graphon}

/-! ## An `L¹`–`L⁴` comparison with no `L^p` theory

`|g| ≤ t + g⁴/t³` pointwise for every `t > 0`: either `|g| ≤ t`, or `|g| > t` and then
`g⁴/t³ > |g|`.  Integrating at `t = h` turns `∫g⁴ ≤ Kh⁴` into `∫|g| ≤ (1+K)h`, which is the
only consequence of `‖f - u_*‖₄ ≤ C h` that Step 3 uses. -/

theorem abs_le_add_div_pow {g t : ℝ} (ht : 0 < t) : |g| ≤ t + g ^ 4 / t ^ 3 := by
  rcases le_total |g| t with hle | hge
  · have : 0 ≤ g ^ 4 / t ^ 3 := by positivity
    linarith
  · have ht3 : (0 : ℝ) < t ^ 3 := by positivity
    have h4 : |g| ^ 4 = g ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ g ^ 4)]
    have hmono : t ^ 3 * |g| ≤ |g| ^ 3 * |g| := by
      have : t ^ 3 ≤ |g| ^ 3 := pow_le_pow_left₀ ht.le hge 3
      nlinarith [abs_nonneg g]
    have : |g| ≤ g ^ 4 / t ^ 3 := by
      rw [le_div_iff₀ ht3]
      nlinarith [h4, hmono]
    linarith

/-! ## The row average `W̄_x` -/

/-- **The row average over the central set**,
`W̄_x = |Ω_ρ(f)|^{-1}∫_{Ω_ρ(f)}W(x,y)dy`, of Step 3 of `lem:graphon-lagrangian-bound`. -/
noncomputable def rowAvg (d : ℕ) (ρ : ℝ) (W : Graphon) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ y in centralSet d ρ f, W.toFun x y ∂unitμ) / (unitμ (centralSet d ρ f)).toReal

/-- `W̄_x ∈ [0,1]`, so `J̃_{p_h}(W̄_x) = J_{p_h}(W̄_x)`. -/
theorem rowAvg_mem_Icc {f : ℝ → ℝ} (hf : Measurable f) {ρ : ℝ}
    (hpos : 0 < (unitμ (centralSet d ρ f)).toReal) (x : ℝ) :
    rowAvg d ρ W f x ∈ Set.Icc (0 : ℝ) 1 := by
  have hm := measurableSet_centralSet hf d ρ
  have hWi : IntegrableOn (fun y => W.toFun x y) (centralSet d ρ f) unitμ :=
    (integrable_of_abs_le (measurable_toFun_right W x) 1
      (fun y => abs_le.mpr ⟨by linarith [W.nonneg' x y], W.le_one' x y⟩)).restrict
  have h0 : 0 ≤ ∫ y in centralSet d ρ f, W.toFun x y ∂unitμ :=
    setIntegral_nonneg hm fun y _ => W.nonneg' x y
  have h1 : (∫ y in centralSet d ρ f, W.toFun x y ∂unitμ)
      ≤ (unitμ (centralSet d ρ f)).toReal := by
    have hle : (∫ y in centralSet d ρ f, W.toFun x y ∂unitμ)
        ≤ ∫ _y in centralSet d ρ f, (1 : ℝ) ∂unitμ :=
      setIntegral_mono_on hWi
        (Integrable.of_bound measurable_const.aestronglyMeasurable 1
          (Filter.Eventually.of_forall fun _ => by simp)) hm
        fun y _ => W.le_one' x y
    rwa [setIntegral_const, smul_eq_mul, measureReal_def, mul_one] at hle
  exact ⟨div_nonneg h0 hpos.le, (div_le_one hpos).mpr h1⟩


/-! ## The `L¹` bound on `Ω_ρ(f)` -/

/-- `∫_G|g| ≤ (1+K)t` whenever `∫g⁴ ≤ Kt⁴`, by `abs_le_add_div_pow` at the scale `t`.
Applied to `g = f - u_*`, this is the only use Step 3 makes of the fourth clause
`‖f - u_*‖₄ ≤ C_{d,m}h` of `eq:graphon-comparison-estimates`. -/
theorem setIntegral_abs_le_of_quart {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hgb : ∀ y, |g y| ≤ C) {G : Set ℝ} (hG : MeasurableSet G) {t K : ℝ} (ht : 0 < t)
    (h4 : (∫ y, g y ^ 4 ∂unitμ) ≤ K * t ^ 4) :
    (∫ y in G, |g y| ∂unitμ) ≤ (1 + K) * t := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hgb 0)
  have ht3 : (0 : ℝ) < t ^ 3 := by positivity
  have hqi : Integrable (fun y => g y ^ 4) unitμ :=
    integrable_of_abs_le (hg.pow_const 4) (C ^ 4) fun y => by
      have h1 : |g y ^ 4| = |g y| ^ 4 := abs_pow (g y) 4
      rw [h1]
      exact pow_le_pow_left₀ (abs_nonneg _) (hgb y) 4
  have hai : Integrable (fun y => |g y|) unitμ :=
    (integrable_of_abs_le hg C hgb).abs
  have hbi : Integrable (fun y => t + g y ^ 4 / t ^ 3) unitμ :=
    (integrable_const t).add (hqi.div_const _)
  -- `∫_G |g| ≤ ∫_G (t + g⁴/t³)`
  have h1 : (∫ y in G, |g y| ∂unitμ) ≤ ∫ y in G, (t + g y ^ 4 / t ^ 3) ∂unitμ :=
    setIntegral_mono_on hai.restrict hbi.restrict hG fun y _ => abs_le_add_div_pow ht
  have h2 : (∫ y in G, (t + g y ^ 4 / t ^ 3) ∂unitμ)
      = t * (unitμ G).toReal + (∫ y in G, g y ^ 4 ∂unitμ) / t ^ 3 := by
    rw [integral_add (integrable_const t).restrict (hqi.div_const _).restrict,
      integral_div, setIntegral_const, measureReal_def, smul_eq_mul, mul_comm]
  have h3 : (unitμ G).toReal ≤ 1 := by
    have hle : unitμ G ≤ 1 := prob_le_one
    calc (unitμ G).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) hle
      _ = 1 := ENNReal.toReal_one
  have h4G : (∫ y in G, g y ^ 4 ∂unitμ) ≤ ∫ y, g y ^ 4 ∂unitμ := by
    have hc : 0 ≤ ∫ y in Gᶜ, g y ^ 4 ∂unitμ :=
      setIntegral_nonneg hG.compl fun y _ => by positivity
    have := integral_add_compl hG hqi
    linarith
  have h5 : (∫ y in G, g y ^ 4 ∂unitμ) / t ^ 3 ≤ K * t := by
    rw [div_le_iff₀ ht3]
    nlinarith [h4G, h4]
  nlinarith [h1, h2, h5, ht.le, mul_le_mul_of_nonneg_left h3 ht.le]

/-! ## The Factor bound on the row integral of the residual -/

/-- **The row integral of the residual over `Ω_ρ(f)`**, bounded through the orthogonality
`eq:rank-one-orthogonality`.  Adding and subtracting `u_*^{d-1}` inside the row
integral and moving the resulting linear term to the tail by `T_E(f^{d-1}) = 0` gives

`u_*^{d-1}|∫_{Ω_ρ(f)}E(x,y)dy| ≤ 5(d-1)4^{d-1}∫_{Ω_ρ(f)}|f-u_*| + 5·2^{d-1}ε_ρ(ν)`,

the two remainders being the spread of `f^{d-1}` across the window and the tail-tail
contribution the orthogonality relation displaces. -/
theorem abs_setIntegral_resid_le (hd : 2 ≤ d) {ρ : ℝ} (P : FactorDecomp d W) {x : ℝ}
    (hx : ∫ y, (W.toFun x y - P.f x * P.f y) * P.f y ^ (d - 1) ∂unitμ = 0) :
    uStar d ^ (d - 1) * |∫ y in centralSet d ρ P.f, P.resid x y ∂unitμ|
      ≤ 5 * (((d - 1 : ℕ) : ℝ) * (2 ^ (d - 1) * 2 ^ (d - 1)))
            * (∫ y in centralSet d ρ P.f, |P.f y - uStar d| ∂unitμ)
          + 5 * 2 ^ (d - 1) * tailMass d ρ P.f := by
  set Ω := centralSet d ρ P.f with hΩ
  have hm : MeasurableSet Ω := measurableSet_centralSet P.meas_f d ρ
  have hu0 : (0 : ℝ) ≤ uStar d := uStar_nonneg hd
  have hu2 : uStar d ≤ 2 := le_trans (uStar_lt_one hd).le (by norm_num)
  -- integrability
  have hEm : Measurable fun y => P.resid x y := P.measurable_resid_right x
  have hEi : Integrable (fun y => P.resid x y) unitμ :=
    integrable_of_abs_le hEm 5 (P.abs_resid_le x)
  have hEfi : Integrable (fun y => P.resid x y * P.f y ^ (d - 1)) unitμ :=
    P.integrable_resid_mul_f_pow x (d - 1)
  have hDi : Integrable (fun y => (uStar d ^ (d - 1) - P.f y ^ (d - 1)) * P.resid x y) unitμ := by
    refine integrable_of_abs_le (((P.measurable_f_pow (d - 1)).const_sub _).mul hEm)
      ((2 ^ (d - 1) + 2 ^ (d - 1)) * 5) fun y => ?_
    rw [abs_mul]
    have h1 : |uStar d ^ (d - 1) - P.f y ^ (d - 1)| ≤ 2 ^ (d - 1) + 2 ^ (d - 1) := by
      refine le_trans (abs_sub _ _) (add_le_add ?_ ?_)
      · rw [abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ hu0 hu2 _
      · rw [abs_of_nonneg (pow_nonneg (P.f_nonneg y) (d - 1))]
        exact pow_le_pow_left₀ (P.f_nonneg y) (P.f_bdd y) _
    exact mul_le_mul h1 (P.abs_resid_le x y) (abs_nonneg _) (by positivity)
  -- the orthogonality moves the linear term to the tail
  have hzero : (∫ y in Ω, P.resid x y * P.f y ^ (d - 1) ∂unitμ)
      + (∫ y in Ωᶜ, P.resid x y * P.f y ^ (d - 1) ∂unitμ) = 0 := by
    rw [integral_add_compl hm hEfi]
    simpa [FactorDecomp.resid] using hx
  have hid : uStar d ^ (d - 1) * (∫ y in Ω, P.resid x y ∂unitμ)
      = (∫ y in Ω, (uStar d ^ (d - 1) - P.f y ^ (d - 1)) * P.resid x y ∂unitμ)
        - ∫ y in Ωᶜ, P.resid x y * P.f y ^ (d - 1) ∂unitμ := by
    have hpt : ∀ y, (uStar d ^ (d - 1) - P.f y ^ (d - 1)) * P.resid x y
        = uStar d ^ (d - 1) * P.resid x y - P.resid x y * P.f y ^ (d - 1) := fun y => by ring
    rw [setIntegral_congr_fun hm (fun y _ => hpt y),
      integral_sub ((hEi.const_mul _).restrict) hEfi.restrict, integral_const_mul]
    linarith [hzero]
  -- the two remainders
  have hb1 : |∫ y in Ω, (uStar d ^ (d - 1) - P.f y ^ (d - 1)) * P.resid x y ∂unitμ|
      ≤ 5 * (((d - 1 : ℕ) : ℝ) * (2 ^ (d - 1) * 2 ^ (d - 1)))
          * ∫ y in Ω, |P.f y - uStar d| ∂unitμ := by
    have hai : IntegrableOn (fun y => |P.f y - uStar d|) Ω unitμ :=
      ((integrable_of_abs_le (P.meas_f.fun_sub measurable_const) 4 fun y => by
        rw [abs_sub_comm]
        exact abs_le.mpr ⟨by linarith [P.f_bdd y, hu0], by linarith [P.f_nonneg y, hu2]⟩).abs).restrict
    have hstep : ∀ y, |(uStar d ^ (d - 1) - P.f y ^ (d - 1)) * P.resid x y|
        ≤ 5 * (((d - 1 : ℕ) : ℝ) * (2 ^ (d - 1) * 2 ^ (d - 1))) * |P.f y - uStar d| := by
      intro y
      rw [abs_mul]
      have hpow : |uStar d ^ (d - 1) - P.f y ^ (d - 1)|
          ≤ ((d - 1 : ℕ) : ℝ) * (2 ^ (d - 1) * 2 ^ (d - 1)) * |uStar d - P.f y| :=
        abs_pow_sub_pow_le_two (d - 1) hu0 hu2 (P.f_nonneg y) (P.f_bdd y)
      rw [abs_sub_comm (uStar d)] at hpow
      have h5 := P.abs_resid_le x y
      nlinarith [abs_nonneg (P.f y - uStar d), abs_nonneg (P.resid x y),
        abs_nonneg (uStar d ^ (d - 1) - P.f y ^ (d - 1)),
        mul_le_mul_of_nonneg_left h5 (abs_nonneg (uStar d ^ (d - 1) - P.f y ^ (d - 1))),
        mul_le_mul_of_nonneg_right hpow (le_of_lt (show (0:ℝ) < 5 by norm_num))]
    have h1 : |∫ y in Ω, (uStar d ^ (d - 1) - P.f y ^ (d - 1)) * P.resid x y ∂unitμ|
        ≤ ∫ y in Ω, |(uStar d ^ (d - 1) - P.f y ^ (d - 1)) * P.resid x y| ∂unitμ := by
      simpa [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := unitμ.restrict Ω)
          fun y => (uStar d ^ (d - 1) - P.f y ^ (d - 1)) * P.resid x y)
    have h2 : (∫ y in Ω, |(uStar d ^ (d - 1) - P.f y ^ (d - 1)) * P.resid x y| ∂unitμ)
        ≤ ∫ y in Ω, 5 * (((d - 1 : ℕ) : ℝ) * (2 ^ (d - 1) * 2 ^ (d - 1)))
            * |P.f y - uStar d| ∂unitμ :=
      setIntegral_mono_on hDi.abs.restrict (hai.const_mul _) hm fun y _ => hstep y
    rw [integral_const_mul] at h2
    linarith
  have hb2 : |∫ y in Ωᶜ, P.resid x y * P.f y ^ (d - 1) ∂unitμ|
      ≤ 5 * 2 ^ (d - 1) * tailMass d ρ P.f := by
    have := abs_setIntegral_le_measure (G := Ωᶜ) hm.compl
      (hEm.fun_mul (P.measurable_f_pow (d - 1))) (C := 5 * 2 ^ (d - 1)) fun y => by
        rw [abs_mul]
        refine mul_le_mul (P.abs_resid_le x y) ?_ (abs_nonneg _) (by norm_num)
        rw [abs_of_nonneg (pow_nonneg (P.f_nonneg y) (d - 1))]
        exact pow_le_pow_left₀ (P.f_nonneg y) (P.f_bdd y) _
    simpa [tailMass, hΩ] using this
  have hkey : uStar d ^ (d - 1) * |∫ y in Ω, P.resid x y ∂unitμ|
      = |uStar d ^ (d - 1) * ∫ y in Ω, P.resid x y ∂unitμ| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 (d - 1))]
  rw [hkey, hid]
  calc |(∫ y in Ω, (uStar d ^ (d - 1) - P.f y ^ (d - 1)) * P.resid x y ∂unitμ)
          - ∫ y in Ωᶜ, P.resid x y * P.f y ^ (d - 1) ∂unitμ|
      ≤ |∫ y in Ω, (uStar d ^ (d - 1) - P.f y ^ (d - 1)) * P.resid x y ∂unitμ|
        + |∫ y in Ωᶜ, P.resid x y * P.f y ^ (d - 1) ∂unitμ| := abs_sub _ _
    _ ≤ _ := by linarith


/-! ## The pinning `|W̄_x - u_* f(x)| ≤ C h` -/

/-- **The row-average pinning of Step 3.**  Splitting `W = f ⊗ f + E` inside the row integral,

`W̄_x - u_*f(x) = f(x)|Ω_ρ(f)|^{-1}∫_{Ω_ρ(f)}(f - u_*) + |Ω_ρ(f)|^{-1}∫_{Ω_ρ(f)}E(x,·)`,

so with `|Ω_ρ(f)| ≥ 1/2`, `0 ≤ f < 2` and `abs_setIntegral_resid_le` the row average is pinned
to the rank-one value at rate `∫_{Ω_ρ(f)}|f - u_*| + ε_ρ(ν)`.  Under
`eq:graphon-comparison-estimates` both are `O(h)`, which is the paper's
`|W̄_x - u_*f(x)| ≤ C_{d,m}h`. -/
theorem abs_rowAvg_sub_le (hd : 2 ≤ d) {ρ : ℝ} (P : FactorDecomp d W) {x : ℝ}
    (hx : ∫ y, (W.toFun x y - P.f x * P.f y) * P.f y ^ (d - 1) ∂unitμ = 0)
    (hhalf : (1 : ℝ) / 2 ≤ (unitμ (centralSet d ρ P.f)).toReal) :
    |rowAvg d ρ W P.f x - uStar d * P.f x|
      ≤ 4 * (∫ y in centralSet d ρ P.f, |P.f y - uStar d| ∂unitμ)
        + 2 / uStar d ^ (d - 1)
            * (5 * (((d - 1 : ℕ) : ℝ) * (2 ^ (d - 1) * 2 ^ (d - 1)))
                  * (∫ y in centralSet d ρ P.f, |P.f y - uStar d| ∂unitμ)
                + 5 * 2 ^ (d - 1) * tailMass d ρ P.f) := by
  set Ω := centralSet d ρ P.f with hΩ
  set M := (unitμ Ω).toReal with hM
  have hM0 : (0 : ℝ) < M := by rw [hM]; linarith
  have hm : MeasurableSet Ω := measurableSet_centralSet P.meas_f d ρ
  have hu0 : (0 : ℝ) < uStar d := uStar_pos hd
  have hup : (0 : ℝ) < uStar d ^ (d - 1) := pow_pos hu0 _
  -- integrability
  have hfi : Integrable (fun y => P.f y) unitμ :=
    integrable_of_abs_le P.meas_f 2 P.abs_f_le
  have hEi : Integrable (fun y => P.resid x y) unitμ :=
    integrable_of_abs_le (P.measurable_resid_right x) 5 (P.abs_resid_le x)
  -- the splitting of the row integral
  have hsplit : (∫ y in Ω, W.toFun x y ∂unitμ)
      = P.f x * (∫ y in Ω, P.f y ∂unitμ) + ∫ y in Ω, P.resid x y ∂unitμ := by
    have hpt : ∀ y, W.toFun x y = P.f x * P.f y + P.resid x y := fun y => by
      simp only [FactorDecomp.resid]; ring
    rw [setIntegral_congr_fun hm (fun y _ => hpt y),
      integral_add ((hfi.const_mul _).restrict) hEi.restrict, integral_const_mul]
  have hshift : (∫ y in Ω, P.f y ∂unitμ) - uStar d * M = ∫ y in Ω, (P.f y - uStar d) ∂unitμ := by
    rw [integral_sub hfi.restrict (integrable_const _).restrict, setIntegral_const,
      measureReal_def, smul_eq_mul, hM]
    ring
  -- the two contributions
  have hEb := abs_setIntegral_resid_le (ρ := ρ) hd P hx
  have hA0 : (0 : ℝ) ≤ ∫ y in Ω, |P.f y - uStar d| ∂unitμ :=
    setIntegral_nonneg hm fun y _ => abs_nonneg _
  have hab : |∫ y in Ω, (P.f y - uStar d) ∂unitμ| ≤ ∫ y in Ω, |P.f y - uStar d| ∂unitμ := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (μ := unitμ.restrict Ω) fun y => P.f y - uStar d)
  have hEabs : |∫ y in Ω, P.resid x y ∂unitμ|
      ≤ (5 * (((d - 1 : ℕ) : ℝ) * (2 ^ (d - 1) * 2 ^ (d - 1)))
            * (∫ y in Ω, |P.f y - uStar d| ∂unitμ)
          + 5 * 2 ^ (d - 1) * tailMass d ρ P.f) / uStar d ^ (d - 1) := by
    rw [le_div_iff₀ hup, mul_comm]
    exact hEb
  -- assemble
  have hid : rowAvg d ρ W P.f x - uStar d * P.f x
      = (P.f x * (∫ y in Ω, (P.f y - uStar d) ∂unitμ) + ∫ y in Ω, P.resid x y ∂unitμ) / M := by
    rw [rowAvg, ← hΩ, ← hM, hsplit, ← hshift]
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hM0]
  have hnum : |P.f x * (∫ y in Ω, (P.f y - uStar d) ∂unitμ) + ∫ y in Ω, P.resid x y ∂unitμ|
      ≤ 2 * (∫ y in Ω, |P.f y - uStar d| ∂unitμ) + |∫ y in Ω, P.resid x y ∂unitμ| := by
    refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
    rw [abs_mul]
    exact mul_le_mul (P.abs_f_le x) hab (abs_nonneg _) (by norm_num)
  rw [div_le_iff₀ hM0]
  have hε0 : (0 : ℝ) ≤ tailMass d ρ P.f := tailMass_nonneg d ρ P.f
  set A := ∫ y in Ω, |P.f y - uStar d| ∂unitμ with hAdef
  set R := 5 * (((d - 1 : ℕ) : ℝ) * (2 ^ (d - 1) * 2 ^ (d - 1))) * A
      + 5 * 2 ^ (d - 1) * tailMass d ρ P.f with hRdef
  have hR0 : (0 : ℝ) ≤ R := by
    have h1 : (0 : ℝ) ≤ 5 * (((d - 1 : ℕ) : ℝ) * (2 ^ (d - 1) * 2 ^ (d - 1))) * A :=
      mul_nonneg (by positivity) hA0
    have h2 : (0 : ℝ) ≤ 5 * 2 ^ (d - 1) * tailMass d ρ P.f := mul_nonneg (by positivity) hε0
    rw [hRdef]; linarith
  have hTot0 : (0 : ℝ) ≤ 4 * A + 2 / uStar d ^ (d - 1) * R := by
    have h3 : (0 : ℝ) ≤ 2 / uStar d ^ (d - 1) * R := mul_nonneg (by positivity) hR0
    linarith
  have hhalfle : (4 * A + 2 / uStar d ^ (d - 1) * R) * (1 / 2)
      ≤ (4 * A + 2 / uStar d ^ (d - 1) * R) * M := by
    have := mul_le_mul_of_nonneg_left hhalf hTot0
    linarith
  have heq : (4 * A + 2 / uStar d ^ (d - 1) * R) * (1 / 2) = 2 * A + R / uStar d ^ (d - 1) := by
    field_simp
    ring
  linarith [hnum, hEabs]


/-! ## Jensen on the central set -/

/-- **Jensen's inequality on `Ω_ρ(f)`**: the row entropy dominates the entropy of the row
average, `∫_{Ω_ρ(f)}J_{p_h}(W(x,y))dy ≥ |Ω_ρ(f)|J_{p_h}(W̄_x)`.  This is the step that
collapses the row to a single value in Step 3 of `lem:graphon-lagrangian-bound`; `J_p` is convex on
`[0,1]` (`convexOn_Jp`) and `W` takes values there. -/
theorem measure_mul_Jp_rowAvg_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {ρ : ℝ} {f : ℝ → ℝ}
    (hf : Measurable f) (hpos : 0 < (unitμ (centralSet d ρ f)).toReal) (x : ℝ) :
    (unitμ (centralSet d ρ f)).toReal * Jp p (rowAvg d ρ W f x)
      ≤ ∫ y in centralSet d ρ f, Jp p (W.toFun x y) ∂unitμ := by
  set Ω := centralSet d ρ f with hΩ
  have hm : MeasurableSet Ω := measurableSet_centralSet hf d ρ
  have hne : unitμ Ω ≠ 0 := by
    intro hz
    rw [hz] at hpos
    simp at hpos
  have htop : unitμ Ω ≠ ⊤ := measure_ne_top _ _
  have hWi : IntegrableOn (fun y => W.toFun x y) Ω unitμ :=
    (integrable_of_abs_le (measurable_toFun_right W x) 1
      (fun y => abs_le.mpr ⟨by linarith [W.nonneg' x y], W.le_one' x y⟩)).restrict
  have hJi : IntegrableOn (fun y => Jp p (W.toFun x y)) Ω unitμ := by
    obtain ⟨CJ, hCJ⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_Jp_Icc hp0 hp1)
    exact (integrable_of_abs_le ((measurable_Jp p).comp (measurable_toFun_right W x)) CJ
      fun y => hCJ _ (W.mem_Icc x y)).restrict
  have hjen := (convexOn_Jp hp0 hp1).map_set_average_le (continuousOn_Jp_Icc hp0 hp1)
    isClosed_Icc hne htop
    (Filter.Eventually.of_forall fun y => W.mem_Icc x y) hWi hJi
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, measureReal_def] at hjen
  have hrow : (unitμ Ω).toReal⁻¹ * ∫ y in Ω, W.toFun x y ∂unitμ = rowAvg d ρ W f x := by
    rw [rowAvg, ← hΩ, div_eq_inv_mul]
  rw [hrow] at hjen
  have := mul_le_mul_of_nonneg_left hjen hpos.le
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul] at this
  exact this

/-! ## Two elementary bounds on the modulus -/

/-- **`ω(τ) = τ(1 + log⁺(1/τ)) ≤ 3√τ` on `[0,9]`.**  For `τ ≤ 1` write
`log(1/τ) = 2log(1/√τ) ≤ 2(1/√τ - 1)`, so `ω(τ) ≤ 2√τ - τ ≤ 3√τ`; for `τ > 1` the positive
part vanishes and `ω(τ) = τ ≤ 3√τ` as long as `τ ≤ 9`.

This crude square-root form is all Step 3 needs: the paper's display keeps `ω_d` itself and
only ever uses that `ω_d(t) → 0` as `t ↓ 0`. -/
theorem logMod_le_sqrt {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ9 : τ ≤ 9) :
    τ * (1 + max 0 (Real.log (1 / τ))) ≤ 3 * Real.sqrt τ := by
  rcases eq_or_lt_of_le hτ0 with h0 | h0
  · rw [← h0]; simp
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr h0
  have hsq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ0
  rcases le_total τ 1 with h1 | h1
  · have hlog : Real.log (1 / τ) ≤ 2 * (1 / Real.sqrt τ - 1) := by
      have hinv : (0 : ℝ) < 1 / Real.sqrt τ := by positivity
      have h := Real.log_le_sub_one_of_pos hinv
      have hpow : (1 / Real.sqrt τ) ^ 2 = 1 / τ := by rw [div_pow, one_pow, hsq]
      have he : Real.log (1 / τ) = 2 * Real.log (1 / Real.sqrt τ) := by
        rw [← hpow, Real.log_pow]; norm_num
      rw [he]
      linarith
    have hmax : max 0 (Real.log (1 / τ)) ≤ 2 * (1 / Real.sqrt τ - 1) := by
      refine max_le ?_ hlog
      have : Real.sqrt τ ≤ 1 := by
        nlinarith [hsq, hs.le, h1]
      have : 1 ≤ 1 / Real.sqrt τ := by rw [le_div_iff₀ hs]; linarith
      linarith
    have hstep : τ * (1 + max 0 (Real.log (1 / τ))) ≤ τ * (1 + 2 * (1 / Real.sqrt τ - 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hτ0
    have he2 : τ * (1 + 2 * (1 / Real.sqrt τ - 1)) = 2 * Real.sqrt τ - τ := by
      field_simp
      nlinarith [hsq]
    linarith
  · have hz : max 0 (Real.log (1 / τ)) = 0 :=
      max_eq_left (Real.log_nonpos (by positivity) (by rw [div_le_one h0]; linarith))
    rw [hz, add_zero, mul_one]
    nlinarith [hsq, hs.le]

/-- **`√t ≤ t/s + s/2` for `t ≥ 0` and `s > 0`**, from `(√t - s)² ≥ 0`.  Used at `s = √h`, to
trade the square root in `logMod_le_sqrt` for the `L¹` bound the calibration display supplies. -/
theorem sqrt_le_div_add_half {t s : ℝ} (ht : 0 ≤ t) (hs : 0 < s) :
    Real.sqrt t ≤ t / s + s / 2 := by
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  have h2s : (0 : ℝ) < 2 * s := by linarith
  have he : (t / s + s / 2) * (2 * s) = 2 * t + s ^ 2 := by field_simp
  have key : Real.sqrt t * (2 * s) ≤ (t / s + s / 2) * (2 * s) := by
    rw [he]
    nlinarith [sq_nonneg (Real.sqrt t - s), hsq, ht]
  exact le_of_mul_le_mul_right (by linarith [key]) h2s


/-! ## The per-row bound -/

/-- **The per-row bound of Step 3**, uniform in `x`.

For a row `x` at which the Factor orthogonality holds, Jensen's inequality collapses the row
to `W̄_x`, `J̃_{p_h}` agrees with `J_{p_h}` there because `W̄_x ∈ [0,1]`, and the modulus `ω_d`
absorbs the two comparisons — the pinning error `|W̄_x - u_*f(x)| ≤ τ` and the spread
`|f(x)f(y) - u_*f(x)| ≤ 2|f(y) - u_*|` across the window:

`∫_{Ω_ρ(f)}{J_{p_h}(W(x,y)) - J̃_{p_h}(f(x)f(y))}dy ≥ -3C_ω√τ - 3C_ω(2A/s + s/2)`

for every `s > 0`, with `A` any bound on `∫_{Ω_ρ(f)}|f - u_*|`.

The paper writes the same estimate as `-ω_d(C_{d,m}h) - ω_d(2√h) - C_{d,m}h²`, splitting the
second integral at `|f - u_*| = √h` and using Markov's inequality.  The route here is the crude
`ω_d(t) ≤ 3√t` of `logMod_le_sqrt` followed by `√(2t) ≤ 2t/s + s/2`, which reaches the same
conclusion — both sides vanish as `h ↓ 0` under `eq:graphon-comparison-estimates`, and that
is all the paper's own use of the display needs. -/
theorem rowJensen_per_row (hd : 2 ≤ d) (B : KKTFamily d) {h ρ : ℝ} (hhb : |h| < B.h₀)
    {Cω : ℝ} (hCω : 0 ≤ Cω)
    (hmod : ∀ z ∈ Set.Icc (0 : ℝ) 4, ∀ z' ∈ Set.Icc (0 : ℝ) 4,
      |B.JpTildeH h z - B.JpTildeH h z'|
        ≤ Cω * |z - z'| * (1 + max 0 (Real.log (1 / |z - z'|))))
    (P : FactorDecomp d W)
    (hhalf : (1 : ℝ) / 2 ≤ (unitμ (centralSet d ρ P.f)).toReal)
    {x τ s A : ℝ} (hs : 0 < s) (hτ9 : τ ≤ 9)
    (hpin : |rowAvg d ρ W P.f x - uStar d * P.f x| ≤ τ)
    (hA : (∫ y in centralSet d ρ P.f, |P.f y - uStar d| ∂unitμ) ≤ A) :
    -(3 * Cω * Real.sqrt τ + 3 * Cω * (2 * A / s + s / 2))
      ≤ ∫ y in centralSet d ρ P.f,
          (Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)) ∂unitμ := by
  set Ω := centralSet d ρ P.f with hΩ
  set M := (unitμ Ω).toReal with hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hMle : M ≤ 1 := by
    have hle : unitμ Ω ≤ 1 := prob_le_one
    rw [hM]
    calc (unitμ Ω).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) hle
      _ = 1 := ENNReal.toReal_one
  have hm : MeasurableSet Ω := measurableSet_centralSet P.meas_f d ρ
  have hp := B.p_mem h hhb
  have hu0 : (0 : ℝ) ≤ uStar d := uStar_nonneg hd
  have hu2 : uStar d ≤ 2 := le_trans (uStar_lt_one hd).le (by norm_num)
  -- integrability of the two row integrands
  obtain ⟨CJ, hCJ⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_Jp_Icc hp.1 hp.2)
  have hcontT : ContinuousOn (B.JpTildeH h) (Set.Icc (0 : ℝ) 4) :=
    ((continuousOn_JpTilde hd).add
        (continuousOn_const.mul continuous_id.continuousOn)).add continuousOn_const
  obtain ⟨CT, hCT⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontT
  have hmemT : ∀ y, P.f x * P.f y ∈ Set.Icc (0 : ℝ) 4 := by
    intro y
    refine ⟨mul_nonneg (P.f_nonneg x) (P.f_nonneg y), ?_⟩
    nlinarith [P.f_nonneg x, P.f_nonneg y, P.f_bdd x, P.f_bdd y]
  have hJi : IntegrableOn (fun y => Jp (B.p h) (W.toFun x y)) Ω unitμ :=
    (integrable_of_abs_le ((measurable_Jp (B.p h)).comp (measurable_toFun_right W x)) CJ
      fun y => hCJ _ (W.mem_Icc x y)).restrict
  have hTi : IntegrableOn (fun y => B.JpTildeH h (P.f x * P.f y)) Ω unitμ :=
    (integrable_of_abs_le
      ((comparison_measurable_JpTildeH B h).comp (measurable_const.mul P.meas_f)) CT
      fun y => hCT _ (hmemT y)).restrict
  have hsplit : (∫ y in Ω, (Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)) ∂unitμ)
      = (∫ y in Ω, Jp (B.p h) (W.toFun x y) ∂unitμ)
        - ∫ y in Ω, B.JpTildeH h (P.f x * P.f y) ∂unitμ := integral_sub hJi hTi
  -- Jensen, then the identification `J̃ = J` at the row average
  have hbar := rowAvg_mem_Icc (W := W) P.meas_f (ρ := ρ) hM0 x
  have hjen : M * Jp (B.p h) (rowAvg d ρ W P.f x) ≤ ∫ y in Ω, Jp (B.p h) (W.toFun x y) ∂unitμ :=
    measure_mul_Jp_rowAvg_le hp.1 hp.2 P.meas_f hM0 x
  have heqJ : B.JpTildeH h (rowAvg d ρ W P.f x) = Jp (B.p h) (rowAvg d ρ W P.f x) :=
    KKTFamily.JpTildeH_eq_Jp hd hhb hbar.1 hbar.2
  -- the pinning comparison
  have hmemU : uStar d * P.f x ∈ Set.Icc (0 : ℝ) 4 := by
    refine ⟨mul_nonneg hu0 (P.f_nonneg x), ?_⟩
    nlinarith [P.f_nonneg x, P.f_bdd x]
  have hb1 : |B.JpTildeH h (rowAvg d ρ W P.f x) - B.JpTildeH h (uStar d * P.f x)|
      ≤ 3 * Cω * Real.sqrt τ := by
    have hz : rowAvg d ρ W P.f x ∈ Set.Icc (0 : ℝ) 4 := ⟨hbar.1, by linarith [hbar.2]⟩
    have h := hmod _ hz _ hmemU
    have hsq := logMod_le_sqrt (abs_nonneg (rowAvg d ρ W P.f x - uStar d * P.f x))
      (le_trans hpin hτ9)
    have hmono : Real.sqrt |rowAvg d ρ W P.f x - uStar d * P.f x| ≤ Real.sqrt τ :=
      Real.sqrt_le_sqrt hpin
    nlinarith [mul_le_mul_of_nonneg_left hsq hCω, mul_le_mul_of_nonneg_left hmono hCω]
  -- the spread comparison
  have hb2 : |(∫ y in Ω, B.JpTildeH h (P.f x * P.f y) ∂unitμ) - M * B.JpTildeH h (uStar d * P.f x)|
      ≤ 3 * Cω * (2 * A / s + s / 2) := by
    have hA0 : (0 : ℝ) ≤ ∫ y in Ω, |P.f y - uStar d| ∂unitμ :=
      setIntegral_nonneg hm fun y _ => abs_nonneg _
    have hshift : (∫ y in Ω, B.JpTildeH h (P.f x * P.f y) ∂unitμ)
        - M * B.JpTildeH h (uStar d * P.f x)
        = ∫ y in Ω, (B.JpTildeH h (P.f x * P.f y) - B.JpTildeH h (uStar d * P.f x)) ∂unitμ := by
      rw [integral_sub hTi (integrable_const _).restrict, setIntegral_const, measureReal_def,
        smul_eq_mul, hM]
    -- the pointwise bound
    have hpt : ∀ y, |B.JpTildeH h (P.f x * P.f y) - B.JpTildeH h (uStar d * P.f x)|
        ≤ 3 * Cω * (2 / s * |P.f y - uStar d| + s / 2) := by
      intro y
      have h := hmod _ (hmemT y) _ hmemU
      have hdiff : |P.f x * P.f y - uStar d * P.f x| ≤ 2 * |P.f y - uStar d| := by
        have he : P.f x * P.f y - uStar d * P.f x = P.f x * (P.f y - uStar d) := by ring
        rw [he, abs_mul]
        exact mul_le_mul_of_nonneg_right (P.abs_f_le x) (abs_nonneg _)
      have h9 : |P.f x * P.f y - uStar d * P.f x| ≤ 9 := by
        have : |P.f y - uStar d| ≤ 4 := by
          rw [abs_sub_comm]
          exact abs_le.mpr ⟨by linarith [P.f_bdd y, hu0], by linarith [P.f_nonneg y, hu2]⟩
        linarith
      have hsq := logMod_le_sqrt (abs_nonneg (P.f x * P.f y - uStar d * P.f x)) h9
      have hmono : Real.sqrt |P.f x * P.f y - uStar d * P.f x|
          ≤ Real.sqrt (2 * |P.f y - uStar d|) := Real.sqrt_le_sqrt hdiff
      have hroot := sqrt_le_div_add_half (t := 2 * |P.f y - uStar d|) (s := s)
        (by positivity) hs
      have hbig : 2 * |P.f y - uStar d| / s + s / 2
          = 2 / s * |P.f y - uStar d| + s / 2 := by ring
      rw [← hbig]
      nlinarith [mul_le_mul_of_nonneg_left hsq hCω, mul_le_mul_of_nonneg_left hmono hCω,
        mul_le_mul_of_nonneg_left hroot hCω, Real.sqrt_nonneg (2 * |P.f y - uStar d|)]
    -- integrate
    have hgi : IntegrableOn
        (fun y => B.JpTildeH h (P.f x * P.f y) - B.JpTildeH h (uStar d * P.f x)) Ω unitμ :=
      hTi.sub (integrable_const _).restrict
    have habi : IntegrableOn (fun y => |P.f y - uStar d|) Ω unitμ :=
      ((integrable_of_abs_le (P.meas_f.fun_sub measurable_const) 4 fun y => by
        rw [abs_sub_comm]
        exact abs_le.mpr ⟨by linarith [P.f_bdd y, hu0],
          by linarith [P.f_nonneg y, hu2]⟩).abs).restrict
    have hmaji : IntegrableOn
        (fun y => 3 * Cω * (2 / s * |P.f y - uStar d| + s / 2)) Ω unitμ :=
      ((habi.const_mul (2 / s)).add (integrable_const _).restrict).const_mul _
    have h1 : |∫ y in Ω, (B.JpTildeH h (P.f x * P.f y) - B.JpTildeH h (uStar d * P.f x)) ∂unitμ|
        ≤ ∫ y in Ω, |B.JpTildeH h (P.f x * P.f y) - B.JpTildeH h (uStar d * P.f x)| ∂unitμ := by
      simpa [Real.norm_eq_abs] using (norm_integral_le_integral_norm
        (μ := unitμ.restrict Ω)
        fun y => B.JpTildeH h (P.f x * P.f y) - B.JpTildeH h (uStar d * P.f x))
    have h2 : (∫ y in Ω, |B.JpTildeH h (P.f x * P.f y) - B.JpTildeH h (uStar d * P.f x)| ∂unitμ)
        ≤ ∫ y in Ω, 3 * Cω * (2 / s * |P.f y - uStar d| + s / 2) ∂unitμ :=
      setIntegral_mono_on hgi.abs hmaji hm fun y _ => hpt y
    have h3 : (∫ y in Ω, 3 * Cω * (2 / s * |P.f y - uStar d| + s / 2) ∂unitμ)
        = 3 * Cω * (2 / s * (∫ y in Ω, |P.f y - uStar d| ∂unitμ) + s / 2 * M) := by
      rw [integral_const_mul, integral_add (habi.const_mul (2 / s))
        (integrable_const _).restrict, integral_const_mul, setIntegral_const,
        measureReal_def, smul_eq_mul, ← hM]
      ring
    rw [hshift]
    have hs2 : (0 : ℝ) ≤ 3 * Cω := by linarith
    have hstep : 3 * Cω * (2 / s * (∫ y in Ω, |P.f y - uStar d| ∂unitμ) + s / 2 * M)
        ≤ 3 * Cω * (2 * A / s + s / 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hs2
      have hd1 : 2 / s * (∫ y in Ω, |P.f y - uStar d| ∂unitμ) ≤ 2 / s * A :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      have hd2 : s / 2 * M ≤ s / 2 := by nlinarith [hs.le, hMle, hM0]
      have he : 2 / s * A = 2 * A / s := by ring
      linarith
    linarith [h1, h2, h3.le, h3.ge, hstep]
  rw [hsplit]
  have hA1 := abs_le.mp hb1
  have hA2 := abs_le.mp hb2
  rw [heqJ] at hA1
  nlinarith [hjen, hA1.1, hA1.2, hA2.1, hA2.2, hMle, hM0]


/-! ## The mixed rectangles and the tail–tail square -/

/-- **The pinning constant of Step 3.**  Packaging `abs_rowAvg_sub_le` against the two clauses
of `eq:graphon-comparison-estimates` that bound the tail mass and `‖f - u_*‖₄`: there is a
`C` with `|W̄_x - u_*f(x)| ≤ Ch` for almost every row, uniformly over competitors. -/
theorem exists_rowAvg_pin_const (hd : 2 ≤ d) (ρ : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : Graphon) (P : FactorDecomp d W) (h : ℝ), 0 < h → h ≤ 1 →
      tailMass d ρ P.f ≤ K * h ^ 4 →
      (∫ y, (P.f y - uStar d) ^ 4 ∂unitμ) ≤ K * h ^ 4 →
      (1 : ℝ) / 2 ≤ (unitμ (centralSet d ρ P.f)).toReal →
      ∀ᵐ x ∂unitμ, |rowAvg d ρ W P.f x - uStar d * P.f x| ≤ C * h := by
  have hu0 : (0 : ℝ) < uStar d := uStar_pos hd
  have hu2 : uStar d ≤ 2 := le_trans (uStar_lt_one hd).le (by norm_num)
  obtain ⟨e, he0, hedef⟩ : ∃ e : ℝ, 0 ≤ e ∧ e = 2 / uStar d ^ (d - 1) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨c, hc0, hcdef⟩ : ∃ c : ℝ, 0 ≤ c ∧
      c = 5 * (((d - 1 : ℕ) : ℝ) * (2 ^ (d - 1) * 2 ^ (d - 1))) := ⟨_, by positivity, rfl⟩
  obtain ⟨b, hb0, hbdef⟩ : ∃ b : ℝ, 0 ≤ b ∧ b = 5 * 2 ^ (d - 1) := ⟨_, by positivity, rfl⟩
  refine ⟨4 * (1 + K) + e * (c * (1 + K) + b * K), by positivity, ?_⟩
  intro W P h hh0 hh1 htail hquart hhalf
  have hh3 : h ^ 3 ≤ 1 := pow_le_one₀ hh0.le hh1
  have hh4 : h ^ 4 ≤ h := by
    nlinarith [mul_nonneg hh0.le (by linarith : (0 : ℝ) ≤ 1 - h ^ 3)]
  have hεh : tailMass d ρ P.f ≤ K * h := le_trans htail (by nlinarith [hh4, hK])
  have hgb : ∀ y, |P.f y - uStar d| ≤ 4 := fun y => by
    rw [abs_sub_comm]
    exact abs_le.mpr ⟨by linarith [P.f_bdd y, hu0.le], by linarith [P.f_nonneg y, hu2]⟩
  have hA : (∫ y in centralSet d ρ P.f, |P.f y - uStar d| ∂unitμ) ≤ (1 + K) * h :=
    setIntegral_abs_le_of_quart (P.meas_f.sub measurable_const) hgb
      (measurableSet_centralSet P.meas_f d ρ) hh0 hquart
  filter_upwards [P.ortho] with x hx
  have hraw := abs_rowAvg_sub_le (ρ := ρ) hd P hx hhalf
  rw [← hcdef, ← hbdef, ← hedef] at hraw
  refine le_trans hraw ?_
  have hstep : c * (∫ y in centralSet d ρ P.f, |P.f y - uStar d| ∂unitμ) + b * tailMass d ρ P.f
      ≤ c * ((1 + K) * h) + b * (K * h) := by
    have ha := mul_le_mul_of_nonneg_left hA hc0
    have hbb := mul_le_mul_of_nonneg_left hεh hb0
    linarith
  have hmul := mul_le_mul_of_nonneg_left hstep he0
  linarith [hmul, hA]

/-- **Step 3, mixed rectangles** of `lem:graphon-lagrangian-bound`.

For every `β > 0` the two rectangles `Ω_ρ(f)^c × Ω_ρ(f)` cost at most `β ε_ρ(ν)` once `h` is
small, under the tail-mass and `L⁴` clauses of `eq:graphon-comparison-estimates`:

`2∬_{Ω_ρ(f)^c×Ω_ρ(f)}{J_{p_h}(W) - J̃_{p_h}(f⊗f)} ≥ -β ε_ρ(ν)`.

The paper takes `β = b_ρ/8`, so that the `b_ρ ε_ρ(ν)` of `lem:auxiliary-lagrangian-bound`
covers this loss with room to spare; stating it for an arbitrary `β` is exactly the content of
the paper's "since `ω_d(t) → 0` as `t ↓ 0`, after decreasing `h_ρ`" (`:2170–2174`).

The proof is `rowJensen_per_row` at `τ = C₁h` and `s = √h`, integrated over `x ∈ Ω_ρ(f)^c`;
the row hypotheses hold for almost every `x`, by `FactorDecomp.ortho`. -/
theorem rowJensen_exists_mixed (hd : 2 ≤ d) (B : KKTFamily d) (ρ : ℝ)
    {β : ℝ} (hβ : 0 < β) {K : ℝ} (hK : 0 ≤ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → |h| < B.h₀ →
      ∀ (W : Graphon) (P : FactorDecomp d W),
        tailMass d ρ P.f ≤ K * h ^ 4 →
        (∫ y, (P.f y - uStar d) ^ 4 ∂unitμ) ≤ K * h ^ 4 →
          -(β * tailMass d ρ P.f)
            ≤ 2 * ∫ x in (centralSet d ρ P.f)ᶜ, (∫ y in centralSet d ρ P.f,
                (Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)) ∂unitμ) ∂unitμ := by
  obtain ⟨Cω, hCω0, δm, hδm0, hmod⟩ := KKTFamily.exists_JpTildeH_modulus hd B
  obtain ⟨C₁, hC₁0, hpin1⟩ := exists_rowAvg_pin_const hd ρ hK
  have hu0 : (0 : ℝ) < uStar d := uStar_pos hd
  have hu2 : uStar d ≤ 2 := le_trans (uStar_lt_one hd).le (by norm_num)
  obtain ⟨C₂, hC₂0, hC₂⟩ : ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      C₂ = 3 * Cω * (Real.sqrt C₁ + 2 * (1 + K) + 1 / 2) := by
    refine ⟨_, ?_, rfl⟩
    have h1 : (0 : ℝ) ≤ Real.sqrt C₁ + 2 * (1 + K) + 1 / 2 := by
      have := Real.sqrt_nonneg C₁; linarith
    have h2 : (0 : ℝ) ≤ 3 * Cω := by linarith
    exact mul_nonneg h2 h1
  refine ⟨min (min 1 δm) (min (1 / (2 * K + 2)) (min (9 / (C₁ + 1)) ((β / (2 * C₂ + 2)) ^ 2))),
    lt_min (lt_min one_pos hδm0) (lt_min (by positivity) (lt_min (by positivity)
      (by positivity))), ?_⟩
  intro h hh0 hhδ hhb W P htail hquart
  have hh1 : h ≤ 1 := le_of_lt (lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hhm : |h| < δm := by
    rw [abs_of_pos hh0]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hhK : h ≤ 1 / (2 * K + 2) :=
    le_of_lt (lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hhC : h ≤ 9 / (C₁ + 1) :=
    le_of_lt (lt_of_lt_of_le hhδ (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hhβ : h ≤ (β / (2 * C₂ + 2)) ^ 2 :=
    le_of_lt (lt_of_lt_of_le hhδ (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hm : MeasurableSet (centralSet d ρ P.f) := measurableSet_centralSet P.meas_f d ρ
  have hε0 : (0 : ℝ) ≤ tailMass d ρ P.f := tailMass_nonneg d ρ P.f
  have hh3 : h ^ 3 ≤ 1 := pow_le_one₀ hh0.le hh1
  have hh4 : h ^ 4 ≤ h := by
    nlinarith [mul_nonneg hh0.le (by linarith : (0 : ℝ) ≤ 1 - h ^ 3)]
  -- `|Ω_ρ(f)| ≥ 1/2`
  have hεhalf : tailMass d ρ P.f ≤ 1 / 2 := by
    have h1 : K * h ^ 4 ≤ K * h := by nlinarith [hh4, hK]
    have h2 : K * h ≤ K * (1 / (2 * K + 2)) := by nlinarith [hhK, hK]
    have h3 : K * (1 / (2 * K + 2)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * K + 2)]
      linarith
    linarith [htail]
  have hhalf : (1 : ℝ) / 2 ≤ (unitμ (centralSet d ρ P.f)).toReal :=
    half_le_measure_centralSet P.meas_f hεhalf
  have hgb : ∀ y, |P.f y - uStar d| ≤ 4 := fun y => by
    rw [abs_sub_comm]
    exact abs_le.mpr ⟨by linarith [P.f_bdd y, hu0.le], by linarith [P.f_nonneg y, hu2]⟩
  have hA : (∫ y in centralSet d ρ P.f, |P.f y - uStar d| ∂unitμ) ≤ (1 + K) * h :=
    setIntegral_abs_le_of_quart (P.meas_f.sub measurable_const) hgb hm hh0 hquart
  -- the per-row bound, for almost every row
  have hrowae : ∀ᵐ x ∂unitμ, -(C₂ * Real.sqrt h)
      ≤ ∫ y in centralSet d ρ P.f,
          (Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)) ∂unitμ := by
    filter_upwards [hpin1 W P h hh0 hh1 htail hquart hhalf] with x hpin
    have hτ9 : C₁ * h ≤ 9 := by
      have h1' : C₁ * h ≤ C₁ * (9 / (C₁ + 1)) := mul_le_mul_of_nonneg_left hhC hC₁0
      have h2' : C₁ * (9 / (C₁ + 1)) ≤ 9 := by
        rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0 : ℝ) < C₁ + 1)]
        nlinarith
      linarith
    have hs : (0 : ℝ) < Real.sqrt h := Real.sqrt_pos.mpr hh0
    have hper := rowJensen_per_row hd B hhb hCω0.le (hmod h hhm hhb) P hhalf hs hτ9 hpin hA
    refine le_trans ?_ hper
    have e1 : Real.sqrt (C₁ * h) = Real.sqrt C₁ * Real.sqrt h := Real.sqrt_mul hC₁0 h
    have e2 : 2 * ((1 + K) * h) / Real.sqrt h = 2 * (1 + K) * Real.sqrt h := by
      rw [show 2 * ((1 + K) * h) / Real.sqrt h = 2 * (1 + K) * (h / Real.sqrt h) by ring,
        Real.div_sqrt]
    rw [neg_le_neg_iff, hC₂, e1, e2]
    exact le_of_eq (by ring)
  -- integrate over the tail
  have hWjoint : Measurable fun z : ℝ × ℝ => W.toFun z.1 z.2 := W.measurable_uncurry
  have hKj : Measurable fun z : ℝ × ℝ =>
      Jp (B.p h) (W.toFun z.1 z.2) - B.JpTildeH h (P.f z.1 * P.f z.2) :=
    ((measurable_Jp (B.p h)).comp hWjoint).sub
      ((comparison_measurable_JpTildeH B h).comp
        ((P.meas_f.comp measurable_fst).mul (P.meas_f.comp measurable_snd)))
  have hp := B.p_mem h hhb
  obtain ⟨CJ, hCJ⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_Jp_Icc hp.1 hp.2)
  have hcontT : ContinuousOn (B.JpTildeH h) (Set.Icc (0 : ℝ) 4) :=
    ((continuousOn_JpTilde hd).add
        (continuousOn_const.mul continuous_id.continuousOn)).add continuousOn_const
  obtain ⟨CT, hCT⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontT
  have hbd : ∀ x y, |Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)| ≤ CJ + CT := by
    intro x y
    have h1 : |Jp (B.p h) (W.toFun x y)| ≤ CJ := hCJ _ (W.mem_Icc x y)
    have h2 : |B.JpTildeH h (P.f x * P.f y)| ≤ CT := by
      refine hCT _ ⟨mul_nonneg (P.f_nonneg x) (P.f_nonneg y), ?_⟩
      nlinarith [P.f_nonneg x, P.f_nonneg y, P.f_bdd x, P.f_bdd y]
    calc |Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)|
        ≤ |Jp (B.p h) (W.toFun x y)| + |B.JpTildeH h (P.f x * P.f y)| := abs_sub _ _
      _ ≤ CJ + CT := by linarith
  have hC0 : (0 : ℝ) ≤ CJ + CT := le_trans (abs_nonneg _) (hbd 0 0)
  have hrowm : Measurable fun x => ∫ y in centralSet d ρ P.f, (Jp (B.p h) (W.toFun x y)
      - B.JpTildeH h (P.f x * P.f y)) ∂unitμ := measurable_setIntegral_row hKj _
  have hrowi : IntegrableOn (fun x => ∫ y in centralSet d ρ P.f, (Jp (B.p h) (W.toFun x y)
      - B.JpTildeH h (P.f x * P.f y)) ∂unitμ) (centralSet d ρ P.f)ᶜ unitμ :=
    (integrable_of_abs_le hrowm (CJ + CT)
      fun x => abs_setIntegral_row_le hKj hC0 hbd hm x).restrict
  have hmono : (∫ _x in (centralSet d ρ P.f)ᶜ, -(C₂ * Real.sqrt h) ∂unitμ)
      ≤ ∫ x in (centralSet d ρ P.f)ᶜ, (∫ y in centralSet d ρ P.f, (Jp (B.p h) (W.toFun x y)
          - B.JpTildeH h (P.f x * P.f y)) ∂unitμ) ∂unitμ :=
    integral_mono_ae (integrable_const _).restrict hrowi (ae_restrict_of_ae hrowae)
  rw [setIntegral_const, measureReal_def, smul_eq_mul] at hmono
  have hεdef : (unitμ (centralSet d ρ P.f)ᶜ).toReal = tailMass d ρ P.f := rfl
  rw [hεdef] at hmono
  have hsmall : 2 * C₂ * Real.sqrt h ≤ β := by
    have hsq : Real.sqrt h ≤ β / (2 * C₂ + 2) := by
      have hle := Real.sqrt_le_sqrt hhβ
      rwa [Real.sqrt_sq (by positivity)] at hle
    have hstep := mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ 2 * C₂)
    have hfin : 2 * C₂ * (β / (2 * C₂ + 2)) ≤ β := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith [hβ.le, hC₂0]
    linarith
  have hprod := mul_le_mul_of_nonneg_right hsmall hε0
  linarith [hmono, hprod]

/-- **Step 3, the tail–tail square**: bounded below by
`-C_dε_ρ(ν)²`, because the true entropy of `W` and the continued entropy of `f ⊗ f` are both
bounded on their compact ranges and the square has measure `ε_ρ(ν)²`.  At the assembly this is
absorbed, like the mixed rectangles, into the `b_ρ ε_ρ(ν)` of
`lem:auxiliary-lagrangian-bound`. -/
theorem rowJensen_exists_tailSq (hd : 2 ≤ d) (B : KKTFamily d) (ρ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      ∀ (W : Graphon) (P : FactorDecomp d W),
        -(C * tailMass d ρ P.f ^ 2)
          ≤ ∫ x in (centralSet d ρ P.f)ᶜ, (∫ y in (centralSet d ρ P.f)ᶜ,
              (Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)) ∂unitμ) ∂unitμ := by
  obtain ⟨CJ, hCJ, δJ, hδJ, hJb⟩ := KKTFamily.exists_abs_Jp_le hd B
  obtain ⟨CT, hCT, δT, hδT, hTb⟩ := KKTFamily.exists_abs_JpTildeH_le hd B
  refine ⟨CJ + CT, by linarith, min δJ δT, lt_min hδJ hδT, ?_⟩
  intro h hhδ W P
  have hhJ : |h| < δJ := lt_of_lt_of_le hhδ (min_le_left _ _)
  have hhT : |h| < δT := lt_of_lt_of_le hhδ (min_le_right _ _)
  have hGc : MeasurableSet (centralSet d ρ P.f)ᶜ := (measurableSet_centralSet P.meas_f d ρ).compl
  have hWjoint : Measurable fun z : ℝ × ℝ => W.toFun z.1 z.2 := W.measurable_uncurry
  have hKj : Measurable fun z : ℝ × ℝ =>
      Jp (B.p h) (W.toFun z.1 z.2) - B.JpTildeH h (P.f z.1 * P.f z.2) :=
    ((measurable_Jp (B.p h)).comp hWjoint).sub
      ((comparison_measurable_JpTildeH B h).comp
        ((P.meas_f.comp measurable_fst).mul (P.meas_f.comp measurable_snd)))
  have hKjb : ∀ x y, |Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)| ≤ CJ + CT := by
    intro x y
    have h1 : |Jp (B.p h) (W.toFun x y)| ≤ CJ := hJb h hhJ _ (W.mem_Icc x y)
    have h2 : |B.JpTildeH h (P.f x * P.f y)| ≤ CT := by
      refine hTb h hhT _ ⟨mul_nonneg (P.f_nonneg x) (P.f_nonneg y), ?_⟩
      nlinarith [P.f_nonneg x, P.f_nonneg y, P.f_bdd x, P.f_bdd y]
    calc |Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)|
        ≤ |Jp (B.p h) (W.toFun x y)| + |B.JpTildeH h (P.f x * P.f y)| := abs_sub _ _
      _ ≤ CJ + CT := by linarith
  have hrowb : ∀ x, |∫ y in (centralSet d ρ P.f)ᶜ,
      (Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)) ∂unitμ|
        ≤ (CJ + CT) * tailMass d ρ P.f := fun x =>
    abs_setIntegral_le_measure hGc (hKj.comp (measurable_const.prodMk measurable_id))
      (hKjb x)
  have hrowm : Measurable fun x => ∫ y in (centralSet d ρ P.f)ᶜ,
      (Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)) ∂unitμ :=
    measurable_setIntegral_row hKj _
  have hep : (0 : ℝ) ≤ tailMass d ρ P.f := tailMass_nonneg d ρ P.f
  have hout := abs_setIntegral_le_measure hGc hrowm hrowb
  have he : (CJ + CT) * tailMass d ρ P.f * (unitμ (centralSet d ρ P.f)ᶜ).toReal
      = (CJ + CT) * tailMass d ρ P.f ^ 2 := by rw [tailMass]; ring
  rw [he] at hout
  linarith [(abs_le.mp hout).1]


/-! ## Three inputs the assembly needs -/

/-- **`‖E‖²_{2,Ω_ρ(f)^c×Ω_ρ(f)} ≤ 25 ε_ρ(ν)`**, from `|E| ≤ 5` and `|Ω_ρ(f)| ≤ 1`.  This is
the mixed-rectangle half of the paper's `‖E‖_{2,[0,1]²∖Ω_ρ(f)²}² ≤ 50ε_ρ(ν)`
; the corner half is `comparisonMain_tailSq_resid_le`. -/
theorem mixed_resid_le {ρ : ℝ} (P : FactorDecomp d W) :
    (∫ x in (centralSet d ρ P.f)ᶜ, (∫ y in centralSet d ρ P.f, P.resid x y ^ 2 ∂unitμ) ∂unitμ)
      ≤ 25 * tailMass d ρ P.f := by
  have hm : MeasurableSet (centralSet d ρ P.f) := measurableSet_centralSet P.meas_f d ρ
  have hEsq : Measurable fun z : ℝ × ℝ => P.resid z.1 z.2 ^ 2 := P.measurable_resid.pow_const 2
  have hEsqb : ∀ x y, |P.resid x y ^ 2| ≤ 25 := by
    intro x y
    rw [abs_of_nonneg (sq_nonneg _)]
    have hb := abs_le.mp (P.abs_resid_le x y)
    nlinarith [hb.1, hb.2]
  have hrow : ∀ x, (∫ y in centralSet d ρ P.f, P.resid x y ^ 2 ∂unitμ) ≤ 25 := fun x =>
    le_trans (le_abs_self _) (abs_setIntegral_row_le hEsq (by norm_num) hEsqb hm x)
  have hrowm : Measurable fun x => ∫ y in centralSet d ρ P.f, P.resid x y ^ 2 ∂unitμ :=
    measurable_setIntegral_row hEsq _
  have hrowi : IntegrableOn (fun x => ∫ y in centralSet d ρ P.f, P.resid x y ^ 2 ∂unitμ)
      (centralSet d ρ P.f)ᶜ unitμ :=
    (integrable_of_abs_le hrowm 25
      fun x => abs_setIntegral_row_le hEsq (by norm_num) hEsqb hm x).restrict
  have hmono : (∫ x in (centralSet d ρ P.f)ᶜ,
        (∫ y in centralSet d ρ P.f, P.resid x y ^ 2 ∂unitμ) ∂unitμ)
      ≤ ∫ _x in (centralSet d ρ P.f)ᶜ, (25 : ℝ) ∂unitμ :=
    setIntegral_mono_on hrowi
      (Integrable.of_bound measurable_const.aestronglyMeasurable 25
        (Filter.Eventually.of_forall fun _ => by simp)) hm.compl fun x _ => hrow x
  rwa [setIntegral_const, measureReal_def, smul_eq_mul, mul_comm] at hmono

/-- **`∫_{Ω_ρ(f)^c}Ψ̃_h(f) ≥ b ε_ρ(ν)`**: the tail bound `Ψ_h ≥ b_ρ` off the window
(`KKTFamily.exists_firstVariation_upperGap`, `lem:first-variation-bound`) integrated over
the tail.  This is where the proof gets the **positive** `ε_ρ(ν)` of
`eq:graphon-lagrangian-bound`; Steps 2 and 3 only spend it. -/
theorem setIntegral_PsiT_ge (hd : 2 ≤ d) (B : KKTFamily d) {h ρ b : ℝ} (hρ0 : 0 < ρ)
    (hhb : |h| < B.h₀)
    (hb : ∀ x ∈ Set.Icc (0 : ℝ) 2, ρ ≤ |x - uStar d| → b ≤ B.PsiT h x)
    {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x) (hbd : ∀ x, f x ≤ 2) :
    b * tailMass d ρ f ≤ ∫ x in (centralSet d ρ f)ᶜ, B.PsiT h (f x) ∂unitμ := by
  have hm : MeasurableSet (centralSet d ρ f) := measurableSet_centralSet hf d ρ
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (KKTFamily.continuousOn_PsiT hd B hhb)
  have hmeas : Measurable fun x => B.PsiT h (f x) := (comparison_measurable_PsiT B h).comp hf
  have hCb : ∀ x, |B.PsiT h (f x)| ≤ C := fun x => by
    simpa [Real.norm_eq_abs] using hC _ ⟨hnn x, hbd x⟩
  have hint : IntegrableOn (fun x => B.PsiT h (f x)) (centralSet d ρ f)ᶜ unitμ :=
    (integrable_of_abs_le hmeas C hCb).restrict
  have hpt : ∀ x ∈ (centralSet d ρ f)ᶜ, b ≤ B.PsiT h (f x) := by
    intro x hx
    refine hb _ ⟨hnn x, hbd x⟩ ?_
    have hnot : f x ∉ centralWindow d ρ := hx
    simp only [centralWindow, Set.mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with h1 | h1
    · rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  have hmono : (∫ _x in (centralSet d ρ f)ᶜ, b ∂unitμ)
      ≤ ∫ x in (centralSet d ρ f)ᶜ, B.PsiT h (f x) ∂unitμ :=
    setIntegral_mono_on (Integrable.of_bound measurable_const.aestronglyMeasurable |b|
      (Filter.Eventually.of_forall fun _ => by simp)) hint hm.compl hpt
  rwa [setIntegral_const, measureReal_def, smul_eq_mul, mul_comm] at hmono

/-- `∫g⁴ ≤ c⁴` from `‖g‖₄ ≤ c`: the bridge between the `Lnorm` form in which
`singular_endpoint_localization` exports `‖f - u_*‖₄ ≤ C_{d,m}h` and the raw fourth moment that
Step 3 consumes. -/
theorem integral_pow_four_le_of_Lnorm {g : ℝ → ℝ} {c : ℝ} (hL : Lnorm unitμ 4 g ≤ c) :
    (∫ y, g y ^ 4 ∂unitμ) ≤ c ^ 4 := by
  have hnat : ((4 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
  have hpt : ∀ y, |g y| ^ (4 : ℝ) = g y ^ 4 := by
    intro y
    rw [← hnat, Real.rpow_natCast, ← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ g y ^ 4)]
  have hrp : Lnorm unitμ 4 g ^ (4 : ℝ) = ∫ y, |g y| ^ (4 : ℝ) ∂unitμ :=
    Lnorm_rpow (by norm_num) g
  have heq : (∫ y, |g y| ^ (4 : ℝ) ∂unitμ) = ∫ y, g y ^ 4 ∂unitμ :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hmono : Lnorm unitμ 4 g ^ (4 : ℝ) ≤ c ^ (4 : ℝ) :=
    Real.rpow_le_rpow (Lnorm_nonneg _ _ _) hL (by norm_num)
  have hc4 : c ^ (4 : ℝ) = c ^ 4 := by rw [← hnat, Real.rpow_natCast]
  rw [hrp, heq, hc4] at hmono
  exact hmono

end SingularEndpoint

end UpperTailOptimizers
