import Mathlib

/-!
# Filled quotients attached to `log (1 + x)`

Two "filled quotient" functions are used repeatedly when a merge perturbation is expanded to
second order around the unperturbed configuration:

* `logQuot x = log (1 + x) / x`, filled with the value `1` at `x = 0`;
* `bennett x = ((1 + x) * log (1 + x) - x) / x ^ 2`, filled with the value `1 / 2` at `x = 0`.

Both are real-analytic at `0`, which is exactly what makes the second-order expansion of a merge
legitimate; the removable singularity is resolved by the division lemma
`exists_factor_of_analyticAt`: a function that is analytic at a point and vanishes there is
`(z - z₀)` times an analytic function.  This is the analytic order machinery of
`Mathlib/Analysis/Analytic/Order.lean` packaged in the shape we need.

The file also records the Taylor data at `0` that the downstream estimates consume:

* `logQuot 0 = 1`, `logQuot' 0 = -1/2`, `logQuot'' 0 = 2/3`;
* `bennett 0 = 1/2`, `bennett' 0 = -1/6`, `bennett'' 0 = 1/6`.

The derivative values are obtained by repeatedly differentiating the two defining identities
`log (1 + x) = x * logQuot x` and `x * bennett x = (1 + x) * logQuot x - 1`, comparing them with the
closed-form derivatives `x ↦ c * (1 + x) ^ m` (`m : ℤ`) of `log (1 + x)`.
-/

namespace UpperTailOptimizers

open Filter Topology

/-! ### A division lemma for analytic functions -/

/-- Factorisation of an analytic function vanishing at the point. -/
theorem exists_factor_of_analyticAt {f : ℝ → ℝ} {z₀ : ℝ}
    (hf : AnalyticAt ℝ f z₀) (h0 : f z₀ = 0) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g z₀ ∧ (∀ᶠ z in nhds z₀, f z = (z - z₀) * g z) := by
  by_cases htop : analyticOrderAt f z₀ = ⊤
  · refine ⟨fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    simpa using hz
  · obtain ⟨g, hg, -, hgeq⟩ := hf.analyticOrderAt_ne_top.mp htop
    have hne : analyticOrderAt f z₀ ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hf, h0⟩
    have hn : analyticOrderNatAt f z₀ ≠ 0 := by
      simp only [analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero]
      exact fun h => h.elim hne htop
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hpoly : AnalyticAt ℝ (fun z : ℝ => (z - z₀) ^ m) z₀ :=
      (analyticAt_id.sub analyticAt_const).pow m
    refine ⟨fun z => (z - z₀) ^ m * g z, hpoly.mul hg, ?_⟩
    filter_upwards [hgeq] with z hz
    rw [hz, hm]
    simp only [smul_eq_mul, Nat.succ_eq_add_one, pow_succ]
    ring

/-! ### Elementary differentiation helpers -/

/-- Points near `0` satisfy `1 + x ≠ 0`. -/
private theorem eventually_one_add_ne_zero : ∀ᶠ x in 𝓝 (0 : ℝ), (1 : ℝ) + x ≠ 0 := by
  filter_upwards [eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)] with x hx
  exact ne_of_gt (by linarith)

/-- Derivative of `y ↦ c * (1 + y) ^ m` for an integer exponent `m`. -/
private theorem hasDerivAt_const_mul_zpow (c : ℝ) (m : ℤ) {x : ℝ} (hx : (1 : ℝ) + x ≠ 0) :
    HasDerivAt (fun y : ℝ => c * (1 + y) ^ m) (c * ((m : ℝ) * (1 + x) ^ (m - 1))) x := by
  have h : HasDerivAt (fun y : ℝ => (1 + y) ^ m) ((m : ℝ) * (1 + x) ^ (m - 1)) x :=
    HasDerivAt.comp_const_add 1 x (hasDerivAt_zpow m (1 + x) (Or.inl hx))
  exact h.const_mul c

/-- The derivative of `y ↦ c * (1 + y) ^ m`, in `deriv` form. -/
private theorem deriv_const_mul_zpow (c : ℝ) (m : ℤ) {x : ℝ} (hx : (1 : ℝ) + x ≠ 0) :
    deriv (fun y : ℝ => c * (1 + y) ^ m) x = c * (m : ℝ) * (1 + x) ^ (m - 1) := by
  rw [(hasDerivAt_const_mul_zpow c m hx).deriv]
  ring

/-- Derivative of `y ↦ y * p y` at a point where `p` is analytic. -/
private theorem deriv_id_mul {p : ℝ → ℝ} {x : ℝ} (hp : AnalyticAt ℝ p x) :
    deriv (fun y : ℝ => y * p y) x = p x + x * deriv p x := by
  have h : HasDerivAt (fun y : ℝ => y * p y) (1 * p x + x * deriv p x) x :=
    (hasDerivAt_id' x).mul hp.differentiableAt.hasDerivAt
  rw [h.deriv]
  ring

/-- Derivative of `y ↦ c * p y + y * p' y` at a point where `p` is analytic. -/
private theorem deriv_add_id_mul {p : ℝ → ℝ} (c : ℝ) {x : ℝ} (hp : AnalyticAt ℝ p x) :
    deriv (fun y : ℝ => c * p y + y * deriv p y) x
      = (c + 1) * deriv p x + x * deriv (deriv p) x := by
  have h1 : HasDerivAt p (deriv p x) x := hp.differentiableAt.hasDerivAt
  have h2 : HasDerivAt (deriv p) (deriv (deriv p) x) x := hp.deriv.differentiableAt.hasDerivAt
  have h : HasDerivAt (fun y : ℝ => c * p y + y * deriv p y)
      (c * deriv p x + (1 * deriv p x + x * deriv (deriv p) x)) x :=
    (h1.const_mul c).add ((hasDerivAt_id' x).mul h2)
  rw [h.deriv]
  ring

/-- Derivative of `y ↦ (1 + y) * p y - 1` at a point where `p` is analytic. -/
private theorem deriv_one_add_mul_sub_one {p : ℝ → ℝ} {x : ℝ} (hp : AnalyticAt ℝ p x) :
    deriv (fun y : ℝ => (1 + y) * p y - 1) x = 1 * p x + (1 + x) * deriv p x := by
  have h0 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id' x).const_add (1 : ℝ)
  have h : HasDerivAt (fun y : ℝ => (1 + y) * p y - 1)
      (1 * p x + (1 + x) * deriv p x) x :=
    (h0.mul hp.differentiableAt.hasDerivAt).sub_const (1 : ℝ)
  rw [h.deriv]

/-- Derivative of `y ↦ c * p y + (1 + y) * p' y` at a point where `p` is analytic. -/
private theorem deriv_add_one_add_mul {p : ℝ → ℝ} (c : ℝ) {x : ℝ} (hp : AnalyticAt ℝ p x) :
    deriv (fun y : ℝ => c * p y + (1 + y) * deriv p y) x
      = (c + 1) * deriv p x + (1 + x) * deriv (deriv p) x := by
  have h0 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id' x).const_add (1 : ℝ)
  have h1 : HasDerivAt p (deriv p x) x := hp.differentiableAt.hasDerivAt
  have h2 : HasDerivAt (deriv p) (deriv (deriv p) x) x := hp.deriv.differentiableAt.hasDerivAt
  have h : HasDerivAt (fun y : ℝ => c * p y + (1 + y) * deriv p y)
      (c * deriv p x + (1 * deriv p x + (1 + x) * deriv (deriv p) x)) x :=
    (h1.const_mul c).add (h0.mul h2)
  rw [h.deriv]
  ring

/-- `x ↦ log (1 + x)` is analytic at `0`. -/
private theorem analyticAt_log_one_add : AnalyticAt ℝ (fun x : ℝ => Real.log (1 + x)) 0 := by
  have h : AnalyticAt ℝ (fun x : ℝ => 1 + x) 0 := analyticAt_const.add analyticAt_id
  exact h.log (by norm_num)

/-! ### The filled quotient `logQuot` -/

/-- `logQuot x = log(1+x)/x`, filled with `1` at `x = 0`. -/
noncomputable def logQuot (x : ℝ) : ℝ := if x = 0 then 1 else Real.log (1 + x) / x

/-- The filled value of `logQuot` at the origin. -/
theorem logQuot_zero : logQuot 0 = 1 := if_pos rfl

/-- Off the origin, `logQuot` is the genuine quotient. -/
private theorem logQuot_of_ne_zero {x : ℝ} (h : x ≠ 0) : logQuot x = Real.log (1 + x) / x :=
  if_neg h

/-- The defining identity for `logQuot`, valid at every real point. -/
private theorem log_one_add_eq (x : ℝ) : Real.log (1 + x) = x * logQuot x := by
  rcases eq_or_ne x 0 with rfl | h
  · simp [logQuot_zero]
  · rw [logQuot_of_ne_zero h]
    field_simp

/-- `logQuot` is real-analytic at the origin: the singularity of `log (1 + x) / x` is removable. -/
theorem analyticAt_logQuot : AnalyticAt ℝ logQuot 0 := by
  have h0 : (fun x : ℝ => Real.log (1 + x)) 0 = 0 := by norm_num
  obtain ⟨g, hg, hgeq⟩ := exists_factor_of_analyticAt analyticAt_log_one_add h0
  have hd : HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    have h : HasDerivAt (fun x : ℝ => Real.log (1 + x)) ((1 + (0 : ℝ))⁻¹) 0 :=
      HasDerivAt.comp_const_add 1 0 (Real.hasDerivAt_log (by norm_num))
    simpa using h
  have hmul : HasDerivAt (fun z : ℝ => (z - 0) * g z) (g 0) 0 := by
    have h : HasDerivAt (fun z : ℝ => (z - 0) * g z)
        (1 * g 0 + (0 - 0) * deriv g 0) 0 :=
      ((hasDerivAt_id' (0 : ℝ)).sub_const (0 : ℝ)).mul hg.differentiableAt.hasDerivAt
    simpa only [one_mul, sub_self, zero_mul, add_zero] using h
  have hg0 : g 0 = 1 := (hd.unique (hmul.congr_of_eventuallyEq hgeq)).symm
  refine hg.congr ?_
  filter_upwards [hgeq] with z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [hg0, logQuot_zero]
  · have hcancel : z * logQuot z = z * g z := by
      linear_combination hz - log_one_add_eq z
    exact (mul_left_cancel₀ hz0 hcancel).symm

/-- The defining identity `log (1 + x) = x * logQuot x`. -/
theorem log_one_add_eq_mul_logQuot {x : ℝ} (hx : -1 < x) :
    Real.log (1 + x) = x * logQuot x := by
  rcases eq_or_ne x 0 with rfl | h
  · simp [logQuot_zero]
  · have hpos : (0 : ℝ) < 1 + x := by linarith
    rw [logQuot_of_ne_zero h]
    field_simp [hpos.ne']

/-- The first three derivatives of `logQuot` at the origin. -/
private theorem logQuot_deriv_aux :
    deriv logQuot 0 = -(1 / 2) ∧ deriv (deriv logQuot) 0 = 2 / 3 ∧
      deriv (deriv (deriv logQuot)) 0 = -(3 / 2) := by
  have hne : ∀ᶠ x in 𝓝 (0 : ℝ), (1 : ℝ) + x ≠ 0 := eventually_one_add_ne_zero
  have han : ∀ᶠ x in 𝓝 (0 : ℝ), AnalyticAt ℝ logQuot x :=
    analyticAt_logQuot.eventually_analyticAt
  have h0 : (fun x : ℝ => Real.log (1 + x)) =ᶠ[𝓝 (0 : ℝ)] fun x : ℝ => x * logQuot x :=
    Eventually.of_forall log_one_add_eq
  have h1 : (fun x : ℝ => (1 : ℝ) * (1 + x) ^ (-1 : ℤ)) =ᶠ[𝓝 (0 : ℝ)]
      fun x : ℝ => (1 : ℝ) * logQuot x + x * deriv logQuot x := by
    filter_upwards [h0.deriv, hne, han] with x hd hx ha
    have hF : deriv (fun y : ℝ => Real.log (1 + y)) x = (1 : ℝ) * (1 + x) ^ (-1 : ℤ) := by
      have hdl : HasDerivAt (fun y : ℝ => Real.log (1 + y)) ((1 + x)⁻¹) x :=
        HasDerivAt.comp_const_add 1 x (Real.hasDerivAt_log hx)
      rw [hdl.deriv, one_mul, zpow_neg_one]
    rw [← hF, hd, deriv_id_mul ha]
    ring
  have h2 : (fun x : ℝ => (-1 : ℝ) * (1 + x) ^ (-2 : ℤ)) =ᶠ[𝓝 (0 : ℝ)]
      fun x : ℝ => (2 : ℝ) * deriv logQuot x + x * deriv (deriv logQuot) x := by
    filter_upwards [h1.deriv, hne, han] with x hd hx ha
    have hF : deriv (fun y : ℝ => (1 : ℝ) * (1 + y) ^ (-1 : ℤ)) x
        = (-1 : ℝ) * (1 + x) ^ (-2 : ℤ) := by
      rw [deriv_const_mul_zpow 1 (-1) hx]
      norm_num
    rw [← hF, hd, deriv_add_id_mul 1 ha]
    ring
  have h3 : (fun x : ℝ => (2 : ℝ) * (1 + x) ^ (-3 : ℤ)) =ᶠ[𝓝 (0 : ℝ)]
      fun x : ℝ => (3 : ℝ) * deriv (deriv logQuot) x + x * deriv (deriv (deriv logQuot)) x := by
    filter_upwards [h2.deriv, hne, han] with x hd hx ha
    have hF : deriv (fun y : ℝ => (-1 : ℝ) * (1 + y) ^ (-2 : ℤ)) x
        = (2 : ℝ) * (1 + x) ^ (-3 : ℤ) := by
      rw [deriv_const_mul_zpow (-1) (-2) hx]
      norm_num
    rw [← hF, hd, deriv_add_id_mul 2 ha.deriv]
    ring
  have h4 : (fun x : ℝ => (-6 : ℝ) * (1 + x) ^ (-4 : ℤ)) =ᶠ[𝓝 (0 : ℝ)]
      fun x : ℝ => (4 : ℝ) * deriv (deriv (deriv logQuot)) x
        + x * deriv (deriv (deriv (deriv logQuot))) x := by
    filter_upwards [h3.deriv, hne, han] with x hd hx ha
    have hF : deriv (fun y : ℝ => (2 : ℝ) * (1 + y) ^ (-3 : ℤ)) x
        = (-6 : ℝ) * (1 + x) ^ (-4 : ℤ) := by
      rw [deriv_const_mul_zpow 2 (-3) hx]
      norm_num
    rw [← hF, hd, deriv_add_id_mul 3 ha.deriv.deriv]
    ring
  have e2 := h2.eq_of_nhds
  have e3 := h3.eq_of_nhds
  have e4 := h4.eq_of_nhds
  norm_num at e2 e3 e4
  refine ⟨by linarith, by linarith, by linarith⟩

/-- `logQuot' 0 = -1/2`. -/
theorem deriv_logQuot_zero : deriv logQuot 0 = -(1 / 2) := logQuot_deriv_aux.1

/-- `logQuot'' 0 = 2/3`. -/
theorem deriv2_logQuot_zero : deriv (deriv logQuot) 0 = 2 / 3 := logQuot_deriv_aux.2.1

/-- The third derivative of `logQuot` at the origin. -/
private theorem deriv3_logQuot_zero : deriv (deriv (deriv logQuot)) 0 = -(3 / 2) :=
  logQuot_deriv_aux.2.2

/-! ### The filled quotient `bennett` -/

/-- `bennett x = ((1+x)·log(1+x) - x)/x²`, filled with `1/2` at `x = 0`. -/
noncomputable def bennett (x : ℝ) : ℝ :=
  if x = 0 then 1/2 else ((1 + x) * Real.log (1 + x) - x) / x ^ 2

/-- The filled value of `bennett` at the origin. -/
theorem bennett_zero : bennett 0 = 1/2 := if_pos rfl

/-- Off the origin, `bennett` is the genuine quotient. -/
private theorem bennett_of_ne_zero {x : ℝ} (h : x ≠ 0) :
    bennett x = ((1 + x) * Real.log (1 + x) - x) / x ^ 2 :=
  if_neg h

/-- The identity linking `bennett` to `logQuot`, valid at every real point. -/
private theorem mul_bennett_eq (x : ℝ) : x * bennett x = (1 + x) * logQuot x - 1 := by
  rcases eq_or_ne x 0 with rfl | h
  · rw [bennett_zero, logQuot_zero]
    norm_num
  · rw [bennett_of_ne_zero h, logQuot_of_ne_zero h]
    field_simp

/-- `bennett` is real-analytic at the origin. -/
theorem analyticAt_bennett : AnalyticAt ℝ bennett 0 := by
  have hK : AnalyticAt ℝ (fun x : ℝ => (1 + x) * logQuot x - 1) 0 :=
    ((analyticAt_const.add analyticAt_id).mul analyticAt_logQuot).sub analyticAt_const
  have hK0 : (fun x : ℝ => (1 + x) * logQuot x - 1) 0 = 0 := by
    simp [logQuot_zero]
  obtain ⟨g, hg, hgeq⟩ := exists_factor_of_analyticAt hK hK0
  have hd : HasDerivAt (fun x : ℝ => (1 + x) * logQuot x - 1) (1 / 2 : ℝ) 0 := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 (0 : ℝ) :=
      (hasDerivAt_id' (0 : ℝ)).const_add (1 : ℝ)
    have h2 : HasDerivAt logQuot (-(1 / 2) : ℝ) 0 := by
      rw [← deriv_logQuot_zero]
      exact analyticAt_logQuot.differentiableAt.hasDerivAt
    have h4 : HasDerivAt (fun y : ℝ => (1 + y) * logQuot y - 1)
        ((1 : ℝ) * logQuot 0 + (1 + 0) * -(1 / 2)) 0 := (h1.mul h2).sub_const (1 : ℝ)
    have e : (1 : ℝ) * logQuot 0 + (1 + 0) * -(1 / 2) = 1 / 2 := by
      rw [logQuot_zero]
      norm_num
    rw [← e]
    exact h4
  have hmul : HasDerivAt (fun z : ℝ => (z - 0) * g z) (g 0) 0 := by
    have h : HasDerivAt (fun z : ℝ => (z - 0) * g z)
        (1 * g 0 + (0 - 0) * deriv g 0) 0 :=
      ((hasDerivAt_id' (0 : ℝ)).sub_const (0 : ℝ)).mul hg.differentiableAt.hasDerivAt
    simpa only [one_mul, sub_self, zero_mul, add_zero] using h
  have hg0 : g 0 = 1 / 2 := (hd.unique (hmul.congr_of_eventuallyEq hgeq)).symm
  refine hg.congr ?_
  filter_upwards [hgeq] with z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [hg0, bennett_zero]
  · have hcancel : z * bennett z = z * g z := by
      linear_combination mul_bennett_eq z + hz
    exact (mul_left_cancel₀ hz0 hcancel).symm

/-- The defining identity `(1 + x) * log (1 + x) - x = x ^ 2 * bennett x`. -/
theorem one_add_mul_log_eq {x : ℝ} (hx : -1 < x) :
    (1 + x) * Real.log (1 + x) - x = x ^ 2 * bennett x := by
  rcases eq_or_ne x 0 with rfl | h
  · rw [bennett_zero]
    norm_num
  · have hpos : (0 : ℝ) < 1 + x := by linarith
    rw [bennett_of_ne_zero h]
    field_simp [hpos.ne']

/-- The first two derivatives of `bennett` at the origin. -/
private theorem bennett_deriv_aux :
    deriv bennett 0 = -(1 / 6) ∧ deriv (deriv bennett) 0 = 1 / 6 := by
  have han : ∀ᶠ x in 𝓝 (0 : ℝ), AnalyticAt ℝ logQuot x :=
    analyticAt_logQuot.eventually_analyticAt
  have hbn : ∀ᶠ x in 𝓝 (0 : ℝ), AnalyticAt ℝ bennett x :=
    analyticAt_bennett.eventually_analyticAt
  have k0 : (fun x : ℝ => (1 + x) * logQuot x - 1) =ᶠ[𝓝 (0 : ℝ)] fun x : ℝ => x * bennett x :=
    Eventually.of_forall fun x => (mul_bennett_eq x).symm
  have k1 : (fun x : ℝ => (1 : ℝ) * logQuot x + (1 + x) * deriv logQuot x) =ᶠ[𝓝 (0 : ℝ)]
      fun x : ℝ => (1 : ℝ) * bennett x + x * deriv bennett x := by
    filter_upwards [k0.deriv, han, hbn] with x hd ha hb
    rw [← deriv_one_add_mul_sub_one ha, hd, deriv_id_mul hb]
    ring
  have k2 : (fun x : ℝ => (2 : ℝ) * deriv logQuot x + (1 + x) * deriv (deriv logQuot) x)
      =ᶠ[𝓝 (0 : ℝ)] fun x : ℝ => (2 : ℝ) * deriv bennett x + x * deriv (deriv bennett) x := by
    filter_upwards [k1.deriv, han, hbn] with x hd ha hb
    have hQ : deriv (fun y : ℝ => (1 : ℝ) * logQuot y + (1 + y) * deriv logQuot y) x
        = (2 : ℝ) * deriv logQuot x + (1 + x) * deriv (deriv logQuot) x := by
      rw [deriv_add_one_add_mul 1 ha]
      ring
    rw [← hQ, hd, deriv_add_id_mul 1 hb]
    ring
  have k3 : (fun x : ℝ => (3 : ℝ) * deriv (deriv logQuot) x
        + (1 + x) * deriv (deriv (deriv logQuot)) x) =ᶠ[𝓝 (0 : ℝ)]
      fun x : ℝ => (3 : ℝ) * deriv (deriv bennett) x + x * deriv (deriv (deriv bennett)) x := by
    filter_upwards [k2.deriv, han, hbn] with x hd ha hb
    have hQ : deriv
          (fun y : ℝ => (2 : ℝ) * deriv logQuot y + (1 + y) * deriv (deriv logQuot) y) x
        = (3 : ℝ) * deriv (deriv logQuot) x + (1 + x) * deriv (deriv (deriv logQuot)) x := by
      rw [deriv_add_one_add_mul 2 ha.deriv]
      ring
    rw [← hQ, hd, deriv_add_id_mul 2 hb.deriv]
    ring
  have f2 := k2.eq_of_nhds
  have f3 := k3.eq_of_nhds
  rw [deriv_logQuot_zero, deriv2_logQuot_zero] at f2
  rw [deriv2_logQuot_zero, deriv3_logQuot_zero] at f3
  norm_num at f2 f3
  exact ⟨by linarith, by linarith⟩

/-- `bennett' 0 = -1/6`. -/
theorem deriv_bennett_zero : deriv bennett 0 = -(1 / 6) := bennett_deriv_aux.1

/-- `bennett'' 0 = 1/6`. -/
theorem deriv2_bennett_zero : deriv (deriv bennett) 0 = 1 / 6 := bennett_deriv_aux.2

/-- `bennett` is twice differentiable near `0`, in the form needed downstream. -/
theorem analyticAt_deriv_bennett : AnalyticAt ℝ (deriv bennett) 0 := analyticAt_bennett.deriv

end UpperTailOptimizers
