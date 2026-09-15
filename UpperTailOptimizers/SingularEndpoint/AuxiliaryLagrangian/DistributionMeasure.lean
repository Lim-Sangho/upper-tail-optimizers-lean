import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.TailScalar

/-!
# The measure half of the tail-uniform two-point interpolation (Section 5)

The closed-window route to `lem:auxiliary-lagrangian-bound` in
`SingularEndpoint/AuxiliaryLagrangian/DistributionQuant.lean` bounds the mixed rectangles by pairing
the two-node interpolation error of `SingularEndpoint/AuxiliaryLagrangian/TailScalar.lean` against a probability measure
on the law interval `[0,2]`.  The scalar half — the interpolation itself, the coefficient
bounds `|A|, |B| ≤ C L_h`, the pointwise estimate `|g(u)| ≤ C L_h δ(u)^{3/4}` and the well
inequality `δ(u)² ≤ |Q_h(u)|` — is `SingularEndpoint/AuxiliaryLagrangian/TailScalar.lean`.  **This file is the measure
half**, and it ends at `KKTFamily.exists_tail_interpolation`, the bound on the window integral
`∫_{𝓝_ρ}J̃_{p_h}(x̃u)dσ(u)` at a frozen point `x̃ ∈ [0,2]`.  This interpolation is not the
paper's: for `y ∈ 𝒯_ρ` the proof of `lem:auxiliary-lagrangian-bound` bounds
`∫_{𝒩_ρ}K_h(x,y)dσ(x)` by subtracting `K_h(u_h,y)` and applying the `1/2`-Hölder bound of
`lem:continuation-kernel-bounds`.

`SingularEndpoint/` contained no measure-on-an-interval material before this file, so the first two
sections set up vocabulary that the rest of that route reuses: the central window
`𝓝_ρ` (`centralWindow`), the two-atom candidate law `ν_h` (`distributionMeasure`), the
integrability package for measures carried by `[0,2]`, and the concave Jensen inequality on a
set of mass at most one.

## No signed measures

The paper writes `σ := ξ - ν_h` (with `ξ = ν` in the proof of `lem:auxiliary-lagrangian-bound`)
and integrates against `σ`.  This file writes each such integral as "integral against `ν`
minus integral against `ν_h`" and never forms a `SignedMeasure`.  That is mathematically the
same statement — both integrals converge separately, since each integrand is continuous on the
compact `[0,2]` and both measures are finite — and it avoids the `MeasureTheory.SignedMeasure`
API entirely.  It is a presentation choice, not a weakening.

## The route

The three estimates combined in `exists_tail_interpolation` are its three `have`s.

* **The `g` term.**  `g` vanishes at both atoms (`gfun_sVal`, `gfun_tVal`), so
  its integral against `ν_h` is `0` and the whole difference is its integral against `ν` over
  the window.  The integrated Hölder chain
  `∫δ^{3/4} ≤ (∫δ²)^{3/8} ≤ (∫|Q_h|)^{3/8} ≤ A_ρ^{3/16}` is short-circuited here: the
  pointwise well inequality `δ(u)² ≤ |Q_h(u)|` gives at once
  `δ(u)^{3/4} ≤ (Q_h(u)²)^{3/16}` (`rpow_three_quarters_le_rpow_sq`), and a single concave
  Jensen step with exponent `3/16` (`setIntegral_rpow_le_rpow_setIntegral`) finishes.  Jensen
  is proved from scratch here — from the two-point weighted AM–GM
  `Real.geom_mean_le_arith_mean2_weighted` through the tangent line `x^θ ≤ θx + (1-θ)` — and
  is stated for a set of mass at most `1`, not for a probability measure, because the window
  carries only part of the mass of `ν`.
* **The mass term.**  `ν(𝓝_ρ) = 1 - ε_ρ`, where `ε_ρ = ν([0,2] ∖ 𝓝_ρ)` is the closed-window
  tail mass (the paper's `ν(𝒯_ρ)` is over the open window), from `ν([0,2]) = 1` and additivity across
  `𝓝_ρ`.
* **The moment term.**  The two `d`-th moments over the window differ by
  `Δ_h(ν) - ∫_{[0,2]∖𝓝_ρ} u^d dν`, and the tail integral is at most `2^d ε_ρ` because
  `0 ≤ u ≤ 2` there.

They are combined through `φ(u) = A + B u^d + g(u)`, which is the definition of `gfun`, and
`exists_coef_bound`.

## Contents

* `centralWindow` — the coalescence window `𝓝_ρ = [u_* - ρ, u_* + ρ]`, with
  `isCompact_centralWindow` and `measurableSet_centralWindow`;
* `ae_mem_Icc_of_distribution`, `restrict_Icc_inter`, `restrict_Icc_self`,
  `integrableOn_of_continuousOn` — the integrability package for a measure carried by `[0,2]`;
* `setIntegral_rpow_le_rpow_setIntegral` — concave Jensen with exponent `θ ∈ (0,1]` on a set
  of mass at most `1`;
* `KKTFamily.distributionMeasure` — the two-atom candidate law `ν_h`, with
  `integral_distributionMeasure`, `isProbabilityMeasure_distributionMeasure`,
  `distributionMeasure_restrict_of_mem` and `integral_pow_distributionMeasure` (its `d`-th moment is
  `q_h`, which is the definition of `qVal`);
* `KKTFamily.exists_atoms_mem_centralWindow` — both atoms lie in the window once `h` is
  small;
* `KKTFamily.exists_tail_interpolation` — the window-integral bound used for the mixed
  rectangles of the closed-window route to `lem:auxiliary-lagrangian-bound`;
* `KKTFamily.continuousOn_JpTildeH`, `.continuousOn_distributionIntegrand` — continuity of
  the displaced continued entropy on `[0,4]` and of its frozen slice on `[0,2]`, shared with
  `SingularEndpoint/AuxiliaryLagrangian/DistributionGap.lean` and `SingularEndpoint/AuxiliaryLagrangian/DistributionQuant.lean`.
-/

namespace UpperTailOptimizers

open Filter MeasureTheory Topology

variable {d : ℕ}

/-! ## The central window -/

/-- **The closed coalescence window** `[u_* - ρ, u_* + ρ]` around the singular endpoint value
`u_*`.  The two atoms of the candidate law sit inside it once `h` is small, and the closed-window
estimates of this development are stated for integrals over it.

**Deviation.**  The paper's `𝒩_ρ := (u_* - ρ, u_* + ρ)` of `sec:auxiliary-lagrangian` is the
*open* interval `openWindow d ρ`.  A pointwise estimate "for all `x ∈ 𝒩_ρ`" proved on the closed
interval is stronger, but integrals and tail masses over the two sets differ for measures with
atoms at `u_* ± ρ`, such as the law of a factor, so the closed-window integral estimates do not
imply the open-window ones.  The paper-form statements with the open window are `first_variation_bound`,
`central_kernel_bound`, `auxiliary_lagrangian_bound` and `graphon_lagrangian_bound`.  The closed
form is kept here because `isCompact_centralWindow` is used to extract uniform bounds. -/
def centralWindow (d : ℕ) (ρ : ℝ) : Set ℝ := Set.Icc (uStar d - ρ) (uStar d + ρ)

/-- The window is compact, being a closed bounded interval. -/
theorem isCompact_centralWindow (d : ℕ) (ρ : ℝ) : IsCompact (centralWindow d ρ) := isCompact_Icc

/-- The window is measurable. -/
theorem measurableSet_centralWindow (d : ℕ) (ρ : ℝ) : MeasurableSet (centralWindow d ρ) :=
  measurableSet_Icc

/-! ## Measures carried by the law interval

The law problem ranges over probability measures on `[0,2]`, which is expressed here as
`ν ([0,2])ᶜ = 0` rather than by a subtype.  These four lemmas are everything the rest of the
file — and `lem:auxiliary-lagrangian-bound` after it — needs about that hypothesis. -/

/-- A measure giving no mass outside `[0,2]` is almost everywhere carried by `[0,2]`. -/
theorem ae_mem_Icc_of_distribution {ν : Measure ℝ} (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) :
    ∀ᵐ u ∂ν, u ∈ Set.Icc (0 : ℝ) 2 := by
  have h : Set.Icc (0 : ℝ) 2 ∈ MeasureTheory.ae ν := mem_ae_iff.mpr hν
  exact h

/-- Restricting to `[0,2] ∩ s` is the same as restricting to `s`. -/
theorem restrict_Icc_inter {ν : Measure ℝ} (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) (s : Set ℝ) :
    ν.restrict (Set.Icc (0 : ℝ) 2 ∩ s) = ν.restrict s := by
  rw [← Measure.restrict_restrict measurableSet_Icc]
  exact Measure.restrict_eq_self_of_ae_mem (ae_restrict_of_ae (ae_mem_Icc_of_distribution hν))

/-- Restricting to `[0,2]` changes nothing. -/
theorem restrict_Icc_self {ν : Measure ℝ} (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) :
    ν.restrict (Set.Icc (0 : ℝ) 2) = ν :=
  Measure.restrict_eq_self_of_ae_mem (ae_mem_Icc_of_distribution hν)

/-- **The integrability package.**  A function continuous on the law interval is
integrable over any compact set against a finite measure carried by `[0,2]`.

The set itself need not be contained in `[0,2]` — `centralWindow d ρ` is not, for large `ρ` —
because the measure sees only its intersection with `[0,2]`, which is again compact. -/
theorem integrableOn_of_continuousOn {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 2))
    {s : Set ℝ} (hs : IsCompact s) : IntegrableOn f s ν := by
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K _ => measure_lt_top ν K⟩
  have h : IntegrableOn f (Set.Icc (0 : ℝ) 2 ∩ s) ν :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.inter hs)
      (hf.mono Set.inter_subset_left)
  rwa [IntegrableOn, restrict_Icc_inter hν] at h

/-! ## Concave Jensen on a set of mass at most one -/

/-- The tangent line to `x ↦ x^θ` at `x = 1`: `x^θ ≤ θx + (1-θ)` for `x ≥ 0` and
`0 ≤ θ ≤ 1`.  This is the two-point weighted AM–GM with weights `θ, 1-θ` at `x` and `1`. -/
private theorem rpow_le_lin {θ x : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hx : 0 ≤ x) :
    x ^ θ ≤ θ * x + (1 - θ) := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := θ) (w₂ := 1 - θ) (p₁ := x)
    (p₂ := 1) hθ0 (by linarith) hx zero_le_one (by ring)
  rw [Real.one_rpow, mul_one, mul_one] at h
  exact h

/-- **Concave Jensen with exponent `θ ∈ (0,1]` on a set of mass at most `1`:**

`∫_s g^θ dν ≤ (∫_s g dν)^θ`   for `g ≥ 0` almost everywhere on `s`.

Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le` is stated for a probability
measure, whereas `ν.restrict s` here has mass `ν s ≤ 1` only.  The proof below is direct: at
`S = ∫_s g dν > 0` the tangent line of `rpow_le_lin` gives the pointwise bound
`g^θ ≤ S^θ θ g / S + S^θ (1-θ)`, whose integral is `S^θ (θ + (1-θ) ν(s)) ≤ S^θ`; the
degenerate case `S = 0` forces `g = 0` almost everywhere on `s`. -/
theorem setIntegral_rpow_le_rpow_setIntegral {ν : Measure ℝ} [IsFiniteMeasure ν] {g : ℝ → ℝ}
    {s : Set ℝ} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hmass : ν s ≤ 1)
    (hg0 : ∀ᵐ u ∂(ν.restrict s), 0 ≤ g u) (hgint : IntegrableOn g s ν)
    (hgθ : IntegrableOn (fun u => g u ^ θ) s ν) :
    ∫ u in s, g u ^ θ ∂ν ≤ (∫ u in s, g u ∂ν) ^ θ := by
  have hS0 : 0 ≤ ∫ u in s, g u ∂ν := integral_nonneg_of_ae hg0
  rcases eq_or_lt_of_le hS0 with hS | hS
  · have hz : (fun u => g u) =ᵐ[ν.restrict s] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hg0 hgint).mp hS.symm
    have h1 : ∫ u in s, g u ^ θ ∂ν = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · filter_upwards [hz] with u hu
        simp only [Pi.zero_apply] at hu
        rw [hu, Real.zero_rpow (ne_of_gt hθ0)]
    rw [h1, ← hS, Real.zero_rpow (ne_of_gt hθ0)]
  · set S := ∫ u in s, g u ∂ν with hSdef
    have hSθ : 0 < S ^ θ := Real.rpow_pos_of_pos hS θ
    have key : ∀ᵐ u ∂(ν.restrict s),
        g u ^ θ ≤ S ^ θ * θ / S * g u + S ^ θ * (1 - θ) := by
      filter_upwards [hg0] with u hu
      have hxθ : (g u / S) ^ θ ≤ θ * (g u / S) + (1 - θ) :=
        rpow_le_lin hθ0.le hθ1 (div_nonneg hu hS.le)
      have hrw : g u ^ θ = S ^ θ * (g u / S) ^ θ := by
        rw [← Real.mul_rpow hS.le (div_nonneg hu hS.le)]
        congr 1
        field_simp
      have hmul := mul_le_mul_of_nonneg_left hxθ hSθ.le
      rw [← hrw] at hmul
      have he : S ^ θ * (θ * (g u / S) + (1 - θ))
          = S ^ θ * θ / S * g u + S ^ θ * (1 - θ) := by
        field_simp
      linarith [he ▸ hmul]
    have hm : ν.real s ≤ 1 := by
      have h := ENNReal.toReal_mono (by simp) hmass
      simpa [measureReal_def] using h
    have hint2 : IntegrableOn (fun u => S ^ θ * θ / S * g u + S ^ θ * (1 - θ)) s ν :=
      (hgint.const_mul _).add integrableOn_const
    calc ∫ u in s, g u ^ θ ∂ν
        ≤ ∫ u in s, (S ^ θ * θ / S * g u + S ^ θ * (1 - θ)) ∂ν :=
          integral_mono_ae hgθ hint2 key
      _ = S ^ θ * θ / S * S + S ^ θ * (1 - θ) * ν.real s := by
          rw [integral_add (hgint.const_mul _) integrableOn_const, integral_const_mul,
            setIntegral_const, smul_eq_mul, ← hSdef]
          ring
      _ ≤ S ^ θ := by
          have h1 : S ^ θ * θ / S * S = S ^ θ * θ := by field_simp
          have h2 : 0 ≤ S ^ θ * (1 - θ) := mul_nonneg hSθ.le (by linarith)
          nlinarith

/-! ## An elementary rearrangement -/

/-- **The short circuit of the Hölder chain.**  If `0 ≤ a` and `a² ≤ |b|`, then
`a^{3/4} ≤ (b²)^{3/16}`.

The chain `∫δ^{3/4} ≤ (∫δ²)^{3/8} ≤ (∫|Q_h|)^{3/8} ≤ A_ρ^{3/16}` takes
three integrated steps.  Pointwise the same three steps collapse to
`a^{3/4} = (a²)^{3/8} ≤ |b|^{3/8} = (b²)^{3/16}`, leaving a single concave Jensen step with
exponent `3/16` to be done at the level of integrals. -/
private theorem rpow_three_quarters_le_rpow_sq {a b : ℝ} (ha : 0 ≤ a) (hab : a ^ 2 ≤ |b|) :
    a ^ (3 / 4 : ℝ) ≤ (b ^ 2) ^ (3 / 16 : ℝ) := by
  have h1 : a ^ (3 / 4 : ℝ) = (a ^ 2) ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha]
    norm_num
  have h2 : (b ^ 2) ^ (3 / 16 : ℝ) = |b| ^ (3 / 8 : ℝ) := by
    rw [← sq_abs b, ← Real.rpow_natCast |b| 2, ← Real.rpow_mul (abs_nonneg b)]
    norm_num
  rw [h1, h2]
  exact Real.rpow_le_rpow (sq_nonneg a) hab (by norm_num)

namespace KKTFamily

/-! ## The candidate law `ν_h` -/

/-- **The candidate law `ν_h`** of `sec:auxiliary-lagrangian`: the two-atom
probability measure `α_h δ_{s_h} + (1-α_h) δ_{t_h}` carried by the two factor values of the
family.  Its `d`-th moment is `q_h` by the definition of `qVal`
(`integral_pow_distributionMeasure`). -/
noncomputable def distributionMeasure (B : KKTFamily d) (h : ℝ) : MeasureTheory.Measure ℝ :=
  ENNReal.ofReal (B.alph h) • MeasureTheory.Measure.dirac (B.sVal h)
    + ENNReal.ofReal (1 - B.alph h) • MeasureTheory.Measure.dirac (B.tVal h)

/-- **Integration against the candidate law** is the two-point average
`α_h f(s_h) + (1-α_h) f(t_h)`.  No measurability of `f` is needed: `MeasureTheory.integral_dirac`
holds for arbitrary `f` on a space with measurable singletons, and each atom carries finite
mass, so `MeasureTheory.integral_add_measure` applies. -/
theorem integral_distributionMeasure (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) (f : ℝ → ℝ) :
    ∫ u, f u ∂(B.distributionMeasure h)
      = B.alph h * f (B.sVal h) + (1 - B.alph h) * f (B.tVal h) := by
  have ha := B.alph_mem h hh
  have hi1 : Integrable f (ENNReal.ofReal (B.alph h) • Measure.dirac (B.sVal h)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hi2 : Integrable f (ENNReal.ofReal (1 - B.alph h) • Measure.dirac (B.tVal h)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [distributionMeasure, integral_add_measure hi1 hi2, integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal ha.1.le,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - B.alph h), smul_eq_mul, smul_eq_mul]

/-- **The candidate law is a probability measure**, because `0 < α_h < 1`
(`KKTFamily.alph_mem`) makes the two weights nonnegative reals summing to `1`. -/
theorem isProbabilityMeasure_distributionMeasure (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) :
    IsProbabilityMeasure (B.distributionMeasure h) := by
  have ha := B.alph_mem h hh
  constructor
  rw [distributionMeasure]
  simp only [Measure.coe_add, Pi.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
  rw [← ENNReal.ofReal_add ha.1.le (by linarith : (0 : ℝ) ≤ 1 - B.alph h)]
  norm_num

/-- **Restricting the candidate law to a set containing both atoms changes nothing.**
This is what makes the window integral against `ν_h` in `lem:auxiliary-lagrangian-bound` equal to
the full integral. -/
theorem distributionMeasure_restrict_of_mem (B : KKTFamily d) {h : ℝ} {s : Set ℝ}
    (hs : B.sVal h ∈ s) (ht : B.tVal h ∈ s) :
    (B.distributionMeasure h).restrict s = B.distributionMeasure h := by
  classical
  rw [distributionMeasure, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
    restrict_dirac, restrict_dirac, if_pos hs, if_pos ht]

/-- **The `d`-th moment of the candidate law is `q_h`** — which is the definition of
`KKTFamily.qVal`. -/
theorem integral_pow_distributionMeasure (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) :
    ∫ u, u ^ d ∂(B.distributionMeasure h) = B.qVal h := by
  rw [integral_distributionMeasure B hh (fun u => u ^ d), qVal]

/-! ## The atoms enter the window -/

/-- **Both atoms lie in the central window once `h` is small.**  Since `s_h = u_h - h` and
`t_h = u_h + h` with `u_h → u_*`, taking `|u_h - u_*| < ρ/2` and `h < ρ/2` puts both inside
`𝓝_ρ`.  Consequently the window carries all the mass of `ν_h`
(`distributionMeasure_restrict_of_mem`). -/
theorem exists_atoms_mem_centralWindow (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      B.sVal h ∈ centralWindow d ρ ∧ B.tVal h ∈ centralWindow d ρ := by
  have hcu : ContinuousAt B.u 0 := u_continuousAt B
  have hev : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), |B.u h - uStar d| < ρ / 2 := by
    have h := Metric.tendsto_nhds.mp hcu (ρ / 2) (by linarith)
    simpa [Real.dist_eq, B.u_zero] using h
  obtain ⟨δ₁, hδ₁, hprop⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min δ₁ (ρ / 2), lt_min hδ₁ (by linarith), ?_⟩
  intro h hh0 hhδ
  have hdist : dist h (0 : ℝ) < δ₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
    exact lt_of_lt_of_le hhδ (min_le_left _ _)
  have hh2 : h < ρ / 2 := lt_of_lt_of_le hhδ (min_le_right _ _)
  have hu := abs_lt.mp (hprop hdist)
  have hs : B.sVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := by
    simp only [sVal]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have ht : B.tVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := by
    simp only [tVal]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  exact ⟨hs, ht⟩

/-! ## Continuity of the integrands -/

/-- The displaced continued entropy is continuous on `[0,4]`: it is `J̃_{p_*}`
(`continuousOn_JpTilde`) plus an affine function. -/
theorem continuousOn_JpTildeH (hd : 2 ≤ d) (B : KKTFamily d) (h : ℝ) :
    ContinuousOn (B.JpTildeH h) (Set.Icc 0 4) := by
  have hcont : ContinuousOn (fun z : ℝ => JpTilde d z
      + (ell (B.p h) - ell (pStar d)) * z + (Jp (B.p h) 0 - Jp (pStar d) 0))
      (Set.Icc (0 : ℝ) 4) :=
    ((continuousOn_JpTilde hd).add (continuousOn_const.mul continuous_id.continuousOn)).add
      continuousOn_const
  exact hcont

/-- The law integrand `u ↦ J̃_{p_h}(x̃u)` is continuous on `[0,2]`, because `x̃ ∈ [0,2]`
maps `[0,2]` into `[0,4]`, which is where the continuation lives. -/
theorem continuousOn_distributionIntegrand (hd : 2 ≤ d) (B : KKTFamily d) (h : ℝ)
    {xt : ℝ} (hxt0 : 0 ≤ xt) (hxt2 : xt ≤ 2) :
    ContinuousOn (fun u => B.JpTildeH h (xt * u)) (Set.Icc 0 2) := by
  have hmaps : Set.MapsTo (fun u : ℝ => xt * u) (Set.Icc (0 : ℝ) 2) (Set.Icc (0 : ℝ) 4) := by
    intro u hu
    exact ⟨mul_nonneg hxt0 hu.1, by nlinarith [hu.1, hu.2]⟩
  exact (continuousOn_JpTildeH hd B h).comp
    (continuous_const.mul continuous_id).continuousOn hmaps

/-! ## The window integral against `σ` -/

/-- **The window integral against `σ`**, the estimate the closed-window route to
`lem:auxiliary-lagrangian-bound` uses for the mixed rectangles (the paper uses the
`1/2`-Hölder bound instead; see the module docstring).  For every window
radius `ρ > 0` there are `C > 0` and `δ > 0` such that, for `0 < h < δ` inside the family
window, every probability measure `ν` carried by `[0,2]` and every `x̃ ∈ [0,2]`,

`|∫_{𝓝_ρ} J̃_{p_h}(x̃u) dν - ∫_{𝓝_ρ} J̃_{p_h}(x̃u) dν_h| ≤ C L_h (ε_ρ + |Δ_h(ν)| + A_ρ^{3/16})`

with `L_h = 1 + log(1/h)`, `ε_ρ = ν([0,2] ∖ 𝓝_ρ)`, `Δ_h(ν) = m_d(ν) - q_h` and
`A_ρ = ∫_{𝓝_ρ} Q_h² dν`.

The integral against `σ = ν - ν_h` is written out as a difference of two integrals; see the
module docstring.  The proof combines the three estimates listed in the module docstring through
`φ(u) = A + B u^d + g(u)`, which is the definition of `KKTFamily.gfun`, and the
coefficient bound `exists_coef_bound`. -/
theorem exists_tail_interpolation (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ0 : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → |h| < B.h₀ →
      ∀ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure ν →
        ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 → ∀ xt ∈ Set.Icc (0 : ℝ) 2,
          |(∫ u in centralWindow d ρ, B.JpTildeH h (xt * u) ∂ν)
             - (∫ u in centralWindow d ρ, B.JpTildeH h (xt * u) ∂(B.distributionMeasure h))|
            ≤ C * (1 + Real.log (1 / h))
                * ((ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
                    + |(∫ u, u ^ d ∂ν) - B.qVal h|
                    + (∫ u in centralWindow d ρ, B.Qh h u ^ 2 ∂ν) ^ (3 / 16 : ℝ)) := by
  obtain ⟨CC, hCC, δC, hδC, hcoef⟩ := exists_coef_bound hd B
  obtain ⟨Cg, hCg, δg, hδg, hgb⟩ := exists_gfun_bound hd B
  obtain ⟨δa, hδa, hatom⟩ := exists_atoms_mem_centralWindow B hρ0
  have h2d : (0 : ℝ) < 2 ^ d := pow_pos (by norm_num) d
  refine ⟨CC * (2 + 2 ^ d) + Cg, by nlinarith, min (min δC δg) (min δa 1),
    lt_min (lt_min hδC hδg) (lt_min hδa one_pos), ?_⟩
  intro h hh0 hhδ hhb ν hν hνc xt hxt
  have : IsProbabilityMeasure ν := hν
  have hδC' : h < δC := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδg' : h < δg := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδa' : h < δa := lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hh1 : h < 1 := lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hlog : 0 ≤ Real.log (1 / h) := by
    rw [one_div, Real.log_inv, neg_nonneg]
    exact Real.log_nonpos hh0.le hh1.le
  have hL : (0 : ℝ) ≤ 1 + Real.log (1 / h) := by linarith
  have hxt0 : (0 : ℝ) ≤ xt := hxt.1
  have hxt2 : xt ≤ 2 := hxt.2
  obtain ⟨hsW, htW⟩ := hatom h hh0 hδa'
  -- the integrands
  have hcphi : ContinuousOn (fun u => B.JpTildeH h (xt * u)) (Set.Icc 0 2) :=
    continuousOn_distributionIntegrand hd B h hxt0 hxt2
  have hcgfun : ContinuousOn (fun u => B.gfun h xt u) (Set.Icc 0 2) := by
    have hc : ContinuousOn (fun u => B.JpTildeH h (xt * u) - B.gCoefA h xt
        - B.gCoefB h xt * u ^ d) (Set.Icc (0 : ℝ) 2) :=
      (hcphi.sub continuousOn_const).sub
        (continuousOn_const.mul (continuous_pow d).continuousOn)
    exact hc
  have hcQ : Continuous (fun u : ℝ => B.Qh h u ^ 2) := by
    have hc : Continuous (fun u : ℝ => ((u - B.sVal h) * (u - B.tVal h)) ^ 2) := by fun_prop
    exact hc
  have hcQr : Continuous (fun u : ℝ => (B.Qh h u ^ 2) ^ (3 / 16 : ℝ)) :=
    hcQ.rpow_const (fun _ => Or.inr (by norm_num))
  -- integrability over the window and over the law interval
  have iphi : IntegrableOn (fun u => B.JpTildeH h (xt * u)) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn hνc hcphi (isCompact_centralWindow d ρ)
  have ipow : IntegrableOn (fun u : ℝ => u ^ d) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn hνc (continuous_pow d).continuousOn
      (isCompact_centralWindow d ρ)
  have ipowIcc : IntegrableOn (fun u : ℝ => u ^ d) (Set.Icc (0 : ℝ) 2) ν :=
    integrableOn_of_continuousOn hνc (continuous_pow d).continuousOn isCompact_Icc
  have igfun : IntegrableOn (fun u => B.gfun h xt u) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn hνc hcgfun (isCompact_centralWindow d ρ)
  have iQ : IntegrableOn (fun u => B.Qh h u ^ 2) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn hνc hcQ.continuousOn (isCompact_centralWindow d ρ)
  have iQr : IntegrableOn (fun u => (B.Qh h u ^ 2) ^ (3 / 16 : ℝ)) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn hνc hcQr.continuousOn (isCompact_centralWindow d ρ)
  -- the integral against the candidate law
  have hprof : ∫ u in centralWindow d ρ, B.JpTildeH h (xt * u) ∂(B.distributionMeasure h)
      = B.gCoefA h xt + B.gCoefB h xt * B.qVal h := by
    rw [distributionMeasure_restrict_of_mem B hsW htW, integral_distributionMeasure B hhb]
    have hs : B.JpTildeH h (xt * B.sVal h) = B.gCoefA h xt + B.gCoefB h xt * B.sVal h ^ d := by
      have hz := B.gfun_sVal h xt
      simp only [gfun] at hz
      linarith
    have ht : B.JpTildeH h (xt * B.tVal h) = B.gCoefA h xt + B.gCoefB h xt * B.tVal h ^ d := by
      have hz := gfun_tVal hd B hh0 hhb xt
      simp only [gfun] at hz
      linarith
    rw [hs, ht, qVal]
    ring
  -- the interpolation error as a difference of window integrals
  have hG : ∫ u in centralWindow d ρ, B.gfun h xt u ∂ν
      = (∫ u in centralWindow d ρ, B.JpTildeH h (xt * u) ∂ν)
        - (B.gCoefA h xt * (ν (centralWindow d ρ)).toReal
            + B.gCoefB h xt * ∫ u in centralWindow d ρ, u ^ d ∂ν) := by
    have hsplit : (fun u => B.gfun h xt u)
        = fun u => B.JpTildeH h (xt * u) - (B.gCoefA h xt + B.gCoefB h xt * u ^ d) := by
      funext u
      simp only [gfun]
      ring
    have hconst : IntegrableOn (fun _ : ℝ => B.gCoefA h xt) (centralWindow d ρ) ν :=
      integrableOn_const
    have hlin : IntegrableOn (fun u : ℝ => B.gCoefA h xt + B.gCoefB h xt * u ^ d)
        (centralWindow d ρ) ν := hconst.add (ipow.const_mul _)
    have h1 : ∫ u in centralWindow d ρ, B.gfun h xt u ∂ν
        = (∫ u in centralWindow d ρ, B.JpTildeH h (xt * u) ∂ν)
          - ∫ u in centralWindow d ρ, (B.gCoefA h xt + B.gCoefB h xt * u ^ d) ∂ν := by
      rw [hsplit]
      exact integral_sub iphi hlin
    have h2 := integral_add hconst (ipow.const_mul (B.gCoefB h xt))
    rw [setIntegral_const, integral_const_mul, smul_eq_mul, measureReal_def] at h2
    linarith
  -- (b) the mass term
  have hmass : (ν (centralWindow d ρ)).toReal
      = 1 - (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := by
    have h1 : ν (Set.Icc (0 : ℝ) 2 ∩ centralWindow d ρ)
        + ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ) = ν (Set.Icc (0 : ℝ) 2) :=
      measure_inter_add_sdiff _ (measurableSet_centralWindow d ρ)
    have h2 : ν (Set.Icc (0 : ℝ) 2) = 1 := (prob_compl_eq_zero_iff measurableSet_Icc).mp hνc
    have h3 : ν (Set.Icc (0 : ℝ) 2 ∩ centralWindow d ρ) = ν (centralWindow d ρ) := by
      have hr := congrArg (fun m : Measure ℝ => m Set.univ)
        (restrict_Icc_inter hνc (centralWindow d ρ))
      simpa [Measure.restrict_apply_univ] using hr
    have h4 : ν (centralWindow d ρ) + ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ) = 1 := by
      rw [← h3, h1, h2]
    have h5 := congrArg ENNReal.toReal h4
    rw [ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _), ENNReal.toReal_one] at h5
    linarith
  -- (c) the moment term
  have hmoment : |(∫ u in centralWindow d ρ, u ^ d ∂ν) - B.qVal h|
      ≤ |(∫ u, u ^ d ∂ν) - B.qVal h|
        + 2 ^ d * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := by
    have hsplit : (∫ u in Set.Icc (0 : ℝ) 2 ∩ centralWindow d ρ, u ^ d ∂ν)
        + (∫ u in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, u ^ d ∂ν)
        = ∫ u in Set.Icc (0 : ℝ) 2, u ^ d ∂ν :=
      integral_inter_add_sdiff (measurableSet_centralWindow d ρ) ipowIcc
    rw [restrict_Icc_inter hνc, restrict_Icc_self hνc] at hsplit
    have hb : ∀ x ∈ Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, ‖x ^ d‖ ≤ 2 ^ d := by
      intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1.1 d)]
      exact pow_le_pow_left₀ hx.1.1 hx.1.2 d
    have htail : |∫ u in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, u ^ d ∂ν|
        ≤ 2 ^ d * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := by
      have hn := norm_setIntegral_le_of_norm_le_const (measure_lt_top ν _) hb
      simpa [Real.norm_eq_abs, measureReal_def] using hn
    have heq : (∫ u in centralWindow d ρ, u ^ d ∂ν) - B.qVal h
        = ((∫ u, u ^ d ∂ν) - B.qVal h)
          - (∫ u in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, u ^ d ∂ν) := by linarith
    rw [heq]
    linarith [abs_sub_le_add ((∫ u, u ^ d ∂ν) - B.qVal h)
      (∫ u in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, u ^ d ∂ν)]
  -- (a) the interpolation-error term
  have hgterm : |∫ u in centralWindow d ρ, B.gfun h xt u ∂ν|
      ≤ Cg * (1 + Real.log (1 / h))
          * (∫ u in centralWindow d ρ, B.Qh h u ^ 2 ∂ν) ^ (3 / 16 : ℝ) := by
    have hae : ∀ᵐ u ∂(ν.restrict (centralWindow d ρ)),
        |B.gfun h xt u|
          ≤ Cg * (1 + Real.log (1 / h)) * (B.Qh h u ^ 2) ^ (3 / 16 : ℝ) := by
      filter_upwards [ae_restrict_of_ae (ae_mem_Icc_of_distribution hνc)] with u hu
      have h1 := hgb h hh0 hδg' hhb xt hxt u hu
      have h2 : (min |u - B.sVal h| |u - B.tVal h|) ^ (3 / 4 : ℝ)
          ≤ (B.Qh h u ^ 2) ^ (3 / 16 : ℝ) :=
        rpow_three_quarters_le_rpow_sq (le_min (abs_nonneg _) (abs_nonneg _))
          (sq_min_dist_le_abs_Qh B hh0 u)
      have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hCg.le hL)
      linarith
    have hjensen : ∫ u in centralWindow d ρ, (B.Qh h u ^ 2) ^ (3 / 16 : ℝ) ∂ν
        ≤ (∫ u in centralWindow d ρ, B.Qh h u ^ 2 ∂ν) ^ (3 / 16 : ℝ) :=
      setIntegral_rpow_le_rpow_setIntegral (by norm_num) (by norm_num) prob_le_one
        (Filter.Eventually.of_forall fun u => sq_nonneg _) iQ iQr
    calc |∫ u in centralWindow d ρ, B.gfun h xt u ∂ν|
        ≤ ∫ u in centralWindow d ρ, |B.gfun h xt u| ∂ν := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := ν.restrict (centralWindow d ρ))
              (f := fun u => B.gfun h xt u)
      _ ≤ ∫ u in centralWindow d ρ,
            Cg * (1 + Real.log (1 / h)) * (B.Qh h u ^ 2) ^ (3 / 16 : ℝ) ∂ν :=
          integral_mono_ae igfun.abs (iQr.const_mul _) hae
      _ = Cg * (1 + Real.log (1 / h))
            * ∫ u in centralWindow d ρ, (B.Qh h u ^ 2) ^ (3 / 16 : ℝ) ∂ν :=
          integral_const_mul _ _
      _ ≤ Cg * (1 + Real.log (1 / h))
            * (∫ u in centralWindow d ρ, B.Qh h u ^ 2 ∂ν) ^ (3 / 16 : ℝ) :=
          mul_le_mul_of_nonneg_left hjensen (mul_nonneg hCg.le hL)
  -- (d) combine
  have hAb := (hcoef h hh0 hδC' hhb xt hxt).1
  have hBb := (hcoef h hh0 hδC' hhb xt hxt).2
  have hε : (0 : ℝ) ≤ (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := ENNReal.toReal_nonneg
  have hΔ : (0 : ℝ) ≤ |(∫ u, u ^ d ∂ν) - B.qVal h| := abs_nonneg _
  have hA0 : (0 : ℝ) ≤ ∫ u in centralWindow d ρ, B.Qh h u ^ 2 ∂ν :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun u => sq_nonneg _)
  have hArp : (0 : ℝ) ≤ (∫ u in centralWindow d ρ, B.Qh h u ^ 2 ∂ν) ^ (3 / 16 : ℝ) :=
    Real.rpow_nonneg hA0 _
  have hdiff : (∫ u in centralWindow d ρ, B.JpTildeH h (xt * u) ∂ν)
      - (∫ u in centralWindow d ρ, B.JpTildeH h (xt * u) ∂(B.distributionMeasure h))
      = B.gCoefA h xt * ((ν (centralWindow d ρ)).toReal - 1)
        + B.gCoefB h xt * ((∫ u in centralWindow d ρ, u ^ d ∂ν) - B.qVal h)
        + ∫ u in centralWindow d ρ, B.gfun h xt u ∂ν := by
    rw [hprof, hG]
    ring
  rw [hdiff]
  have hterm1 : |B.gCoefA h xt * ((ν (centralWindow d ρ)).toReal - 1)|
      ≤ CC * (1 + Real.log (1 / h))
          * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := by
    rw [abs_mul, hmass]
    have habs : |1 - (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal - 1|
        = (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := by
      rw [show (1 : ℝ) - (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal - 1
        = -(ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal by ring, abs_neg,
        abs_of_nonneg hε]
    rw [habs]
    exact mul_le_mul_of_nonneg_right hAb hε
  have hterm2 : |B.gCoefB h xt * ((∫ u in centralWindow d ρ, u ^ d ∂ν) - B.qVal h)|
      ≤ CC * (1 + Real.log (1 / h))
          * (|(∫ u, u ^ d ∂ν) - B.qVal h|
              + 2 ^ d * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal) := by
    rw [abs_mul]
    exact mul_le_mul hBb hmoment (abs_nonneg _) (mul_nonneg hCC.le hL)
  have htri : |B.gCoefA h xt * ((ν (centralWindow d ρ)).toReal - 1)
        + B.gCoefB h xt * ((∫ u in centralWindow d ρ, u ^ d ∂ν) - B.qVal h)
        + ∫ u in centralWindow d ρ, B.gfun h xt u ∂ν|
      ≤ |B.gCoefA h xt * ((ν (centralWindow d ρ)).toReal - 1)|
          + |B.gCoefB h xt * ((∫ u in centralWindow d ρ, u ^ d ∂ν) - B.qVal h)|
          + |∫ u in centralWindow d ρ, B.gfun h xt u ∂ν| := by
    have t1 := abs_add_le (B.gCoefA h xt * ((ν (centralWindow d ρ)).toReal - 1)
      + B.gCoefB h xt * ((∫ u in centralWindow d ρ, u ^ d ∂ν) - B.qVal h))
      (∫ u in centralWindow d ρ, B.gfun h xt u ∂ν)
    have t2 := abs_add_le (B.gCoefA h xt * ((ν (centralWindow d ρ)).toReal - 1))
      (B.gCoefB h xt * ((∫ u in centralWindow d ρ, u ^ d ∂ν) - B.qVal h))
    linarith
  have hεL : (0 : ℝ) ≤ (1 + Real.log (1 / h))
      * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := mul_nonneg hL hε
  have hΔL : (0 : ℝ) ≤ (1 + Real.log (1 / h)) * |(∫ u, u ^ d ∂ν) - B.qVal h| :=
    mul_nonneg hL hΔ
  have hAL : (0 : ℝ) ≤ (1 + Real.log (1 / h))
      * (∫ u in centralWindow d ρ, B.Qh h u ^ 2 ∂ν) ^ (3 / 16 : ℝ) := mul_nonneg hL hArp
  nlinarith [mul_nonneg hCC.le hεL, mul_nonneg hCg.le hεL, mul_nonneg hCC.le hΔL,
    mul_nonneg hCg.le hΔL, mul_nonneg hCC.le hAL,
    mul_nonneg (mul_nonneg hCC.le h2d.le) hεL,
    mul_nonneg (mul_nonneg hCC.le h2d.le) hΔL,
    mul_nonneg (mul_nonneg hCC.le h2d.le) hAL]

end KKTFamily

end UpperTailOptimizers
