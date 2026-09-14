import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.DistributionVariance
import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.TailScalar
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.EdgeGap

/-!
# Automatic localization of the one-dimensional law (Section 5)

*Every exact minimizer of the law problem is automatically localized.*  The paper reaches this conclusion at the graphon level: `lem:localization-rank-one` localizes the competitor `W` directly, and the rank-one law `ν`
enters `sec:auxiliary-lagrangian` already localized.  This file runs the localization
argument on the distribution itself, kernel-free, and nothing below consumes the kernel bound `lem:central-kernel-bound`.  Five
statements are realised, each listed with its nearest anchor in the paper:

* the comparison at a fixed `d`-th moment — `KKTFamily.distributionJ_eq` and its consequence
  `KKTFamily.gamAvg_le_of_distributionJ_le`; the paper's counterpart is `eq:graphon-cost-decomposition`, stated
  for `W` with `e(W)` and `∫Γ_d(W)`, without the fixed-moment normalization;
* the variance bootstrap, with `𝒢` on the right — `exists_variance_le_sqrt_gamAvg`; the
  paper carries no such display: the pointwise bound
  `0 ≤ z^d - r_*^d - d r_*^{d-1}(z - r_*) ≤ C_dΓ_d(z)^{1/2}` plays this role in the proof of
  `lem:localization-rank-one`;
* the mean bootstrap — `KKTFamily.exists_mean_bootstrap`; no display in the
  paper, where the resulting lower bound for `e(W) - e(W_h)` plays its role;
* the localization `𝒢 = O(h⁴)` — `KKTFamily.exists_gamAvg_localization`, the target;
  the paper's counterpart is `eq:moment-and-cost-gap-bounds`,
  `0 ≤ ∫W^d - r_h^d ≤ C_d h⁴` and `0 ≤ ∫Γ_d(W) ≤ C_d h⁴`, in the proof of
  `lem:localization-rank-one`;
* the tail-mass estimate — `KKTFamily.exists_tail_mass_le`; the paper's counterpart is
  `eq:factor-tail-mass`, proved for the factor `f` by Chebyshev
  (here the tail mass is a consequence of the localization above rather than an
  assumption).

The candidate bound `𝒢_h = O(h⁴)` is `KKTFamily.exists_gamAvg_distribution_le`; the paper's
counterpart is `∫Γ_d(W_h) = O_d(h⁴)` in the same proof.

## Two functionals, both iterated integrals

`gamAvg d ν = ∫∫Γ̃_d(xy) dν dν` is the Lean's `𝒢 = EΓ̃_d(XY)` (the paper does not form this
average), and `KKTFamily.distributionJ B h ν = ∫∫J̃_{p_h}(xy) dν dν` is the paper's `𝒥_h(ν)`.  As in
`SingularEndpoint/AuxiliaryLagrangian/DistributionVariance.lean`, independence is expressed by an iterated integral rather
than by a product measure: the inner integral is computed explicitly and the outer integral
is the same computation again, so no Fubini theorem is used.  What that costs is one limit
theorem, `continuousOn_innerIntegral`: for `g` continuous on `[0,4]` the map
`x ↦ ∫g(xy) dν(y)` is continuous on `[0,2]`, by dominated convergence against the constant
`sup_{[0,4]}|g|`.  It is applied to `Γ̃_d` and to `z ↦ (z - r_*)⁴`, and it is the only place
where a convergence theorem appears.

## Two simplifications

* **No crude bound.**  Deriving `𝒢 = O(h²)`, hence `Var(X) = o(1)`, hence `x̄ → u_*`, only to
  invert `z ↦ z^d` near `u_*`, is not needed: `abs_sub_uStar_mul_le` inverts the power map on the whole nonnegative
  axis — the cofactor of the geometric-sum factorisation is bounded below by its `i = 0`
  term `u_*^{d-1} > 0` — so the crude bound is not needed.  The mean bootstrap's conclusion
  is unchanged.
* **No compactness in the tail step.**  The positive lower bound for `Γ̃_d` on the separated
  set comes from the continued quartic bound `exists_quartic_le_GamTilde`, which is
  quantitative: `Γ̃_d(z) ≥ |z - r_*|⁴/C₀`.

## Contents

* `gamAvg`, `gamAvg_nonneg` — the averaged continued gap `𝒢`;
* `exists_variance_le_sqrt_gamAvg` — **the variance bootstrap** against `𝒢^{1/2}`;
* `KKTFamily.Lam`, `KKTFamily.Cconst`, `KKTFamily.distributionJ` — the law
  functional and the two displacement coefficients `Λ_h`, `C_h` (`Λ_h` is defined in the
  paper just before `eq:entropy-parameter-shift`; `C_h` is a Lean name for a constant the
  paper leaves unnamed);
* `KKTFamily.distributionJ_eq`, `KKTFamily.gamAvg_le_of_distributionJ_le` —
  **the comparison at a fixed `d`-th moment**;
* `KKTFamily.distributionMeasure_Icc_compl`, `KKTFamily.gamAvg_distributionMeasure`,
  `KKTFamily.exists_gamAvg_distribution_le` — the candidate law and its `O(h⁴)` average;
* `KKTFamily.exists_mean_bootstrap` — **the mean bootstrap**;
* `KKTFamily.exists_gamAvg_localization` — **the localization `𝒢 = O(h⁴)`**;
* `KKTFamily.exists_tail_mass_le` — **the tail-mass estimate**;
* `continuousOn_innerIntegral` — `x ↦ ∫ g(xy) dν(y)` is continuous on `[0,2]`, shared with
  `SingularEndpoint/AuxiliaryLagrangian/DistributionQuant.lean`.

The second half of the law lemma — the localized lower bounds now stated as
`eq:auxiliary-lagrangian-bound` in `lem:auxiliary-lagrangian-bound`, which consume the
kernel bound `lem:central-kernel-bound` — is not in this file; it is
`SingularEndpoint/AuxiliaryLagrangian/DistributionGap.lean`, `SingularEndpoint/AuxiliaryLagrangian/DistributionQuant.lean` and `SingularEndpoint/AuxiliaryLagrangian/DistributionAbsorption.lean`,
assembled in `SingularEndpoint/AuxiliaryLagrangian/DistributionFinal.lean`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter MeasureTheory Topology

variable {d : ℕ}

/-! ## The averaged continued gap `𝒢` -/

/-- **The averaged continued gap `𝒢 = E Γ̃_d(XY)`** of the law-level localization proof
(the paper's `lem:localization-rank-one` works with `∫Γ_d(W)` at the graphon level and does
not form this average), written as an iterated integral rather than through a product
measure: `X, Y` independent with common law `ν` is the same number as `∫∫Γ̃_d(xy) dν dν`, and
no Fubini theorem is needed to compute it. -/
noncomputable def gamAvg (d : ℕ) (ν : Measure ℝ) : ℝ := ∫ x, ∫ y, GamTilde d (x * y) ∂ν ∂ν

/-- `𝒢 ≥ 0` for a measure carried by the law interval: the products `xy` then lie in
`[0,4]`, where `Γ̃_d ≥ 0` (`GamTilde_nonneg`). -/
theorem gamAvg_nonneg (hd : 2 ≤ d) {ν : Measure ℝ} (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) :
    0 ≤ gamAvg d ν := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_mem_Icc_of_distribution hν] with x hx
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_mem_Icc_of_distribution hν] with y hy
  exact GamTilde_nonneg hd (mul_nonneg hx.1 hy.1)

/-! ## The inner integral of a continued kernel -/

/-- **The inner integral of `g(xy)` is continuous in `x` on the law interval.**

Every functional of this file is an iterated integral `∫∫g(xy)`, and splitting the outer
integral needs the inner one to be `ν`-integrable.  For `g` continuous on `[0,4]` — which is
`Γ̃_d`, and also `z ↦ (z - r_*)⁴` — the map `x ↦ ∫g(xy) dν(y)` is continuous on `[0,2]` by
dominated convergence with the constant bound `sup_{[0,4]}|g|`: the products `xy` stay in
`[0,4]`, and `x ↦ g(xy)` is continuous on `[0,2]` for each `y ∈ [0,2]`.

This is the only limit theorem the file uses. -/
theorem continuousOn_innerIntegral {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 4)) :
    ContinuousOn (fun x => ∫ y, g (x * y) ∂ν) (Set.Icc 0 2) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := g) hg
  have hmaps : ∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2,
      x * y ∈ Set.Icc (0 : ℝ) 4 := by
    intro x hx y hy
    exact ⟨mul_nonneg hx.1 hy.1, by nlinarith [hx.1, hx.2, hy.1, hy.2]⟩
  have hinty : ∀ x ∈ Set.Icc (0 : ℝ) 2, Integrable (fun y => g (x * y)) ν := by
    intro x hx
    refine integrable_of_continuousOn hν ?_
    exact hg.comp (continuous_const.mul continuous_id).continuousOn fun y hy => hmaps x hx y hy
  have hcontx : ∀ y ∈ Set.Icc (0 : ℝ) 2, ContinuousOn (fun x : ℝ => g (x * y)) (Set.Icc 0 2) :=
    fun y hy => hg.comp (continuous_id.mul continuous_const).continuousOn
      fun x hx => hmaps x hx y hy
  intro x₀ hx₀
  refine continuousWithinAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
  · exact eventually_nhdsWithin_of_forall fun x hx => (hinty x hx).aestronglyMeasurable
  · refine eventually_nhdsWithin_of_forall fun x hx => ?_
    filter_upwards [ae_mem_Icc_of_distribution hν] with y hy
    exact hM _ (hmaps x hx y hy)
  · filter_upwards [ae_mem_Icc_of_distribution hν] with y hy
    exact (hcontx y hy).continuousWithinAt hx₀

/-- The integrability corollary of `continuousOn_innerIntegral`. -/
private theorem integrable_innerIntegral {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 4)) :
    Integrable (fun x => ∫ y, g (x * y) ∂ν) ν :=
  integrable_of_continuousOn hν (continuousOn_innerIntegral hν hg)

/-- The moment expansion of `a x^k + b x + c`, the shape in which every affine-plus-power
integrand of this file is integrated.  A local copy of the private `integral_pow_affine` of
`SingularEndpoint/AuxiliaryLagrangian/DistributionVariance.lean`, carrying a leading coefficient. -/
private theorem integral_affine_pow {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) (k : ℕ) (a b c : ℝ) :
    ∫ x, (a * x ^ k + b * x + c) ∂ν = a * (∫ x, x ^ k ∂ν) + b * (∫ x, x ∂ν) + c := by
  have ik : Integrable (fun x : ℝ => a * x ^ k) ν :=
    (integrable_of_continuousOn hν (f := fun x : ℝ => x ^ k) (by fun_prop)).const_mul a
  have i1 : Integrable (fun x : ℝ => b * x) ν :=
    (integrable_of_continuousOn hν (f := fun x : ℝ => x) (by fun_prop)).const_mul b
  have is : Integrable (fun x : ℝ => a * x ^ k + b * x) ν := ik.add i1
  rw [integral_add is (integrable_const c), integral_add ik i1, integral_const_mul,
    integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul]

/-! ## Two shape lemmas -/

/-- A function with a finite rate at the origin is `O(|h|^n)`: if `f(h)/h^n → L` then
`|f(h)| ≤ (|L|+1)|h|^n` on a punctured neighbourhood.  The `|h|^n` form — rather than the
`h^n` of the identically named private helper of `SingularEndpoint/LocalizationRankOne/FamilyLocalization.lean` — is what
lets the same lemma serve the odd rate `(α_h - 1/2)/h`. -/
private theorem exists_eventual_abs_bound {f : ℝ → ℝ} {L : ℝ} {n : ℕ}
    (hf : Tendsto (fun h : ℝ => f h / h ^ n) (𝓝[≠] (0 : ℝ)) (𝓝 L)) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ h in 𝓝[≠] (0 : ℝ), |f h| ≤ M * |h| ^ n := by
  refine ⟨|L| + 1, by positivity, ?_⟩
  have hlt := hf.abs.eventually_lt_const (show |L| < |L| + 1 by linarith)
  filter_upwards [hlt, self_mem_nhdsWithin] with h hh hmem
  have hne : h ≠ 0 := hmem
  have hp : (0 : ℝ) < |h| ^ n := pow_pos (abs_pos.mpr hne) n
  rw [abs_div, abs_pow] at hh
  exact ((div_lt_iff₀ hp).mp hh).le

/-- A punctured-neighbourhood eventuality read as an explicit width: this is the
`eventually_nhdsWithin_iff` + `Metric.eventually_nhds_iff` idiom of `SingularEndpoint/LocalizationRankOne/Gap.lean`, used
to put every conclusion of this file in the `0 < h < δ` form of
`sec:auxiliary-lagrangian`. -/
private theorem exists_delta_of_eventually {P : ℝ → Prop} (hP : ∀ᶠ h in 𝓝[≠] (0 : ℝ), P h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → P h := by
  rw [eventually_nhdsWithin_iff] at hP
  obtain ⟨ε, hε, hprop⟩ := Metric.eventually_nhds_iff.mp hP
  refine ⟨ε, hε, fun h hh0 hhε => hprop ?_ ?_⟩
  · rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
    exact hhε
  · simpa using hh0.ne'

/-! ## The variance bootstrap, with `𝒢` on the right -/

/-- **The variance bootstrap.**  There is a constant `C > 0` with

`Var(X) ≤ C·𝒢^{1/2}`

for every probability measure `ν` on `ℝ` carried by the law interval `[0,2]`.

The paper states no such bound: its
localization runs at the graphon level, where the pointwise bound
`z^d - r_*^d - d r_*^{d-1}(z - r_*) ≤ C_dΓ_d(z)^{1/2}` (the Lean's `R_d² ≤ C_dΓ_d`) and
Cauchy–Schwarz play this role in the proof of `lem:localization-rank-one`.  The chain here is
different.  `two_mul_rStar_mul_variance_le` of `SingularEndpoint/AuxiliaryLagrangian/DistributionVariance.lean` gives
`2r_*Var(X) ≤ E(XY - r_*)²`; Cauchy–Schwarz
(`integral_sq_le_sqrt_integral_pow_four`) raises the exponent to `4`; and the continued
quartic bound `exists_quartic_le_GamTilde` — `|z - r_*|⁴ ≤ C₀Γ̃_d(z)` on `[0,4]` — turns the
fourth moment into `C₀𝒢`.  **This is the step for which the continuation exists**: `x, y ∈ [0,2]`
puts `xy` in `[0,4]`, where `Γ_d` itself has no meaning. -/
theorem exists_variance_le_sqrt_gamAvg (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
      (∫ x, x ^ 2 ∂ν) - (∫ x, x ∂ν) ^ 2 ≤ C * Real.sqrt (gamAvg d ν) := by
  obtain ⟨C₀, hC₀, hquart⟩ := exists_quartic_le_GamTilde hd
  have hr : (0 : ℝ) < 2 * rStar d := by linarith [rStar_pos hd]
  refine ⟨Real.sqrt C₀ / (2 * rStar d), div_pos (Real.sqrt_pos.mpr hC₀) hr, ?_⟩
  intro ν hνp hν
  have : IsProbabilityMeasure ν := hνp
  -- the fourth moment of `XY - r_*` is at most `C₀𝒢`
  have hGint : Integrable (fun x => ∫ y, GamTilde d (x * y) ∂ν) ν :=
    integrable_innerIntegral hν (continuousOn_GamTilde hd)
  have h4int : Integrable (fun x => ∫ y, (x * y - rStar d) ^ 4 ∂ν) ν :=
    integrable_innerIntegral hν (g := fun z => (z - rStar d) ^ 4) (by fun_prop)
  have hae : ∀ᵐ x ∂ν, (∫ y, (x * y - rStar d) ^ 4 ∂ν) ≤ C₀ * ∫ y, GamTilde d (x * y) ∂ν := by
    filter_upwards [ae_mem_Icc_of_distribution hν] with x hx
    have hmaps : ∀ y ∈ Set.Icc (0 : ℝ) 2, x * y ∈ Set.Icc (0 : ℝ) 4 := by
      intro y hy
      exact ⟨mul_nonneg hx.1 hy.1, by nlinarith [hx.1, hx.2, hy.1, hy.2]⟩
    have i1 : Integrable (fun y => (x * y - rStar d) ^ 4) ν :=
      integrable_of_continuousOn hν (by fun_prop)
    have i2 : Integrable (fun y => C₀ * GamTilde d (x * y)) ν := by
      refine Integrable.const_mul (integrable_of_continuousOn hν ?_) C₀
      exact (continuousOn_GamTilde hd).comp (continuous_const.mul continuous_id).continuousOn
        hmaps
    have hmono := integral_mono_ae i1 i2 ?_
    · rwa [integral_const_mul] at hmono
    · filter_upwards [ae_mem_Icc_of_distribution hν] with y hy
      have habs : (x * y - rStar d) ^ 4 = |x * y - rStar d| ^ 4 := by
        rw [← abs_pow, abs_of_nonneg (by positivity)]
      rw [habs]
      exact hquart _ (hmaps y hy)
  have hfour : (∫ x, ∫ y, (x * y - rStar d) ^ 4 ∂ν ∂ν) ≤ C₀ * gamAvg d ν := by
    have h := integral_mono_ae h4int (hGint.const_mul C₀) hae
    rwa [integral_const_mul] at h
  -- assemble the three inequalities
  have h2 := two_mul_rStar_mul_variance_le hd ν hν
  have h3 := integral_sq_le_sqrt_integral_pow_four ν hν (rStar d)
  have h4 : Real.sqrt (∫ x, ∫ y, (x * y - rStar d) ^ 4 ∂ν ∂ν)
      ≤ Real.sqrt C₀ * Real.sqrt (gamAvg d ν) := by
    rw [← Real.sqrt_mul hC₀.le]
    exact Real.sqrt_le_sqrt hfour
  rw [div_mul_eq_mul_div, le_div_iff₀ hr]
  linarith

/-! ## Inverting `z ↦ z^d` at the singular endpoint value -/

/-- **The inversion of the power map at `u_*`**: for every `m ≥ 0`,

`|m - u_*|·u_*^{d-1} ≤ |m^d - u_*^d|`.

Inverting `z ↦ z^d` only near `u_*` would first need the crude bound `𝒢 = O(h²)` — through
`Var(X) = o(1)` — to know that the mean is near `u_*` (the paper has no law-level
counterpart of this step).  On the
nonnegative axis no such preparation is needed: the geometric-sum factorisation
`m^d - u_*^d = (m - u_*)∑_{i<d}m^i u_*^{d-1-i}` has a cofactor all of whose terms are
nonnegative and whose `i = 0` term is already `u_*^{d-1} > 0`.  The formalisation therefore
skips the crude bound; the conclusion of the mean bootstrap is unchanged. -/
private theorem abs_sub_uStar_mul_le (hd : 2 ≤ d) {m : ℝ} (hm : 0 ≤ m) :
    |m - uStar d| * uStar d ^ (d - 1) ≤ |m ^ d - uStar d ^ d| := by
  have hu : 0 < uStar d := uStar_pos hd
  have hnn : ∀ i ∈ Finset.range d, 0 ≤ m ^ i * uStar d ^ (d - 1 - i) := fun i _ =>
    mul_nonneg (pow_nonneg hm i) (pow_nonneg hu.le _)
  have hsum : uStar d ^ (d - 1) ≤ ∑ i ∈ Finset.range d, m ^ i * uStar d ^ (d - 1 - i) := by
    have h := Finset.single_le_sum hnn (Finset.mem_range.mpr (show 0 < d by omega))
    simpa using h
  rw [pow_sub_pow_eq m (uStar d) d, abs_mul, abs_of_nonneg (Finset.sum_nonneg hnn)]
  exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)

/-- The mean of a probability measure carried by `[0,2]` lies in `[0,2]`.  Used for both the
competitor and the candidate, to bound the factor `x̄ + x̄_h` of `x̄² - x̄_h²` by `4`. -/
private theorem mean_mem_Icc {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) : 0 ≤ (∫ x, x ∂ν) ∧ (∫ x, x ∂ν) ≤ 2 := by
  refine ⟨integral_nonneg_of_ae ?_, ?_⟩
  · filter_upwards [ae_mem_Icc_of_distribution hν] with x hx using hx.1
  · have h := integral_mono_ae
      (integrable_of_continuousOn hν (f := fun x : ℝ => x) (by fun_prop))
      (integrable_const (2 : ℝ))
      (by filter_upwards [ae_mem_Icc_of_distribution hν] with x hx using hx.2)
    rwa [integral_const, probReal_univ, smul_eq_mul, one_mul] at h

/-! ## The Young step -/

/-- **The arithmetic core of the localization `exists_gamAvg_localization`**, stated for
plain reals so that the measure-theoretic assembly below is a single application.

Reading `G = 𝒢`, `Gh = 𝒢_h`, `L = Λ_h`, `m = x̄`, `n = x̄_h`, `V = Var(X)` and `S² = G`, the
hypotheses are the exact comparison at fixed moment (`gamAvg_le_of_distributionJ_le`), the
candidate bound `𝒢_h = O(h⁴)`, the variance bootstrap (`exists_variance_le_sqrt_gamAvg`),
the mean bootstrap (`exists_mean_bootstrap`) and `Λ_h = O(h²)`.  The conclusion chains them into
`G ≤ Ah⁴ + Bh²S` and closes that by Young's inequality `2Bh²S ≤ B²h⁴ + S²`, which is
`sq_nonneg (Bh² - S)`. -/
private theorem localization_arith {G Gh L m n V S C₁ Cv K₁ K₂ Mm ML h : ℝ}
    (hS : S ^ 2 = G) (hm0 : 0 ≤ m) (hm2 : m ≤ 2) (hn0 : 0 ≤ n) (hn2 : n ≤ 2)
    (hML : 0 ≤ ML) (hK₁ : 0 ≤ K₁)
    (hcomp : G + L * m ^ 2 ≤ Gh + L * n ^ 2) (hGh : Gh ≤ C₁ * h ^ 4)
    (hVar : V ≤ Cv * S) (hmb : |m - n| ≤ K₁ * V + (K₂ + Mm) * h ^ 2)
    (hLb : |L| ≤ ML * h ^ 2) :
    G ≤ (2 * (C₁ + 4 * ML * (K₂ + Mm)) + (4 * ML * K₁ * Cv) ^ 2) * h ^ 4 := by
  have hsum : |n + m| ≤ 4 := by
    rw [abs_le]
    constructor <;> linarith
  have hsq : |n ^ 2 - m ^ 2| ≤ 4 * |m - n| := by
    have e : n ^ 2 - m ^ 2 = -((m - n) * (n + m)) := by ring
    rw [e, abs_neg, abs_mul]
    have h := mul_le_mul_of_nonneg_left hsum (abs_nonneg (m - n))
    linarith
  have hd2 : L * (n ^ 2 - m ^ 2) ≤ |L| * (4 * |m - n|) :=
    le_trans (le_trans (le_abs_self _) (le_of_eq (abs_mul L (n ^ 2 - m ^ 2))))
      (mul_le_mul_of_nonneg_left hsq (abs_nonneg L))
  have hd4 : |L| * (4 * |m - n|) ≤ (ML * h ^ 2) * (4 * (K₁ * V + (K₂ + Mm) * h ^ 2)) :=
    mul_le_mul hLb (by linarith) (by positivity) (mul_nonneg hML (sq_nonneg h))
  have hd5 : (4 * ML * h ^ 2 * K₁) * V ≤ (4 * ML * h ^ 2 * K₁) * (Cv * S) :=
    mul_le_mul_of_nonneg_left hVar
      (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg h)) hK₁)
  have hfin : G ≤ (C₁ + 4 * ML * (K₂ + Mm)) * h ^ 4
      + (4 * ML * K₁ * Cv) * h ^ 2 * S := by linarith
  nlinarith [sq_nonneg ((4 * ML * K₁ * Cv) * h ^ 2 - S), hfin, hS]

/-! ## Ingredients of the tail estimate -/

/-- **The separation `|xy - r_*| ≥ c_ρ`** of the tail estimate (the paper's `eq:factor-tail-mass` is instead proved by Chebyshev for the factor `f`).  If `x`
lies outside the window `𝓝_ρ` while `y` lies in the half window `𝓝_{ρ/2}`, and `ρ ≤ u_*/2`,
then

`|xy - r_*| ≥ u_*ρ/4 > 0`.

The division is avoidable: since `r_* = u_*²`,

`xy - r_* = y(x - u_*) + u_*(y - u_*)`,

and `ρ ≤ u_*/2` forces `y ≥ 3u_*/4`, so the first term is at least `(3u_*/4)ρ` in modulus
while the second is at most `u_*ρ/2`. -/
private theorem sep_of_tail_window (hd : 2 ≤ d) {ρ x y : ℝ} (hρ0 : 0 < ρ)
    (hρu : ρ ≤ uStar d / 2) (hxT : x ∉ centralWindow d ρ)
    (hy : y ∈ centralWindow d (ρ / 2)) : uStar d * ρ / 4 ≤ |x * y - rStar d| := by
  have hu : 0 < uStar d := uStar_pos hd
  simp only [centralWindow, Set.mem_Icc] at hy
  have hy0 : 3 * uStar d / 4 ≤ y := by linarith [hy.1]
  have hyb : |y - uStar d| ≤ ρ / 2 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hxu : ρ ≤ |x - uStar d| := by
    simp only [centralWindow, Set.mem_Icc, not_and_or, not_le] at hxT
    rcases hxT with hlt | hgt
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  have key : x * y - rStar d = y * (x - uStar d) + uStar d * (y - uStar d) := by
    rw [← uStar_sq hd]
    ring
  have hya : 3 * uStar d / 4 * ρ ≤ y * |x - uStar d| :=
    mul_le_mul hy0 hxu hρ0.le (by linarith)
  have hyu : uStar d * |y - uStar d| ≤ uStar d * (ρ / 2) := mul_le_mul_of_nonneg_left hyb hu.le
  have hstep : |y * (x - uStar d)| - |uStar d * (y - uStar d)|
      ≤ |y * (x - uStar d) + uStar d * (y - uStar d)| := by
    have h := abs_sub_abs_le_abs_sub (y * (x - uStar d)) (-(uStar d * (y - uStar d)))
    rwa [abs_neg, sub_neg_eq_add] at h
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y), abs_of_pos hu] at hstep
  rw [key]
  linarith

/-- **Chebyshev's inequality** in the form the tail estimate needs: if every point of a
measurable set `s` is at distance at least `a` from the mean, then `a²ν(s) ≤ Var(X)`.

Proved from `∫_s a² ≤ ∫_s(x - x̄)² ≤ ∫(x - x̄)²`, the last integral being `m₂ - m₁²` by the
same moment expansion (`integral_affine_pow`) that runs through the whole file. -/
private theorem chebyshev_tail {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) {s : Set ℝ} (hs : MeasurableSet s) {a : ℝ} (ha : 0 ≤ a)
    (hpt : ∀ x ∈ s, a ≤ |x - ∫ y, y ∂ν|) :
    a ^ 2 * ν.real s ≤ (∫ x, x ^ 2 ∂ν) - (∫ x, x ∂ν) ^ 2 := by
  have hint : Integrable (fun x : ℝ => (x - ∫ y, y ∂ν) ^ 2) ν :=
    integrable_of_continuousOn hν (by fun_prop)
  have hvar : (∫ x, (x - ∫ y, y ∂ν) ^ 2 ∂ν) = (∫ x, x ^ 2 ∂ν) - (∫ x, x ∂ν) ^ 2 := by
    have he : (fun x : ℝ => (x - ∫ y, y ∂ν) ^ 2)
        = fun x : ℝ => 1 * x ^ 2 + (-(2 * ∫ y, y ∂ν)) * x + (∫ y, y ∂ν) ^ 2 := by
      funext x
      ring
    rw [he, integral_affine_pow hν 2]
    ring
  have h1 : a ^ 2 * ν.real s ≤ ∫ x in s, (x - ∫ y, y ∂ν) ^ 2 ∂ν := by
    have h := setIntegral_mono_on (f := fun _ : ℝ => a ^ 2)
      (g := fun x : ℝ => (x - ∫ y, y ∂ν) ^ 2) integrableOn_const hint.integrableOn hs ?_
    · rw [setIntegral_const, smul_eq_mul] at h
      linarith
    · intro x hx
      calc a ^ 2 ≤ |x - ∫ y, y ∂ν| ^ 2 := pow_le_pow_left₀ ha (hpt x hx) 2
        _ = (x - ∫ y, y ∂ν) ^ 2 := sq_abs _
  have h2 : (∫ x in s, (x - ∫ y, y ∂ν) ^ 2 ∂ν) ≤ ∫ x, (x - ∫ y, y ∂ν) ^ 2 ∂ν :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  rw [hvar] at h2
  linarith

/-- **The rectangle lower bound for `𝒢`**.  If `Γ̃_d(xy) ≥ c` whenever `x` lies in a
measurable `T ⊆ [0,2]` and `y` in a measurable `N`, then

`c·ν(N)·ν(T) ≤ 𝒢(ν)`.

Read off here by two applications of
`setIntegral_le_integral` — legitimate because `Γ̃_d ≥ 0` on `[0,4]` — sandwiching the
constant `c` first in the inner variable and then in the outer one. -/
private theorem gamAvg_ge_rect (hd : 2 ≤ d) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) {T N : Set ℝ} (hT : MeasurableSet T)
    (hN : MeasurableSet N) (hTsub : T ⊆ Set.Icc 0 2) {c : ℝ}
    (hpt : ∀ x ∈ T, ∀ y ∈ N, y ∈ Set.Icc (0 : ℝ) 2 → c ≤ GamTilde d (x * y)) :
    c * ν.real N * ν.real T ≤ gamAvg d ν := by
  have hGnn : ∀ᵐ x ∂ν, 0 ≤ ∫ y, GamTilde d (x * y) ∂ν := by
    filter_upwards [ae_mem_Icc_of_distribution hν] with x hx
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_mem_Icc_of_distribution hν] with y hy
    exact GamTilde_nonneg hd (mul_nonneg hx.1 hy.1)
  have hGint : Integrable (fun x => ∫ y, GamTilde d (x * y) ∂ν) ν :=
    integrable_innerIntegral hν (continuousOn_GamTilde hd)
  have hinner : ∀ x ∈ T, c * ν.real N ≤ ∫ y, GamTilde d (x * y) ∂ν := by
    intro x hxT
    have hx := hTsub hxT
    have hig : Integrable (fun y => GamTilde d (x * y)) ν := by
      refine integrable_of_continuousOn hν
        ((continuousOn_GamTilde hd).comp (continuous_const.mul continuous_id).continuousOn ?_)
      intro y hy
      exact ⟨mul_nonneg hx.1 hy.1, by nlinarith [hx.1, hx.2, hy.1, hy.2]⟩
    have hstep1 : c * ν.real N ≤ ∫ y in N, GamTilde d (x * y) ∂ν := by
      have h := setIntegral_mono_on_ae (f := fun _ : ℝ => c)
        (g := fun y : ℝ => GamTilde d (x * y)) integrableOn_const hig.integrableOn hN ?_
      · rw [setIntegral_const, smul_eq_mul] at h
        linarith
      · filter_upwards [ae_mem_Icc_of_distribution hν] with y hy hyN
        exact hpt x hxT y hyN hy
    have hstep2 : (∫ y in N, GamTilde d (x * y) ∂ν) ≤ ∫ y, GamTilde d (x * y) ∂ν := by
      refine setIntegral_le_integral hig ?_
      filter_upwards [ae_mem_Icc_of_distribution hν] with y hy
      exact GamTilde_nonneg hd (mul_nonneg hx.1 hy.1)
    linarith
  have houter : c * ν.real N * ν.real T ≤ ∫ x in T, (∫ y, GamTilde d (x * y) ∂ν) ∂ν := by
    have h := setIntegral_mono_on (f := fun _ : ℝ => c * ν.real N)
      (g := fun x => ∫ y, GamTilde d (x * y) ∂ν) integrableOn_const hGint.integrableOn hT hinner
    rw [setIntegral_const, smul_eq_mul] at h
    linarith
  exact le_trans houter (setIntegral_le_integral hGint hGnn)

/-- **The smallness device.**  A quantity bounded by `c h²` is below any prescribed `b > 0`
once `h < 1` and `h < b/(c+1)`: then `c h² ≤ c h ≤ c b/(c+1) ≤ b`.  Both places where the
tail estimate needs "for `h` small enough" go through this, which is what keeps the width `δ`
explicit. -/
private theorem le_of_sq_bound {A c b h : ℝ} (hc : 0 ≤ c) (hb : 0 < b) (hh0 : 0 < h)
    (hh1 : h < 1) (hhb : h < b / (c + 1)) (hA : A ≤ c * h ^ 2) : A ≤ b := by
  have hsq : h ^ 2 ≤ h := by nlinarith
  have h1 : c * h ^ 2 ≤ c * h := mul_le_mul_of_nonneg_left hsq hc
  have h2 : c * h ≤ c * (b / (c + 1)) := mul_le_mul_of_nonneg_left hhb.le hc
  have h3 : c * (b / (c + 1)) ≤ b := by
    rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- `Var(X) ≤ C_v𝒢^{1/2}` and `𝒢 ≤ Ch⁴` give `Var(X) ≤ C_v√C h²`, the form in which the
variance enters the two smallness thresholds of the tail estimate. -/
private theorem var_le_sq {V G C Cv h : ℝ} (hC : 0 < C) (hCv : 0 ≤ Cv)
    (hv : V ≤ Cv * Real.sqrt G) (hG : G ≤ C * h ^ 4) : V ≤ Cv * Real.sqrt C * h ^ 2 := by
  have h2 : Real.sqrt G ≤ Real.sqrt C * h ^ 2 := by
    have h3 : Real.sqrt G ≤ Real.sqrt (C * (h ^ 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_mul hC.le, Real.sqrt_sq (sq_nonneg h)] at h3
  have h4 : Cv * Real.sqrt G ≤ Cv * (Real.sqrt C * h ^ 2) := mul_le_mul_of_nonneg_left h2 hCv
  linarith

/-- A point outside the half window `𝓝_{ρ/2}` is at distance at least `ρ/4` from any `m`
within `ρ/4` of `u_*`.  This is the hypothesis `chebyshev_tail` asks for. -/
private theorem quarter_le_abs_sub {ρ x m : ℝ} (hρ : 0 < ρ)
    (hxn : x ∉ centralWindow d (ρ / 2)) (hm : |m - uStar d| ≤ ρ / 4) : ρ / 4 ≤ |x - m| := by
  have hxu : ρ / 2 ≤ |x - uStar d| := by
    simp only [centralWindow, Set.mem_Icc, not_and_or, not_le] at hxn
    rcases hxn with hlt | hgt
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  have htri := abs_sub_le x m (uStar d)
  linarith

/-- If the part of the law interval outside a set `N` carries at most half of the mass,
then `N` carries at least half of it — the measure of `[0,2]` being `1`. -/
private theorem half_le_measureReal_window {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) {N : Set ℝ}
    (hhalf : ν.real (Set.Icc (0 : ℝ) 2 \ N) ≤ 1 / 2) : (1 : ℝ) / 2 ≤ ν.real N := by
  have hIcc : ν.real (Set.Icc (0 : ℝ) 2) = 1 := by
    have h : ν (Set.Icc (0 : ℝ) 2) = 1 := by
      have hcompl := measure_add_measure_compl (μ := ν) (s := Set.Icc (0 : ℝ) 2)
        measurableSet_Icc
      rw [hν, add_zero, measure_univ] at hcompl
      exact hcompl
    rw [measureReal_def, h]
    simp
  have hcover : Set.Icc (0 : ℝ) 2 ⊆ (Set.Icc (0 : ℝ) 2 \ N) ∪ N := by
    intro x hx
    by_cases hxN : x ∈ N
    · exact Or.inr hxN
    · exact Or.inl ⟨hx, hxN⟩
  have hmono := measureReal_mono (μ := ν) hcover (measure_ne_top ν _)
  have hunion := measureReal_union_le (μ := ν) (Set.Icc (0 : ℝ) 2 \ N) N
  rw [hIcc] at hmono
  linarith

namespace KKTFamily

/-! ## The law functional and its comparison form -/

/-- **`Λ_h = ℓ(p_h) - ℓ(p_*)`**, the linear displacement of the continued entropy: the
abbreviation the paper introduces at the start of `sec:constant-graphon-comparison`,
with the displacement identity `eq:entropy-parameter-shift`; `eq:rank-one-parameter-expansions`
gives `Λ_h = O_d(h²)`.  A name for the coefficient that
`KKTFamily.JpTildeH` carries anonymously. -/
noncomputable def Lam (B : KKTFamily d) (h : ℝ) : ℝ := ell (B.p h) - ell (pStar d)

/-- The constant term of the law comparison `distributionJ_eq`: the two `h`-dependent
constants of `eq:entropy-continuation` and of the displacement `eq:entropy-parameter-shift`
collected (`C_h` is a Lean name; the paper leaves this constant unnamed),

`C_h = J_{p_*}(r_*) - β_d r_*^d + (J_{p_h}(0) - J_{p_*}(0))`.

Only its independence of `ν` matters below. -/
noncomputable def Cconst (B : KKTFamily d) (h : ℝ) : ℝ :=
  Jp (pStar d) (rStar d) - betaD d * rStar d ^ d + (Jp (B.p h) 0 - Jp (pStar d) 0)

/-- **The one-dimensional law functional `𝒥_h(ν)`** of
`sec:auxiliary-lagrangian`: the continued entropy `J̃_{p_h}` averaged over the
product of two independent copies of `ν`, written as an iterated integral. -/
noncomputable def distributionJ (B : KKTFamily d) (h : ℝ) (ν : Measure ℝ) : ℝ :=
  ∫ x, ∫ y, B.JpTildeH h (x * y) ∂ν ∂ν

/-- **The exact decomposition of the law functional.**  For every probability measure
`ν` carried by the law interval,

`𝒥_h(ν) = 𝒢(ν) + Λ_h·(EX)² + β_d·(EX^d)² + C_h`.

This is the one-dimensional form of the entropy comparison; the paper runs the corresponding
comparison,
`eq:graphon-cost-decomposition`, at the graphon level with `e(W)` and `∫Γ_d(W)`.

This is pure unfolding: `J̃_{p_h}(z) = Γ̃_d(z) + β_d z^d + Λ_h z + C_h` by
`eq:entropy-continuation`, and under the iterated integral `(xy)^d = x^d y^d` and `xy`
factorise, turning the two moment terms into *squares* of the corresponding moments.  No
Fubini theorem and no product measure appear: the inner integral is computed explicitly for
each `x ∈ [0,2]` (`integral_affine_pow`) and the outer integral is the same computation
again, exactly as in `SingularEndpoint/AuxiliaryLagrangian/DistributionVariance.lean`.

The only non-elementary ingredient is the `ν`-integrability of the inner gap average
`x ↦ ∫Γ̃_d(xy) dν(y)`, which is `integrable_innerIntegral`. -/
theorem distributionJ_eq (hd : 2 ≤ d) (B : KKTFamily d) (h : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) :
    B.distributionJ h ν = gamAvg d ν + B.Lam h * (∫ x, x ∂ν) ^ 2
      + betaD d * (∫ x, x ^ d ∂ν) ^ 2 + B.Cconst h := by
  have hpt : ∀ z : ℝ, B.JpTildeH h z
      = GamTilde d z + betaD d * z ^ d + B.Lam h * z + B.Cconst h := by
    intro z
    simp only [JpTildeH, JpTilde, Lam, Cconst]
    ring
  have hinner : ∀ x ∈ Set.Icc (0 : ℝ) 2, (∫ y, B.JpTildeH h (x * y) ∂ν)
      = (∫ y, GamTilde d (x * y) ∂ν)
        + ((betaD d * (∫ y, y ^ d ∂ν)) * x ^ d + (B.Lam h * (∫ y, y ∂ν)) * x + B.Cconst h) := by
    intro x hx
    have hmaps : ∀ y ∈ Set.Icc (0 : ℝ) 2, x * y ∈ Set.Icc (0 : ℝ) 4 := by
      intro y hy
      exact ⟨mul_nonneg hx.1 hy.1, by nlinarith [hx.1, hx.2, hy.1, hy.2]⟩
    have ig : Integrable (fun y => GamTilde d (x * y)) ν :=
      integrable_of_continuousOn hν
        ((continuousOn_GamTilde hd).comp (continuous_const.mul continuous_id).continuousOn hmaps)
    have i1 : Integrable (fun y : ℝ => (betaD d * x ^ d) * y ^ d) ν :=
      (integrable_of_continuousOn hν (f := fun y : ℝ => y ^ d) (by fun_prop)).const_mul _
    have i2 : Integrable (fun y : ℝ => (B.Lam h * x) * y) ν :=
      (integrable_of_continuousOn hν (f := fun y : ℝ => y) (by fun_prop)).const_mul _
    have heq : (fun y => B.JpTildeH h (x * y))
        = fun y => GamTilde d (x * y) + (betaD d * x ^ d) * y ^ d + (B.Lam h * x) * y
            + B.Cconst h := by
      funext y
      rw [hpt (x * y), mul_pow]
      ring
    have s1 : Integrable (fun y : ℝ => GamTilde d (x * y) + (betaD d * x ^ d) * y ^ d) ν :=
      ig.add i1
    have s2 : Integrable (fun y : ℝ => GamTilde d (x * y) + (betaD d * x ^ d) * y ^ d
        + (B.Lam h * x) * y) ν := s1.add i2
    rw [heq, integral_add s2 (integrable_const _), integral_add s1 i2, integral_add ig i1,
      integral_const_mul, integral_const_mul, integral_const, probReal_univ, smul_eq_mul,
      one_mul]
    ring
  have hGint : Integrable (fun x => ∫ y, GamTilde d (x * y) ∂ν) ν :=
    integrable_innerIntegral hν (continuousOn_GamTilde hd)
  have hPint : Integrable (fun x : ℝ => (betaD d * (∫ y, y ^ d ∂ν)) * x ^ d
      + (B.Lam h * (∫ y, y ∂ν)) * x + B.Cconst h) ν :=
    integrable_of_continuousOn hν (by fun_prop)
  have hcong : B.distributionJ h ν = ∫ x, ((∫ y, GamTilde d (x * y) ∂ν)
      + ((betaD d * (∫ y, y ^ d ∂ν)) * x ^ d + (B.Lam h * (∫ y, y ∂ν)) * x
        + B.Cconst h)) ∂ν := by
    rw [distributionJ]
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Icc_of_distribution hν] with x hx
    exact hinner x hx
  rw [hcong, integral_add hGint hPint, integral_affine_pow hν d]
  simp only [gamAvg]
  ring

/-! ## The candidate law is carried by `[0,2]` -/

/-- **The candidate law `ν_h` is carried by the law interval.**  Both atoms lie in
`(0,1)` (`sVal_pos`, `tVal_lt_one`), so the restriction to `[0,2]` is the whole measure
(`distributionMeasure_restrict_of_mem`) and the complement is null.  This is the hypothesis under
which every lemma of `SingularEndpoint/AuxiliaryLagrangian/DistributionVariance.lean` applies to `ν_h`. -/
theorem distributionMeasure_Icc_compl (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) :
    B.distributionMeasure h (Set.Icc (0 : ℝ) 2)ᶜ = 0 := by
  have hs : B.sVal h ∈ Set.Icc (0 : ℝ) 2 :=
    ⟨(sVal_pos hh).le, by linarith [sVal_lt_one hh]⟩
  have ht : B.tVal h ∈ Set.Icc (0 : ℝ) 2 :=
    ⟨(tVal_pos hh).le, by linarith [tVal_lt_one hh]⟩
  have hres := distributionMeasure_restrict_of_mem B hs ht
  calc B.distributionMeasure h (Set.Icc (0 : ℝ) 2)ᶜ
      = (B.distributionMeasure h).restrict (Set.Icc (0 : ℝ) 2) (Set.Icc (0 : ℝ) 2)ᶜ := by rw [hres]
    _ = 0 := by
        rw [Measure.restrict_apply measurableSet_Icc.compl, Set.compl_inter_self,
          measure_empty]

/-! ## The comparison at a fixed `d`-th moment -/

/-- **The entropy comparison at a fixed `d`-th moment**.  At the fixed moment
`EX^d = q_h` the `β_d` term of `eq:entropy-continuation` is the same for `ν` and for
the admissible candidate `ν_h`, so a competitor at least as cheap as `ν_h` satisfies

`𝒢(ν) + Λ_h x̄² ≤ 𝒢(ν_h) + Λ_h x̄_h²`.

Both `C_h` and `β_d q_h²` cancel, which is the whole point of imposing the moment
constraint. -/
theorem gamAvg_le_of_distributionJ_le (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ}
    (hh : |h| < B.h₀) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) (hmom : (∫ x, x ^ d ∂ν) = B.qVal h)
    (hle : B.distributionJ h ν ≤ B.distributionJ h (B.distributionMeasure h)) :
    gamAvg d ν + B.Lam h * (∫ x, x ∂ν) ^ 2
      ≤ gamAvg d (B.distributionMeasure h)
        + B.Lam h * (∫ x, x ∂(B.distributionMeasure h)) ^ 2 := by
  have := isProbabilityMeasure_distributionMeasure B hh
  have e1 := distributionJ_eq hd B h ν hν
  have e2 := distributionJ_eq hd B h (B.distributionMeasure h) (distributionMeasure_Icc_compl B hh)
  rw [hmom] at e1
  rw [integral_pow_distributionMeasure B hh] at e2
  linarith

/-! ## The candidate average is `O(h⁴)` -/

/-- **The averaged continued gap of the candidate is the block average of `∫Γ_d(W_h)`**
(whose expansion `d³h⁴/3 + O_d(h⁶)` is the first half of `eq:family-gap-expansion`, in the proof
of `lem:constant-graphon-comparison`).  Integrating twice against the
two-atom measure `ν_h`
(`integral_distributionMeasure`) produces the three edge values `s_h², s_h t_h, t_h²`, all of which
lie in `[0,1]`; there `Γ̃_d = Γ_d` (`GamTilde_of_le_one`), so the continuation is invisible and
the result is literally the function whose `h⁴` rate `tendsto_gamInt_block` computes. -/
theorem gamAvg_distributionMeasure (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) :
    gamAvg d (B.distributionMeasure h)
      = B.alph h ^ 2 * Gam d (B.sVal h ^ 2)
        + 2 * B.alph h * (1 - B.alph h) * Gam d (B.sVal h * B.tVal h)
        + (1 - B.alph h) ^ 2 * Gam d (B.tVal h ^ 2) := by
  have ess : GamTilde d (B.sVal h * B.sVal h) = Gam d (B.sVal h ^ 2) := by
    rw [← pow_two, GamTilde_of_le_one (sq_sVal_mem hh).2]
  have est : GamTilde d (B.sVal h * B.tVal h) = Gam d (B.sVal h * B.tVal h) :=
    GamTilde_of_le_one (cross_mem hh).2
  have ets : GamTilde d (B.tVal h * B.sVal h) = Gam d (B.sVal h * B.tVal h) := by
    rw [mul_comm]
    exact GamTilde_of_le_one (cross_mem hh).2
  have ett : GamTilde d (B.tVal h * B.tVal h) = Gam d (B.tVal h ^ 2) := by
    rw [← pow_two, GamTilde_of_le_one (sq_tVal_mem hh).2]
  simp only [gamAvg, integral_distributionMeasure B hh, ess, est, ets, ett]
  ring

/-- **The candidate average is `O(h⁴)`** — the paper's counterpart is `∫Γ_d(W_h) = O_d(h⁴)` in the proof of
`lem:localization-rank-one`.  There are `C > 0` and `δ > 0` with
`𝒢(ν_h) ≤ C h⁴` for `0 < h < δ` inside the family window.

Immediate from `gamAvg_distributionMeasure` and `tendsto_gamInt_block`
(`SingularEndpoint/ConstantGraphonComparison/GamAverage.lean`), whose limit `d³/3` is turned into a two-sided bound by
`exists_eventual_abs_bound`.  Only the upper bound is kept; the constant is not `d³/3`. -/
theorem exists_gamAvg_distribution_le (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, |h| < B.h₀ → 0 < h → h < δ → gamAvg d (B.distributionMeasure h) ≤ C * h ^ 4 := by
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ h : ℝ, F h
      = B.alph h ^ 2 * Gam d (B.sVal h ^ 2)
        + 2 * B.alph h * (1 - B.alph h) * Gam d (B.sVal h * B.tVal h)
        + (1 - B.alph h) ^ 2 * Gam d (B.tVal h ^ 2) := ⟨_, fun _ => rfl⟩
  have hlim : Tendsto (fun h : ℝ => F h / h ^ 4) (𝓝[≠] (0 : ℝ)) (𝓝 ((d : ℝ) ^ 3 / 3)) := by
    simpa only [hF] using tendsto_gamInt_block hd B
  obtain ⟨M, hM, hev⟩ := exists_eventual_abs_bound hlim
  obtain ⟨δ, hδ, hprop⟩ := exists_delta_of_eventually hev
  refine ⟨M, hM, δ, hδ, fun h hh hh0 hhδ => ?_⟩
  have hb := hprop h hh0 hhδ
  rw [abs_of_pos hh0] at hb
  rw [gamAvg_distributionMeasure B hh, ← hF h]
  exact le_trans (le_abs_self _) hb

/-! ## The mean bootstrap -/

/-- **The candidate mean is `u_* + O(h²)`.**  Since
`x̄_h = α_h s_h + (1-α_h)t_h = u_h + (1 - 2α_h)h` exactly, the two family rates
`u_h - u_* = O(h²)` (`tendsto_u_coeff`) and `α_h - 1/2 = O(h)` (`tendsto_alph_slope`) give
`|x̄_h - u_*| ≤ Mh²`. -/
private theorem exists_distributionMean_bound (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < B.h₀ → 0 < h → h < δ →
      |(∫ x, x ∂(B.distributionMeasure h)) - uStar d| ≤ M * h ^ 2 := by
  obtain ⟨Mu, hMu, hevu⟩ := exists_eventual_abs_bound (tendsto_u_coeff B)
  have halph : Tendsto (fun h : ℝ => (B.alph h - 1 / 2) / h ^ 1) (𝓝[≠] (0 : ℝ))
      (𝓝 (2 * (d : ℝ) ^ 2 * uStar d / (3 * ((d : ℝ) - 1)))) := by
    simpa only [pow_one] using tendsto_alph_slope B hd
  obtain ⟨Ma, hMa, heva⟩ := exists_eventual_abs_bound halph
  obtain ⟨δ, hδ, hprop⟩ := exists_delta_of_eventually (hevu.and heva)
  refine ⟨Mu + 2 * Ma, by linarith, δ, hδ, fun h hh hh0 hhδ => ?_⟩
  obtain ⟨hu, ha⟩ := hprop h hh0 hhδ
  rw [abs_of_pos hh0] at hu ha
  rw [pow_one] at ha
  have hmean : (∫ x, x ∂(B.distributionMeasure h)) = B.u h + (1 - 2 * B.alph h) * h := by
    rw [integral_distributionMeasure B hh (fun x => x)]
    simp only [sVal, tVal]
    ring
  have hrw : B.u h + (1 - 2 * B.alph h) * h - uStar d
      = (B.u h - uStar d) - 2 * (B.alph h - 1 / 2) * h := by ring
  rw [hmean, hrw]
  obtain ⟨h1lo, h1hi⟩ := abs_le.mp hu
  obtain ⟨h2lo, h2hi⟩ := abs_le.mp ha
  have h3 : (B.alph h - 1 / 2) * h ≤ Ma * h * h := mul_le_mul_of_nonneg_right h2hi hh0.le
  have h4 : -(Ma * h) * h ≤ (B.alph h - 1 / 2) * h := mul_le_mul_of_nonneg_right h2lo hh0.le
  rw [abs_le]
  constructor <;> nlinarith [h1lo, h1hi, h3, h4]

/-- **The mean bootstrap**.  There are
constants `K₁, K₂ ≥ 0` and a width `δ > 0` such that, for `0 < h < δ` inside the family
window, every probability measure `ν` carried by `[0,2]` whose `d`-th moment is `q_h`
satisfies

`|x̄ - u_*| ≤ K₁·Var(X) + K₂h²`.

Three inputs: the Taylor moment bound `0 ≤ EX^d - x̄^d ≤ C·Var(X)`
(`exists_moment_sub_pow_le_variance`), the family expansion `q_h = u_*^d + O(h²)`
(`tendsto_qVal_coeff`, from the proof in `app:rank-one-parameter-expansions`), and the inversion
`abs_sub_uStar_mul_le` of `z ↦ z^d`.  The moment constraint enters only here. -/
theorem exists_mean_bootstrap (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, |h| < B.h₀ → 0 < h → h < δ →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
          (∫ x, x ^ d ∂ν) = B.qVal h →
            |(∫ x, x ∂ν) - uStar d|
              ≤ K₁ * ((∫ x, x ^ 2 ∂ν) - (∫ x, x ∂ν) ^ 2) + K₂ * h ^ 2 := by
  obtain ⟨Ct, hCt, htay⟩ := exists_moment_sub_pow_le_variance hd
  obtain ⟨Mq, hMq, hevq⟩ := exists_eventual_abs_bound (tendsto_qVal_coeff B hd)
  obtain ⟨δ, hδ, hprop⟩ := exists_delta_of_eventually hevq
  have hE : (0 : ℝ) < uStar d ^ (d - 1) := pow_pos (uStar_pos hd) _
  refine ⟨Ct / uStar d ^ (d - 1), by positivity, Mq / uStar d ^ (d - 1), by positivity, δ, hδ, ?_⟩
  intro h hh hh0 hhδ ν hνp hν hmom
  have : IsProbabilityMeasure ν := hνp
  have hq := hprop h hh0 hhδ
  rw [abs_of_pos hh0] at hq
  obtain ⟨hlow, hupp⟩ := htay ν hνp hν
  have hm0 : 0 ≤ ∫ x, x ∂ν :=
    integral_nonneg_of_ae (by filter_upwards [ae_mem_Icc_of_distribution hν] with x hx using hx.1)
  have e1 : |(∫ x, x ∂ν) ^ d - B.qVal h|
      ≤ Ct * ((∫ x, x ^ 2 ∂ν) - (∫ x, x ∂ν) ^ 2) := by
    rw [← hmom, abs_sub_comm, abs_of_nonneg hlow]
    exact hupp
  have hkey : |(∫ x, x ∂ν) ^ d - uStar d ^ d|
      ≤ Ct * ((∫ x, x ^ 2 ∂ν) - (∫ x, x ∂ν) ^ 2) + Mq * h ^ 2 :=
    le_trans (abs_sub_le _ (B.qVal h) _) (by linarith)
  have hinv := abs_sub_uStar_mul_le hd hm0 (d := d)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, le_div_iff₀ hE]
  linarith

/-! ## The localization `𝒢 = O(h⁴)` -/

/-- **The localization `𝒢 = O(h⁴)`**, the target of this file
(the paper's counterpart of this bound is `eq:moment-and-cost-gap-bounds` in the proof of
`lem:localization-rank-one`, which feeds `eq:graphon-quartic-localization`).

There are `C > 0` and `δ > 0` such that, for every `0 < h < δ` inside the family window and
every probability measure `ν` on `ℝ` carried by `[0,2]` with `EX^d = q_h` that costs no more
than the candidate law `ν_h`,

`𝒢(ν) = E Γ̃_d(XY) ≤ C h⁴`.

*Every exact minimizer is automatically localized*: no minimality is assumed beyond the
inequality `𝒥_h(ν) ≤ 𝒥_h(ν_h)`, and the conclusion is the same `h⁴` rate that the candidate
itself achieves.

The five inputs mirror the localization step in the proof of `lem:localization-rank-one`:
`gamAvg_le_of_distributionJ_le` (counterpart `eq:graphon-cost-decomposition`),
`exists_gamAvg_distribution_le` (`𝒢(ν_h) = O(h⁴)`, counterpart `∫Γ_d(W_h) = O_d(h⁴)`),
`exists_variance_le_sqrt_gamAvg`, and `exists_mean_bootstrap` together with
`exists_distributionMean_bound` (together the counterpart of the pointwise bound
`z^d - r_*^d - d r_*^{d-1}(z - r_*) ≤ C_dΓ_d(z)^{1/2}` and the resulting lower bound for
`e(W) - e(W_h)`), and `tendsto_ell_coeff` (`Λ_h = O(h²)`); `localization_arith` chains them
and applies Young's inequality. -/
theorem exists_gamAvg_localization (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, |h| < B.h₀ → 0 < h → h < δ →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
          (∫ x, x ^ d ∂ν) = B.qVal h →
            B.distributionJ h ν ≤ B.distributionJ h (B.distributionMeasure h) →
              gamAvg d ν ≤ C * h ^ 4 := by
  obtain ⟨C₁, hC₁, δ₁, hδ₁, hcand⟩ := exists_gamAvg_distribution_le hd B
  obtain ⟨Cv, hCv, hvar⟩ := exists_variance_le_sqrt_gamAvg hd
  obtain ⟨K₁, hK₁, K₂, hK₂, δ₂, hδ₂, hmean⟩ := exists_mean_bootstrap hd B
  obtain ⟨Mm, hMm, δ₃, hδ₃, hcmean⟩ := exists_distributionMean_bound hd B
  have hLamlim : Tendsto (fun h : ℝ => B.Lam h / h ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (Lcoeff B)) :=
    (tendsto_ell_coeff B hd).2
  obtain ⟨ML, hML, hevL⟩ := exists_eventual_abs_bound hLamlim
  obtain ⟨δ₄, hδ₄, hLamb⟩ := exists_delta_of_eventually hevL
  have hCpos : 0 < 2 * (C₁ + 4 * ML * (K₂ + Mm)) + (4 * ML * K₁ * Cv) ^ 2 := by
    have h1 : (0 : ℝ) ≤ 4 * ML * (K₂ + Mm) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [sq_nonneg (4 * ML * K₁ * Cv)]
  refine ⟨_, hCpos, min (min δ₁ δ₂) (min δ₃ δ₄),
    lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ hδ₄), ?_⟩
  intro h hh hh0 hhδ ν hνp hν hmom hcost
  have : IsProbabilityMeasure ν := hνp
  have := isProbabilityMeasure_distributionMeasure B hh
  have hd1 : h < δ₁ := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hd2 : h < δ₂ := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hd3 : h < δ₃ := lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hd4 : h < δ₄ := lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hLb := hLamb h hh0 hd4
  rw [abs_of_pos hh0] at hLb
  have hmb : |(∫ x, x ∂ν) - (∫ x, x ∂(B.distributionMeasure h))|
      ≤ K₁ * ((∫ x, x ^ 2 ∂ν) - (∫ x, x ∂ν) ^ 2) + (K₂ + Mm) * h ^ 2 := by
    have e1 := hmean h hh hh0 hd2 ν hνp hν hmom
    have e2 := hcmean h hh hh0 hd3
    have e3 := abs_sub_le (∫ x, x ∂ν) (uStar d) (∫ x, x ∂(B.distributionMeasure h))
    rw [abs_sub_comm (uStar d)] at e3
    linarith
  obtain ⟨hm0, hm2⟩ := mean_mem_Icc hν
  obtain ⟨hn0, hn2⟩ := mean_mem_Icc (distributionMeasure_Icc_compl B hh)
  exact localization_arith (Real.sq_sqrt (gamAvg_nonneg hd hν)) hm0 hm2 hn0 hn2 hML.le hK₁
    (gamAvg_le_of_distributionJ_le hd B hh ν hν hmom hcost) (hcand h hh hh0 hd1)
    (hvar ν hνp hν) hmb hLb

/-! ## `eq:graphon-comparison-estimates` -/

/-- `eq:graphon-comparison-estimates` for a window radius small enough that
`sep_of_tail_window` applies.  The general case is `exists_tail_mass_le`, by monotonicity of
the tail set in `ρ`. -/
private theorem exists_tail_mass_le_small (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρu : ρ ≤ uStar d / 2) :
    ∃ K : ℝ, 0 < K ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, |h| < B.h₀ → 0 < h → h < δ →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
          (∫ x, x ^ d ∂ν) = B.qVal h →
            B.distributionJ h ν ≤ B.distributionJ h (B.distributionMeasure h) →
              (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal ≤ K * h ^ 4 := by
  obtain ⟨C, hC, δ₁, hδ₁, hloc⟩ := exists_gamAvg_localization hd B
  obtain ⟨Cv, hCv, hvar⟩ := exists_variance_le_sqrt_gamAvg hd
  obtain ⟨K₁, hK₁, K₂, hK₂, δ₂, hδ₂, hmean⟩ := exists_mean_bootstrap hd B
  obtain ⟨C₀, hC₀, hquart⟩ := exists_quartic_le_GamTilde hd
  have hu : 0 < uStar d := uStar_pos hd
  -- the three derived constants, introduced opaquely to keep the arithmetic contexts small
  obtain ⟨Cvar, hCvar0, hCvar⟩ : ∃ Cvar : ℝ, 0 ≤ Cvar ∧ Cvar = Cv * Real.sqrt C :=
    ⟨_, mul_nonneg hCv.le (Real.sqrt_nonneg C), rfl⟩
  obtain ⟨Cm, hCm0, hCm⟩ : ∃ Cm : ℝ, 0 ≤ Cm ∧ Cm = K₁ * Cvar + K₂ :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨c, hc, hcdef⟩ : ∃ c : ℝ, 0 < c ∧ c = (uStar d * ρ / 4) ^ 4 / C₀ :=
    ⟨_, by positivity, rfl⟩
  refine ⟨2 * C / c, div_pos (by linarith) hc,
    min (min δ₁ δ₂) (min 1 (min (ρ / 4 / (Cm + 1)) (ρ ^ 2 / 32 / (Cvar + 1)))),
    lt_min (lt_min hδ₁ hδ₂) (lt_min one_pos (lt_min (div_pos (by linarith) (by linarith))
      (div_pos (by positivity) (by linarith)))), ?_⟩
  intro h hh hh0 hhδ ν hνp hν hmom hcost
  have : IsProbabilityMeasure ν := hνp
  have hd1 : h < δ₁ := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hd2 : h < δ₂ := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hh1 : h < 1 := lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hd3 : h < ρ / 4 / (Cm + 1) :=
    lt_of_lt_of_le hhδ (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hd4 : h < ρ ^ 2 / 32 / (Cvar + 1) :=
    lt_of_lt_of_le hhδ (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hG := hloc h hh hh0 hd1 ν hνp hν hmom hcost
  -- `𝒢 = O(h⁴)`, hence `Var(X) ≤ C_var h²` and, for `h` small, `|x̄ - u_*| ≤ ρ/4`
  have hVarh : (∫ x, x ^ 2 ∂ν) - (∫ x, x ∂ν) ^ 2 ≤ Cvar * h ^ 2 := by
    rw [hCvar]
    exact var_le_sq hC hCv.le (hvar ν hνp hν) hG
  have hmeanb : |(∫ x, x ∂ν) - uStar d| ≤ ρ / 4 := by
    refine le_of_sq_bound hCm0 (by linarith) hh0 hh1 hd3 ?_
    have h2 : K₁ * ((∫ x, x ^ 2 ∂ν) - (∫ x, x ∂ν) ^ 2) ≤ K₁ * (Cvar * h ^ 2) :=
      mul_le_mul_of_nonneg_left hVarh hK₁
    rw [hCm]
    linarith only [hmean h hh hh0 hd2 ν hνp hν hmom, h2]
  -- Chebyshev: the half window carries at least half of the mass
  have hNmass : (1 : ℝ) / 2 ≤ ν.real (centralWindow d (ρ / 2)) := by
    refine half_le_measureReal_window hν ?_
    have hcheb := chebyshev_tail hν
      (s := Set.Icc (0 : ℝ) 2 \ centralWindow d (ρ / 2)) (a := ρ / 4)
      (measurableSet_Icc.diff (measurableSet_centralWindow d (ρ / 2)))
      (by linarith) (fun x hx => quarter_le_abs_sub hρ0 hx.2 hmeanb)
    have hle : (ρ / 4) ^ 2 * ν.real (Set.Icc (0 : ℝ) 2 \ centralWindow d (ρ / 2))
        ≤ ρ ^ 2 / 32 := by
      refine le_of_sq_bound hCvar0 (by positivity) hh0 hh1 hd4 ?_
      linarith only [hcheb, hVarh]
    nlinarith only [hle, mul_pos hρ0 hρ0,
      measureReal_nonneg (μ := ν) (s := Set.Icc (0 : ℝ) 2 \ centralWindow d (ρ / 2))]
  -- the rectangle bound, and the conclusion
  have hrect := gamAvg_ge_rect hd hν
    (measurableSet_Icc.diff (measurableSet_centralWindow d ρ))
    (measurableSet_centralWindow d (ρ / 2)) (fun x hx => hx.1) (c := c) ?_
  · have hstep : c * (1 / 2) * ν.real (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)
        ≤ c * ν.real (centralWindow d (ρ / 2))
          * ν.real (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNmass hc.le) measureReal_nonneg
    rw [← measureReal_def, div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith only [hstep, hrect, hG]
  · intro x hxT y hyN hy
    have hx := hxT.1
    have hsep := sep_of_tail_window hd hρ0 hρu hxT.2 hyN
    have hmem : x * y ∈ Set.Icc (0 : ℝ) 4 :=
      ⟨mul_nonneg hx.1 hy.1, by nlinarith only [hx.1, hx.2, hy.1, hy.2]⟩
    have h4 : (uStar d * ρ / 4) ^ 4 ≤ |x * y - rStar d| ^ 4 :=
      pow_le_pow_left₀ (by positivity) hsep 4
    rw [hcdef, div_le_iff₀ hC₀]
    linarith only [h4, hquart _ hmem]

/-- **`eq:graphon-comparison-estimates`**, the one-dimensional tail
estimate that the localization bound also yields.

For each window radius `ρ > 0` there are `K > 0` and `δ > 0` such that, for `0 < h < δ` inside
the family window, every competitor `ν` as in `exists_gamAvg_localization` puts at most
`Kh⁴` of its mass outside the coalescence window `𝓝_ρ`.

Three steps.  Chebyshev together with the mean bootstrap
gives
`ν(𝓝_{ρ/2}) ≥ 1/2` once `h` is small.  The separation `sep_of_tail_window` then makes
`Γ̃_d(xy) ≥ c_ρ > 0` on the rectangle `([0,2] \ 𝓝_ρ) × 𝓝_{ρ/2}` — the positive lower bound
comes from the continued quartic bound `exists_quartic_le_GamTilde` rather than from a
compactness argument.  The rectangle bound `gamAvg_ge_rect` and
the localization bound then close the estimate.

The reduction to a small `ρ`, where the separation is available, is monotonicity: shrinking
`ρ` enlarges the tail set. -/
theorem exists_tail_mass_le (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, |h| < B.h₀ → 0 < h → h < δ →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
          (∫ x, x ^ d ∂ν) = B.qVal h →
            B.distributionJ h ν ≤ B.distributionJ h (B.distributionMeasure h) →
              (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal ≤ K * h ^ 4 := by
  have hu : 0 < uStar d := uStar_pos hd
  obtain ⟨K, hK, δ, hδ, hmain⟩ := exists_tail_mass_le_small hd B
    (ρ := min ρ (uStar d / 2)) (lt_min hρ (by linarith)) (min_le_right _ _)
  refine ⟨K, hK, δ, hδ, fun h hh hh0 hhδ ν hνp hν hmom hcost => ?_⟩
  refine le_trans ?_ (hmain h hh hh0 hhδ ν hνp hν hmom hcost)
  have hwin : centralWindow d (min ρ (uStar d / 2)) ⊆ centralWindow d ρ := by
    intro x hx
    simp only [centralWindow, Set.mem_Icc] at hx ⊢
    have hmin : min ρ (uStar d / 2) ≤ ρ := min_le_left _ _
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact ENNReal.toReal_mono (measure_ne_top ν _)
    (measure_mono (Set.sdiff_subset_sdiff_right hwin))

end KKTFamily

end SingularEndpoint

end UpperTailOptimizers
