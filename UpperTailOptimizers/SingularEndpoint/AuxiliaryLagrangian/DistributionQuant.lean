import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.DistributionGap
import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.PowFirstOrder

/-!
# The quantitative half of the rank-one law comparison (Section 5)

The comparison, in `sec:auxiliary-lagrangian`, of the distribution `ν` of the values of `f`
with `ν_h` has two ingredients: the localisation estimates inherited from
`lem:localization-rank-one` (in the paper `eq:rank-one-reduction-bounds` and
`eq:factor-tail-mass`; for the Lean distribution problem,
`SingularEndpoint/AuxiliaryLagrangian/DistributionLocal.lean` — `exists_gamAvg_localization`, `exists_tail_mass_le`,
`exists_mean_bootstrap`) and the lower bound `lem:auxiliary-lagrangian-bound`
("Lower bound for the auxiliary Lagrangian difference"), whose conclusion is
`eq:auxiliary-lagrangian-bound`.
The exact expansion the lower bound starts from is the unlabelled Lagrangian expansion
following `eq:first-variation`, in the Lean
`KKTFamily.distributionJ_sub_eq` (`SingularEndpoint/AuxiliaryLagrangian/DistributionGap.lean`).  **This file is what comes
after that expansion**, on closed windows: the estimate of the quadratic form `∬K_h dσdσ` over the central
square — in the paper a lemma of its own, `lem:central-kernel-bound`
("Central kernel bound", conclusion `eq:central-kernel-bound`) — and over the mixed
rectangles and the tail square, which the paper estimates inside the proof of
`lem:auxiliary-lagrangian-bound`.

Notation: the paper writes `A_{h,ρ}(ν) := ∫_{𝒩_ρ}Q_h²dν` and `ν(𝒯_ρ)`, with
`𝒯_ρ := [0,2] \ 𝒩_ρ`; the docstrings below abbreviate the closed-window versions, over
`𝓝_ρ = centralWindow d ρ` and `T_ρ = [0,2] \ 𝓝_ρ`, as `A_ρ` and `ε_ρ`.  In the paper the
constant of `lem:central-kernel-bound` is `ρ`-uniform (`C_d`); the constants `C_ρ` below are
produced at a given radius.

## What is assumed, and why

Two ingredients of the kernel decomposition in the proof of
`lem:central-kernel-bound` live *above* this file in the import order, so every
theorem below that needs them carries them as **explicit hypotheses** rather than as axioms,
in the transcription-as-hypothesis idiom the project uses elsewhere:

* the corner clause — the paper's `sup_{0<h<h_ρ}‖Θ_h - d³/4‖_{L^∞(𝒩_ρ²)} ≤ a/4`, with `a = d³/24` the constant of
  `lem:first-variation-bound`.  It appears, with the tighter accuracy `a/8`, as
  `hCorner : ∀ x ∈ centralWindow d ρ, ∀ y ∈ centralWindow d ρ,
   |B.kernelTheta h x y - (d:ℝ)^3/4| ≤ δ` together with `hδ : δ ≤ a/8`;
* the boundedness of the one-variable functions `u_{0,h}` and `u_{d,h}` of the
  decomposition.  The four coefficients of
  `P_h` are bounded in `SingularEndpoint/AuxiliaryLagrangian/PowFirstOrder.lean` (`exists_kp00_window`,
  `exists_kpd0_window`, `exists_kp0d_window`, `exists_kpdd_window`), which this file imports;
  the one-variable ones appear here as
  `hu0 : ∀ x ∈ centralWindow d ρ, |B.u0 h x| ≤ Cu` and the same for `B.ud`.

Neither hypothesis is a weakening of the conclusion: both are proved in
`SingularEndpoint/AuxiliaryLagrangian/KernelError.lean` (`exists_kernelTheta_error`, `exists_u0_window`,
`exists_ud_window`, `exists_kernelTheta_bound`), and `SingularEndpoint/AuxiliaryLagrangian/DistributionWindow.lean` — which
imports that file and this one — discharges them all at once in
`KKTFamily.exists_distribution_window` and `distributionGap_lower_window`.  Nothing else is
assumed: the four `P_h`-coefficient bounds, the tail interpolation
`exists_tail_interpolation`, the first-variation bounds `exists_firstVariation_lower` and
`exists_firstVariation_upperGap`, and the localisation `exists_tail_mass_le` are all consumed in
their proved form.

## The σ-integral in explicit form

`SingularEndpoint/AuxiliaryLagrangian/DistributionGap.lean` defines `KKTFamily.sigmaInt h ν A f = ∫_Afdν - ∫_Afdν_h`; no
signed measure is ever formed.  Every computation below goes through
`sigmaInt_of_atoms_mem`, which evaluates the `ν_h` half explicitly once both atoms lie in
`A`:

`∫_Afdσ = ∫_Afdν - {α_hf(s_h) + (1-α_h)f(t_h)}`.

That is what makes the term-by-term bookkeeping of the paper's central-square estimate purely
a matter of `ν`-integrability: the candidate side needs none.

## What is **not** here

`eq:auxiliary-lagrangian-bound` itself.  Exactly one step separates this file from it, the
absorption of the mixed and tail losses bounded here.  This development performs it by the
absorption step

`C_ρL_hε_ρA_ρ^{3/16} ≤ (a/8)A_ρ + C'_ρ(L_hε_ρ)^{16/13}`,
`(L_hε_ρ)^{16/13} = L_h^{16/13}ε_ρ^{3/13}ε_ρ ≤ L_h^{16/13}(Kh^4)^{3/13}ε_ρ`,

which turns the two losses into `ζ(h)ε_ρ` with
`ζ(h) = C_{ρ,K}(L_h^{16/13}h^{12/13} + L_hh^4) → 0`, after which the localisation bounds
`ε_ρ ≤ Kh⁴`, `|Δ_h(ν)| ≤ Kh⁴` (the paper has `ν(𝒯_ρ) ≤ C_{d,ρ}h⁴` from `eq:factor-tail-mass`
and the weaker `|Δ_h(ν)| ≤ C_dh²` from `eq:rank-one-reduction-bounds`) and
`exists_firstVariation_upperGap` conclude.  The paper reaches the same point without a Young step: its mixed-rectangle bound carries no
`A_ρ^{3/16}` term to absorb.  That step is `SingularEndpoint/AuxiliaryLagrangian/DistributionAbsorption.lean`
(`KKTFamily.exists_distributionGap_refined`, `.exists_distributionGap`), and everything it consumes
is proved below: `distributionGap_lower_of_bounds` is the inequality it acts on,
`exists_abs_mixedQuad_le` supplies `C_m = C_ρL_hε_ρ(ε_ρ + |Δ_h(ν)| + A_ρ^{3/16})` and
`exists_abs_tailQuad_le` supplies `C_t = Cε_ρ²`.  No uniqueness statement is here either:
the paper proves uniqueness only at graphon level, in the last step of the proof of
`thm:singular-endpoint` (`sec:singular-proof`); a distribution-level analogue is
`KKTFamily.distribution_unique` in `SingularEndpoint/Proof/DistributionUnique.lean`.

## Contents

*The `σ`-integral toolkit.*

* `KKTFamily.sigmaInt_of_atoms_mem` — the explicit form of the σ-integral;
* `KKTFamily.Qh_sVal`, `.Qh_tVal` — `Q_h` vanishes at both atoms, hence on the
  support of `ν_h`, which is what makes `∫|Q_h|dν_h = 0` in the proof of
  `lem:central-kernel-bound`;
* `KKTFamily.integral_abs_Qh_le_sqrt`,
  `KKTFamily.abs_setIntegral_le_of_le_abs_Qh` — the Cauchy–Schwarz step
  `∫_{𝓝_ρ}|Q_h|dν ≤ A_ρ^{1/2}` in the proof of `lem:central-kernel-bound`, and its use;
* `KKTFamily.measureReal_window_add_tail`, `.sigmaInt_one_window`,
  `.abs_sigmaInt_pow_window_le` — the two moments of `σ` on the window, `σ(𝓝_ρ) = -ε_ρ` and
  `|∫_{𝓝_ρ}x^ddσ| ≤ |Δ_h(ν)| + 2^dε_ρ` .

*The central square.*

* `KKTFamily.resA`, `.resB`, `.tailSqRes` — the residuals `R_h^xA_h = Q_hu_{0,h}`,
  `R_h^xB_h = Q_hu_{d,h}` and the corner remainder `Q_h(x)Q_h(y){Θ_h(x,y) - d³/4}`, with
  `resA_eq_Qh_mul`, `resB_eq_Qh_mul`, the node values `resA_sVal`, `resA_tVal`,
  `resB_sVal`, `resB_tVal`, `tailSqRes_sVal_right`, `.tailSqRes_tVal_right`,
  `.tailSqRes_sVal_left`, `.tailSqRes_tVal_left`;
* `KKTFamily.kernel_window_decomposition` — the kernel decomposition of the proof of
  `lem:central-kernel-bound` on `𝓝_ρ²`
  in residual form, with the nonnegative square `(d³/4)Q_h(x)Q_h(y)` split off;
* `KKTFamily.continuousOn_kernelCoefA`, `.continuousOn_kernelCoefB`,
  `.continuousOn_resA`, `.continuousOn_resB`, `.continuousOn_tailSqRes_snd` — everything the
  bookkeeping integrates is continuous **on the window**, with no regularity input about
  `u_{0,h}`, `u_{d,h}` or `Θ_h`;
* `KKTFamily.innerSigma`, `.tailSqSigma`, `.centralQuad`, with `tailSqSigma_sVal`,
  `.tailSqSigma_tVal`;
* `KKTFamily.innerSigma_eq` and **`KKTFamily.centralQuad_eq`** — the exact
  term-by-term expansion of `∬_{𝓝_ρ²}K_hdσdσ` ;
* `KKTFamily.abs_tailSqSigma_le` and **`KKTFamily.centralQuad_lower`** — the
  central-square estimate `≥ -(δ + a/8)A_ρ - C_ρ{(1+2^d)ε_ρ + |Δ_h(ν)|}²` .

*The mixed and tail parts.*

* `KKTFamily.mixedQuad`, `.tailQuad`, `.tailSlice`;
* **`KKTFamily.exists_abs_mixedQuad_le`** — `exists_tail_interpolation` integrated
  over the tail, `|2∬_{𝓝_ρ×T_ρ}| ≤ C L_hε_ρ(ε_ρ + |Δ_h(ν)| + A_ρ^{3/16})` ;
* `KKTFamily.exists_abs_JpTildeH_le` and **`KKTFamily.exists_abs_tailQuad_le`** —
  `sup_{[0,4]}|J̃_{p_h}| ≤ C` and the crude bound `|∬_{T_ρ²}| ≤ Cε_ρ²` .

*The split and the assembly.*

* `KKTFamily.sigmaQuad_eq_sigmaInt` — `∬K_hdσdσ` as an iterated σ-integral;
* `KKTFamily.sigmaInt_tailSlice_eq_mixedQuad` — the two mixed rectangles agree (the
  paper's factor `2`), the one place a Fubini exchange is used;
* **`KKTFamily.sigmaQuad_split`** — `∬K_hdσdσ = central + 2·mixed + tail` ;
* `KKTFamily.exists_firstVariation_lower_PsiT` — the central bound `Ψ_h ≥ aQ_h²`, `a = d³/24`,
  of `lem:first-variation-bound` transferred to the continued potential;
* **`KKTFamily.distributionGap_lower`** and **`KKTFamily.distributionGap_lower_of_bounds`** —
  the assembled gap bound, the refined form of `eq:auxiliary-lagrangian-bound` with the
  mixed and tail terms
  still exact, respectively replaced by their bounds.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-! ## Integrability and continuity helpers -/

/-- Integrability on a compact subset of the law interval, from continuity **on that
subset only**.  The variant `integrableOn_of_continuousOn` of `SingularEndpoint/AuxiliaryLagrangian/DistributionMeasure.lean`
asks for continuity on all of `[0,2]`, which the interpolation residuals of
`lem:central-kernel-bound` do not have: they are built from `J_{p_h}` evaluated at
products of window points, and leave `(0,1)` outside the window. -/
private theorem integrableOn_of_continuousOn_compact {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) {f : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) : IntegrableOn f s ν := by
  have h1 : IntegrableOn f (Set.Icc (0 : ℝ) 2 ∩ s) ν :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.inter hs)
      (hf.mono Set.inter_subset_right)
  rw [IntegrableOn, restrict_Icc_inter hν] at h1
  exact h1

/-- A restriction of a law-carried measure is again law-carried.  This is what lets
`continuousOn_innerIntegral` be applied to `ν.restrict (centralWindow d ρ)`, giving the
continuity of the *window* inner integral `x ↦ ∫_{𝓝_ρ}g(xy)dν(y)`. -/
private theorem restrict_distribution_compl {ν : Measure ℝ} (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0)
    (s : Set ℝ) : (ν.restrict s) (Set.Icc (0 : ℝ) 2)ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Icc.compl]
  exact measure_mono_null Set.inter_subset_left hν

namespace KKTFamily

/-! ## The σ-integral over a set carrying both atoms -/

/-- **The σ-integral in explicit form.**  If both atoms lie in `A` then `ν_h` restricted to
`A` is `ν_h` itself (`distributionMeasure_restrict_of_mem`), whose integrals are the explicit
two-point averages, so

`∫_Afdσ = ∫_Afdν - {α_hf(s_h) + (1-α_h)f(t_h)}`.

Every term-by-term computation of the central-square estimate goes through this form: the
candidate side is then pure algebra and only the `ν` side needs integrability. -/
theorem sigmaInt_of_atoms_mem (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    (ν : Measure ℝ) {A : Set ℝ} (hs : B.sVal h ∈ A) (ht : B.tVal h ∈ A) (f : ℝ → ℝ) :
    B.sigmaInt h ν A f
      = (∫ x in A, f x ∂ν)
        - (B.alph h * f (B.sVal h) + (1 - B.alph h) * f (B.tVal h)) := by
  rw [sigmaInt, distributionMeasure_restrict_of_mem B hs ht, integral_distributionMeasure B hh]

/-! ## `Q_h` vanishes on the support of `ν_h` -/

/-- `Q_h(s_h) = 0`. -/
theorem Qh_sVal (B : KKTFamily d) (h : ℝ) : B.Qh h (B.sVal h) = 0 := by
  rw [Qh]
  ring

/-- `Q_h(t_h) = 0`. -/
theorem Qh_tVal (B : KKTFamily d) (h : ℝ) : B.Qh h (B.tVal h) = 0 := by
  rw [Qh]
  ring

/-! ## The Cauchy–Schwarz step -/

/-- **`∫_{𝓝_ρ}|Q_h|dν ≤ A_ρ^{1/2}`**, where
`A_ρ = ∫_{𝓝_ρ}Q_h²dν`.  This is `setIntegral_rpow_le_rpow_setIntegral`
(`SingularEndpoint/AuxiliaryLagrangian/DistributionMeasure.lean`) at exponent `1/2` applied to `Q_h²`, the concave Jensen step
that plays the role of Cauchy–Schwarz; the mass hypothesis `ν(𝓝_ρ) ≤ 1` is automatic for a
probability measure. -/
theorem integral_abs_Qh_le_sqrt (B : KKTFamily d) (h ρ : ℝ) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) :
    ∫ x in centralWindow d ρ, |B.Qh h x| ∂ν
      ≤ Real.sqrt (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν) := by
  have hcQ : Continuous (fun x : ℝ => B.Qh h x ^ 2) := by
    have hc : Continuous (fun x : ℝ => ((x - B.sVal h) * (x - B.tVal h)) ^ 2) := by fun_prop
    exact hc
  have hcQr : Continuous (fun x : ℝ => (B.Qh h x ^ 2) ^ (1 / 2 : ℝ)) :=
    hcQ.rpow_const (fun _ => Or.inr (by norm_num))
  have iQ : IntegrableOn (fun x => B.Qh h x ^ 2) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn hν hcQ.continuousOn (isCompact_centralWindow d ρ)
  have iQr : IntegrableOn (fun x => (B.Qh h x ^ 2) ^ (1 / 2 : ℝ)) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn hν hcQr.continuousOn (isCompact_centralWindow d ρ)
  have hkey := setIntegral_rpow_le_rpow_setIntegral (ν := ν) (g := fun x => B.Qh h x ^ 2)
    (s := centralWindow d ρ) (θ := 1 / 2) (by norm_num) (by norm_num) prob_le_one
    (Filter.Eventually.of_forall fun x => sq_nonneg _) iQ iQr
  have hpt : ∀ x : ℝ, (B.Qh h x ^ 2) ^ (1 / 2 : ℝ) = |B.Qh h x| := by
    intro x
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
  simp only [hpt] at hkey
  rwa [← Real.sqrt_eq_rpow] at hkey

/-! ## The two moments of `σ` on the window -/

/-- **The window mass and the tail mass add up to one**, for a probability measure carried by
the law interval.  This is the identity behind `σ(𝓝_ρ) = -ε_ρ`. -/
theorem measureReal_window_add_tail {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) (d : ℕ) (ρ : ℝ) :
    (ν (centralWindow d ρ)).toReal
        + (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal = 1 := by
  have hsplit : ν (Set.Icc (0 : ℝ) 2 ∩ centralWindow d ρ)
      + ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ) = ν (Set.Icc (0 : ℝ) 2) :=
    measure_inter_add_sdiff _ (measurableSet_centralWindow d ρ)
  have hnull : ν (centralWindow d ρ \ Set.Icc (0 : ℝ) 2) = 0 :=
    measure_mono_null (fun x hx => hx.2) hν
  have hinter : ν (Set.Icc (0 : ℝ) 2 ∩ centralWindow d ρ) = ν (centralWindow d ρ) := by
    have h1 : ν (centralWindow d ρ ∩ Set.Icc (0 : ℝ) 2)
        + ν (centralWindow d ρ \ Set.Icc (0 : ℝ) 2) = ν (centralWindow d ρ) :=
      measure_inter_add_sdiff _ measurableSet_Icc
    rw [hnull, add_zero] at h1
    rw [Set.inter_comm]
    exact h1
  have huniv : ν (Set.Icc (0 : ℝ) 2) = 1 :=
    (prob_compl_eq_zero_iff measurableSet_Icc).mp hν
  rw [hinter, huniv] at hsplit
  have h2 : (ν (centralWindow d ρ)).toReal
      + (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
      = (ν (centralWindow d ρ) + ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal :=
    (ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _)).symm
  rw [h2, hsplit, ENNReal.toReal_one]

/-- **`σ(𝓝_ρ) = -ε_ρ`**, the first of the two moments of `σ`
on which the polynomial part of `lem:central-kernel-bound` depends. -/
theorem sigmaInt_one_window (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) {ρ : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ) :
    B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
      = -(ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := by
  have hkey := measureReal_window_add_tail hν d ρ
  rw [sigmaInt_of_atoms_mem B hh ν hs ht, setIntegral_const, measureReal_def]
  simp only [smul_eq_mul, mul_one]
  linarith

/-- **`|∫_{𝓝_ρ}x^ddσ| ≤ |Δ_h(ν)| + 2^dε_ρ`**, the second
of the two moments.  The window integral is the full moment minus the tail integral, and on
the tail `0 ≤ x ≤ 2` gives `|∫_{T_ρ}x^ddν| ≤ 2^dε_ρ`. -/
theorem abs_sigmaInt_pow_window_le (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) {ρ : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ) :
    |B.sigmaInt h ν (centralWindow d ρ) (fun x => x ^ d)|
      ≤ |(∫ x, x ^ d ∂ν) - B.qVal h|
        + 2 ^ d * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := by
  have hcpow : ContinuousOn (fun x : ℝ => x ^ d) (Set.Icc 0 2) := (continuous_pow d).continuousOn
  have hfull : ∫ x in Set.Icc (0 : ℝ) 2, x ^ d ∂ν
      = (∫ x in centralWindow d ρ, x ^ d ∂ν)
        + ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, x ^ d ∂ν := by
    have hint : IntegrableOn (fun x : ℝ => x ^ d) (Set.Icc (0 : ℝ) 2) ν :=
      integrableOn_of_continuousOn hν hcpow isCompact_Icc
    have hsplit := integral_inter_add_sdiff (measurableSet_centralWindow d ρ) hint
    rw [restrict_Icc_inter hν] at hsplit
    exact hsplit.symm
  rw [restrict_Icc_self hν] at hfull
  have htail : |∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, x ^ d ∂ν|
      ≤ 2 ^ d * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := by
    have hb : ∀ x ∈ Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, ‖x ^ d‖ ≤ 2 ^ d := by
      intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1.1 d)]
      exact pow_le_pow_left₀ hx.1.1 hx.1.2 d
    have hn := norm_setIntegral_le_of_norm_le_const (μ := ν) (measure_lt_top ν _) hb
    simpa [Real.norm_eq_abs, measureReal_def] using hn
  have hnode : B.alph h * B.sVal h ^ d + (1 - B.alph h) * B.tVal h ^ d = B.qVal h := by
    rw [qVal]
  rw [sigmaInt_of_atoms_mem B hh ν hs ht, hnode]
  have heq : (∫ x in centralWindow d ρ, x ^ d ∂ν) - B.qVal h
      = ((∫ x, x ^ d ∂ν) - B.qVal h)
        - ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, x ^ d ∂ν := by
    rw [hfull]
    ring
  rw [heq]
  have := abs_sub (((∫ x, x ^ d ∂ν) - B.qVal h))
    (∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, x ^ d ∂ν)
  calc |((∫ x, x ^ d ∂ν) - B.qVal h)
          - ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, x ^ d ∂ν|
      ≤ |(∫ x, x ^ d ∂ν) - B.qVal h|
          + |∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, x ^ d ∂ν| := abs_sub _ _
    _ ≤ |(∫ x, x ^ d ∂ν) - B.qVal h|
          + 2 ^ d * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := by linarith


/-! ## The central window sits inside `(0,1)`, with room to square -/

/-- **The window `𝓝_ρ` lies in `[u_*/2, 1]`** once `ρ ≤ u_*/2` and `ρ ≤ (1-u_*)/2`.  These are
the two smallness hypotheses on `ρ` already used by `exists_window_package`
(`SingularEndpoint/AuxiliaryLagrangian/PowFirstOrder.lean`); they are what makes the product of two window points land in
`[0,1]`, where `J̃_{p_h} = J_{p_h}` and `lem:central-kernel-bound` applies. -/
private theorem window_bounds (hd : 2 ≤ d) {ρ : ℝ} (hρu : ρ ≤ uStar d / 2)
    (hρ1 : ρ ≤ (1 - uStar d) / 2) {x : ℝ} (hx : x ∈ centralWindow d ρ) :
    uStar d / 2 ≤ x ∧ x ≤ 1 := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  have hx' : x ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hx
  exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩

/-- The window is contained in the law interval. -/
private theorem window_subset_Icc (hd : 2 ≤ d) {ρ : ℝ} (hρu : ρ ≤ uStar d / 2)
    (hρ1 : ρ ≤ (1 - uStar d) / 2) : centralWindow d ρ ⊆ Set.Icc (0 : ℝ) 2 := by
  intro x hx
  have hb := window_bounds hd hρu hρ1 hx
  have hu0 : 0 < uStar d := uStar_pos hd
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

/-! ## The interpolation residuals `Q_hu_{0,h}` and `Q_hu_{d,h}` -/

/-- **The residual of the constant coefficient slice**, `R_h^xA_h`.  By `powResid_eq_mfac_mul`
it equals `Q_h·u_{0,h}` (`resA_eq_Qh_mul`), but *as written* it is a three-term combination
of values of `A_h`, hence continuous wherever `A_h` is.  That is what makes the
central-square bookkeeping integrable without any regularity input about `u_{0,h}`, which is
not available. -/
noncomputable def resA (B : KKTFamily d) (h x : ℝ) : ℝ :=
  powResid d (B.kernelCoefA h) (B.sVal h) (B.tVal h) x

/-- **The residual of the `y^d` coefficient slice**, `R_h^xB_h = Q_h·u_{d,h}`. -/
noncomputable def resB (B : KKTFamily d) (h x : ℝ) : ℝ :=
  powResid d (B.kernelCoefB h) (B.sVal h) (B.tVal h) x

/-- **The corner remainder** `Q_h(x)Q_h(y){Θ_h(x,y) - d³/4}`:
the fourth term of the kernel decomposition in the proof of `lem:central-kernel-bound` with
the nonnegative square `(d³/4)Q_h(x)Q_h(y)` split off.  The corner estimate of that proof,
`sup_{0<h<h_ρ}‖Θ_h - d³/4‖_{L^∞(𝒩_ρ²)} ≤ a/4`, bounds it by `(a/4)|Q_h(x)||Q_h(y)|`; here the
accuracy is a parameter `δ`. -/
noncomputable def tailSqRes (B : KKTFamily d) (h x y : ℝ) : ℝ :=
  B.Qh h x * B.Qh h y * (B.kernelTheta h x y - (d : ℝ) ^ 3 / 4)

/-- **`R_h^xA_h = Q_h u_{0,h}`**, the identification of the residual with the paper's
one-variable function.  This is `powResid_eq_mfac_mul` with `u_{0,h}` unfolded. -/
theorem resA_eq_Qh_mul (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    (hpos : 0 < h) {x : ℝ} (hx : 0 ≤ x) : B.resA h x = B.Qh h x * B.u0 h x := by
  have hd0 : d ≠ 0 := by omega
  have hs : (0 : ℝ) ≤ B.sVal h := (sVal_pos hh).le
  have ht : (0 : ℝ) ≤ B.tVal h := (tVal_pos hh).le
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hpos
  rw [resA, powResid_eq_mfac_mul hd0 _ hs ht hx hst]
  simp only [Qh, u0]

/-- **`R_h^xB_h = Q_h u_{d,h}`**, the same identification for the second slice. -/
theorem resB_eq_Qh_mul (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    (hpos : 0 < h) {x : ℝ} (hx : 0 ≤ x) : B.resB h x = B.Qh h x * B.ud h x := by
  have hd0 : d ≠ 0 := by omega
  have hs : (0 : ℝ) ≤ B.sVal h := (sVal_pos hh).le
  have ht : (0 : ℝ) ≤ B.tVal h := (tVal_pos hh).le
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hpos
  rw [resB, powResid_eq_mfac_mul hd0 _ hs ht hx hst]
  simp only [Qh, ud]

/-- The residual vanishes at the lower node (`powResid_left`). -/
theorem resA_sVal (B : KKTFamily d) (h : ℝ) : B.resA h (B.sVal h) = 0 :=
  powResid_left d _ _ _

/-- The residual vanishes at the lower node (`powResid_left`). -/
theorem resB_sVal (B : KKTFamily d) (h : ℝ) : B.resB h (B.sVal h) = 0 :=
  powResid_left d _ _ _

/-- The residual vanishes at the upper node (`powResid_right`); the nodes are separated
because `t_h - s_h = 2h > 0`. -/
theorem resA_tVal (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    (hpos : 0 < h) : B.resA h (B.tVal h) = 0 := by
  have hd0 : d ≠ 0 := by omega
  have hs : (0 : ℝ) ≤ B.sVal h := (sVal_pos hh).le
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hpos
  exact powResid_right hd0 _ hs hst

/-- The residual vanishes at the upper node (`powResid_right`). -/
theorem resB_tVal (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    (hpos : 0 < h) : B.resB h (B.tVal h) = 0 := by
  have hd0 : d ≠ 0 := by omega
  have hs : (0 : ℝ) ≤ B.sVal h := (sVal_pos hh).le
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hpos
  exact powResid_right hd0 _ hs hst

/-- The corner remainder vanishes when either argument is a node, because `Q_h` does. -/
theorem tailSqRes_sVal_right (B : KKTFamily d) (h x : ℝ) :
    B.tailSqRes h x (B.sVal h) = 0 := by
  have h1 : B.Qh h (B.sVal h) = 0 := Qh_sVal B h
  simp only [tailSqRes, h1, mul_zero, zero_mul]

/-- The corner remainder vanishes when either argument is a node. -/
theorem tailSqRes_tVal_right (B : KKTFamily d) (h x : ℝ) :
    B.tailSqRes h x (B.tVal h) = 0 := by
  have h1 : B.Qh h (B.tVal h) = 0 := Qh_tVal B h
  simp only [tailSqRes, h1, mul_zero, zero_mul]

/-- The corner remainder vanishes when either argument is a node. -/
theorem tailSqRes_sVal_left (B : KKTFamily d) (h y : ℝ) :
    B.tailSqRes h (B.sVal h) y = 0 := by
  have h1 : B.Qh h (B.sVal h) = 0 := Qh_sVal B h
  simp only [tailSqRes, h1, zero_mul]

/-- The corner remainder vanishes when either argument is a node. -/
theorem tailSqRes_tVal_left (B : KKTFamily d) (h y : ℝ) :
    B.tailSqRes h (B.tVal h) y = 0 := by
  have h1 : B.Qh h (B.tVal h) = 0 := Qh_tVal B h
  simp only [tailSqRes, h1, zero_mul]

/-! ## The kernel decomposition of `lem:central-kernel-bound` on the window, in residual form -/

/-- **The kernel decomposition of the proof of `lem:central-kernel-bound` on the central
square**, with the two one-variable
terms written as the residuals `R_h^xA_h`, `R_h^xB_h` and the corner term split into its
nonnegative square and the remainder `tailSqRes`:

`J̃_{p_h}(xy) = P_h(x,y) + {R_h^xA_h(x) + R_h^xB_h(x)y^d} + {R_h^xA_h(y) + R_h^xB_h(y)x^d}
             + (d³/4)Q_h(x)Q_h(y) + Q_h(x)Q_h(y){Θ_h(x,y) - d³/4}`.

The continued entropy may be replaced by `J_{p_h}` because two window points multiply into
`[0,1]` (`window_bounds`); the rest is `kernel_decomposition` together with
`resA_eq_Qh_mul`, `resB_eq_Qh_mul`. -/
theorem kernel_window_decomposition (hd : 2 ≤ d) (B : KKTFamily d) {h ρ : ℝ}
    (hh : |h| < B.h₀) (hpos : 0 < h) (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    {x y : ℝ} (hx : x ∈ centralWindow d ρ) (hy : y ∈ centralWindow d ρ) :
    B.JpTildeH h (x * y)
      = B.kernelPoly h x y + (B.resA h x + B.resB h x * y ^ d)
        + (B.resA h y + B.resB h y * x ^ d)
        + (d : ℝ) ^ 3 / 4 * (B.Qh h x * B.Qh h y)
        + B.tailSqRes h x y := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hxb := window_bounds hd hρu hρ1 hx
  have hyb := window_bounds hd hρu hρ1 hy
  have hx0 : (0 : ℝ) ≤ x := by linarith [hxb.1]
  have hy0 : (0 : ℝ) ≤ y := by linarith [hyb.1]
  have hxy1 : x * y ≤ 1 := by nlinarith [hxb.1, hxb.2, hyb.1, hyb.2]
  rw [JpTildeH_eq_Jp hd hh (mul_nonneg hx0 hy0) hxy1,
    kernel_decomposition hd B hh hpos hx0 hy0,
    resA_eq_Qh_mul hd B hh hpos hx0, resA_eq_Qh_mul hd B hh hpos hy0,
    resB_eq_Qh_mul hd B hh hpos hx0, resB_eq_Qh_mul hd B hh hpos hy0, tailSqRes]
  ring

/-! ## Continuity of the pieces on the window -/

/-- `z ↦ J_{p_h}(zc)` is continuous on the window for a frozen window point `c`: the product
of two window points lies in `[0,1]`, where `continuousOn_Jp_Icc` applies. -/
private theorem continuousOn_Jp_window (hd : 2 ≤ d) (B : KKTFamily d) {h ρ : ℝ}
    (hh : |h| < B.h₀) (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    {c : ℝ} (hc : c ∈ centralWindow d ρ) :
    ContinuousOn (fun z : ℝ => Jp (B.p h) (z * c)) (centralWindow d ρ) := by
  have hp := B.p_mem h hh
  have hu0 : 0 < uStar d := uStar_pos hd
  have hcb := window_bounds hd hρu hρ1 hc
  have hmaps : Set.MapsTo (fun z : ℝ => z * c) (centralWindow d ρ) (Set.Icc (0 : ℝ) 1) := by
    intro z hz
    have hzb := window_bounds hd hρu hρ1 hz
    exact ⟨mul_nonneg (by linarith [hzb.1]) (by linarith [hcb.1]),
      by nlinarith [hzb.1, hzb.2, hcb.1, hcb.2]⟩
  exact (continuousOn_Jp_Icc hp.1 hp.2).comp
    (continuous_id.mul continuous_const).continuousOn hmaps

/-- **The `y^d` coefficient slice is continuous on the window.**  It is the explicit divided
difference `(J_{p_h}(xt_h) - J_{p_h}(xs_h))/(t_h^d - s_h^d)`. -/
theorem continuousOn_kernelCoefB (hd : 2 ≤ d) (B : KKTFamily d) {h ρ : ℝ}
    (hh : |h| < B.h₀) (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ) :
    ContinuousOn (B.kernelCoefB h) (centralWindow d ρ) := by
  have heq : B.kernelCoefB h = fun z : ℝ =>
      (Jp (B.p h) (z * B.tVal h) - Jp (B.p h) (z * B.sVal h))
        / (B.tVal h ^ d - B.sVal h ^ d) := rfl
  rw [heq]
  exact ((continuousOn_Jp_window hd B hh hρu hρ1 ht).sub
    (continuousOn_Jp_window hd B hh hρu hρ1 hs)).div_const _

/-- **The constant coefficient slice is continuous on the window**, being
`J_{p_h}(xs_h) - B_h(x)s_h^d`. -/
theorem continuousOn_kernelCoefA (hd : 2 ≤ d) (B : KKTFamily d) {h ρ : ℝ}
    (hh : |h| < B.h₀) (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ) :
    ContinuousOn (B.kernelCoefA h) (centralWindow d ρ) := by
  have heq : B.kernelCoefA h = fun z : ℝ =>
      Jp (B.p h) (z * B.sVal h) - B.kernelCoefB h z * B.sVal h ^ d := rfl
  rw [heq]
  exact (continuousOn_Jp_window hd B hh hρu hρ1 hs).sub
    ((continuousOn_kernelCoefB hd B hh hρu hρ1 hs ht).mul continuousOn_const)

/-- **The residual `R_h^xA_h` is continuous on the window**: the two interpolation
coefficients are constants, so the residual is `A_h` minus an affine function of `x^d`. -/
theorem continuousOn_resA (hd : 2 ≤ d) (B : KKTFamily d) {h ρ : ℝ}
    (hh : |h| < B.h₀) (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ) :
    ContinuousOn (B.resA h) (centralWindow d ρ) := by
  have heq : B.resA h = fun z : ℝ => B.kernelCoefA h z
      - powCoefA d (B.kernelCoefA h) (B.sVal h) (B.tVal h)
      - powCoefB d (B.kernelCoefA h) (B.sVal h) (B.tVal h) * z ^ d := rfl
  rw [heq]
  exact ((continuousOn_kernelCoefA hd B hh hρu hρ1 hs ht).sub continuousOn_const).sub
    (continuousOn_const.mul (continuous_pow d).continuousOn)

/-- **The residual `R_h^xB_h` is continuous on the window.** -/
theorem continuousOn_resB (hd : 2 ≤ d) (B : KKTFamily d) {h ρ : ℝ}
    (hh : |h| < B.h₀) (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ) :
    ContinuousOn (B.resB h) (centralWindow d ρ) := by
  have heq : B.resB h = fun z : ℝ => B.kernelCoefB h z
      - powCoefA d (B.kernelCoefB h) (B.sVal h) (B.tVal h)
      - powCoefB d (B.kernelCoefB h) (B.sVal h) (B.tVal h) * z ^ d := rfl
  rw [heq]
  exact ((continuousOn_kernelCoefB hd B hh hρu hρ1 hs ht).sub continuousOn_const).sub
    (continuousOn_const.mul (continuous_pow d).continuousOn)

/-- **The corner remainder is continuous in its second argument on the window.**  Nothing is
known about the regularity of `Θ_h`; what is used is that `tailSqRes` *equals*, on the
window, a difference of continuous functions — the rearranged
`kernel_window_decomposition`. -/
theorem continuousOn_tailSqRes_snd (hd : 2 ≤ d) (B : KKTFamily d) {h ρ : ℝ}
    (hh : |h| < B.h₀) (hpos : 0 < h) (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ)
    {x : ℝ} (hx : x ∈ centralWindow d ρ) :
    ContinuousOn (fun y => B.tailSqRes h x y) (centralWindow d ρ) := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hxb := window_bounds hd hρu hρ1 hx
  have hx0 : (0 : ℝ) ≤ x := by linarith [hxb.1]
  have hx2 : x ≤ 2 := by linarith [hxb.2]
  have hsub := window_subset_Icc hd hρu hρ1 (d := d) (ρ := ρ)
  have hJ : ContinuousOn (fun y : ℝ => B.JpTildeH h (x * y)) (centralWindow d ρ) :=
    (continuousOn_distributionIntegrand hd B h hx0 hx2).mono hsub
  have hpoly : ContinuousOn (fun y : ℝ => B.kernelPoly h x y) (centralWindow d ρ) := by
    have hc : Continuous (fun y : ℝ => B.kp00 h + B.kpd0 h * x ^ d + B.kp0d h * y ^ d
        + B.kpdd h * (x ^ d * y ^ d)) := by fun_prop
    exact hc.continuousOn
  have hQ : ContinuousOn (fun y : ℝ => B.Qh h y) (centralWindow d ρ) := by
    have hc : Continuous (fun y : ℝ => (y - B.sVal h) * (y - B.tVal h)) := by fun_prop
    exact hc.continuousOn
  have hcont : ContinuousOn (fun y : ℝ => B.JpTildeH h (x * y) - B.kernelPoly h x y
      - (B.resA h x + B.resB h x * y ^ d) - (B.resA h y + B.resB h y * x ^ d)
      - (d : ℝ) ^ 3 / 4 * (B.Qh h x * B.Qh h y)) (centralWindow d ρ) :=
    (((hJ.sub hpoly).sub (continuousOn_const.add
        (continuousOn_const.mul (continuous_pow d).continuousOn))).sub
      ((continuousOn_resA hd B hh hρu hρ1 hs ht).add
        (continuousOn_resB hd B hh hρu hρ1 hs ht |>.mul continuousOn_const))).sub
      (continuousOn_const.mul (continuousOn_const.mul hQ))
  refine hcont.congr ?_
  intro y hy
  have hdec := kernel_window_decomposition hd B hh hpos hρu hρ1 hx hy
  linarith

/-! ## The central square: the exact expansion -/

/-- **The inner window σ-integral** `Φ_h(x) = ∫_{𝓝_ρ}K_h(x,y)dσ(y)` of the central-square
estimate. -/
noncomputable def innerSigma (B : KKTFamily d) (h ρ : ℝ) (ν : Measure ℝ) (x : ℝ) : ℝ :=
  B.sigmaInt h ν (centralWindow d ρ) (fun y => B.JpTildeH h (x * y))

/-- The corner remainder integrated in its second variable,
`∫_{𝓝_ρ}Q_h(x)Q_h(y){Θ_h(x,y) - d³/4}dν(y)`.  Because `Q_h` vanishes at both atoms the
`ν`-integral is already the σ-integral. -/
noncomputable def tailSqSigma (B : KKTFamily d) (h ρ : ℝ) (ν : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ y in centralWindow d ρ, B.tailSqRes h x y ∂ν

/-- **The central part of the σ-quadratic form**, `∬_{𝓝_ρ²}K_hdσdσ`, as an iterated
σ-integral. -/
noncomputable def centralQuad (B : KKTFamily d) (h ρ : ℝ) (ν : Measure ℝ) : ℝ :=
  B.sigmaInt h ν (centralWindow d ρ) (B.innerSigma h ρ ν)

/-- The corner remainder vanishes at the lower node, so its window integral does. -/
theorem tailSqSigma_sVal (B : KKTFamily d) (h ρ : ℝ) (ν : Measure ℝ) :
    B.tailSqSigma h ρ ν (B.sVal h) = 0 := by
  simp only [tailSqSigma, tailSqRes_sVal_left, integral_zero]

/-- The corner remainder vanishes at the upper node, so its window integral does. -/
theorem tailSqSigma_tVal (B : KKTFamily d) (h ρ : ℝ) (ν : Measure ℝ) :
    B.tailSqSigma h ρ ν (B.tVal h) = 0 := by
  simp only [tailSqSigma, tailSqRes_tVal_left, integral_zero]

end KKTFamily

/-- Additivity of a set integral over a six-term sum.  Both the inner and the outer
integration of the central-square estimate split into exactly six pieces. -/
private theorem setIntegral_add_six {ν : Measure ℝ} {A : Set ℝ}
    {f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ} (h₁ : IntegrableOn f₁ A ν) (h₂ : IntegrableOn f₂ A ν)
    (h₃ : IntegrableOn f₃ A ν) (h₄ : IntegrableOn f₄ A ν) (h₅ : IntegrableOn f₅ A ν)
    (h₆ : IntegrableOn f₆ A ν) :
    ∫ y in A, (f₁ y + f₂ y + f₃ y + f₄ y + f₅ y + f₆ y) ∂ν
      = (∫ y in A, f₁ y ∂ν) + (∫ y in A, f₂ y ∂ν) + (∫ y in A, f₃ y ∂ν)
        + (∫ y in A, f₄ y ∂ν) + (∫ y in A, f₅ y ∂ν) + (∫ y in A, f₆ y ∂ν) := by
  have e₂ : ∫ y in A, (f₁ y + f₂ y) ∂ν
      = (∫ y in A, f₁ y ∂ν) + ∫ y in A, f₂ y ∂ν := integral_add h₁ h₂
  have e₃ : ∫ y in A, (f₁ y + f₂ y + f₃ y) ∂ν
      = (∫ y in A, (f₁ y + f₂ y) ∂ν) + ∫ y in A, f₃ y ∂ν := integral_add (h₁.add h₂) h₃
  have e₄ : ∫ y in A, (f₁ y + f₂ y + f₃ y + f₄ y) ∂ν
      = (∫ y in A, (f₁ y + f₂ y + f₃ y) ∂ν) + ∫ y in A, f₄ y ∂ν :=
    integral_add ((h₁.add h₂).add h₃) h₄
  have e₅ : ∫ y in A, (f₁ y + f₂ y + f₃ y + f₄ y + f₅ y) ∂ν
      = (∫ y in A, (f₁ y + f₂ y + f₃ y + f₄ y) ∂ν) + ∫ y in A, f₅ y ∂ν :=
    integral_add (((h₁.add h₂).add h₃).add h₄) h₅
  have e₆ : ∫ y in A, (f₁ y + f₂ y + f₃ y + f₄ y + f₅ y + f₆ y) ∂ν
      = (∫ y in A, (f₁ y + f₂ y + f₃ y + f₄ y + f₅ y) ∂ν) + ∫ y in A, f₆ y ∂ν :=
    integral_add ((((h₁.add h₂).add h₃).add h₄).add h₅) h₆
  rw [e₆, e₅, e₄, e₃, e₂]

namespace KKTFamily

/-- **The inner σ-integral of the kernel over the central window**, term by term.  Inserting
`kernel_window_decomposition` and integrating in `y` leaves an affine function of `x^d`, two
residual terms, one `Q_h`-term and the corner remainder:

`∫_{𝓝_ρ}K_h(x,y)dσ(y) = {p_{00}σ(𝓝_ρ) + p_{0d}∫x^ddσ + ∫R^xA_hdν}
  + {p_{d0}σ(𝓝_ρ) + p_{dd}∫x^ddσ + ∫R^xB_hdν}x^d
  + σ(𝓝_ρ)R^xA_h(x) + (∫x^ddσ)R^xB_h(x)
  + (d³/4)(∫Q_hdν)Q_h(x) + ∫Q_h(x)Q_h(y){Θ_h(x,y) - d³/4}dν(y)`.

This is the exact form of the paper's assertion that the
polynomial part depends only on `σ(𝓝_ρ)` and `∫_{𝓝_ρ}x^ddσ`, and that every term with exactly
one factor of `Q_h` carries a `∫_{𝓝_ρ}|Q_h|dν`. -/
theorem innerSigma_eq (hd : 2 ≤ d) (B : KKTFamily d) {h ρ : ℝ} (hh : |h| < B.h₀)
    (hpos : 0 < h) (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ)
    {x : ℝ} (hx : x ∈ centralWindow d ρ) :
    B.innerSigma h ρ ν x
      = (B.kp00 h * B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
            + B.kp0d h * B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
            + ∫ y in centralWindow d ρ, B.resA h y ∂ν)
        + (B.kpd0 h * B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
            + B.kpdd h * B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
            + ∫ y in centralWindow d ρ, B.resB h y ∂ν) * x ^ d
        + B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1) * B.resA h x
        + B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d) * B.resB h x
        + ((d : ℝ) ^ 3 / 4 * ∫ y in centralWindow d ρ, B.Qh h y ∂ν) * B.Qh h x
        + B.tailSqSigma h ρ ν x := by
  have hmN := measurableSet_centralWindow d ρ
  have hcpt := isCompact_centralWindow d ρ
  have hdec : ∀ y ∈ centralWindow d ρ, B.JpTildeH h (x * y)
      = (B.kp00 h + B.kpd0 h * x ^ d + B.resA h x)
        + (B.kp0d h + B.kpdd h * x ^ d + B.resB h x) * y ^ d
        + B.resA h y + x ^ d * B.resB h y
        + ((d : ℝ) ^ 3 / 4 * B.Qh h x) * B.Qh h y
        + B.tailSqRes h x y := by
    intro y hy
    rw [kernel_window_decomposition hd B hh hpos hρu hρ1 hx hy, kernelPoly]
    ring
  have hQc : ContinuousOn (fun y : ℝ => B.Qh h y) (centralWindow d ρ) := by
    have hc : Continuous (fun y : ℝ => (y - B.sVal h) * (y - B.tVal h)) := by fun_prop
    exact hc.continuousOn
  have i1 : IntegrableOn
      (fun _ : ℝ => B.kp00 h + B.kpd0 h * x ^ d + B.resA h x) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn_compact hν hcpt continuousOn_const
  have i2 : IntegrableOn
      (fun y : ℝ => (B.kp0d h + B.kpdd h * x ^ d + B.resB h x) * y ^ d)
      (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn_compact hν hcpt
      (continuousOn_const.mul (continuous_pow d).continuousOn)
  have i3 : IntegrableOn (fun y : ℝ => B.resA h y) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn_compact hν hcpt (continuousOn_resA hd B hh hρu hρ1 hs ht)
  have i4 : IntegrableOn (fun y : ℝ => x ^ d * B.resB h y) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn_compact hν hcpt
      (continuousOn_const.mul (continuousOn_resB hd B hh hρu hρ1 hs ht))
  have i5 : IntegrableOn (fun y : ℝ => ((d : ℝ) ^ 3 / 4 * B.Qh h x) * B.Qh h y)
      (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn_compact hν hcpt (continuousOn_const.mul hQc)
  have i6 : IntegrableOn (fun y : ℝ => B.tailSqRes h x y) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn_compact hν hcpt
      (continuousOn_tailSqRes_snd hd B hh hpos hρu hρ1 hs ht hx)
  have hsplit : (∫ y in centralWindow d ρ,
        ((B.kp00 h + B.kpd0 h * x ^ d + B.resA h x)
          + (B.kp0d h + B.kpdd h * x ^ d + B.resB h x) * y ^ d
          + B.resA h y + x ^ d * B.resB h y
          + ((d : ℝ) ^ 3 / 4 * B.Qh h x) * B.Qh h y
          + B.tailSqRes h x y) ∂ν)
      = (∫ y in centralWindow d ρ, (B.kp00 h + B.kpd0 h * x ^ d + B.resA h x) ∂ν)
        + (∫ y in centralWindow d ρ,
            (B.kp0d h + B.kpdd h * x ^ d + B.resB h x) * y ^ d ∂ν)
        + (∫ y in centralWindow d ρ, B.resA h y ∂ν)
        + (∫ y in centralWindow d ρ, x ^ d * B.resB h y ∂ν)
        + (∫ y in centralWindow d ρ, ((d : ℝ) ^ 3 / 4 * B.Qh h x) * B.Qh h y ∂ν)
        + ∫ y in centralWindow d ρ, B.tailSqRes h x y ∂ν :=
    setIntegral_add_six i1 i2 i3 i4 i5 i6
  have hnS : B.JpTildeH h (x * B.sVal h)
      = (B.kp00 h + B.kpd0 h * x ^ d + B.resA h x)
        + (B.kp0d h + B.kpdd h * x ^ d + B.resB h x) * B.sVal h ^ d := by
    rw [hdec _ hs, resA_sVal, resB_sVal, Qh_sVal, tailSqRes_sVal_right]
    ring
  have hnT : B.JpTildeH h (x * B.tVal h)
      = (B.kp00 h + B.kpd0 h * x ^ d + B.resA h x)
        + (B.kp0d h + B.kpdd h * x ^ d + B.resB h x) * B.tVal h ^ d := by
    rw [hdec _ ht, resA_tVal hd B hh hpos, resB_tVal hd B hh hpos, Qh_tVal,
      tailSqRes_tVal_right]
    ring
  have hS1 : B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
      = (ν (centralWindow d ρ)).toReal - 1 := by
    rw [sigmaInt_of_atoms_mem B hh ν hs ht, setIntegral_const, measureReal_def, smul_eq_mul]
    ring
  have hSd : B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
      = (∫ y in centralWindow d ρ, y ^ d ∂ν)
        - (B.alph h * B.sVal h ^ d + (1 - B.alph h) * B.tVal h ^ d) :=
    sigmaInt_of_atoms_mem B hh ν hs ht _
  rw [innerSigma, sigmaInt_of_atoms_mem B hh ν hs ht,
    setIntegral_congr_fun hmN (fun y hy => hdec y hy), hsplit, hnS, hnT, hS1, hSd, tailSqSigma]
  rw [setIntegral_const, measureReal_def, integral_const_mul, integral_const_mul,
    integral_const_mul, smul_eq_mul]
  ring

/-- **The inner window σ-integral is continuous on the law interval.**  Only the
continuity of `J̃_{p_h}` on `[0,4]` is used: the `ν`-half is `continuousOn_innerIntegral`
applied to `ν` restricted to the window, and the `ν_h`-half is the explicit two-point
average. -/
private theorem continuousOn_innerSigma (hd : 2 ≤ d) (B : KKTFamily d) {h ρ : ℝ}
    (hh : |h| < B.h₀) (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ) :
    ContinuousOn (B.innerSigma h ρ ν) (Set.Icc 0 2) := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hsb := window_bounds hd hρu hρ1 hs
  have htb := window_bounds hd hρu hρ1 ht
  have : IsFiniteMeasure (ν.restrict (centralWindow d ρ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_lt_top ν _⟩
  have h1 : ContinuousOn (fun x => ∫ y in centralWindow d ρ, B.JpTildeH h (x * y) ∂ν)
      (Set.Icc 0 2) :=
    continuousOn_innerIntegral (restrict_distribution_compl hν _) (continuousOn_JpTildeH hd B h)
  have h2 : ContinuousOn (fun x : ℝ => B.JpTildeH h (x * B.sVal h)) (Set.Icc 0 2) := by
    refine (continuousOn_distributionIntegrand hd B h (xt := B.sVal h) (by linarith [hsb.1])
      (by linarith [hsb.2])).congr ?_
    intro x _
    show B.JpTildeH h (x * B.sVal h) = B.JpTildeH h (B.sVal h * x)
    rw [mul_comm]
  have h3 : ContinuousOn (fun x : ℝ => B.JpTildeH h (x * B.tVal h)) (Set.Icc 0 2) := by
    refine (continuousOn_distributionIntegrand hd B h (xt := B.tVal h) (by linarith [htb.1])
      (by linarith [htb.2])).congr ?_
    intro x _
    show B.JpTildeH h (x * B.tVal h) = B.JpTildeH h (B.tVal h * x)
    rw [mul_comm]
  have hcont : ContinuousOn (fun x : ℝ =>
      (∫ y in centralWindow d ρ, B.JpTildeH h (x * y) ∂ν)
        - (B.alph h * B.JpTildeH h (x * B.sVal h)
          + (1 - B.alph h) * B.JpTildeH h (x * B.tVal h))) (Set.Icc 0 2) :=
    h1.sub ((continuousOn_const.mul h2).add (continuousOn_const.mul h3))
  refine hcont.congr ?_
  intro x _
  rw [innerSigma, sigmaInt_of_atoms_mem B hh ν hs ht]

/-- **The window integral of the corner remainder is continuous on the window.**  Again
nothing is assumed about `Θ_h`: by `innerSigma_eq` the function `tailSqSigma` *equals* the
inner σ-integral minus an explicit continuous expression. -/
private theorem continuousOn_tailSqSigma (hd : 2 ≤ d) (B : KKTFamily d) {h ρ : ℝ}
    (hh : |h| < B.h₀) (hpos : 0 < h) (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ) :
    ContinuousOn (B.tailSqSigma h ρ ν) (centralWindow d ρ) := by
  have hsub : centralWindow d ρ ⊆ Set.Icc (0 : ℝ) 2 := window_subset_Icc hd hρu hρ1
  have hQc : ContinuousOn (fun x : ℝ => B.Qh h x) (centralWindow d ρ) := by
    have hc : Continuous (fun x : ℝ => (x - B.sVal h) * (x - B.tVal h)) := by fun_prop
    exact hc.continuousOn
  have hI : ContinuousOn (B.innerSigma h ρ ν) (centralWindow d ρ) :=
    (continuousOn_innerSigma hd B hh hρu hρ1 hν hs ht).mono hsub
  have hcont : ContinuousOn (fun x : ℝ => B.innerSigma h ρ ν x
      - ((B.kp00 h * B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
            + B.kp0d h * B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
            + ∫ y in centralWindow d ρ, B.resA h y ∂ν)
          + (B.kpd0 h * B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
            + B.kpdd h * B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
            + ∫ y in centralWindow d ρ, B.resB h y ∂ν) * x ^ d
          + B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1) * B.resA h x
          + B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d) * B.resB h x
          + ((d : ℝ) ^ 3 / 4 * ∫ y in centralWindow d ρ, B.Qh h y ∂ν) * B.Qh h x))
      (centralWindow d ρ) :=
    hI.sub ((((continuousOn_const.add
      (continuousOn_const.mul (continuous_pow d).continuousOn)).add
      (continuousOn_const.mul (continuousOn_resA hd B hh hρu hρ1 hs ht))).add
      (continuousOn_const.mul (continuousOn_resB hd B hh hρu hρ1 hs ht))).add
      (continuousOn_const.mul hQc))
  refine hcont.congr ?_
  intro x hx
  have hkey := innerSigma_eq hd B hh hpos hρu hρ1 hν hs ht hx
  linarith

/-- **The central square, expanded exactly**.  Writing
`S₁ = σ(𝓝_ρ)`, `S_d = ∫_{𝓝_ρ}x^ddσ`, `I_A = ∫_{𝓝_ρ}R^xA_hdν`, `I_B = ∫_{𝓝_ρ}R^xB_hdν` and
`I_Q = ∫_{𝓝_ρ}Q_hdν`,

`∬_{𝓝_ρ²}K_hdσdσ = p_{00}S₁² + (p_{0d}+p_{d0})S₁S_d + p_{dd}S_d²
   + 2S₁I_A + 2S_dI_B + (d³/4)I_Q² + ∫_{𝓝_ρ}∫_{𝓝_ρ}Q_h(x)Q_h(y){Θ_h(x,y)-d³/4}dνdν`.

The three groups are the paper's: a polynomial part depending only on the two moments of `σ`
on the window, two one-`Q_h` terms, and the corner term with its nonnegative square
`(d³/4)(∫_{𝓝_ρ}Q_hdσ)²` — here `(d³/4)I_Q²`, the two being equal because `Q_h` vanishes on
the support of `ν_h`.  **No estimate is used**: this is an identity. -/
theorem centralQuad_eq (hd : 2 ≤ d) (B : KKTFamily d) {h ρ : ℝ} (hh : |h| < B.h₀)
    (hpos : 0 < h) (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ) :
    B.centralQuad h ρ ν
      = B.kp00 h * B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1) ^ 2
        + (B.kp0d h + B.kpd0 h)
            * (B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
              * B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d))
        + B.kpdd h * B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d) ^ 2
        + 2 * (B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
            * ∫ y in centralWindow d ρ, B.resA h y ∂ν)
        + 2 * (B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
            * ∫ y in centralWindow d ρ, B.resB h y ∂ν)
        + (d : ℝ) ^ 3 / 4 * (∫ y in centralWindow d ρ, B.Qh h y ∂ν) ^ 2
        + ∫ x in centralWindow d ρ, B.tailSqSigma h ρ ν x ∂ν := by
  have hmN := measurableSet_centralWindow d ρ
  have hcpt := isCompact_centralWindow d ρ
  have hQc : ContinuousOn (fun x : ℝ => B.Qh h x) (centralWindow d ρ) := by
    have hc : Continuous (fun x : ℝ => (x - B.sVal h) * (x - B.tVal h)) := by fun_prop
    exact hc.continuousOn
  have hdec : ∀ x ∈ centralWindow d ρ, B.innerSigma h ρ ν x
      = (B.kp00 h * B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
            + B.kp0d h * B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
            + ∫ y in centralWindow d ρ, B.resA h y ∂ν)
        + (B.kpd0 h * B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
            + B.kpdd h * B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
            + ∫ y in centralWindow d ρ, B.resB h y ∂ν) * x ^ d
        + B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1) * B.resA h x
        + B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d) * B.resB h x
        + ((d : ℝ) ^ 3 / 4 * ∫ y in centralWindow d ρ, B.Qh h y ∂ν) * B.Qh h x
        + B.tailSqSigma h ρ ν x :=
    fun x hx => innerSigma_eq hd B hh hpos hρu hρ1 hν hs ht hx
  have j1 : IntegrableOn
      (fun _ : ℝ => B.kp00 h * B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
            + B.kp0d h * B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
            + ∫ y in centralWindow d ρ, B.resA h y ∂ν) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn_compact hν hcpt continuousOn_const
  have j2 : IntegrableOn
      (fun x : ℝ => (B.kpd0 h * B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
            + B.kpdd h * B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
            + ∫ y in centralWindow d ρ, B.resB h y ∂ν) * x ^ d) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn_compact hν hcpt
      (continuousOn_const.mul (continuous_pow d).continuousOn)
  have j3 : IntegrableOn
      (fun x : ℝ => B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1) * B.resA h x)
      (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn_compact hν hcpt
      (continuousOn_const.mul (continuousOn_resA hd B hh hρu hρ1 hs ht))
  have j4 : IntegrableOn
      (fun x : ℝ => B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d) * B.resB h x)
      (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn_compact hν hcpt
      (continuousOn_const.mul (continuousOn_resB hd B hh hρu hρ1 hs ht))
  have j5 : IntegrableOn
      (fun x : ℝ => ((d : ℝ) ^ 3 / 4 * ∫ y in centralWindow d ρ, B.Qh h y ∂ν)
        * B.Qh h x) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn_compact hν hcpt (continuousOn_const.mul hQc)
  have j6 : IntegrableOn (fun x : ℝ => B.tailSqSigma h ρ ν x) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn_compact hν hcpt
      (continuousOn_tailSqSigma hd B hh hpos hρu hρ1 hν hs ht)
  have hsplit := setIntegral_add_six j1 j2 j3 j4 j5 j6
  have hnS : B.innerSigma h ρ ν (B.sVal h)
      = (B.kp00 h * B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
            + B.kp0d h * B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
            + ∫ y in centralWindow d ρ, B.resA h y ∂ν)
        + (B.kpd0 h * B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
            + B.kpdd h * B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
            + ∫ y in centralWindow d ρ, B.resB h y ∂ν) * B.sVal h ^ d := by
    rw [hdec _ hs, resA_sVal, resB_sVal, Qh_sVal, tailSqSigma_sVal]
    ring
  have hnT : B.innerSigma h ρ ν (B.tVal h)
      = (B.kp00 h * B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
            + B.kp0d h * B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
            + ∫ y in centralWindow d ρ, B.resA h y ∂ν)
        + (B.kpd0 h * B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
            + B.kpdd h * B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
            + ∫ y in centralWindow d ρ, B.resB h y ∂ν) * B.tVal h ^ d := by
    rw [hdec _ ht, resA_tVal hd B hh hpos, resB_tVal hd B hh hpos, Qh_tVal,
      tailSqSigma_tVal]
    ring
  have hS1 : B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)
      = (ν (centralWindow d ρ)).toReal - 1 := by
    rw [sigmaInt_of_atoms_mem B hh ν hs ht, setIntegral_const, measureReal_def, smul_eq_mul]
    ring
  have hSd : B.sigmaInt h ν (centralWindow d ρ) (fun y => y ^ d)
      = (∫ y in centralWindow d ρ, y ^ d ∂ν)
        - (B.alph h * B.sVal h ^ d + (1 - B.alph h) * B.tVal h ^ d) :=
    sigmaInt_of_atoms_mem B hh ν hs ht _
  rw [centralQuad, sigmaInt_of_atoms_mem B hh ν hs ht,
    setIntegral_congr_fun hmN (fun x hx => hdec x hx), hsplit, hnS, hnT, hS1, hSd]
  rw [setIntegral_const, measureReal_def, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, smul_eq_mul]
  ring

/-! ## The central-square estimate -/

/-- **Every window integral of a `Q_h`-dominated function is `O(A_ρ^{1/2})`.**  This is the
Cauchy–Schwarz mechanism of the proof of `lem:central-kernel-bound`: `|f| ≤ C|Q_h|` on `𝓝_ρ` gives
`|∫_{𝓝_ρ}fdν| ≤ C∫_{𝓝_ρ}|Q_h|dν ≤ CA_ρ^{1/2}` by `integral_abs_Qh_le_sqrt`. -/
theorem abs_setIntegral_le_of_le_abs_Qh (B : KKTFamily d) (h ρ : ℝ) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) {f : ℝ → ℝ}
    (hint : IntegrableOn f (centralWindow d ρ) ν) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x ∈ centralWindow d ρ, |f x| ≤ C * |B.Qh h x|) :
    |∫ x in centralWindow d ρ, f x ∂ν|
      ≤ C * Real.sqrt (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν) := by
  have hmN := measurableSet_centralWindow d ρ
  have hcpt := isCompact_centralWindow d ρ
  have hQabs : IntegrableOn (fun x => |B.Qh h x|) (centralWindow d ρ) ν := by
    refine integrableOn_of_continuousOn_compact hν hcpt ?_
    have hc : Continuous (fun x : ℝ => |(x - B.sVal h) * (x - B.tVal h)|) := by fun_prop
    exact hc.continuousOn
  have h1 : |∫ x in centralWindow d ρ, f x ∂ν| ≤ ∫ x in centralWindow d ρ, |f x| ∂ν := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := ν.restrict (centralWindow d ρ)) f
  have h2 : (∫ x in centralWindow d ρ, |f x| ∂ν)
      ≤ ∫ x in centralWindow d ρ, C * |B.Qh h x| ∂ν :=
    setIntegral_mono_on hint.abs (hQabs.const_mul C) hmN hf
  have h3 : (∫ x in centralWindow d ρ, C * |B.Qh h x| ∂ν)
      = C * ∫ x in centralWindow d ρ, |B.Qh h x| ∂ν := integral_const_mul _ _
  have h4 := integral_abs_Qh_le_sqrt B h ρ hν
  nlinarith [h1, h2, h3, h4]

/-- **The corner remainder is `δ|Q_h(x)|A_ρ^{1/2}` pointwise**, which is the corner estimate
of the proof of `lem:central-kernel-bound` integrated in one variable.  The clause is a
hypothesis; see the module docstring. -/
theorem abs_tailSqSigma_le (hd : 2 ≤ d) (B : KKTFamily d) {h ρ δ : ℝ} (hh : |h| < B.h₀)
    (hpos : 0 < h) (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ) (hδ : 0 ≤ δ)
    (hCorner : ∀ x ∈ centralWindow d ρ, ∀ y ∈ centralWindow d ρ,
      |B.kernelTheta h x y - (d : ℝ) ^ 3 / 4| ≤ δ)
    {x : ℝ} (hx : x ∈ centralWindow d ρ) :
    |B.tailSqSigma h ρ ν x|
      ≤ (δ * |B.Qh h x|)
          * Real.sqrt (∫ y in centralWindow d ρ, B.Qh h y ^ 2 ∂ν) := by
  have hint : IntegrableOn (fun y : ℝ => B.tailSqRes h x y) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn_compact hν (isCompact_centralWindow d ρ)
      (continuousOn_tailSqRes_snd hd B hh hpos hρu hρ1 hs ht hx)
  refine abs_setIntegral_le_of_le_abs_Qh B h ρ hν hint
    (mul_nonneg hδ (abs_nonneg _)) ?_
  intro y hy
  have hb := hCorner x hx y hy
  have habs : |B.tailSqRes h x y|
      = |B.Qh h x| * |B.Qh h y| * |B.kernelTheta h x y - (d : ℝ) ^ 3 / 4| := by
    rw [tailSqRes, abs_mul, abs_mul]
  rw [habs]
  have h1 : |B.Qh h x| * |B.Qh h y| * |B.kernelTheta h x y - (d : ℝ) ^ 3 / 4|
      ≤ |B.Qh h x| * |B.Qh h y| * δ :=
    mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  nlinarith [h1]

/-- The arithmetic of the central-square estimate, isolated as a statement about plain
reals.  `L = d³/192 = a/8` and `K = 192C_u²/d³ = C_u²/L` are the constants of this Lean
estimate's single Young step `2C_u√A(E + X) ≤ L·A + K(E + X)²`, which treats both one-`Q_h`
terms at once (the paper's proof of `lem:central-kernel-bound` applies
`uv ≤ (a/8)u² + (2/a)v²` to each of them separately); the
hypotheses `hL`, `hK` state them without division so that the proof is a `linear_combination`. -/
private theorem central_arith {kp00 kpd0 kp0d kpdd S1 Sd IA IB IQ CS A sA E X Cp Cu δ dd
    K L : ℝ} (hdd : 0 < dd) (hL : L * 192 = dd) (hK : K * dd = 192 * Cu ^ 2)
    (hCp : 0 ≤ Cp) (_hCu : 0 ≤ Cu) (_hδ : 0 ≤ δ)
    (_hsA0 : 0 ≤ sA) (hsA : sA * sA = A) (hE : 0 ≤ E) (hX : 0 ≤ X)
    (h00 : |kp00| ≤ Cp) (hd0 : |kpd0| ≤ Cp) (h0d : |kp0d| ≤ Cp) (hddc : |kpdd| ≤ Cp)
    (hS1 : |S1| ≤ E) (hSd : |Sd| ≤ X)
    (hIA : |IA| ≤ Cu * sA) (hIB : |IB| ≤ Cu * sA) (hCS : |CS| ≤ δ * A) :
    -(δ + L) * A - (Cp + K) * (E + X) ^ 2
      ≤ kp00 * S1 ^ 2 + (kp0d + kpd0) * (S1 * Sd) + kpdd * Sd ^ 2
        + 2 * (S1 * IA) + 2 * (Sd * IB) + dd / 4 * IQ ^ 2 + CS := by
  have hA0 : 0 ≤ A := by nlinarith [hsA, mul_self_nonneg sA]
  have habs00 : |kp00 * S1 ^ 2| ≤ Cp * E ^ 2 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul h00 (pow_le_pow_left₀ (abs_nonneg S1) hS1 2) (by positivity) hCp
  have habsdd : |kpdd * Sd ^ 2| ≤ Cp * X ^ 2 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hddc (pow_le_pow_left₀ (abs_nonneg Sd) hSd 2) (by positivity) hCp
  have habsMix : |(kp0d + kpd0) * (S1 * Sd)| ≤ 2 * Cp * (E * X) := by
    rw [abs_mul, abs_mul]
    have h1 : |kp0d + kpd0| ≤ 2 * Cp := le_trans (abs_add_le _ _) (by linarith)
    have h2 : |S1| * |Sd| ≤ E * X :=
      mul_le_mul hS1 hSd (abs_nonneg _) hE
    exact mul_le_mul h1 h2 (by positivity) (by linarith)
  have habsA : |2 * (S1 * IA)| ≤ 2 * (E * (Cu * sA)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hS1 hIA (abs_nonneg _) hE) (by norm_num)
  have habsB : |2 * (Sd * IB)| ≤ 2 * (X * (Cu * sA)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hSd hIB (abs_nonneg _) hX) (by norm_num)
  have hIQ0 : 0 ≤ dd / 4 * IQ ^ 2 := by positivity
  have hyoung : 2 * (E * (Cu * sA)) + 2 * (X * (Cu * sA)) ≤ L * A + K * (E + X) ^ 2 := by
    have hkey : (0 : ℝ) ≤ (dd * sA - 192 * Cu * (E + X)) ^ 2 := sq_nonneg _
    have hexp : (dd * sA - 192 * Cu * (E + X)) ^ 2
        = 192 * dd * (L * A + K * (E + X) ^ 2
            - (2 * (E * (Cu * sA)) + 2 * (X * (Cu * sA)))) := by
      linear_combination (dd ^ 2) * hsA + (-(dd * A)) * hL + (-(192 * (E + X) ^ 2)) * hK
    nlinarith [hkey, hexp, hdd]
  have step1 : -(Cp * E ^ 2 + 2 * Cp * (E * X) + Cp * X ^ 2)
      - (2 * (E * (Cu * sA)) + 2 * (X * (Cu * sA))) - δ * A
      ≤ kp00 * S1 ^ 2 + (kp0d + kpd0) * (S1 * Sd) + kpdd * Sd ^ 2
        + 2 * (S1 * IA) + 2 * (Sd * IB) + dd / 4 * IQ ^ 2 + CS := by
    have e1 := neg_abs_le (kp00 * S1 ^ 2)
    have e2 := neg_abs_le ((kp0d + kpd0) * (S1 * Sd))
    have e3 := neg_abs_le (kpdd * Sd ^ 2)
    have e4 := neg_abs_le (2 * (S1 * IA))
    have e5 := neg_abs_le (2 * (Sd * IB))
    have e6 := neg_abs_le CS
    linarith [habs00, habsMix, habsdd, habsA, habsB, hCS, hIQ0]
  linarith [step1, hyoung]

/-- **The central-square lower bound**.  For window
radius `ρ` small enough that `𝓝_ρ ⊂ (0,1)` with room to square, and for `0 < h` with both
atoms in the window,

`∬_{𝓝_ρ²}K_hdσdσ ≥ -(δ + a/8)A_ρ - C_ρ{(1+2^d)ε_ρ + |Δ_h(ν)|}²`,   `a = d³/24`,

with `C_ρ = C_p + 192C_u²/d³` explicit.  The three inputs that the proof of
`lem:central-kernel-bound` establishes along the way — the four coefficient bounds
`C_p`, the bounds `C_u` on `u_{0,h}, u_{d,h}`, and the corner estimate for
`Θ_h - d³/4` — are hypotheses here; all three are proved elsewhere
(`exists_kp00_window` and friends in `SingularEndpoint/AuxiliaryLagrangian/PowFirstOrder.lean`, `exists_u0_window`,
`exists_ud_window` and `exists_kernelTheta_error` in `SingularEndpoint/AuxiliaryLagrangian/KernelError.lean`) and
discharged in `SingularEndpoint/AuxiliaryLagrangian/DistributionWindow.lean`; see the module docstring.

The nonnegative square `(d³/4)(∫_{𝒩_ρ}Q_hdσ)²` of the paper (here over `𝓝_ρ`) is discarded
through `dd/4·I_Q² ≥ 0`, exactly as the paper does. -/
theorem centralQuad_lower (hd : 2 ≤ d) (B : KKTFamily d) {h ρ δ Cu Cp : ℝ}
    (hh : |h| < B.h₀) (hpos : 0 < h) (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ)
    (hδ : 0 ≤ δ) (hCu : 0 ≤ Cu) (hCp : 0 ≤ Cp)
    (h00 : |B.kp00 h| ≤ Cp) (hd0 : |B.kpd0 h| ≤ Cp) (h0d : |B.kp0d h| ≤ Cp)
    (hddc : |B.kpdd h| ≤ Cp)
    (hu0 : ∀ x ∈ centralWindow d ρ, |B.u0 h x| ≤ Cu)
    (hud : ∀ x ∈ centralWindow d ρ, |B.ud h x| ≤ Cu)
    (hCorner : ∀ x ∈ centralWindow d ρ, ∀ y ∈ centralWindow d ρ,
      |B.kernelTheta h x y - (d : ℝ) ^ 3 / 4| ≤ δ) :
    -(δ + (d : ℝ) ^ 3 / 192) * (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
        - (Cp + 192 * Cu ^ 2 / (d : ℝ) ^ 3)
          * ((1 + 2 ^ d) * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
              + |(∫ x, x ^ d ∂ν) - B.qVal h|) ^ 2
      ≤ B.centralQuad h ρ ν := by
  have hu0R : (0 : ℝ) < uStar d := uStar_pos hd
  have hdR : (0 : ℝ) < (d : ℝ) := dpos hd
  have hdd : (0 : ℝ) < (d : ℝ) ^ 3 := by positivity
  have hmN := measurableSet_centralWindow d ρ
  have hcpt := isCompact_centralWindow d ρ
  have hA0 : (0 : ℝ) ≤ ∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν :=
    setIntegral_nonneg hmN fun x _ => sq_nonneg _
  have hsA0 : (0 : ℝ) ≤ Real.sqrt (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν) :=
    Real.sqrt_nonneg _
  have hsA : Real.sqrt (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
      * Real.sqrt (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
      = ∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν := Real.mul_self_sqrt hA0
  have hE : (0 : ℝ) ≤ (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := ENNReal.toReal_nonneg
  have hX : (0 : ℝ) ≤ |(∫ x, x ^ d ∂ν) - B.qVal h|
      + 2 ^ d * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := by positivity
  -- the two moments of `σ` on the window
  have hS1 : |B.sigmaInt h ν (centralWindow d ρ) (fun _ => 1)|
      ≤ (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := by
    rw [sigmaInt_one_window B hh hν hs ht, abs_neg, abs_of_nonneg hE]
  have hSd := abs_sigmaInt_pow_window_le B hh hν hs ht
  -- the two one-`Q_h` integrals
  have hIA : |∫ y in centralWindow d ρ, B.resA h y ∂ν|
      ≤ Cu * Real.sqrt (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν) := by
    refine abs_setIntegral_le_of_le_abs_Qh B h ρ hν
      (integrableOn_of_continuousOn_compact hν hcpt
        (continuousOn_resA hd B hh hρu hρ1 hs ht)) hCu ?_
    intro y hy
    have hyb := window_bounds hd hρu hρ1 hy
    rw [resA_eq_Qh_mul hd B hh hpos (by linarith [hyb.1] : (0 : ℝ) ≤ y), abs_mul]
    exact mul_le_mul_of_nonneg_left (hu0 y hy) (abs_nonneg _) |>.trans_eq (by ring)
  have hIB : |∫ y in centralWindow d ρ, B.resB h y ∂ν|
      ≤ Cu * Real.sqrt (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν) := by
    refine abs_setIntegral_le_of_le_abs_Qh B h ρ hν
      (integrableOn_of_continuousOn_compact hν hcpt
        (continuousOn_resB hd B hh hρu hρ1 hs ht)) hCu ?_
    intro y hy
    have hyb := window_bounds hd hρu hρ1 hy
    rw [resB_eq_Qh_mul hd B hh hpos (by linarith [hyb.1] : (0 : ℝ) ≤ y), abs_mul]
    exact mul_le_mul_of_nonneg_left (hud y hy) (abs_nonneg _) |>.trans_eq (by ring)
  -- the corner remainder
  have hCS : |∫ x in centralWindow d ρ, B.tailSqSigma h ρ ν x ∂ν|
      ≤ δ * ∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν := by
    have hb := abs_setIntegral_le_of_le_abs_Qh B h ρ hν
      (integrableOn_of_continuousOn_compact hν hcpt
        (continuousOn_tailSqSigma hd B hh hpos hρu hρ1 hν hs ht))
      (mul_nonneg hδ hsA0)
      (fun x hx => (abs_tailSqSigma_le hd B hh hpos hρu hρ1 hν hs ht hδ hCorner hx).trans_eq
        (by ring))
    nlinarith [hb, hsA]
  -- the arithmetic
  have hL : (d : ℝ) ^ 3 / 192 * 192 = (d : ℝ) ^ 3 := by ring
  have hK : 192 * Cu ^ 2 / (d : ℝ) ^ 3 * (d : ℝ) ^ 3 = 192 * Cu ^ 2 := by
    field_simp
  have hmain := central_arith (kp00 := B.kp00 h) (kpd0 := B.kpd0 h) (kp0d := B.kp0d h)
    (kpdd := B.kpdd h) (IQ := ∫ y in centralWindow d ρ, B.Qh h y ∂ν)
    hdd hL hK hCp hCu hδ hsA0 hsA hE hX h00 hd0 h0d hddc hS1 hSd hIA hIB hCS
  rw [centralQuad_eq hd B hh hpos hρu hρ1 hν hs ht]
  have hrw : (Cp + 192 * Cu ^ 2 / (d : ℝ) ^ 3)
      * ((ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
          + (|(∫ x, x ^ d ∂ν) - B.qVal h|
            + 2 ^ d * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal)) ^ 2
      = (Cp + 192 * Cu ^ 2 / (d : ℝ) ^ 3)
        * ((1 + 2 ^ d) * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
            + |(∫ x, x ^ d ∂ν) - B.qVal h|) ^ 2 := by ring
  linarith [hmain, hrw.symm.le, hrw.le]

/-! ## The mixed and tail parts -/

/-- **The mixed part** `2∬_{𝓝_ρ×T_ρ}K_hdσdσ`, in the one-sided form
`∫_{T_ρ}(∫_{𝓝_ρ}K_h(x,y)dσ(y))dν(x)` in which `exists_tail_interpolation` applies
directly to the inner integral. -/
noncomputable def mixedQuad (B : KKTFamily d) (h ρ : ℝ) (ν : Measure ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.innerSigma h ρ ν x ∂ν

/-- **The tail part** `∬_{T_ρ²}K_hdσdσ`; on the tail `σ` coincides with `ν`
(`sigmaInt_tail`), so this is a plain double `ν`-integral. -/
noncomputable def tailQuad (B : KKTFamily d) (h ρ : ℝ) (ν : Measure ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ,
    (∫ y in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.JpTildeH h (x * y) ∂ν) ∂ν

/-- **The mixed estimate**.  For every window radius
`ρ > 0` there are `C > 0` and a threshold such that

`|∫_{T_ρ}(∫_{𝓝_ρ}K_hdσ)dν| ≤ C L_h ε_ρ (ε_ρ + |Δ_h(ν)| + A_ρ^{3/16})`,  `L_h = 1 + log(1/h)`.

The inner σ-integral *is* the left-hand side of `exists_tail_interpolation`
at the frozen tail point, so the only work is to integrate a
constant bound over `T_ρ`.  This is the step at which the singularities of the entropy along
the tail are harmless: no derivative in the tail variable is used. -/
theorem exists_abs_mixedQuad_le (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ0 : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → |h| < B.h₀ →
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
        |B.mixedQuad h ρ ν|
          ≤ C * (1 + Real.log (1 / h))
              * ((ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
                  + |(∫ u, u ^ d ∂ν) - B.qVal h|
                  + (∫ u in centralWindow d ρ, B.Qh h u ^ 2 ∂ν) ^ (3 / 16 : ℝ))
              * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := by
  obtain ⟨C, hC, δ, hδ, hbnd⟩ := exists_tail_interpolation hd B hρ0
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro h hh0 hhδ hhb ν hνp hν
  have : IsProbabilityMeasure ν := hνp
  have hptw : ∀ x ∈ Set.Icc (0 : ℝ) 2 \ centralWindow d ρ,
      ‖B.innerSigma h ρ ν x‖
        ≤ C * (1 + Real.log (1 / h))
            * ((ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
                + |(∫ u, u ^ d ∂ν) - B.qVal h|
                + (∫ u in centralWindow d ρ, B.Qh h u ^ 2 ∂ν) ^ (3 / 16 : ℝ)) := by
    intro x hx
    rw [Real.norm_eq_abs, innerSigma, sigmaInt]
    exact hbnd h hh0 hhδ hhb ν hνp hν x hx.1
  have hn := norm_setIntegral_le_of_norm_le_const (μ := ν)
    (measure_lt_top ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)) hptw
  rw [mixedQuad]
  simpa [Real.norm_eq_abs, measureReal_def] using hn

/-- **The continued entropy is bounded on `[0,4]`, uniformly in small `h`.**  The
displacement `eq:entropy-parameter-shift` makes this a compactness bound on `J̃_{p_*}` alone plus the
two `h`-dependent constants `Λ_h` and `C_h`, both continuous and vanishing at `h = 0`.  This
is the `sup_{[0,4]}|J̃_{p_h}| ≤ C` of the crude tail estimate. -/
theorem exists_abs_JpTildeH_le (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      ∀ z ∈ Set.Icc (0 : ℝ) 4, |B.JpTildeH h z| ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    (continuousOn_JpTilde hd)
  have hC₀0 : (0 : ℝ) ≤ C₀ := le_trans (norm_nonneg _) (hC₀ 0 ⟨le_rfl, by norm_num⟩)
  have hLam : ContinuousAt (fun h : ℝ => ell (B.p h) - ell (pStar d)) 0 :=
    (ell_p_continuousAt hd B).sub continuousAt_const
  have hLam0 : (fun h : ℝ => ell (B.p h) - ell (pStar d)) 0 = 0 := by
    simp only [B.p_zero, sub_self]
  have hcst : ContinuousAt (fun h : ℝ => Jp (B.p h) 0 - Jp (pStar d) 0) 0 :=
    (Jp_p_zero_continuousAt hd B).sub continuousAt_const
  have hcst0 : (fun h : ℝ => Jp (B.p h) 0 - Jp (pStar d) 0) 0 = 0 := by
    simp only [B.p_zero, sub_self]
  obtain ⟨δ₁, hδ₁, hb₁'⟩ := exists_close_of_continuousAt hLam hLam0
  obtain ⟨δ₂, hδ₂, hb₂'⟩ := exists_close_of_continuousAt hcst hcst0
  have hb₁ : ∀ h : ℝ, |h| < δ₁ → |ell (B.p h) - ell (pStar d)| ≤ 1 := by
    intro h hh; simpa using hb₁' h hh
  have hb₂ : ∀ h : ℝ, |h| < δ₂ → |Jp (B.p h) 0 - Jp (pStar d) 0| ≤ 1 := by
    intro h hh; simpa using hb₂' h hh
  refine ⟨C₀ + 5, by linarith, min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro h hh z hz
  have hh1 : |h| < δ₁ := lt_of_lt_of_le hh (min_le_left _ _)
  have hh2 : |h| < δ₂ := lt_of_lt_of_le hh (min_le_right _ _)
  have hbase : |JpTilde d z| ≤ C₀ := by
    have hb := hC₀ z hz
    rwa [Real.norm_eq_abs] at hb
  have hL := hb₁ h hh1
  have hK := hb₂ h hh2
  have hprod : |(ell (B.p h) - ell (pStar d)) * z| ≤ 4 := by
    rw [abs_mul, abs_of_nonneg hz.1]
    nlinarith [abs_nonneg (ell (B.p h) - ell (pStar d)), hz.1, hz.2]
  have ht1 := abs_add_le (JpTilde d z + (ell (B.p h) - ell (pStar d)) * z)
    (Jp (B.p h) 0 - Jp (pStar d) 0)
  have ht2 := abs_add_le (JpTilde d z) ((ell (B.p h) - ell (pStar d)) * z)
  rw [JpTildeH]
  linarith

/-- **The crude tail estimate**: with
`sup_{[0,4]}|J̃_{p_h}| ≤ C`,

`|∬_{T_ρ²}K_hdσdσ| ≤ Cε_ρ²`.

No structure of the kernel is used — this is the one place in the proof where the tail is
handled by nothing but boundedness. -/
theorem exists_abs_tailQuad_le (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      ∀ ρ : ℝ, ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
        |B.tailQuad h ρ ν|
          ≤ C * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal ^ 2 := by
  obtain ⟨C, hC, δ, hδ, hbnd⟩ := exists_abs_JpTildeH_le hd B
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro h hh ρ ν hνp hν
  have : IsProbabilityMeasure ν := hνp
  have hmul : ∀ x ∈ Set.Icc (0 : ℝ) 2 \ centralWindow d ρ,
      ∀ y ∈ Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, x * y ∈ Set.Icc (0 : ℝ) 4 := by
    intro x hx y hy
    exact ⟨mul_nonneg hx.1.1 hy.1.1, by nlinarith [hx.1.1, hx.1.2, hy.1.1, hy.1.2]⟩
  have hinner : ∀ x ∈ Set.Icc (0 : ℝ) 2 \ centralWindow d ρ,
      ‖∫ y in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.JpTildeH h (x * y) ∂ν‖
        ≤ C * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := by
    intro x hx
    have hb : ∀ y ∈ Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, ‖B.JpTildeH h (x * y)‖ ≤ C := by
      intro y hy
      rw [Real.norm_eq_abs]
      exact hbnd h hh _ (hmul x hx y hy)
    have hn := norm_setIntegral_le_of_norm_le_const (μ := ν)
      (measure_lt_top ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)) hb
    simpa [measureReal_def] using hn
  have hn := norm_setIntegral_le_of_norm_le_const (μ := ν)
    (measure_lt_top ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)) hinner
  rw [tailQuad]
  have hfin : ‖∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ,
      (∫ y in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.JpTildeH h (x * y) ∂ν) ∂ν‖
      ≤ C * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
        * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal := by
    simpa [measureReal_def] using hn
  rw [Real.norm_eq_abs] at hfin
  nlinarith [hfin]

/-! ## The three-way split of the σ-quadratic form -/

/-- **The σ-quadratic form is an iterated σ-integral**,

`∬K_hdσdσ = ∫_{[0,2]}(∫_{[0,2]}K_h(x,y)dσ(y))dσ(x)`.

`KKTFamily.sigmaQuad` is *defined* by its expansion
`𝒥_h(ν) - 2∫𝒦_hdν + 𝒥_h(ν_h)` (`SingularEndpoint/AuxiliaryLagrangian/DistributionGap.lean`); this identifies it with the
iterated form the paper's central/mixed/tail split acts on.  **No Fubini theorem is used**:
the inner integral against `ν_h` is the explicit two-point average, so the two mixed terms
are computed rather than exchanged. -/
theorem sigmaQuad_eq_sigmaInt (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) :
    B.sigmaQuad h ν
      = B.sigmaInt h ν (Set.Icc 0 2)
          (fun x => B.sigmaInt h ν (Set.Icc 0 2) (fun y => B.JpTildeH h (x * y))) := by
  have := isProbabilityMeasure_distributionMeasure B hh
  have hsIcc : B.sVal h ∈ Set.Icc (0 : ℝ) 2 :=
    ⟨(sVal_pos hh).le, by linarith [sVal_lt_one hh]⟩
  have htIcc : B.tVal h ∈ Set.Icc (0 : ℝ) 2 :=
    ⟨(tVal_pos hh).le, by linarith [tVal_lt_one hh]⟩
  have hinner : ∀ x : ℝ, B.sigmaInt h ν (Set.Icc 0 2) (fun y => B.JpTildeH h (x * y))
      = (∫ y, B.JpTildeH h (x * y) ∂ν) - B.crossK h x := by
    intro x
    rw [sigmaInt, restrict_Icc_self hν, restrict_Icc_self (distributionMeasure_Icc_compl B hh),
      integral_distributionMeasure_kernel B hh]
  have hint1 : Integrable (fun x => ∫ y, B.JpTildeH h (x * y) ∂ν) ν :=
    integrable_of_continuousOn hν
      (continuousOn_innerIntegral hν (continuousOn_JpTildeH hd B h))
  have hint2 : Integrable (B.crossK h) ν :=
    integrable_of_continuousOn hν (continuousOn_crossK hd B hh)
  have is : Integrable (fun y => B.JpTildeH h (B.sVal h * y)) ν :=
    integrable_of_continuousOn hν (continuousOn_distributionIntegrand hd B h hsIcc.1 hsIcc.2)
  have it : Integrable (fun y => B.JpTildeH h (B.tVal h * y)) ν :=
    integrable_of_continuousOn hν (continuousOn_distributionIntegrand hd B h htIcc.1 htIcc.2)
  have hcross : B.alph h * (∫ y, B.JpTildeH h (B.sVal h * y) ∂ν)
      + (1 - B.alph h) * (∫ y, B.JpTildeH h (B.tVal h * y) ∂ν)
      = ∫ y, B.crossK h y ∂ν := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (is.const_mul _) (it.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    rw [crossK, mul_comm y (B.sVal h), mul_comm y (B.tVal h)]
  have hnuh : B.alph h * B.crossK h (B.sVal h) + (1 - B.alph h) * B.crossK h (B.tVal h)
      = B.distributionJ h (B.distributionMeasure h) := by
    rw [distributionJ_distributionMeasure_eq_integral_crossK B hh, integral_distributionMeasure B hh]
  have hpJ : B.distributionJ h ν = ∫ x, (∫ y, B.JpTildeH h (x * y) ∂ν) ∂ν := rfl
  rw [sigmaInt_of_atoms_mem B hh ν hsIcc htIcc]
  simp only [hinner]
  rw [restrict_Icc_self hν, integral_sub hint1 hint2, sigmaQuad, hpJ]
  linarith [hcross, hnuh]

/-- The kernel with its argument clamped to `[0,4]`: a globally continuous and globally
bounded function of one variable agreeing with `J̃_{p_h}` on `[0,4]`.  Its only purpose is to
make the Fubini exchange between the two mixed rectangles a statement about a bounded
continuous function, so that no measurability argument about `J̃_{p_h}` is needed. -/
private noncomputable def kclamp (B : KKTFamily d) (h u : ℝ) : ℝ :=
  B.JpTildeH h (min (max u 0) 4)

private theorem kclamp_mem (u : ℝ) : min (max u 0) 4 ∈ Set.Icc (0 : ℝ) 4 :=
  ⟨le_min (le_max_right u 0) (by norm_num), min_le_right _ _⟩

private theorem continuous_kclamp (hd : 2 ≤ d) (B : KKTFamily d) (h : ℝ) :
    Continuous (B.kclamp h) :=
  (continuousOn_JpTildeH hd B h).comp_continuous (by fun_prop) kclamp_mem

private theorem kclamp_eq (B : KKTFamily d) (h : ℝ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 4) : B.kclamp h u = B.JpTildeH h u := by
  rw [kclamp, max_eq_left hu.1, min_eq_left hu.2]

/-- **The Fubini exchange between the two mixed rectangles.**  The paper writes the mixed
part as `2∬_{𝒩_ρ×𝒯_ρ}`, using the symmetry of the kernel and Fubini's theorem; formally the two orders of
integration have to be identified, and that is this lemma.  The integrand is replaced by the
clamped kernel, which is bounded and continuous on all of `ℝ²`, so the product-integrability
hypothesis of `integral_integral_swap` is immediate. -/
private theorem integral_swap_window_tail (hd : 2 ≤ d) (B : KKTFamily d) {h ρ C : ℝ}
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0)
    (hbnd : ∀ z ∈ Set.Icc (0 : ℝ) 4, |B.JpTildeH h z| ≤ C) :
    ∫ x in centralWindow d ρ,
        (∫ y in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.JpTildeH h (x * y) ∂ν) ∂ν
      = ∫ y in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ,
        (∫ x in centralWindow d ρ, B.JpTildeH h (x * y) ∂ν) ∂ν := by
  have hf1 : IsFiniteMeasure (ν.restrict (centralWindow d ρ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_lt_top ν _⟩
  have hf2 : IsFiniteMeasure (ν.restrict (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_lt_top ν _⟩
  have hcc : Continuous (Function.uncurry (fun x y : ℝ => B.kclamp h (x * y))) := by
    have hc : Continuous (fun p : ℝ × ℝ => B.kclamp h (p.1 * p.2)) :=
      (continuous_kclamp hd B h).comp (continuous_fst.mul continuous_snd)
    exact hc
  have hbk : ∀ u : ℝ, ‖B.kclamp h u‖ ≤ C := by
    intro u
    rw [Real.norm_eq_abs, kclamp]
    exact hbnd _ (kclamp_mem u)
  have hintg : Integrable (Function.uncurry (fun x y : ℝ => B.kclamp h (x * y)))
      ((ν.restrict (centralWindow d ρ)).prod
        (ν.restrict (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ))) :=
    Integrable.mono' (integrable_const C) hcc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hbk _)
  have hswap := integral_integral_swap hintg
  have hprod : ∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2,
      x * y ∈ Set.Icc (0 : ℝ) 4 := by
    intro x hx y hy
    exact ⟨mul_nonneg hx.1 hy.1, by nlinarith [hx.1, hx.2, hy.1, hy.2]⟩
  have hL : ∫ x in centralWindow d ρ,
      (∫ y in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.kclamp h (x * y) ∂ν) ∂ν
      = ∫ x in centralWindow d ρ,
      (∫ y in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.JpTildeH h (x * y) ∂ν) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Icc_of_distribution (restrict_distribution_compl hν (centralWindow d ρ))]
      with x hx
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Icc_of_distribution
      (restrict_distribution_compl hν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ))] with y hy
    exact kclamp_eq B h (hprod x hx y hy)
  have hR : ∫ y in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ,
      (∫ x in centralWindow d ρ, B.kclamp h (x * y) ∂ν) ∂ν
      = ∫ y in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ,
      (∫ x in centralWindow d ρ, B.JpTildeH h (x * y) ∂ν) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Icc_of_distribution
      (restrict_distribution_compl hν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ))] with y hy
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Icc_of_distribution (restrict_distribution_compl hν (centralWindow d ρ))]
      with x hx
    exact kclamp_eq B h (hprod x hx y hy)
  rw [← hL, ← hR]
  exact hswap

/-- **The tail slice** `x ↦ ∫_{T_ρ}K_h(x,y)dν(y)`, the inner integral of the *other* mixed
rectangle. -/
noncomputable def tailSlice (B : KKTFamily d) (h ρ : ℝ) (ν : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ y in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.JpTildeH h (x * y) ∂ν

/-- **The two mixed rectangles agree.**  `∫_{𝓝_ρ}(∫_{T_ρ}K_hdν)dσ = ∫_{T_ρ}(∫_{𝓝_ρ}K_hdσ)dν`:
the `ν_h`-halves are the same cross-kernel integral over the tail, and the `ν⊗ν` halves are
exchanged by `integral_swap_window_tail`.  This is the formal content of the paper's factor
`2` in `2∬_{𝒩_ρ×𝒯_ρ}K_hdσdσ` (here over `𝓝_ρ × T_ρ`). -/
theorem sigmaInt_tailSlice_eq_mixedQuad (hd : 2 ≤ d) (B : KKTFamily d) {h ρ C : ℝ}
    (hh : |h| < B.h₀) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) (hs : B.sVal h ∈ centralWindow d ρ)
    (ht : B.tVal h ∈ centralWindow d ρ)
    (hbnd : ∀ z ∈ Set.Icc (0 : ℝ) 4, |B.JpTildeH h z| ≤ C) :
    B.sigmaInt h ν (centralWindow d ρ) (B.tailSlice h ρ ν) = B.mixedQuad h ρ ν := by
  have hsIcc : B.sVal h ∈ Set.Icc (0 : ℝ) 2 :=
    ⟨(sVal_pos hh).le, by linarith [sVal_lt_one hh]⟩
  have htIcc : B.tVal h ∈ Set.Icc (0 : ℝ) 2 :=
    ⟨(tVal_pos hh).le, by linarith [tVal_lt_one hh]⟩
  have iOn : ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc (0 : ℝ) 2) →
      IntegrableOn f (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ) ν := fun f hf =>
    (integrableOn_of_continuousOn hν hf isCompact_Icc).mono_set Set.sdiff_subset
  have is := iOn _ (continuousOn_distributionIntegrand hd B h hsIcc.1 hsIcc.2)
  have it := iOn _ (continuousOn_distributionIntegrand hd B h htIcc.1 htIcc.2)
  have icross := iOn _ (continuousOn_crossK hd B hh)
  have iinner := iOn _ (continuousOn_innerIntegral
    (restrict_distribution_compl hν (centralWindow d ρ)) (continuousOn_JpTildeH hd B h))
  have hatoms : B.alph h * B.tailSlice h ρ ν (B.sVal h)
      + (1 - B.alph h) * B.tailSlice h ρ ν (B.tVal h)
      = ∫ y in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.crossK h y ∂ν := by
    rw [tailSlice, tailSlice, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (is.const_mul _) (it.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    rw [crossK, mul_comm y (B.sVal h), mul_comm y (B.tVal h)]
  have hmix : B.mixedQuad h ρ ν
      = (∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ,
          (∫ y in centralWindow d ρ, B.JpTildeH h (x * y) ∂ν) ∂ν)
        - ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.crossK h x ∂ν := by
    rw [mixedQuad, ← integral_sub iinner icross]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [innerSigma, sigmaInt_of_atoms_mem B hh ν hs ht]
    rfl
  have hcomm : ∫ y in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ,
      (∫ x in centralWindow d ρ, B.JpTildeH h (x * y) ∂ν) ∂ν
      = ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ,
      (∫ y in centralWindow d ρ, B.JpTildeH h (x * y) ∂ν) ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    show B.JpTildeH h (w * z) = B.JpTildeH h (z * w)
    rw [mul_comm]
  have hleft : ∫ x in centralWindow d ρ, B.tailSlice h ρ ν x ∂ν
      = ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ,
        (∫ y in centralWindow d ρ, B.JpTildeH h (x * y) ∂ν) ∂ν := by
    simp only [tailSlice]
    rw [integral_swap_window_tail hd B (ρ := ρ) hν hbnd, hcomm]
  rw [sigmaInt_of_atoms_mem B hh ν hs ht, hatoms, hleft, hmix]

/-- **The three-way split of the σ-quadratic form**:

`∬K_hdσdσ = ∬_{𝓝_ρ²}K_hdσdσ + 2∬_{𝓝_ρ×T_ρ}K_hdσdσ + ∬_{T_ρ²}K_hdσdσ`.

The outer and inner σ-integrals are split with `sigmaInt_split`, the tail halves are
`ν`-integrals by `sigmaInt_tail`, and the two mixed rectangles are identified by
`sigmaInt_tailSlice_eq_mixedQuad`. -/
theorem sigmaQuad_split (hd : 2 ≤ d) (B : KKTFamily d) {h ρ C : ℝ} (hh : |h| < B.h₀)
    (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ)
    (hbnd : ∀ z ∈ Set.Icc (0 : ℝ) 4, |B.JpTildeH h z| ≤ C) :
    B.sigmaQuad h ν
      = B.centralQuad h ρ ν + 2 * B.mixedQuad h ρ ν + B.tailQuad h ρ ν := by
  have hsIcc : B.sVal h ∈ Set.Icc (0 : ℝ) 2 :=
    ⟨(sVal_pos hh).le, by linarith [sVal_lt_one hh]⟩
  have htIcc : B.tVal h ∈ Set.Icc (0 : ℝ) 2 :=
    ⟨(tVal_pos hh).le, by linarith [tVal_lt_one hh]⟩
  have hcI : ContinuousOn (B.innerSigma h ρ ν) (Set.Icc 0 2) :=
    continuousOn_innerSigma hd B hh hρu hρ1 hν hs ht
  have hcT : ContinuousOn (B.tailSlice h ρ ν) (Set.Icc 0 2) :=
    continuousOn_innerIntegral
      (restrict_distribution_compl hν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ))
      (continuousOn_JpTildeH hd B h)
  have hfull : ∀ x ∈ Set.Icc (0 : ℝ) 2,
      B.sigmaInt h ν (Set.Icc 0 2) (fun y => B.JpTildeH h (x * y))
        = B.innerSigma h ρ ν x + B.tailSlice h ρ ν x := by
    intro x hx
    rw [sigmaInt_split B hh hν (continuousOn_distributionIntegrand hd B h hx.1 hx.2) ρ,
      sigmaInt_tail B ν _ hs ht]
    rfl
  have hiI : IntegrableOn (B.innerSigma h ρ ν) (Set.Icc (0 : ℝ) 2) ν :=
    integrableOn_of_continuousOn hν hcI isCompact_Icc
  have hiT : IntegrableOn (B.tailSlice h ρ ν) (Set.Icc (0 : ℝ) 2) ν :=
    integrableOn_of_continuousOn hν hcT isCompact_Icc
  have hsumI := integral_Icc_split hν hcI (measurableSet_centralWindow d ρ)
  have hsumT := integral_Icc_split hν hcT (measurableSet_centralWindow d ρ)
  have hcen : B.centralQuad h ρ ν
      = (∫ x in centralWindow d ρ, B.innerSigma h ρ ν x ∂ν)
        - (B.alph h * B.innerSigma h ρ ν (B.sVal h)
          + (1 - B.alph h) * B.innerSigma h ρ ν (B.tVal h)) := by
    rw [centralQuad]
    exact sigmaInt_of_atoms_mem B hh ν hs ht _
  have hM1 : B.mixedQuad h ρ ν
      = (∫ x in centralWindow d ρ, B.tailSlice h ρ ν x ∂ν)
        - (B.alph h * B.tailSlice h ρ ν (B.sVal h)
          + (1 - B.alph h) * B.tailSlice h ρ ν (B.tVal h)) := by
    rw [← sigmaInt_tailSlice_eq_mixedQuad hd B hh hν hs ht hbnd]
    exact sigmaInt_of_atoms_mem B hh ν hs ht _
  have hM2 : B.mixedQuad h ρ ν
      = ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.innerSigma h ρ ν x ∂ν := rfl
  have hTQ : B.tailQuad h ρ ν
      = ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.tailSlice h ρ ν x ∂ν := rfl
  have h2m : 2 * B.mixedQuad h ρ ν
      = ((∫ x in centralWindow d ρ, B.tailSlice h ρ ν x ∂ν)
          - (B.alph h * B.tailSlice h ρ ν (B.sVal h)
            + (1 - B.alph h) * B.tailSlice h ρ ν (B.tVal h)))
        + ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.innerSigma h ρ ν x ∂ν := by
    linarith [hM1, hM2]
  rw [sigmaQuad_eq_sigmaInt hd B hh hν, sigmaInt_of_atoms_mem B hh ν hsIcc htIcc,
    setIntegral_congr_fun measurableSet_Icc (fun x hx => hfull x hx),
    integral_add hiI hiT, hfull _ hsIcc, hfull _ htIcc, hcen, h2m, hTQ, hsumI, hsumT]
  ring

/-! ## The dual split, and the assembled gap bound -/

/-- **The quartic first-variation bound, transferred to the continued potential and to the window.**
`exists_firstVariation_lower` is stated for `Ψ_h`; `PsiT_eq_Psi` transfers it to `Ψ̃_h`, whose
hypotheses hold on `𝓝_ρ` because two window points multiply into `[0,1]`.  This is the central
bound `Ψ_h ≥ aQ_h²` of `lem:first-variation-bound`, with `a = d³/24`, which gives
`∫Ψ_hdν ≥ aA_ρ + ∫_{T_ρ}Ψ_hdν` in the proof of `lem:auxiliary-lagrangian-bound`. -/
theorem exists_firstVariation_lower_PsiT (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ w : ℝ, 0 < w ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → |h| < B.h₀ →
      ∀ ρ : ℝ, ρ ≤ w → ρ ≤ uStar d / 2 → ρ ≤ (1 - uStar d) / 2 →
        ∀ x ∈ centralWindow d ρ, (d : ℝ) ^ 3 / 24 * B.Qh h x ^ 2 ≤ B.PsiT h x := by
  obtain ⟨w, hw, δ, hδ, hlow⟩ := exists_firstVariation_lower hd B
  refine ⟨w, hw, δ, hδ, ?_⟩
  intro h hh0 hhδ hhb ρ hρw hρu hρ1 x hx
  have hu0 : 0 < uStar d := uStar_pos hd
  have hxb := window_bounds hd hρu hρ1 hx
  have hx0 : (0 : ℝ) ≤ x := by linarith [hxb.1]
  have hs0 : (0 : ℝ) < B.sVal h := sVal_pos hhb
  have ht0 : (0 : ℝ) < B.tVal h := tVal_pos hhb
  have hs1 : B.sVal h < 1 := sVal_lt_one hhb
  have ht1 : B.tVal h < 1 := tVal_lt_one hhb
  have hxmem : x ∈ Set.Icc (uStar d - w) (uStar d + w) := by
    have hx' : x ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  rw [PsiT_eq_Psi hd hhb (mul_nonneg hx0 hs0.le) (by nlinarith [hxb.2])
    (mul_nonneg hx0 ht0.le) (by nlinarith [hxb.2])]
  exact hlow h hh0 hhδ hhb x hxmem

/-- **The assembled gap bound**, the refined form of `eq:auxiliary-lagrangian-bound`
with the mixed and tail
terms still exact.  Writing
`A_ρ = ∫_{𝓝_ρ}Q_h²dν`, `ε_ρ = ν(T_ρ)` and `Δ = Δ_h(ν)`,

`𝒥_h(ν) - 𝒥_h(ν_h) - η_hΔ ≥ (d³/32)A_ρ + ∫_{T_ρ}Ψ̃_hdν
    - C_ρ{(1+2^d)ε_ρ + |Δ|}² + 2∬_{𝓝_ρ×T_ρ}K_hdσdσ + ∬_{T_ρ²}K_hdσdσ`.

Four inputs are combined: the exact expansion following `eq:first-variation`
(`distributionJ_sub_eq`), the split of `∫Ψ_hdν` over `𝓝_ρ ⊔ T_ρ` with the first-variation bound
`a = d³/24` of `lem:first-variation-bound`, the three-way split `sigmaQuad_split`, and the central estimate
`centralQuad_lower`.  The coefficient is `a - δ - a/8 ≥ d³/32` once `δ ≤ a/8`.

**What remains** to reach the refined form verbatim is only the absorption of
the mixed and tail terms into `ζ(h)ε_ρ`, for which `exists_abs_mixedQuad_le` and
`exists_abs_tailQuad_le` supply the two estimates; see the module docstring. -/
theorem distributionGap_lower (hd : 2 ≤ d) (B : KKTFamily d) {h ρ δ Cu Cp C : ℝ}
    (hh : |h| < B.h₀) (hpos : 0 < h) (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ)
    (hδ : 0 ≤ δ) (hδ8 : δ ≤ (d : ℝ) ^ 3 / 192) (hCu : 0 ≤ Cu) (hCp : 0 ≤ Cp)
    (h00 : |B.kp00 h| ≤ Cp) (hd0 : |B.kpd0 h| ≤ Cp) (h0d : |B.kp0d h| ≤ Cp)
    (hddc : |B.kpdd h| ≤ Cp)
    (hu0 : ∀ x ∈ centralWindow d ρ, |B.u0 h x| ≤ Cu)
    (hud : ∀ x ∈ centralWindow d ρ, |B.ud h x| ≤ Cu)
    (hCorner : ∀ x ∈ centralWindow d ρ, ∀ y ∈ centralWindow d ρ,
      |B.kernelTheta h x y - (d : ℝ) ^ 3 / 4| ≤ δ)
    (hTW : ∀ x ∈ centralWindow d ρ, (d : ℝ) ^ 3 / 24 * B.Qh h x ^ 2 ≤ B.PsiT h x)
    (hbnd : ∀ z ∈ Set.Icc (0 : ℝ) 4, |B.JpTildeH h z| ≤ C) :
    (d : ℝ) ^ 3 / 32 * (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
        + (∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.PsiT h x ∂ν)
        - (Cp + 192 * Cu ^ 2 / (d : ℝ) ^ 3)
          * ((1 + 2 ^ d) * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
              + |(∫ x, x ^ d ∂ν) - B.qVal h|) ^ 2
        + (2 * B.mixedQuad h ρ ν + B.tailQuad h ρ ν)
      ≤ B.distributionJ h ν - B.distributionJ h (B.distributionMeasure h)
          - B.etaVal h * ((∫ x, x ^ d ∂ν) - B.qVal h) := by
  have hmN := measurableSet_centralWindow d ρ
  have hcpt := isCompact_centralWindow d ρ
  have hA0 : (0 : ℝ) ≤ ∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν :=
    setIntegral_nonneg hmN fun x _ => sq_nonneg _
  have hcQ : Continuous (fun x : ℝ => B.Qh h x ^ 2) := by
    have hc : Continuous (fun x : ℝ => ((x - B.sVal h) * (x - B.tVal h)) ^ 2) := by fun_prop
    exact hc
  have iQ : IntegrableOn (fun x : ℝ => (d : ℝ) ^ 3 / 24 * B.Qh h x ^ 2)
      (centralWindow d ρ) ν :=
    (integrableOn_of_continuousOn hν hcQ.continuousOn hcpt).const_mul _
  have iP : IntegrableOn (B.PsiT h) (centralWindow d ρ) ν :=
    integrableOn_of_continuousOn hν (continuousOn_PsiT hd B hh) hcpt
  have hPsiN : (d : ℝ) ^ 3 / 24 * (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
      ≤ ∫ x in centralWindow d ρ, B.PsiT h x ∂ν := by
    have hmono := setIntegral_mono_on iQ iP hmN hTW
    rwa [integral_const_mul] at hmono
  have hPsiSplit : ∫ x, B.PsiT h x ∂ν
      = (∫ x in centralWindow d ρ, B.PsiT h x ∂ν)
        + ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.PsiT h x ∂ν := by
    have hsp := integral_Icc_split hν (continuousOn_PsiT hd B hh) hmN
    rwa [restrict_Icc_self hν] at hsp
  have hdec := distributionJ_sub_eq hd B hh ν hν
  have hcen := centralQuad_lower hd B hh hpos hρu hρ1 hν hs ht hδ hCu hCp h00 hd0 h0d hddc
    hu0 hud hCorner
  have hsp := sigmaQuad_split hd B hh hρu hρ1 hν hs ht hbnd
  have hprod : (0 : ℝ) ≤ ((d : ℝ) ^ 3 / 192 - δ)
      * ∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν :=
    mul_nonneg (by linarith) hA0
  linarith [hdec, hPsiN, hPsiSplit, hcen, hsp, hprod]

/-- **The gap bound with the mixed and tail terms replaced by their bounds.**  Feeding
`exists_abs_mixedQuad_le` and `exists_abs_tailQuad_le` into `distributionGap_lower` gives the
inequality that the Young absorption of `SingularEndpoint/AuxiliaryLagrangian/DistributionAbsorption.lean` acts on:

`𝒥_h(ν) - 𝒥_h(ν_h) - η_hΔ ≥ (d³/32)A_ρ + ∫_{T_ρ}Ψ̃_hdν - C_ρ{(1+2^d)ε_ρ + |Δ|}²
  - 2C_m - C_t`,

where `C_m` bounds `|∬_{𝓝_ρ×T_ρ}K_hdσdσ|` and `C_t` bounds `|∬_{T_ρ²}K_hdσdσ|`, with
`C_m = C_ρL_hε_ρ(ε_ρ + |Δ| + A_ρ^{3/16})` and `C_t = Cε_ρ²`.  The paper's corresponding
display has the mixed loss `C_dh^{1/2}ν(𝒯_ρ) + C_dν(𝒯_ρ)²` instead, which needs no Young step. -/
theorem distributionGap_lower_of_bounds (hd : 2 ≤ d) (B : KKTFamily d)
    {h ρ δ Cu Cp C Cm Ct : ℝ} (hh : |h| < B.h₀) (hpos : 0 < h) (hρu : ρ ≤ uStar d / 2)
    (hρ1 : ρ ≤ (1 - uStar d) / 2) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) (hs : B.sVal h ∈ centralWindow d ρ)
    (ht : B.tVal h ∈ centralWindow d ρ)
    (hδ : 0 ≤ δ) (hδ8 : δ ≤ (d : ℝ) ^ 3 / 192) (hCu : 0 ≤ Cu) (hCp : 0 ≤ Cp)
    (h00 : |B.kp00 h| ≤ Cp) (hd0 : |B.kpd0 h| ≤ Cp) (h0d : |B.kp0d h| ≤ Cp)
    (hddc : |B.kpdd h| ≤ Cp)
    (hu0 : ∀ x ∈ centralWindow d ρ, |B.u0 h x| ≤ Cu)
    (hud : ∀ x ∈ centralWindow d ρ, |B.ud h x| ≤ Cu)
    (hCorner : ∀ x ∈ centralWindow d ρ, ∀ y ∈ centralWindow d ρ,
      |B.kernelTheta h x y - (d : ℝ) ^ 3 / 4| ≤ δ)
    (hTW : ∀ x ∈ centralWindow d ρ, (d : ℝ) ^ 3 / 24 * B.Qh h x ^ 2 ≤ B.PsiT h x)
    (hbnd : ∀ z ∈ Set.Icc (0 : ℝ) 4, |B.JpTildeH h z| ≤ C)
    (hmixb : |B.mixedQuad h ρ ν| ≤ Cm) (htailb : |B.tailQuad h ρ ν| ≤ Ct) :
    (d : ℝ) ^ 3 / 32 * (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
        + (∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.PsiT h x ∂ν)
        - (Cp + 192 * Cu ^ 2 / (d : ℝ) ^ 3)
          * ((1 + 2 ^ d) * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
              + |(∫ x, x ^ d ∂ν) - B.qVal h|) ^ 2
        - (2 * Cm + Ct)
      ≤ B.distributionJ h ν - B.distributionJ h (B.distributionMeasure h)
          - B.etaVal h * ((∫ x, x ^ d ∂ν) - B.qVal h) := by
  have hmain := distributionGap_lower hd B hh hpos hρu hρ1 hν hs ht hδ hδ8 hCu hCp h00 hd0 h0d
    hddc hu0 hud hCorner hTW hbnd
  have hm := neg_abs_le (B.mixedQuad h ρ ν)
  have hmu := le_abs_self (B.mixedQuad h ρ ν)
  have hti := neg_abs_le (B.tailQuad h ρ ν)
  have htu := le_abs_self (B.tailQuad h ρ ν)
  linarith [hmain, hm, hmu, hti, htu, hmixb, htailb]
