import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.DistributionLocal

/-!
# The exact quadratic expansion of the law gap (Section 5)

The expansion following `eq:first-variation`, the algebraic
core of the quantitative half of `lem:auxiliary-lagrangian-bound`.  With the law
kernel `K_h(x,y) = J̃_{p_h}(xy)`, the
two-atom candidate `ν_h`, `σ = ν - ν_h` and `η_h = 2γ_hq_h/d`, the identity is

`𝒥_h(ν) - 𝒥_h(ν_h) = ∫Ψ_h dν + η_hΔ_h(ν) + ∬K_h dσdσ`,

and `KKTFamily.distributionJ_sub_eq` is exactly that identity.  It is the paper's display
following `eq:first-variation` (at `ξ = ν`) with the `μ_h`-terms cancelled from both sides —
the graph-free form used throughout the `SingularEndpoint` layer — and with
`∫Ψ_h dσ = ∫Ψ_h dν`, which the paper records after `lem:first-variation-bound`.  Nothing here
is an estimate.  The whole content is a four-line computation:

* `K_h` is symmetric, so `𝒥_h(ν) - 𝒥_h(ν_h) = 2∬K_h dσdν_h + ∬K_h dσdσ`;
* the inner integral against the two-atom `ν_h` is explicit,
  `∫K_h(x,y) dν_h(y) = α_h J̃_{p_h}(x s_h) + (1-α_h) J̃_{p_h}(x t_h) =: 𝒦_h(x)`
  (`KKTFamily.crossK`, `KKTFamily.integral_distributionMeasure_kernel`), and
  `2𝒦_h = Ψ_h + η_h x^d + κ_h` **by the definition** of `KKTFamily.PsiT`
  (`KKTFamily.two_mul_crossK`);
* `∫dσ = 0` kills `κ_h` and `∫x^d dσ = Δ_h(ν)`;
* `∫Ψ_h dν_h = 0` because `Ψ_h` vanishes at both atoms
  (`KKTFamily.PsiT_sVal`, `KKTFamily.PsiT_tVal`), which is
  `KKTFamily.Psi_sVal`/`.Psi_tVal` transferred through `PsiT_eq_Psi`: its hypotheses
  hold at `x = s_h` and at `x = t_h` because `factor_mem` puts `s_h, t_h` in `(0,1)`, so the
  three products `s_h², s_ht_h, t_h²` lie in `[0,1]`.

The only analytic input is integrability, and it is the cheapest possible one: `Ψ_h` and
`x ↦ x^d` are continuous on the law interval `[0,2]`, so `integrable_of_continuousOn`
(`SingularEndpoint/AuxiliaryLagrangian/DistributionVariance.lean`) applies to any finite measure carried by `[0,2]`.

## No signed measures

As in `SingularEndpoint/AuxiliaryLagrangian/DistributionMeasure.lean`, the paper's `σ = ν - ν_h` is never formed as a
`MeasureTheory.SignedMeasure`: every integral against it is "integral against `ν` minus integral
against `ν_h`".  Accordingly `KKTFamily.sigmaQuad` *defines* `∬K_h dσdσ` by its
expansion, and `KKTFamily.sigmaQuad_eq` records that this is the bilinear expansion
`∬K_h dνdν - 2∬K_h dν_h dν + ∬K_h dν_h dν_h`.  Both integrals converge separately —
each integrand is continuous on the compact `[0,2]` and both measures are finite — so this is
the same statement, not a weakening.

## The `σ`-integral toolkit

The quantitative estimate that consumes this expansion splits
`∬K_h dσdσ` over the central square `𝓝_ρ²`, the mixed rectangles and the tail square
`T_ρ = [0,2] ∖ 𝓝_ρ`.  `KKTFamily.sigmaInt` is the one-variable σ-integral over a set,
with the four facts that split uses: additivity over `[0,2] = 𝓝_ρ ⊔ T_ρ`
(`sigmaInt_split`), the disappearance of `ν_h` from the tail once both atoms are in the
window (`sigmaInt_tail`, whose hypothesis is supplied by `exists_atoms_mem_centralWindow`),
`∫1 dσ = 0` (`sigmaInt_one`) and the crude sup bound (`abs_sigmaInt_le`).

## Contents

* `KKTFamily.crossK` — the cross kernel `𝒦_h`, with `integral_distributionMeasure_kernel`,
  `two_mul_crossK` and `continuousOn_crossK`;
* `KKTFamily.continuousOn_PsiT` — `Ψ_h` is continuous on `[0,2]`;
* `KKTFamily.PsiT_sVal`, `.PsiT_tVal`, `.integral_PsiT_distributionMeasure` — `Ψ_h` vanishes
  on the support of `ν_h`;
* `KKTFamily.distributionJ_distributionMeasure_eq_integral_crossK` and
  `KKTFamily.distributionJ_distributionMeasure` — `𝒥_h(ν_h)`, as a `𝒦_h`-integral and in closed
  form `(η_hq_h + κ_h)/2`;
* `KKTFamily.sigmaQuad`, `KKTFamily.sigmaQuad_eq` — the quadratic form `∬K_hdσdσ`;
* `KKTFamily.distributionJ_sub_eq` — **the expansion following `eq:first-variation`**;
* `KKTFamily.distributionMeasure_eq_zero_of_notMem`, `KKTFamily.sigmaInt`,
  `sigmaInt_split`, `sigmaInt_tail`, `sigmaInt_one`, `abs_sigmaInt_le` — the σ-integral
  toolkit;
* `KKTFamily.integral_Icc_split` — additivity over `[0,2] = A ⊔ ([0,2] ∖ A)`, shared
  with `SingularEndpoint/AuxiliaryLagrangian/DistributionQuant.lean`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

namespace KKTFamily

/-! ## The cross kernel -/

/-- **The cross kernel `𝒦_h(x) = ∫K_h(x,y)dν_h(y)`** of the proof of
`lem:auxiliary-lagrangian-bound`: the law kernel `K_h(x,y) = J̃_{p_h}(xy)` averaged in one
variable against the two-atom candidate law `ν_h`.  It is written out here rather than as
an integral because that average is explicit — `integral_distributionMeasure_kernel` — and because
`2𝒦_h` is the dual potential up to the two normalising terms (`two_mul_crossK`). -/
noncomputable def crossK (B : KKTFamily d) (h x : ℝ) : ℝ :=
  B.alph h * B.JpTildeH h (x * B.sVal h) + (1 - B.alph h) * B.JpTildeH h (x * B.tVal h)

/-- **The inner integral of the law kernel against `ν_h` is the cross kernel.**  This is
`integral_distributionMeasure` at `f = J̃_{p_h}(x·)`; no hypothesis on `x` is needed. -/
theorem integral_distributionMeasure_kernel (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    (x : ℝ) :
    ∫ y, B.JpTildeH h (x * y) ∂(B.distributionMeasure h) = B.crossK h x := by
  rw [crossK]
  exact integral_distributionMeasure B hh _

/-- **`2𝒦_h = Ψ_h + η_hx^d + κ_h`.**  Pure unfolding: this *is* the definition of
`KKTFamily.PsiT` (`eq:first-variation` through the continued entropy), read as a
statement about the cross kernel. -/
theorem two_mul_crossK (B : KKTFamily d) (h x : ℝ) :
    2 * B.crossK h x = B.PsiT h x + B.etaVal h * x ^ d + B.kappaVal h := by
  rw [crossK, PsiT]
  ring

/-- **The cross kernel is continuous on the law interval.**  Both atoms lie in `(0,1)`
(`factor_mem`), so `x ↦ x s_h` and `x ↦ x t_h` map `[0,2]` into `[0,4]`, where the
continuation lives. -/
theorem continuousOn_crossK (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) :
    ContinuousOn (B.crossK h) (Set.Icc 0 2) := by
  have hmaps : ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
      Set.MapsTo (fun x : ℝ => x * c) (Set.Icc (0 : ℝ) 2) (Set.Icc (0 : ℝ) 4) := by
    intro c hc0 hc1 x hx
    exact ⟨mul_nonneg hx.1 hc0, by nlinarith [hx.1, hx.2]⟩
  have hcs : ContinuousOn (fun x : ℝ => B.JpTildeH h (x * B.sVal h)) (Set.Icc 0 2) :=
    (continuousOn_JpTildeH hd B h).comp (continuous_id.mul continuous_const).continuousOn
      (hmaps _ (sVal_pos hh).le (sVal_lt_one hh).le)
  have hct : ContinuousOn (fun x : ℝ => B.JpTildeH h (x * B.tVal h)) (Set.Icc 0 2) :=
    (continuousOn_JpTildeH hd B h).comp (continuous_id.mul continuous_const).continuousOn
      (hmaps _ (tVal_pos hh).le (tVal_lt_one hh).le)
  have hc : ContinuousOn (fun x : ℝ => B.alph h * B.JpTildeH h (x * B.sVal h)
      + (1 - B.alph h) * B.JpTildeH h (x * B.tVal h)) (Set.Icc 0 2) :=
    (continuousOn_const.mul hcs).add (continuousOn_const.mul hct)
  exact hc

/-- **The dual potential is continuous on the law interval**, being `2𝒦_h` minus a
polynomial (`two_mul_crossK`).  This is what makes `Ψ_h` integrable against every finite
measure carried by `[0,2]`. -/
theorem continuousOn_PsiT (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) :
    ContinuousOn (B.PsiT h) (Set.Icc 0 2) := by
  have hc : ContinuousOn (fun x : ℝ => 2 * B.crossK h x - B.etaVal h * x ^ d - B.kappaVal h)
      (Set.Icc 0 2) :=
    ((continuousOn_const.mul (continuousOn_crossK hd B hh)).sub
      (continuousOn_const.mul (continuous_pow d).continuousOn)).sub continuousOn_const
  have heq : (fun x : ℝ => 2 * B.crossK h x - B.etaVal h * x ^ d - B.kappaVal h)
      = fun x : ℝ => B.PsiT h x := by
    funext x
    have h1 := two_mul_crossK B h x
    linarith
  rw [heq] at hc
  exact hc

/-! ## `Ψ_h` vanishes on the support of `ν_h` -/

/-- **`Ψ_h(s_h) = 0`**, the first value contact `KKTFamily.Psi_sVal` transferred to the
continued potential.  The transfer is legitimate because `PsiT_eq_Psi` needs only
`s_h², s_ht_h ∈ [0,1]`, which `factor_mem` gives through `sq_sVal_mem` and `cross_mem`. -/
theorem PsiT_sVal (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) :
    B.PsiT h (B.sVal h) = 0 := by
  have hss := sq_sVal_mem hh (B := B)
  have hst := cross_mem hh (B := B)
  have e1 : B.sVal h * B.sVal h = B.sVal h ^ 2 := by ring
  rw [PsiT_eq_Psi hd hh (by rw [e1]; exact hss.1) (by rw [e1]; exact hss.2) hst.1 hst.2,
    Psi_sVal]

/-- **`Ψ_h(t_h) = 0`**, the second value contact `KKTFamily.Psi_tVal` — block-weight
stationarity — transferred to the continued potential, as in `PsiT_sVal`. -/
theorem PsiT_tVal (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) :
    B.PsiT h (B.tVal h) = 0 := by
  have htt := sq_tVal_mem hh (B := B)
  have hst := cross_mem hh (B := B)
  have e1 : B.tVal h * B.tVal h = B.tVal h ^ 2 := by ring
  have e2 : B.tVal h * B.sVal h = B.sVal h * B.tVal h := mul_comm _ _
  rw [PsiT_eq_Psi hd hh (by rw [e2]; exact hst.1) (by rw [e2]; exact hst.2)
      (by rw [e1]; exact htt.1) (by rw [e1]; exact htt.2), Psi_tVal hd hh]

/-- **`∫Ψ_hdν_h = 0`**, the step of `paper/sections/singular_auxiliary_lagrangian.tex` reading
"`Ψ_h` vanishes at both points in the support of `ν_h`" (used there as
`∫Ψ_h dσ = ∫Ψ_h dξ`).  Immediate from `PsiT_sVal` and `PsiT_tVal`, since `ν_h` is carried by the
two atoms. -/
theorem integral_PsiT_distributionMeasure (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ}
    (hh : |h| < B.h₀) : ∫ x, B.PsiT h x ∂(B.distributionMeasure h) = 0 := by
  rw [integral_distributionMeasure B hh, PsiT_sVal hd B hh, PsiT_tVal hd B hh]
  ring

/-! ## The functional at the candidate -/

/-- **`𝒥_h(ν_h) = ∫𝒦_hdν_h`.**  The inner integral of the iterated form is the cross kernel
at every point (`integral_distributionMeasure_kernel`), so the outer integral is the same
computation once more. -/
theorem distributionJ_distributionMeasure_eq_integral_crossK (B : KKTFamily d) {h : ℝ}
    (hh : |h| < B.h₀) :
    B.distributionJ h (B.distributionMeasure h) = ∫ x, B.crossK h x ∂(B.distributionMeasure h) := by
  simp only [distributionJ, integral_distributionMeasure_kernel B hh]

/-- **`𝒥_h(ν_h) = (η_hq_h + κ_h)/2` in closed form.**  Both value contacts enter: `2𝒦_h` is
`Ψ_h + η_hx^d + κ_h`, `Ψ_h` vanishes at the two atoms, and the two-point average of `x^d` is
`q_h` by the definition of `KKTFamily.qVal`. -/
theorem distributionJ_distributionMeasure (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ}
    (hh : |h| < B.h₀) :
    B.distributionJ h (B.distributionMeasure h) = (B.etaVal h * B.qVal h + B.kappaVal h) / 2 := by
  have hs : B.crossK h (B.sVal h) = (B.etaVal h * B.sVal h ^ d + B.kappaVal h) / 2 := by
    have h1 := two_mul_crossK B h (B.sVal h)
    rw [PsiT_sVal hd B hh] at h1
    linarith
  have ht : B.crossK h (B.tVal h) = (B.etaVal h * B.tVal h ^ d + B.kappaVal h) / 2 := by
    have h1 := two_mul_crossK B h (B.tVal h)
    rw [PsiT_tVal hd B hh] at h1
    linarith
  rw [distributionJ_distributionMeasure_eq_integral_crossK B hh, integral_distributionMeasure B hh, hs, ht,
    qVal]
  ring

/-! ## The quadratic form in `σ` -/

/-- **The quadratic form `∬K_hdσdσ`** of `paper/sections/singular_auxiliary_lagrangian.tex`,
defined by its expansion rather than through a signed measure: with `σ = ν - ν_h` and
`∫K_h(x,·)dν_h = 𝒦_h` (`integral_distributionMeasure_kernel`),

`∬K_hdσdσ = 𝒥_h(ν) - 2∫𝒦_hdν + 𝒥_h(ν_h)`.

`sigmaQuad_eq` records that the right-hand side is the bilinear expansion
`∬K_hdνdν - 2∬K_hdν_hdν + ∬K_hdν_hdν_h`. -/
noncomputable def sigmaQuad (B : KKTFamily d) (h : ℝ) (ν : Measure ℝ) : ℝ :=
  B.distributionJ h ν - 2 * (∫ x, B.crossK h x ∂ν) + B.distributionJ h (B.distributionMeasure h)

/-- **`sigmaQuad` is `∬K_hdσdσ`**, written with the mixed term as an iterated integral of the
kernel itself.  Nothing but `integral_distributionMeasure_kernel` under the outer integral. -/
theorem sigmaQuad_eq (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) (ν : Measure ℝ) :
    B.sigmaQuad h ν
      = B.distributionJ h ν
        - 2 * ∫ x, (∫ y, B.JpTildeH h (x * y) ∂(B.distributionMeasure h)) ∂ν
        + B.distributionJ h (B.distributionMeasure h) := by
  simp only [sigmaQuad, integral_distributionMeasure_kernel B hh]

/-! ## The expansion following `eq:first-variation` -/

/-- **The expansion following `eq:first-variation`**, in graph-free form.  For every
probability measure `ν` carried by the law interval `[0,2]`,

`𝒥_h(ν) - 𝒥_h(ν_h) = ∫Ψ_hdν + η_hΔ_h(ν) + ∬K_hdσdσ`,   `Δ_h(ν) = m_d(ν) - q_h`.

The proof is the two identities `2∫𝒦_hdν = ∫Ψ_hdν + η_hm_d(ν) + κ_h` (from `two_mul_crossK`,
using `∫dν = 1`) and `2𝒥_h(ν_h) = η_hq_h + κ_h` (`distributionJ_distributionMeasure`); subtracting them
cancels `κ_h`, which is the paper's "`∫dσ = 0`", and leaves `η_hΔ_h(ν)`, the paper's
"`∫x^d dσ = Δ_h(ξ)`" term.  The vanishing of `Ψ_h` at both points in the support of `ν_h`
(the paper's `∫Ψ_h dσ = ∫Ψ_h dξ`) has already been used inside
`distributionJ_distributionMeasure`. -/
theorem distributionJ_sub_eq (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) :
    B.distributionJ h ν - B.distributionJ h (B.distributionMeasure h)
      = (∫ x, B.PsiT h x ∂ν) + B.etaVal h * ((∫ x, x ^ d ∂ν) - B.qVal h)
        + B.sigmaQuad h ν := by
  have iPsi : Integrable (fun x => B.PsiT h x) ν :=
    integrable_of_continuousOn hν (continuousOn_PsiT hd B hh)
  have ipow : Integrable (fun x : ℝ => x ^ d) ν :=
    integrable_of_continuousOn hν (by fun_prop)
  have hfun : (fun x => 2 * B.crossK h x)
      = fun x => B.PsiT h x + B.etaVal h * x ^ d + B.kappaVal h :=
    funext fun x => two_mul_crossK B h x
  have i1 : Integrable (fun x : ℝ => B.etaVal h * x ^ d) ν := ipow.const_mul _
  have i2 : Integrable (fun x : ℝ => B.PsiT h x + B.etaVal h * x ^ d) ν := iPsi.add i1
  have hcross : 2 * (∫ x, B.crossK h x ∂ν)
      = (∫ x, B.PsiT h x ∂ν) + B.etaVal h * (∫ x, x ^ d ∂ν) + B.kappaVal h := by
    calc 2 * (∫ x, B.crossK h x ∂ν)
        = ∫ x, 2 * B.crossK h x ∂ν := (integral_const_mul _ _).symm
      _ = ∫ x, (B.PsiT h x + B.etaVal h * x ^ d + B.kappaVal h) ∂ν := by rw [hfun]
      _ = (∫ x, B.PsiT h x ∂ν) + B.etaVal h * (∫ x, x ^ d ∂ν) + B.kappaVal h := by
          rw [integral_add i2 (integrable_const _), integral_add iPsi i1, integral_const_mul,
            integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hnuh := distributionJ_distributionMeasure hd B hh
  rw [sigmaQuad]
  linear_combination hcross - 2 * hnuh

/-! ## The `σ`-integral toolkit -/

/-- **A set missed by both atoms is `ν_h`-null.**  The two Dirac masses see only their own
atoms. -/
theorem distributionMeasure_eq_zero_of_notMem (B : KKTFamily d) (h : ℝ) {A : Set ℝ}
    (hs : B.sVal h ∉ A) (ht : B.tVal h ∉ A) : B.distributionMeasure h A = 0 := by
  simp [distributionMeasure, Measure.dirac_apply, Set.indicator_of_notMem hs,
    Set.indicator_of_notMem ht]

/-- **The one-variable `σ`-integral over a set**, `∫_Afdσ = ∫_Afdν - ∫_Afdν_h`.  As
everywhere in `SingularEndpoint/`, `σ = ν - ν_h` is a difference of two integrals and never a signed
measure. -/
noncomputable def sigmaInt (B : KKTFamily d) (h : ℝ) (ν : Measure ℝ) (A : Set ℝ)
    (f : ℝ → ℝ) : ℝ :=
  (∫ x in A, f x ∂ν) - ∫ x in A, f x ∂(B.distributionMeasure h)

/-- The additivity of a single set integral over the split `[0,2] = A ⊔ ([0,2] ∖ A)`, for a
measure carried by `[0,2]` and a continuous integrand. -/
theorem integral_Icc_split {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ (Set.Icc (0 : ℝ) 2)ᶜ = 0) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 2))
    {A : Set ℝ} (hA : MeasurableSet A) :
    ∫ x in Set.Icc (0 : ℝ) 2, f x ∂μ
      = (∫ x in A, f x ∂μ) + ∫ x in Set.Icc (0 : ℝ) 2 \ A, f x ∂μ := by
  have hint : IntegrableOn f (Set.Icc (0 : ℝ) 2) μ :=
    integrableOn_of_continuousOn hμ hf isCompact_Icc
  have hsplit := integral_inter_add_sdiff hA hint
  rw [restrict_Icc_inter hμ] at hsplit
  exact hsplit.symm

/-- **Additivity of the `σ`-integral over the central/tail split** `[0,2] = 𝓝_ρ ⊔ T_ρ`.  Both
measures are carried by `[0,2]`, so both halves split; the integrand is asked only to be
continuous on `[0,2]`. -/
theorem sigmaInt_split (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 2)) (ρ : ℝ) :
    B.sigmaInt h ν (Set.Icc (0 : ℝ) 2) f
      = B.sigmaInt h ν (centralWindow d ρ) f
        + B.sigmaInt h ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ) f := by
  have := isProbabilityMeasure_distributionMeasure B hh
  rw [sigmaInt, sigmaInt, sigmaInt,
    integral_Icc_split hν hf (measurableSet_centralWindow d ρ),
    integral_Icc_split (distributionMeasure_Icc_compl B hh) hf (measurableSet_centralWindow d ρ)]
  ring

/-- **On the tail the `σ`-integral is the `ν`-integral alone**, provided both atoms lie in the
central window — which is what `KKTFamily.exists_atoms_mem_centralWindow` supplies for
small `h`.  This is the step of `paper/sections/singular_auxiliary_lagrangian.tex` reading
"`σ = ν` on `𝒯_ρ`" (in the proof of `lem:auxiliary-lagrangian-bound`). -/
theorem sigmaInt_tail (B : KKTFamily d) {h ρ : ℝ} (ν : Measure ℝ) (f : ℝ → ℝ)
    (hs : B.sVal h ∈ centralWindow d ρ) (ht : B.tVal h ∈ centralWindow d ρ) :
    B.sigmaInt h ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ) f
      = ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, f x ∂ν := by
  have hz : B.distributionMeasure h (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ) = 0 :=
    distributionMeasure_eq_zero_of_notMem B h (fun hx => hx.2 hs) (fun hx => hx.2 ht)
  rw [sigmaInt, Measure.restrict_eq_zero.mpr hz, integral_zero_measure, sub_zero]

/-- **`∫1dσ = 0`** over the whole law interval: both measures are probability measures
carried by `[0,2]`.  This is the paper's `∫dσ = 0`, and the reason `κ_h` drops out of
the expansion following `eq:first-variation`. -/
theorem sigmaInt_one (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) :
    B.sigmaInt h ν (Set.Icc (0 : ℝ) 2) (fun _ => 1) = 0 := by
  have := isProbabilityMeasure_distributionMeasure B hh
  have hν1 : ν (Set.Icc (0 : ℝ) 2) = 1 := (prob_compl_eq_zero_iff measurableSet_Icc).mp hν
  have hh1 : B.distributionMeasure h (Set.Icc (0 : ℝ) 2) = 1 :=
    (prob_compl_eq_zero_iff measurableSet_Icc).mp (distributionMeasure_Icc_compl B hh)
  rw [sigmaInt, setIntegral_const, setIntegral_const, measureReal_def, measureReal_def, hν1,
    hh1]
  simp

/-- **The crude sup bound** `|∫_Afdσ| ≤ sup_A|f|·(ν(A) + ν_h(A))`, the estimate used on the
tail square `T_ρ²`, where no structure of the kernel is available.  No integrability
hypothesis is needed: `norm_setIntegral_le_of_norm_le_const` covers the non-integrable case
by returning `0`. -/
theorem abs_sigmaInt_le (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) {ν : Measure ℝ}
    [IsFiniteMeasure ν] {A : Set ℝ} {f : ℝ → ℝ} {M : ℝ} (hf : ∀ x ∈ A, |f x| ≤ M) :
    |B.sigmaInt h ν A f| ≤ M * ((ν A).toReal + (B.distributionMeasure h A).toReal) := by
  have := isProbabilityMeasure_distributionMeasure B hh
  have hb : ∀ x ∈ A, ‖f x‖ ≤ M := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact hf x hx
  have h1 : |∫ x in A, f x ∂ν| ≤ M * (ν A).toReal := by
    have hn := norm_setIntegral_le_of_norm_le_const (μ := ν) (measure_lt_top ν A) hb
    simpa [Real.norm_eq_abs, measureReal_def] using hn
  have h2 : |∫ x in A, f x ∂(B.distributionMeasure h)| ≤ M * (B.distributionMeasure h A).toReal := by
    have hn := norm_setIntegral_le_of_norm_le_const (μ := B.distributionMeasure h)
      (measure_lt_top _ A) hb
    simpa [Real.norm_eq_abs, measureReal_def] using hn
  have h3 := abs_sub_le_add (∫ x in A, f x ∂ν) (∫ x in A, f x ∂(B.distributionMeasure h))
  rw [sigmaInt]
  nlinarith [h1, h2, h3]

end KKTFamily

end SingularEndpoint

end UpperTailOptimizers
