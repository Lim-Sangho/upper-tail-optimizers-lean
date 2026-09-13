import UpperTailOptimizers.Bipodality.Concavity
import UpperTailOptimizers.KRRS.PsiExists
import UpperTailOptimizers.Graphon.ExternalInputs

/-!
# First-order efficiency of the entropy against the moment

With `ψ_* := ψ_d(ε, ζ_d(ε))`, the **gap function** `Γ(u) := ψ_*·𝒟_ε(u) - 𝒩_ε(u)` is nonnegative
on `[0,1]`: this is maximality of `ζ_d(ε)` for `ψ_d(ε,·)`.  Integrated against a graphon of
edge density `ε`, the linear parts of `𝒩_ε` and `𝒟_ε` drop out, giving the exact identity

  `∫∫ Γ(W) = ψ_*(∫∫W^d - ε^d) - 2(s(W) - S₀(ε))`,

and the generalized Hölder inequality `t(H,W) ≤ (∫∫W^d)^{m/d}` turns it into the first-order
efficiency bound of the bipodality draft (`kb:lem:efficiency`).
-/

namespace UpperTailOptimizers

open MeasureTheory Real

/-- `ψ_* = ψ_d(ε, ζ_d(ε))`, the maximal value of `ψ_d(ε,·)`. -/
noncomputable def psiStar (d : ℕ) (ε : ℝ) : ℝ := psiD d ε (zetaFun d ε)

/-- The gap function `Γ(u) = ψ_*·𝒟_ε(u) - 𝒩_ε(u)`. -/
noncomputable def gapFun (d : ℕ) (ε u : ℝ) : ℝ := psiStar d ε * Dfun d ε u - Nfun ε u

theorem continuous_gapFun (d : ℕ) (ε : ℝ) : Continuous (fun u => gapFun d ε u) := by
  unfold gapFun
  exact ((continuous_Dfun d ε).const_mul _).sub (continuous_Nfun ε)

theorem psiStar_neg {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1)
    (hεr : ε ≠ rStar d) : psiStar d ε < 0 := by
  obtain ⟨hz, hzne, -⟩ := zetaFun_crit hd hε.1 hε.2 hεr
  exact psiD_neg hd hε.1 hε.2 hz.1 hz.2 hzne

/-- **The gap function is nonnegative.** -/
theorem gapFun_nonneg {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1)
    {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) : 0 ≤ gapFun d ε u := by
  -- first on the open interval, then by continuity at the endpoints
  have hopen : ∀ w ∈ Set.Ioo (0:ℝ) 1, 0 ≤ gapFun d ε w := by
    intro w hw
    by_cases hwe : w = ε
    · subst hwe; unfold gapFun Dfun Nfun; ring_nf; rfl
    · have hD : 0 < Dfun d ε w := Dfun_pos hd hε.1 hw.1.le hwe
      have hmax : psiD d ε w ≤ psiStar d ε := zetaFun_isMax hd hε w hw hwe
      have hN : Nfun ε w = psiD d ε w * Dfun d ε w := by
        unfold psiD; field_simp
      unfold gapFun
      rw [hN]
      nlinarith [hmax, hD]
  have hcl : closure (Set.Ioo (0:ℝ) 1) = Set.Icc 0 1 := closure_Ioo zero_ne_one
  have hsub : Set.Icc (0:ℝ) 1 ⊆ {w | 0 ≤ gapFun d ε w} := by
    rw [← hcl]
    exact closure_minimal hopen (isClosed_le continuous_const (continuous_gapFun d ε))
  exact hsub hu

/-- **The efficiency identity**, for a graphon of edge density `ε`. -/
theorem Graphon.integral_gapFun_eq (W : Graphon) {d : ℕ} {ε : ℝ} (he : W.edgeDensity = ε) :
    ∫ z, gapFun d ε (W.toFun z.1 z.2) ∂gμ
      = psiStar d ε * (W.Wmoment d - ε ^ d) - 2 * (W.entropy - S0 ε) := by
  have hint : Integrable (fun z : ℝ × ℝ => W.toFun z.1 z.2) gμ :=
    W.integrable_comp (g := fun t => t) measurable_id continuousOn_id
  have hS0m : Measurable S0 := continuous_S0.measurable
  have hIS : Integrable (fun z : ℝ × ℝ => S0 (W.toFun z.1 z.2)) gμ :=
    W.integrable_comp hS0m continuous_S0.continuousOn
  have hIpow : Integrable (fun z : ℝ × ℝ => (W.toFun z.1 z.2) ^ d) gμ :=
    W.integrable_comp (g := fun t => t ^ d) (by fun_prop) (by fun_prop)
  have hmean : ∫ z, (W.toFun z.1 z.2 - ε) ∂gμ = 0 := by
    rw [integral_sub hint (integrable_const ε), integral_const]
    have h' : ∫ z, W.toFun z.1 z.2 ∂gμ = ε := he
    simp [h']
  have hlin : Integrable (fun z : ℝ × ℝ => W.toFun z.1 z.2 - ε) gμ := hint.sub (integrable_const ε)
  have hD : ∫ z, Dfun d ε (W.toFun z.1 z.2) ∂gμ = W.Wmoment d - ε ^ d := by
    unfold Dfun Graphon.Wmoment
    have hB : Integrable (fun z : ℝ × ℝ => (d : ℝ) * ε ^ (d - 1) * (W.toFun z.1 z.2 - ε)) gμ :=
      hlin.const_mul _
    have hA : Integrable (fun z : ℝ × ℝ => (W.toFun z.1 z.2) ^ d - ε ^ d) gμ :=
      hIpow.sub (integrable_const _)
    rw [integral_sub hA hB, integral_sub hIpow (integrable_const _),
      integral_const_mul, hmean, integral_const]
    simp
  have hN : ∫ z, Nfun ε (W.toFun z.1 z.2) ∂gμ = 2 * (W.entropy - S0 ε) := by
    unfold Nfun
    have hB : Integrable (fun z : ℝ × ℝ => dS0 ε * (W.toFun z.1 z.2 - ε)) gμ := hlin.const_mul _
    have hA : Integrable (fun z : ℝ × ℝ => S0 (W.toFun z.1 z.2) - S0 ε) gμ :=
      hIS.sub (integrable_const _)
    rw [integral_const_mul, integral_sub hA hB,
      integral_sub hIS (integrable_const _), integral_const_mul, hmean, integral_const,
      ← W.entropy_eq_integral_S0]
    simp
  have hIN : Integrable (fun z : ℝ × ℝ => Nfun ε (W.toFun z.1 z.2)) gμ :=
    W.integrable_comp (continuous_Nfun ε).measurable (continuous_Nfun ε).continuousOn
  have hID : Integrable (fun z : ℝ × ℝ => Dfun d ε (W.toFun z.1 z.2)) gμ :=
    W.integrable_comp (continuous_Dfun d ε).measurable (continuous_Dfun d ε).continuousOn
  unfold gapFun
  rw [integral_sub (hID.const_mul _) hIN, integral_const_mul, hD, hN]

/-- **First-order efficiency.**  For a `d`-regular `H` and a graphon with edge density `ε`,
`2(S₀(ε) - s(W)) ≥ |ψ_*|·(t(H,W)^{d/m} - ε^d) + ∫∫Γ(W)`. -/
theorem Graphon.efficiency_bound {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) (W : Graphon) {ε : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1)
    (hεr : ε ≠ rStar d) (he : W.edgeDensity = ε) :
    -psiStar d ε * (Real.rpow (W.tDensity H) ((d : ℝ) / (H.edgeFinset.card : ℝ)) - ε ^ d)
      + ∫ z, gapFun d ε (W.toFun z.1 z.2) ∂gμ ≤ 2 * (S0 ε - W.entropy) := by
  have hid := W.integral_gapFun_eq (d := d) he
  have hneg := psiStar_neg hd hε hεr
  have hholder := generalized_holder H hd hreg hm W
  have hmom0 : 0 ≤ W.Wmoment d := by
    unfold Graphon.Wmoment
    exact integral_nonneg (fun z => pow_nonneg (W.nonneg' z.1 z.2) d)
  have ht0 : 0 ≤ W.tDensity H := by
    unfold Graphon.tDensity
    refine integral_nonneg (fun x => Finset.prod_nonneg (fun e _ => ?_))
    induction e using Sym2.ind with
    | h a b => exact W.nonneg' (x a) (x b)
  have hmR : (0:ℝ) < (H.edgeFinset.card : ℝ) := by exact_mod_cast hm
  have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  -- `t^{d/m} ≤ ∫∫W^d`
  have hpow : Real.rpow (W.tDensity H) ((d : ℝ) / (H.edgeFinset.card : ℝ)) ≤ W.Wmoment d := by
    have h1 := Real.rpow_le_rpow ht0 hholder (le_of_lt (div_pos hdR hmR))
    have h2 : Real.rpow (Real.rpow (W.Wmoment d) ((H.edgeFinset.card : ℝ) / (d : ℝ)))
        ((d : ℝ) / (H.edgeFinset.card : ℝ)) = W.Wmoment d := by
      show (W.Wmoment d ^ ((H.edgeFinset.card : ℝ) / (d : ℝ))) ^ ((d : ℝ) / (H.edgeFinset.card : ℝ))
        = W.Wmoment d
      rw [← Real.rpow_mul hmom0,
        show (H.edgeFinset.card : ℝ) / (d : ℝ) * ((d : ℝ) / (H.edgeFinset.card : ℝ)) = 1 by
          field_simp,
        Real.rpow_one]
    exact h2 ▸ h1
  nlinarith [hid, hneg, hpow]

end UpperTailOptimizers
