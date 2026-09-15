import UpperTailOptimizers.SingularEndpoint.GraphonComparison.RowWindow
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.FactorStability
import UpperTailOptimizers.SingularEndpoint.Proof.BipodalTransport

/-!
# The rigidity extracted from a vanishing residual (Section 5, `paper/sections/singular.tex`)

This is the rigidity step of `sec:singular-proof`, the one that feeds the uniqueness
clause of `thm:singular-endpoint`: the paper's "Since `A_{h,ρ}(ν)=0` and `ν(𝒯_ρ)=0`, `ν` is
supported on `{s_h,t_h}`, and `Δ_h(ν)=0` implies `ν=α_hδ_{s_h}+(1-α_h)δ_{t_h}`.  Moreover,
`E≡0` implies that `W=f⊗f`", read on `[0,1]` rather than on the law interval.

`singular_endpoint_endgame` returns `Δ = 0` and `R = 0` alongside `g = 0`, where

`R = ‖E‖₂² + ∫_{G_ρ} Q_h(f)² + |G_ρᶜ|`,

with `G_ρ = {x : f(x) ∈ 𝓝_ρ}` for the closed window `𝓝_ρ = [u_* - ρ, u_* + ρ]`; the last two
summands are the Lean counterparts of the paper's `A_{h,ρ}(ν)` and `ν(𝒯_ρ)`.

All three summands are nonnegative, so `R = 0` forces each to vanish, and this file converts
that into structure:

* `‖E‖₂² = 0` gives `W = f ⊗ f` almost everywhere;
* `|G_ρᶜ| = 0` says almost every row is central, so the second summand's *restricted* vanishing
  is in fact global: `Q_h(f(x)) = 0` for a.e. `x`, i.e. `f(x) ∈ {s_h, t_h}` a.e.

Together these say `W` is almost everywhere the two-block value with vertex class
`A = [0,1] ∩ {f = s_h}` and levels `s_h², s_h t_h, t_h²`, which is exactly the hypothesis of
`exists_relabel_eq_bipodalGraphon`.  The identification `|A| = α_h` is the second half of this
file: it needs the further input `Δ = 0`, since `R = 0` alone fixes the two levels but not the
size of the class.

## Contents

* `FactorDecomp.ae_eq_rankOne_of_residSq_zero` — `‖E‖₂² = 0 ⟹ W = f ⊗ f` a.e.;
* `ae_mem_centralSet_of_tailMass_zero` — `|G_ρᶜ| = 0 ⟹` a.e. row is central;
* **`ae_twoValued_of_R_zero`** — `f ∈ {s_h, t_h}` a.e.;
* **`ae_bipodalValue_of_R_zero`** — `W` is a.e. the two-block value with class `[0,1] ∩ {f = s_h}`;
* `integral_of_ae_twoValued` — the integral of an a.e. two-valued function on `[0,1]`;
* **`measure_eq_alph_of_qVal_eq`** — `Δ = 0` pins the block size, `|A| = α_h`.
-/

namespace UpperTailOptimizers

open MeasureTheory

open scoped Classical

variable {d : ℕ} {W : Graphon}

namespace FactorDecomp

/-- **A vanishing residual makes `W` exactly rank one.**  `‖E‖₂² = ∫E²` with `E²  ≥ 0`
integrable, so `E = 0` almost everywhere. -/
theorem ae_eq_rankOne_of_residSq_zero (P : FactorDecomp d W) (hR : P.residSq = 0) :
    ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = P.f z.1 * P.f z.2 := by
  have hz : (fun z : ℝ × ℝ => P.resid z.1 z.2 ^ 2) =ᵐ[gμ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) P.integrable_resid_sq).mp hR
  filter_upwards [hz] with z hzz
  have hsq : P.resid z.1 z.2 ^ 2 = 0 := by simpa using hzz
  have h0 : P.resid z.1 z.2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  simpa [FactorDecomp.resid, sub_eq_zero] using h0

end FactorDecomp

/-- **No rare rows.**  `|G_ρᶜ| = 0` as a real number, together with finiteness of `unitμ`,
says the rare set is genuinely null, i.e. almost every row is central. -/
theorem ae_mem_centralSet_of_tailMass_zero (d : ℕ) (ρ : ℝ) {f : ℝ → ℝ}
    (hε : tailMass d ρ f = 0) : ∀ᵐ x ∂unitμ, x ∈ centralSet d ρ f := by
  have hfin : unitμ (centralSet d ρ f)ᶜ ≠ ⊤ := measure_ne_top _ _
  have hzero : unitμ (centralSet d ρ f)ᶜ = 0 := by
    rw [tailMass] at hε
    exact (ENNReal.toReal_eq_zero_iff _).mp hε |>.resolve_right hfin
  rw [ae_iff]
  exact measure_mono_null (fun x hx => hx) hzero

/-- **The factor is two-valued.**  `∫_{G_ρ}Q_h(f)² = 0` gives `Q_h(f) = 0` on the central rows,
and `|G_ρᶜ| = 0` says that is almost all of them.  `Q_h(u) = (u - s_h)(u - t_h)` vanishes only
at the two contacts. -/
theorem ae_twoValued_of_R_zero {f : ℝ → ℝ} (hf : Measurable f) (hfb : ∀ x, |f x| ≤ 2)
    (B : KKTFamily d) {h ρ : ℝ}
    (hQ : ∫ x in centralSet d ρ f, B.Qh h (f x) ^ 2 ∂unitμ = 0)
    (hε : tailMass d ρ f = 0) :
    ∀ᵐ x ∂unitμ, f x = B.sVal h ∨ f x = B.tVal h := by
  have hmeasC : MeasurableSet (centralSet d ρ f) := measurableSet_centralSet hf d ρ
  have hmQ : Measurable fun x => B.Qh h (f x) ^ 2 :=
    (((hf.sub measurable_const).mul (hf.sub measurable_const))).pow_const 2
  have hint : Integrable (fun x => B.Qh h (f x) ^ 2) (unitμ.restrict (centralSet d ρ f)) :=
    Integrable.of_bound hmQ.aestronglyMeasurable
      (((2 + |B.sVal h|) * (2 + |B.tVal h|)) ^ 2)
      (Filter.Eventually.of_forall fun x => by
        have habs : ∀ c : ℝ, |f x - c| ≤ 2 + |c| := fun c => by
          have h0 := abs_add_le (f x) (-c)
          rw [abs_neg, ← sub_eq_add_neg] at h0
          linarith [hfb x]
        have hs0 : (0 : ℝ) ≤ 2 + |B.sVal h| := by positivity
        rw [Real.norm_eq_abs, KKTFamily.Qh, abs_pow, abs_mul]
        exact pow_le_pow_left₀ (by positivity)
          (mul_le_mul (habs _) (habs _) (abs_nonneg _) hs0) 2)
  have hae : ∀ᵐ x ∂(unitμ.restrict (centralSet d ρ f)), B.Qh h (f x) ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint).mp hQ
  rw [ae_restrict_iff' hmeasC] at hae
  filter_upwards [hae, ae_mem_centralSet_of_tailMass_zero d ρ hε] with x hx hxc
  have hQ0 : B.Qh h (f x) = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hx hxc)
  rw [KKTFamily.Qh, mul_eq_zero] at hQ0
  rcases hQ0 with h1 | h2
  · exact Or.inl (by linarith [sub_eq_zero.mp h1])
  · exact Or.inr (by linarith [sub_eq_zero.mp h2])

/-- **`W` is almost everywhere two-block.**  Combining the three consequences of `R = 0`:
`W = f ⊗ f` a.e., and `f` takes only the values `s_h, t_h` a.e., so `W` takes only the three
values `s_h², s_h t_h, t_h²` according to the vertex class `A = [0,1] ∩ {f = s_h}`.

This is exactly the hypothesis of `exists_relabel_eq_bipodalGraphon`. -/
theorem ae_bipodalValue_of_R_zero (P : FactorDecomp d W) (B : KKTFamily d) {h ρ : ℝ}
    (hE : P.residSq = 0)
    (hQ : ∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ = 0)
    (hε : tailMass d ρ P.f = 0) :
    ∀ᵐ z ∂gμ, W.toFun z.1 z.2
      = bipodalValue (Set.Icc 0 1 ∩ {x | P.f x = B.sVal h})
          (B.sVal h ^ 2) (B.sVal h * B.tVal h) (B.tVal h ^ 2) z := by
  have hfb : ∀ x, |P.f x| ≤ 2 := fun x => by
    rw [abs_of_nonneg (P.f_nonneg x)]; exact P.f_bdd x
  have h2v := ae_twoValued_of_R_zero P.meas_f hfb B hQ hε
  have hIcc : ∀ᵐ x ∂unitμ, x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [unitμ, ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun x hx => hx
  have key : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → (P.f x = B.sVal h ∨ P.f x = B.tVal h) →
      P.f x = if x ∈ Set.Icc (0 : ℝ) 1 ∩ {y | P.f y = B.sVal h} then B.sVal h else B.tVal h := by
    intro x hx hv
    by_cases hm : x ∈ Set.Icc (0 : ℝ) 1 ∩ {y | P.f y = B.sVal h}
    · rw [if_pos hm]; exact hm.2
    · rw [if_neg hm]
      exact hv.resolve_left fun h1 => hm ⟨hx, h1⟩
  filter_upwards [P.ae_eq_rankOne_of_residSq_zero hE, ae_gμ_of_ae_unitμ h2v,
    ae_gμ_of_ae_unitμ hIcc] with z hz hv hi
  rw [hz, key z.1 hi.1 hv.1, key z.2 hi.2 hv.2, bipodalValue]
  split_ifs <;> ring

/-! ## The block size, from `Δ = 0` -/

/-- The integral of an almost-everywhere two-valued function on `[0,1]`. -/
theorem integral_of_ae_twoValued {g : ℝ → ℝ} {A : Set ℝ} (hA : MeasurableSet A) (s t : ℝ)
    (hae : ∀ᵐ x ∂unitμ, g x = if x ∈ A then s else t) :
    ∫ x, g x ∂unitμ = (unitμ A).toReal * s + (1 - (unitμ A).toReal) * t := by
  have hsplit : (fun x => if x ∈ A then s else t)
      = fun x => A.indicator (fun _ => s) x + Aᶜ.indicator (fun _ => t) x := by
    funext x
    by_cases hx : x ∈ A
    · rw [if_pos hx, Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx),
        add_zero]
    · rw [if_neg hx, Set.indicator_of_notMem hx, Set.indicator_of_mem (show x ∈ Aᶜ from hx),
        zero_add]
  have hi1 : Integrable (fun x => A.indicator (fun _ => s) x) unitμ :=
    (integrable_const s).indicator hA
  have hi2 : Integrable (fun x => Aᶜ.indicator (fun _ => t) x) unitμ :=
    (integrable_const t).indicator hA.compl
  have hcompl : (unitμ Aᶜ).toReal = 1 - (unitμ A).toReal := by
    rw [prob_compl_eq_one_sub hA]
    rw [ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  rw [integral_congr_ae hae, hsplit, integral_add hi1 hi2, integral_indicator_const _ hA,
    integral_indicator_const _ hA.compl, smul_eq_mul, smul_eq_mul, measureReal_def,
    measureReal_def, hcompl]

/-- **`Δ = 0` pins the block size.**  For a two-valued `f`, `q = ∫f^d = |A| s_h^d + (1-|A|)t_h^d`,
while `q_h = α_h s_h^d + (1-α_h)t_h^d`.  For `h > 0` we have `0 < s_h < t_h`, so `s_h^d ≠ t_h^d`
and the equation `q = q_h` has the single solution `|A| = α_h`. -/
theorem measure_eq_alph_of_qVal_eq (hd : 2 ≤ d) (P : FactorDecomp d W) (B : KKTFamily d)
    {h ρ : ℝ} (hhb : |h| < B.h₀) (hh0 : 0 < h)
    (hQ : ∫ x in centralSet d ρ P.f, B.Qh h (P.f x) ^ 2 ∂unitμ = 0)
    (hε : tailMass d ρ P.f = 0) (hΔ : P.qVal = B.qVal h) :
    (unitμ (Set.Icc 0 1 ∩ {x | P.f x = B.sVal h})).toReal = B.alph h := by
  obtain ⟨A, hAdef⟩ : ∃ S : Set ℝ, S = Set.Icc (0 : ℝ) 1 ∩ {x | P.f x = B.sVal h} := ⟨_, rfl⟩
  have hA : MeasurableSet A := by
    rw [hAdef]
    exact measurableSet_Icc.inter (P.meas_f (measurableSet_singleton _))
  have hfb : ∀ x, |P.f x| ≤ 2 := fun x => by
    rw [abs_of_nonneg (P.f_nonneg x)]; exact P.f_bdd x
  have h2v := ae_twoValued_of_R_zero P.meas_f hfb B hQ hε
  have hIcc : ∀ᵐ x ∂unitμ, x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [unitμ, ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun x hx => hx
  -- `f^d` is two-valued with values `s_h^d, t_h^d`
  have hae : ∀ᵐ x ∂unitμ, P.f x ^ d = if x ∈ A then B.sVal h ^ d else B.tVal h ^ d := by
    filter_upwards [h2v, hIcc] with x hv hx
    by_cases hm : x ∈ A
    · rw [if_pos hm]
      rw [hAdef] at hm
      rw [hm.2]
    · rw [if_neg hm]
      refine congrArg (· ^ d) (hv.resolve_left fun h1 => hm ?_)
      rw [hAdef]; exact ⟨hx, h1⟩
  have hq : P.qVal = (unitμ A).toReal * B.sVal h ^ d
      + (1 - (unitμ A).toReal) * B.tVal h ^ d :=
    integral_of_ae_twoValued hA _ _ hae
  -- `s_h^d < t_h^d`
  have hst : B.sVal h ^ d < B.tVal h ^ d := by
    have hs : 0 < B.sVal h := KKTFamily.sVal_pos hhb
    have hlt : B.sVal h < B.tVal h := B.sVal_lt_tVal hh0
    exact pow_lt_pow_left₀ hlt hs.le (by omega)
  rw [← hAdef]
  rw [hq, KKTFamily.qVal] at hΔ
  have hne : B.sVal h ^ d - B.tVal h ^ d ≠ 0 := by linarith
  have hfac : ((unitμ A).toReal - B.alph h) * (B.sVal h ^ d - B.tVal h ^ d) = 0 := by
    nlinarith [hΔ]
  have := mul_eq_zero.mp hfac
  rcases this with h1 | h1
  · linarith
  · exact absurd h1 hne

end UpperTailOptimizers
