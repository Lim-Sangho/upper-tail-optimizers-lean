import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.FirstVariation
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.Gap

/-!
# The family cost gap and the collapsed dual potential (Section 5)

Two exact consequences of the family data, both proved outright.

**The cost gap.**  `lem:constant-graphon-comparison` of `paper/sections/singular.tex` runs through
the identity `eq:constant-comparison-identity`

`I_{p_h}(W_h) - J_{p_h}(r_h) = ∫Γ_d(W_h) - Γ_d(r_h) + (ℓ(p_h) - ℓ_*)(e(W_h) - r_h)`,

whose middle term drops out of the general `Ip_sub_Jp_eq` because the candidate saturates
its own `d`-th moment: `∫∫W_h^d = q_h² = r_h^d`.  The lemma's *expansion*
`-d³h⁴/3 + O_d(h⁶)` needs `eq:rank-one-parameter-expansions`; its leading order is
`tendsto_cost_gap` (`SingularEndpoint/ConstantGraphonComparison/StrictImprovement.lean`), which is all that
`singular_endpoint_strict_improvement` consumes; the sharper `O_d(h⁶)` remainder is
`constant_graphon_comparison` (`SingularEndpoint/ConstantGraphonComparison/CostRemainder.lean`).

**The collapsed dual potential.**  At `h = 0` the two wells merge and
`lem:first-variation-bound` records `eq:endpoint-first-variation`,
`Ψ_0(x) = 2Γ̃_d(u_* x)`.  That is an identity between the family's `h = 0` data and the
singular endpoint gap, and this file proves it, hence also `Ψ_0 ≥ 0` with a unique zero at `u_*`
`eq:endpoint-gap-positivity`.  The `h > 0` first-variation bounds are `exists_firstVariation_lower`
(`SingularEndpoint/AuxiliaryLagrangian/FirstVariationBound.lean`) and `exists_firstVariation_upperGap` (`SingularEndpoint/AuxiliaryLagrangian/PsiTilde.lean`), which
replace the paper's analytic division of `Ψ_h` by `Q_h²` (in the proof of
`lem:first-variation-bound`) by a two-node Hermite remainder.

## Contents

* `KKTFamily.qVal_lt_one`, `.rVal_pos`, `.rVal_lt_one`, `.rVal_pow_d`;
* `KKTFamily.graphon_Wmoment_eq_rVal_pow` — `∫∫W_h^d = r_h^d`;
* `KKTFamily.gamInt_graphon` — `∫Γ_d(W_h)` in block form;
* `KKTFamily.cost_gap_eq` — `eq:constant-comparison-identity`;
* `KKTFamily.sVal_zero`, `.tVal_zero`, `.qVal_zero`, `.etaVal_zero`, `.kappaVal_zero`;
* `KKTFamily.Psi_zero` — `eq:endpoint-first-variation`;
* `KKTFamily.Psi_zero_nonneg`, `.Psi_zero_eq_zero_iff`.
-/

namespace UpperTailOptimizers

namespace KKTFamily

open MeasureTheory Real

variable {d : ℕ} {B : KKTFamily d}

/-! ## The density `r_h` -/

theorem qVal_lt_one (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) : B.qVal h < 1 := by
  have ha := B.alph_mem h hh
  have hs : B.sVal h ^ d < 1 := pow_lt_one₀ (sVal_pos hh).le (sVal_lt_one hh) (by omega)
  have ht : B.tVal h ^ d < 1 := pow_lt_one₀ (tVal_pos hh).le (tVal_lt_one hh) (by omega)
  have h1 : B.alph h * B.sVal h ^ d < B.alph h * 1 :=
    mul_lt_mul_of_pos_left hs ha.1
  have h2 : (1 - B.alph h) * B.tVal h ^ d < (1 - B.alph h) * 1 :=
    mul_lt_mul_of_pos_left ht (by linarith [ha.2])
  rw [qVal]
  linarith

theorem rVal_pos (_hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) : 0 < B.rVal h :=
  Real.rpow_pos_of_pos (qVal_pos hh) _

theorem rVal_lt_one (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) : B.rVal h < 1 := by
  have hdpos : (0 : ℝ) < 2 / (d : ℝ) := by
    have := dpos hd; positivity
  exact Real.rpow_lt_one (qVal_pos hh).le (qVal_lt_one hd hh) hdpos

/-- `r_h^d = q_h²`: the defining property of `r_h = q_h^{2/d}`. -/
theorem rVal_pow_d (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) :
    B.rVal h ^ d = B.qVal h ^ 2 := by
  have hq : 0 < B.qVal h := qVal_pos hh
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  rw [rVal, show Real.rpow (B.qVal h) (2 / (d : ℝ)) = B.qVal h ^ (2 / (d : ℝ)) from rfl,
    ← Real.rpow_natCast (B.qVal h ^ (2 / (d : ℝ))) d, ← Real.rpow_mul hq.le,
    ← Real.rpow_natCast (B.qVal h) 2]
  congr 1
  push_cast
  field_simp

/-- `∫∫W_h^d = r_h^d`: the candidate saturates the `d`-th moment at its own density, which
is why the `β_d` term drops out of the cost gap. -/
theorem graphon_Wmoment_eq_rVal_pow (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) :
    (B.graphon hh).Wmoment d = B.rVal h ^ d := by
  rw [graphon_Wmoment hh, rVal_pow_d hd hh]

/-! ## The cost gap -/

/-- `∫Γ_d(W_h)` in block form: the three edge values of the candidate weighted by the block
proportions. -/
theorem gamInt_graphon {h : ℝ} (hh : |h| < B.h₀) :
    GamInt d (B.graphon hh)
      = B.alph h ^ 2 * Gam d (B.sVal h ^ 2)
        + 2 * B.alph h * (1 - B.alph h) * Gam d (B.sVal h * B.tVal h)
        + (1 - B.alph h) ^ 2 * Gam d (B.tVal h ^ 2) := by
  have ha := B.alph_mem h hh
  show ∫ z, Gam d ((B.graphon hh).toFun z.1 z.2) ∂gμ = _
  rw [graphon, bipodalGraphon_integral_comp (Gam d), unitμ_Icc_toReal ha.1.le ha.2.le]
  ring

/-- **`eq:constant-comparison-identity`**: the exact cost gap of the candidate against the
constant graphon of the same `H`-density,

`I_{p_h}(W_h) - J_{p_h}(r_h) = (∫Γ_d(W_h) - Γ_d(r_h)) + Λ_h (e(W_h) - r_h)`,

with `Λ_h = ℓ(p_h) - ℓ(p_*)`.  The `β_d`-term of the general identity `Ip_sub_Jp_eq`
vanishes because `∫∫W_h^d = r_h^d`. -/
theorem cost_gap_eq (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) :
    (B.graphon hh).Ip (B.p h) - Jp (B.p h) (B.rVal h)
      = (GamInt d (B.graphon hh) - Gam d (B.rVal h))
        + (ell (B.p h) - ell (pStar d)) * ((B.graphon hh).edgeDensity - B.rVal h) := by
  have hp := B.p_mem h hh
  have hmom := graphon_Wmoment_eq_rVal_pow hd hh
  have := Ip_sub_Jp_eq hd hp.1 hp.2 (rVal_pos hd hh).le (rVal_lt_one hd hh).le (B.graphon hh)
  rw [this, hmom]
  ring

/-! ## The collapsed dual potential -/

theorem sVal_zero (B : KKTFamily d) : B.sVal 0 = uStar d := by
  rw [sVal, B.u_zero]; ring

theorem tVal_zero (B : KKTFamily d) : B.tVal 0 = uStar d := by
  rw [tVal, B.u_zero]; ring

/-- `q_0 = u_*^d`. -/
theorem qVal_zero (B : KKTFamily d) : B.qVal 0 = uStar d ^ d := by
  rw [qVal, sVal_zero, tVal_zero]; ring

/-- `r_0 = r_*`, the second half of the singular endpoint value `(p_0, r_0) = P_*` of
`thm:singular-endpoint`.  (`p_0 = p_*` is the field `p_zero`.) -/
theorem rVal_zero (hd : 2 ≤ d) (B : KKTFamily d) : B.rVal 0 = rStar d := by
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  have hu : (0 : ℝ) ≤ uStar d := le_of_lt (uStar_pos hd)
  have hmul : (d : ℝ) * (2 / (d : ℝ)) = 2 := by field_simp
  have key : ((uStar d ^ d : ℝ)) ^ (2 / (d : ℝ)) = uStar d ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (uStar d) d, ← Real.rpow_mul hu, hmul,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [rVal, qVal_zero]
  exact key.trans (uStar_sq hd)

/-- `η_0 = 2β_d u_*^d`. -/
theorem etaVal_zero (hd : 2 ≤ d) (B : KKTFamily d) :
    B.etaVal 0 = 2 * betaD d * uStar d ^ d := by
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  rw [etaVal, qVal_zero, B.gam_zero, betaD]
  field_simp

/-- `κ_0 = 2J_{p_*}(r_*) - 2β_d r_*^d`. -/
theorem kappaVal_zero (hd : 2 ≤ d) (B : KKTFamily d) :
    B.kappaVal 0
      = 2 * Jp (pStar d) (rStar d) - 2 * betaD d * rStar d ^ d := by
  have huu : uStar d ^ 2 = rStar d := uStar_sq hd
  have hud : uStar d ^ d * uStar d ^ d = rStar d ^ d := by
    rw [← pow_add, ← two_mul, pow_mul, huu]
  have huu' : uStar d * uStar d = rStar d := by rw [← huu]; ring
  have e1 : Jp (pStar d) (uStar d ^ 2) = Jp (pStar d) (rStar d) := by rw [huu]
  have e2 : Jp (pStar d) (uStar d * uStar d) = Jp (pStar d) (rStar d) := by rw [huu']
  rw [kappaVal, sVal_zero, tVal_zero, B.p_zero, B.alph_zero, etaVal_zero hd, e1, e2]
  linear_combination (-2 * betaD d) * hud

/-- **`eq:endpoint-first-variation`**: at the singular endpoint the one-point dual potential
is twice the singular endpoint supporting gap, rescaled: `Ψ_0(x) = 2Γ_d(u_* x)`. -/
theorem Psi_zero (hd : 2 ≤ d) (B : KKTFamily d) (x : ℝ) :
    B.Psi 0 x = 2 * Gam d (uStar d * x) := by
  have hxu : (uStar d * x) ^ d = uStar d ^ d * x ^ d := mul_pow _ _ _
  rw [Psi, sVal_zero, tVal_zero, B.p_zero, B.alph_zero, etaVal_zero hd, kappaVal_zero hd,
    Gam, hxu, mul_comm x (uStar d)]
  ring

/-- `Ψ_0 ≥ 0` wherever the rescaled argument stays in `[0,1]`, from
`eq:endpoint-gap-positivity`. -/
theorem Psi_zero_nonneg (hd : 2 ≤ d) (B : KKTFamily d) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : uStar d * x ≤ 1) : 0 ≤ B.Psi 0 x := by
  have h0 : 0 ≤ uStar d * x := mul_nonneg (uStar_nonneg hd) hx0
  rw [Psi_zero hd]
  have := Gam_nonneg hd h0 hx1
  linarith

/-- `Ψ_0` has its unique zero at `x = u_*` — the collapsed form of the two contacts
`Ψ_h(s_h) = Ψ_h(t_h) = 0`. -/
theorem Psi_zero_eq_zero_iff (hd : 2 ≤ d) (B : KKTFamily d) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : uStar d * x ≤ 1) : B.Psi 0 x = 0 ↔ x = uStar d := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have h0 : 0 ≤ uStar d * x := mul_nonneg hu0.le hx0
  rw [Psi_zero hd]
  constructor
  · intro hz
    have hgam : Gam d (uStar d * x) = 0 := by linarith
    have := (Gam_eq_zero_iff hd h0 hx1).mp hgam
    have hsq : uStar d * x = uStar d * uStar d := by
      rw [this, ← uStar_sq hd]; ring
    exact (mul_left_cancel₀ (ne_of_gt hu0) hsq)
  · rintro rfl
    have : uStar d * uStar d = rStar d := by rw [← uStar_sq hd]; ring
    rw [this, Gam_rStar hd]
    ring

end KKTFamily

end UpperTailOptimizers
