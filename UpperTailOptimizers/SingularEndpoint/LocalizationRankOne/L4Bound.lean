import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.Localization
import UpperTailOptimizers.Preliminaries.Graphons.ExternalInputs

/-!
# The coercive step of `lem:localization-rank-one` (Section 5)

`Localization.lean` proves the exact cost comparison `eq:graphon-cost-decomposition`, used
under `I_p(W) ≤ I_p(W')` in the form

`(β_d + Λ/(d r_*^{d-1}))(S - S_h) + 𝒢_Γ ≤ 𝒢_{Γ,h} + Λ(𝒱_R - 𝒱_{R,h})`,

in the Lean notation `S = ∫W^d`, `S_h = ∫W'^d`, `𝒢_Γ = ∫Γ_d(W)`, `𝒢_{Γ,h} = ∫Γ_d(W')`,
`𝒱_R = ∫R_d(W)`, `𝒱_{R,h} = ∫R_d(W')` (the paper names none of these), together with the
Cauchy–Schwarz bound `𝒱_R² ≤ C_d 𝒢_Γ` and the quartic lower bound
`c∫|W - r_*|⁴ ≤ 𝒢_Γ`.  This file performs the absorption step of the proof of
`lem:localization-rank-one` that leads to `eq:moment-and-cost-gap-bounds`: the cross term
`Λ𝒱_R` is absorbed into half of `𝒢_Γ` by Young's inequality, at the cost of a `C_d Λ²/2`
remainder, which leaves the coercive inequality behind `eq:graphon-quartic-localization` for
`∫|W - r_*|⁴`.  (The paper bounds the edge-density correction by `C_d h²(∫Γ_d(W))^{1/2}` and
absorbs it into `½∫Γ_d(W)` in the same way.)

The absorption is isolated as `localization_absorption`, a statement of pure real arithmetic
with no measure theory in it: given `V² ≤ C·G` and the comparison, one gets the same
comparison with `G/2` on the left and an explicit `C·Λ²/2` on the right.  The quantitative
`O(h⁴)` input — the smallness of `Λ_h`, `𝒢_{Γ,h}` and `𝒱_{R,h}` along the singular endpoint family —
is *not* supplied here; it needs `eq:rank-one-parameter-expansions` and is the instantiation
performed in `SingularEndpoint/LocalizationRankOne/FamilyLocalization.lean` (`family_localization`).  The bounds below need
no family input: the two positivity lemmas and the Young absorption are unconditional, and the
two graphon statements ask only for feasibility of `W`, a moment-saturating reference `W'` and
the cost comparison `I_p(W) ≤ I_p(W')` — no smallness of `h`.

## Contents

* `gamInt_nonneg`, `rdInt_nonneg` — positivity of the two integrals `𝒢_Γ = ∫Γ_d(W)` and
  `𝒱_R = ∫R_d(W)`, from the pointwise `eq:endpoint-gap-positivity` and the nonnegativity of
  the scalar convexity defect `R_d` (`SingularEndpoint/RankOneStationaryFamily/Defs.lean`; the paper uses the
  corresponding pointwise bound `0 ≤ z^d - r_*^d - d r_*^{d-1}(z - r_*)` without naming it);
* `localization_absorption` — the Young absorption, as pure arithmetic;
* `gamInt_localized` — `eq:graphon-cost-decomposition` after absorption, at graphon level;
* `integral_dist_pow_four_localized` — `eq:graphon-quartic-localization`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory Real

variable {d : ℕ}

/-! ## Positivity of the two integrals -/

/-- `𝒢_Γ = ∫Γ_d(W) ≥ 0`, by the pointwise `eq:endpoint-gap-positivity` at the values of `W`,
which lie in `[0,1]`. -/
theorem gamInt_nonneg (hd : 2 ≤ d) (W : Graphon) : 0 ≤ GamInt d W := by
  unfold GamInt
  exact integral_nonneg fun z =>
    Gam_nonneg hd (W.mem_Icc z.1 z.2).1 (W.mem_Icc z.1 z.2).2

/-- `𝒱_R = ∫R_d(W) ≥ 0`: the scalar convexity defect `R_d` (`SingularEndpoint/RankOneStationaryFamily/Defs.lean`) is
pointwise nonnegative on `[0,∞)`, hence at the values of `W`. -/
theorem rdInt_nonneg (hd : 2 ≤ d) (W : Graphon) : 0 ≤ RdInt d W := by
  unfold RdInt
  exact integral_nonneg fun z => Rd_nonneg hd (W.mem_Icc z.1 z.2).1

/-! ## The Young absorption -/

/-- **The coercive step of `lem:localization-rank-one`, as pure arithmetic.**

Read `S = ∫W^d`, `S_h = ∫W_h^d`, `G = 𝒢_Γ`, `G_h = 𝒢_{Γ,h}`, `V = 𝒱_R`, `V_h = 𝒱_{R,h}`,
`Lam = Λ_h` and `Cc = C_d`.  Starting from `eq:graphon-cost-decomposition` in the form
`hmain`, and given the Cauchy–Schwarz bound `V² ≤ C_d G` of `R_d² ≤ C_dΓ_d`,
Young's inequality `|Λ|V ≤ C_dΛ²/2 + V²/(2C_d)` absorbs the cross term into half of `G`:

`b₀(S - S_h) + G/2 ≤ G_h + |Λ||V_h| + C_dΛ²/2`.

The remainder `C_dΛ²/2` is what the paper's `Λ_h = O(h²)` turns into `O(h⁴)`. -/
theorem localization_absorption {S Sh G Gh V Vh Lam b0 Cc : ℝ}
    (_hb0 : 0 < b0) (_hSS : Sh ≤ S) (_hG : 0 ≤ G) (hV : 0 ≤ V) (hCc : 0 < Cc)
    (hVG : V ^ 2 ≤ Cc * G)
    (hmain : b0 * (S - Sh) + G ≤ Gh + Lam * (V - Vh)) :
    b0 * (S - Sh) + G / 2 ≤ Gh + |Lam| * |Vh| + Cc * Lam ^ 2 / 2 := by
  -- Step 1: the cross term is dominated by its absolute value.
  have hcross : Lam * (V - Vh) ≤ |Lam| * V + |Lam| * |Vh| := by
    have h1 : Lam * V ≤ |Lam| * V := mul_le_mul_of_nonneg_right (le_abs_self Lam) hV
    have h2 : -(Lam * Vh) ≤ |Lam| * |Vh| := by
      have h := neg_abs_le (Lam * Vh)
      rw [abs_mul] at h
      linarith
    linarith
  -- Step 2: the sqrt-free Young inequality, together with `V² ≤ Cc·G`, after clearing
  -- the denominator `2Cc`.
  have hscaled : 2 * Cc * (|Lam| * V) ≤ 2 * Cc * (Cc * |Lam| ^ 2 / 2 + G / 2) := by
    nlinarith [sq_nonneg (Cc * |Lam| - V), hVG]
  have hyoung : |Lam| * V ≤ Cc * |Lam| ^ 2 / 2 + G / 2 :=
    le_of_mul_le_mul_left hscaled (by linarith)
  rw [sq_abs] at hyoung
  -- Step 3: combine and cancel `G/2`.
  linarith

/-! ## The graphon form -/

/-- **`eq:graphon-cost-decomposition` after Young absorption.**  Let `H` be `d`-regular with
at least one edge, let `W` be feasible for `(H, r)` and let `W'` be a reference graphon
saturating the moment, `∫W'^d = r^d`, with `I_p(W) ≤ I_p(W')`.  If `b₀` is a positive lower
bound for the coefficient `β_d + Λ/(d r_*^{d-1})` of `eq:graphon-cost-decomposition` and
`C_d` is the constant of `R_d² ≤ C_dΓ_d`, then

`b₀(∫W^d - r^d) + 𝒢_Γ/2 ≤ 𝒢_{Γ,h} + |Λ||𝒱_{R,h}| + C_dΛ²/2`,  `Λ = ℓ(p) - ℓ(p_*)`.

Generalized Hölder (`holder_moment`) supplies `r^d ≤ ∫W^d`, so the `b₀`-term is
nonnegative. -/
theorem gamInt_localized (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hr0 : 0 ≤ r) {W W' : Graphon}
    (hfeas : r ^ H.edgeFinset.card ≤ W.tDensity H)
    (hmom : W'.Wmoment d = r ^ d)
    (hcost : W.Ip p ≤ W'.Ip p)
    {b0 Cc : ℝ} (hb0 : 0 < b0) (hCc : 0 < Cc)
    (hVG : ∀ X : Graphon, RdInt d X ^ 2 ≤ Cc * GamInt d X)
    (hb0le : b0 ≤ betaD d + (ell p - ell (pStar d)) / ((d : ℝ) * rStar d ^ (d - 1))) :
    b0 * (W.Wmoment d - r ^ d) + GamInt d W / 2
      ≤ GamInt d W' + |ell p - ell (pStar d)| * |RdInt d W'|
          + Cc * (ell p - ell (pStar d)) ^ 2 / 2 := by
  -- Feasibility and generalized Hölder give `S_h ≤ S`.
  have hSS : r ^ d ≤ W.Wmoment d :=
    holder_moment H hreg hd W hr0 hm hfeas
  -- The exact cost comparison, with the reference moment rewritten as `r^d`.
  have hbasic := localization_basic hd hp0 hp1 hcost
  rw [hmom] at hbasic
  -- Weaken the coefficient to `b0`, using `S - S_h ≥ 0`.
  have hweak : b0 * (W.Wmoment d - r ^ d)
      ≤ (betaD d + (ell p - ell (pStar d)) / ((d : ℝ) * rStar d ^ (d - 1)))
          * (W.Wmoment d - r ^ d) :=
    mul_le_mul_of_nonneg_right hb0le (sub_nonneg.mpr hSS)
  have hmain : b0 * (W.Wmoment d - r ^ d) + GamInt d W
      ≤ GamInt d W' + (ell p - ell (pStar d)) * (RdInt d W - RdInt d W') := by
    linarith
  exact localization_absorption hb0 hSS (gamInt_nonneg hd W) (rdInt_nonneg hd W) hCc
    (hVG W) hmain

/-- **`eq:graphon-quartic-localization`.**  Dropping the nonnegative moment term from
`gamInt_localized` and feeding the result into the integrated quartic bound
`eq:endpoint-gap-quartic-bound` gives the `L⁴` localization

`c∫|W - r_*|⁴ ≤ 2(𝒢_{Γ,h} + |Λ||𝒱_{R,h}| + C_dΛ²/2)`.

Along the singular endpoint family the right-hand side is `O(h⁴)`, which gives
`eq:graphon-quartic-localization` in the form `∫|W - r_*|⁴ ≤ Mh⁴`; an `L²` companion (not stated
in the paper) follows from it by Cauchy–Schwarz. -/
theorem integral_dist_pow_four_localized (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hr0 : 0 ≤ r) {W W' : Graphon}
    (hfeas : r ^ H.edgeFinset.card ≤ W.tDensity H)
    (hmom : W'.Wmoment d = r ^ d)
    (hcost : W.Ip p ≤ W'.Ip p)
    {b0 Cc : ℝ} (hb0 : 0 < b0) (hCc : 0 < Cc)
    (hVG : ∀ X : Graphon, RdInt d X ^ 2 ≤ Cc * GamInt d X)
    (hb0le : b0 ≤ betaD d + (ell p - ell (pStar d)) / ((d : ℝ) * rStar d ^ (d - 1)))
    {c : ℝ} (_hc0 : 0 < c)
    (hcG : ∀ X : Graphon, c * ∫ z, |X.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ ≤ GamInt d X) :
    c * ∫ z, |W.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ
      ≤ 2 * (GamInt d W' + |ell p - ell (pStar d)| * |RdInt d W'|
          + Cc * (ell p - ell (pStar d)) ^ 2 / 2) := by
  have hmoment : r ^ d ≤ W.Wmoment d :=
    holder_moment H hreg hd W hr0 hm hfeas
  have hdrop : 0 ≤ b0 * (W.Wmoment d - r ^ d) :=
    mul_nonneg hb0.le (sub_nonneg.mpr hmoment)
  have hloc := gamInt_localized hd H hreg hm hp0 hp1 hr0 hfeas hmom hcost hb0 hCc hVG hb0le
  linarith [hcG W]

end SingularEndpoint

end UpperTailOptimizers
