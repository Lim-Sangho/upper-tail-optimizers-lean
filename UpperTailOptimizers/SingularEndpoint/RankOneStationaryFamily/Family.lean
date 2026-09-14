import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.RankOne
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.Identities
import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.BipodalUpper

/-!
# The coalescing rank-one stationary family (Section 5, `paper/sections/singular.tex`)

`lem:rank-one-kkt-family` of `paper/sections/singular.tex` produces, near the singular
endpoint, a one-parameter analytic family
`h ↦ (u_h, p_h, γ_h, α_h)` through `(u_*, p_*, γ_*, 1/2)` whose two-valued rank-one graphon
`W_h = f_{α_h,s_h,t_h} ⊗ f_{α_h,s_h,t_h}`, `s_h = u_h - h`, `t_h = u_h + h`, is stationary
for `I_{p_h} - μ_h t(H,·)` both under bounded symmetric perturbations of the graphon and
under variations of the block weight.

This file packages the analytic family and the scalar KKT and block-balance equations
as a structure, `KKTFamily d`. The first-variation conditions `eq:graphon-stationarity` and
`eq:block-stationarity` themselves are formalised as `IsStationary`
(`SingularEndpoint/RankOneStationaryFamily/Stationarity.lean`) and `IsBlockStationary`
(`SingularEndpoint/RankOneStationaryFamily/StationaryReduction.lean`); their equivalence with the scalar conditions is
`kkt_scalar_of_stationary`, `isStationary_of_kkt_scalar` and `blockStationary_iff_rowBalance`.
This file then derives the
algebra and measure theory: the derived scalars `s_h, t_h, q_h, r_h`, the candidate graphon
`W_h` as a `bipodalGraphon`, and closed forms for its edge density, `d`-th moment,
cost `I_{p_h}` and `H`-density.

**Status.** Everything in this file, and everything downstream of it, is stated *relative
to* a given `KKTFamily d`, so this layer introduces no new axiom and assumes nothing
silently.  That relativisation is no longer a limitation: `SingularEndpoint/RankOneStationaryFamily/FamilyBuild.lean` proves
`exists_kktFamily : 2 ≤ d → Nonempty (KKTFamily d)`, so the results below are
unconditional for every `d ≥ 2`.

What the structure does *not* carry, and what therefore still has to be proved separately
where it is wanted, is the expansions `eq:rank-one-parameter-expansions`, the
ordering `p_h < r_h`, and local exhaustiveness (its scalar content being available as
`exists_scalar_family_locally_unique`).

## Contents

* `Mfun` — `𝓜_{p,γ}(z) = J_p(z) - (γ/d)z^d`, the antiderivative of the rank-one KKT
  function `F_{p,γ}`, with `hasDerivAt_Mfun`;
* `KKTFamily` — the family data of `lem:rank-one-kkt-family`;
* `KKTFamily.sVal`, `.tVal`, `.qVal`, `.rVal` — the derived scalars, with
  `.sVal_lt_tVal` the separation `s_h < t_h` for `h > 0`, the ranges `.sVal_pos`, `.tVal_pos`,
  `.sVal_lt_one`, `.tVal_lt_one`, `.qVal_pos`, and the three edge-value memberships
  `.sq_sVal_mem`, `.cross_mem`, `.sq_tVal_mem`;
* `KKTFamily.sVal_neg`, `.tVal_neg`, `.qVal_even`, `.rVal_even` — reflection in `h`,
  inherited from the symmetries `u_{-h} = u_h` and `α_{-h} = 1 - α_h` of
  `lem:rank-one-kkt-family`;
* `KKTFamily.graphon` — the candidate `W_h`, and the four closed forms
  `graphon_edgeDensity`, `graphon_Wmoment`, `graphon_Ip`, `graphon_tDensity`;
* `KKTFamily.rVal_pow_card_edges` and `.graphon_tDensity_eq_rVal_pow` — `r_h^m = q_h^v`,
  hence `t(H, W_h) = r_h^m` (`thm:singular-endpoint`);
* `bipodalGraphon_integral_comp` — the four-cell splitting of `∫∫φ(W)` for a two-block
  graphon, used here for the `d`-th moment and downstream for `∫Γ_d(W_h)`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory Real

variable {d : ℕ}

/-! ## The antiderivative `𝓜` of the rank-one KKT function -/

/-- `𝓜_{p,γ}(z) = J_p(z) - (γ/d)z^d`.  Its derivative is the rank-one KKT function
`F_{p,γ}(z) = J_p'(z) - γz^{d-1}`, so the three KKT equations of
`eq:three-value-kkt` say exactly that `s_h², s_h t_h, t_h²` are critical points of
`𝓜_{p_h,γ_h}` (`lem:rank-one-kkt-family`). -/
noncomputable def Mfun (d : ℕ) (p γ z : ℝ) : ℝ := Jp p z - (γ / (d : ℝ)) * z ^ d

theorem hasDerivAt_Mfun (hd : 2 ≤ d) {p γ z : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hz0 : 0 < z) (hz1 : z < 1) : HasDerivAt (Mfun d p γ) (Fkkt d p γ z) z := by
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  have e1 : HasDerivAt (Jp p) (Jp' p z) z := hasDerivAt_Jp hp0 hp1 hz0 hz1
  have e2 : HasDerivAt (fun x : ℝ => (γ / (d : ℝ)) * x ^ d)
      ((γ / (d : ℝ)) * ((d : ℝ) * z ^ (d - 1))) z := (hasDerivAt_pow d z).const_mul _
  have e := e1.sub e2
  have hval : Jp' p z - γ / (d : ℝ) * ((d : ℝ) * z ^ (d - 1)) = Fkkt d p γ z := by
    rw [Fkkt]; field_simp
  rw [hval] at e
  exact e

/-! ## The family -/

/-- **The coalescing rank-one stationary family** of `lem:rank-one-kkt-family`.

The fields record the following parts of the lemma's conclusions:

* `u, p, gam, alph` — the real-analytic functions `u_h, p_h, γ_h, α_h` on `(-h₀, h₀)`,
  through `(u_*, p_*, γ_*, 1/2)` at `h = 0`;
* `u_even`, `p_even`, `gam_even`, `alph_reflect` — the lemma's symmetry
  `u_{-h} = u_h`, `p_{-h} = p_h`, `γ_{-h} = γ_h`, `α_{-h} = 1 - α_h`
  (changing the sign of the half-gap exchanges the two blocks);
* `p_mem`, `factor_mem`, `alph_mem` — the admissibility clause
  `0 < p_h < 1`, `0 < s_h, t_h < 1`, `0 < α_h < 1` after shrinking `h₀`;
* `kkt_ss`, `kkt_st`, `kkt_tt` — the three rank-one KKT equations
  `eq:three-value-kkt`, in the quotient-free form `F_{p_h,γ_h} = 0` of
  `eq:rank-one-kkt`;
* `rowBalance` — block-weight stationarity `eq:block-proportion-balance`.

Three statements are deliberately **not** fields.

* The expansions `eq:rank-one-parameter-expansions`, which the paper states separately as
  `lem:rank-one-parameter-expansions`: nothing below consumes them, and carrying them would
  make the structure harder to construct.
* The ordering `p_h < r_h` of the admissibility clause: again unused downstream.
* Local exhaustiveness, the lemma's converse assertion: "let `W = f ⊗ f` be a nearby
  nonconstant rank-one graphon whose factor `f` is bounded away from `0` and `1`. If `W`
  satisfies the KKT conditions with multiplier `μ` and `eq:block-stationarity` holds, then
  `W` agrees, up to measure-preserving relabeling, with a unique member `W_h` indexed by
  `h ∈ (0, h₀)`, and `μ = μ_h`" (made precise after the statement, with `h = (t-s)/2`).
  Its *base-point* instance is proved outright, and separately, as `triple_contact_forced`
  (`SingularEndpoint/RankOneStationaryFamily/Forced.lean`).

Four clauses that the paper states here are **derived** rather than assumed, and so are
theorems rather than fields: the bounds `0 < r_h < 1` (`KKTFamily.rVal_pos`,
`KKTFamily.rVal_lt_one`, `SingularEndpoint/ConstantGraphonComparison/CostGap.lean`), the constraint
`t(H, W_h) = r_h^m` (`graphon_tDensity_eq_rVal_pow`), the nonconstancy of `W_h`
(`graphon_not_ae_const`, `SingularEndpoint/Proof/Terminal.lean`), and the scalar content of the
local uniqueness clause (`exists_scalar_family_locally_unique`,
`SingularEndpoint/RankOneStationaryFamily/FamilyUnique.lean`).  `rank_one_kkt_family`
(`SingularEndpoint/RankOneStationaryFamily/RankOneKKTFamily.lean`) states the whole lemma for every `KKTFamily`,
including `p_h < r_h`, the KKT conditions for `W_h` and local exhaustiveness. -/
structure KKTFamily (d : ℕ) where
  /-- Half-width of the parameter interval. -/
  h₀ : ℝ
  h₀_pos : 0 < h₀
  /-- The midpoint `u_h` of the two factor values. -/
  u : ℝ → ℝ
  /-- The ambient density `p_h`. -/
  p : ℝ → ℝ
  /-- The scalar multiplier `γ_h`. -/
  gam : ℝ → ℝ
  /-- The block weight `α_h`. -/
  alph : ℝ → ℝ
  u_zero : u 0 = uStar d
  p_zero : p 0 = pStar d
  gam_zero : gam 0 = gammaStar d
  alph_zero : alph 0 = 1 / 2
  analyticAt_u : ∀ h : ℝ, |h| < h₀ → AnalyticAt ℝ u h
  analyticAt_p : ∀ h : ℝ, |h| < h₀ → AnalyticAt ℝ p h
  analyticAt_gam : ∀ h : ℝ, |h| < h₀ → AnalyticAt ℝ gam h
  analyticAt_alph : ∀ h : ℝ, |h| < h₀ → AnalyticAt ℝ alph h
  u_even : ∀ h : ℝ, u (-h) = u h
  p_even : ∀ h : ℝ, p (-h) = p h
  gam_even : ∀ h : ℝ, gam (-h) = gam h
  alph_reflect : ∀ h : ℝ, alph (-h) = 1 - alph h
  p_mem : ∀ h : ℝ, |h| < h₀ → 0 < p h ∧ p h < 1
  factor_mem : ∀ h : ℝ, |h| < h₀ → 0 < u h - |h| ∧ u h + |h| < 1
  alph_mem : ∀ h : ℝ, |h| < h₀ → 0 < alph h ∧ alph h < 1
  kkt_ss : ∀ h : ℝ, |h| < h₀ → Fkkt d (p h) (gam h) ((u h - h) ^ 2) = 0
  kkt_st : ∀ h : ℝ, |h| < h₀ → Fkkt d (p h) (gam h) ((u h - h) * (u h + h)) = 0
  kkt_tt : ∀ h : ℝ, |h| < h₀ → Fkkt d (p h) (gam h) ((u h + h) ^ 2) = 0
  rowBalance : ∀ h : ℝ, |h| < h₀ →
    alph h * (Mfun d (p h) (gam h) ((u h - h) ^ 2)
        - Mfun d (p h) (gam h) ((u h - h) * (u h + h)))
      = (1 - alph h) * (Mfun d (p h) (gam h) ((u h + h) ^ 2)
        - Mfun d (p h) (gam h) ((u h - h) * (u h + h)))

namespace KKTFamily

variable {d : ℕ} (B : KKTFamily d)

/-- The lower factor value `s_h = u_h - h`. -/
def sVal (h : ℝ) : ℝ := B.u h - h

/-- The upper factor value `t_h = u_h + h`. -/
def tVal (h : ℝ) : ℝ := B.u h + h

/-- The rank-one moment `q_h = α_h s_h^d + (1-α_h) t_h^d`. -/
noncomputable def qVal (h : ℝ) : ℝ :=
  B.alph h * B.sVal h ^ d + (1 - B.alph h) * B.tVal h ^ d

/-- The density `r_h = q_h^{2/d}`, so that `r_h^d = q_h²` and `r_h^m = q_h^v`. -/
noncomputable def rVal (h : ℝ) : ℝ := Real.rpow (B.qVal h) (2 / (d : ℝ))

variable {B}

/-! ### Reflection in `h`

`lem:rank-one-kkt-family` states `u_{-h} = u_h`, `p_{-h} = p_h`, `γ_{-h} = γ_h` and
`α_{-h} = 1 - α_h`, and its proof notes that `q_h`, `r_h` and `μ_h` are even as well.  The
structure carries the four primitive symmetries as fields; the derived scalars inherit them
here.  Reflection exchanges the two factor values, and `q_h` is symmetric
under exchanging them *together with* the block weight, which is exactly `alph_reflect`. -/

/-- `s_{-h} = t_h`: reflection exchanges the two factor values. -/
theorem sVal_neg (h : ℝ) : B.sVal (-h) = B.tVal h := by
  rw [sVal, tVal, B.u_even]; ring

/-- `t_{-h} = s_h`. -/
theorem tVal_neg (h : ℝ) : B.tVal (-h) = B.sVal h := by
  rw [sVal, tVal, B.u_even]; ring

/-- `q_{-h} = q_h`.  The two terms of `q_h` are swapped by `sVal_neg`/`tVal_neg` and swapped
back by `alph_reflect`. -/
theorem qVal_even (h : ℝ) : B.qVal (-h) = B.qVal h := by
  rw [qVal, qVal, sVal_neg, tVal_neg, B.alph_reflect]; ring

/-- `r_{-h} = r_h`, the evenness of `r_h` noted in the proof of `lem:rank-one-kkt-family`. -/
theorem rVal_even (h : ℝ) : B.rVal (-h) = B.rVal h := by
  rw [rVal, rVal, qVal_even]

theorem sVal_pos {h : ℝ} (hh : |h| < B.h₀) : 0 < B.sVal h := by
  have := (B.factor_mem h hh).1
  have hle : -|h| ≤ -h := neg_le_neg (le_abs_self h)
  have : B.u h - |h| ≤ B.u h - h := by linarith
  exact lt_of_lt_of_le (B.factor_mem h hh).1 this

theorem tVal_pos {h : ℝ} (hh : |h| < B.h₀) : 0 < B.tVal h := by
  have h1 := (B.factor_mem h hh).1
  have h2 : -|h| ≤ h := neg_abs_le h
  have : B.u h - |h| ≤ B.u h + h := by linarith
  exact lt_of_lt_of_le h1 this

theorem sVal_lt_one {h : ℝ} (hh : |h| < B.h₀) : B.sVal h < 1 := by
  have h2 := (B.factor_mem h hh).2
  have : B.u h - h ≤ B.u h + |h| := by
    have := neg_abs_le h
    linarith
  exact lt_of_le_of_lt this h2

theorem tVal_lt_one {h : ℝ} (hh : |h| < B.h₀) : B.tVal h < 1 := by
  have h2 := (B.factor_mem h hh).2
  have : B.u h + h ≤ B.u h + |h| := by
    have := le_abs_self h
    linarith
  exact lt_of_le_of_lt this h2

variable (B)

/-- **The two atoms are ordered for `h > 0`:** `s_h = u_h - h < u_h + h = t_h`.  No window
hypothesis is needed — `sVal` and `tVal` are unconditional definitions. -/
theorem sVal_lt_tVal {h : ℝ} (hh : 0 < h) : B.sVal h < B.tVal h := by
  show B.u h - h < B.u h + h
  linarith

variable {B}

theorem qVal_pos {h : ℝ} (hh : |h| < B.h₀) : 0 < B.qVal h := by
  have hs := sVal_pos hh
  have ht := tVal_pos hh
  have ha := B.alph_mem h hh
  have h1 : 0 < B.alph h * B.sVal h ^ d := mul_pos ha.1 (pow_pos hs d)
  have h2 : 0 < (1 - B.alph h) * B.tVal h ^ d :=
    mul_pos (by linarith [ha.2]) (pow_pos ht d)
  rw [qVal]
  linarith

/-! ### The three edge values lie in `[0,1]` -/

theorem sq_sVal_mem {h : ℝ} (hh : |h| < B.h₀) :
    B.sVal h ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sq_nonneg _, by nlinarith [sVal_pos hh, sVal_lt_one hh]⟩

theorem cross_mem {h : ℝ} (hh : |h| < B.h₀) :
    B.sVal h * B.tVal h ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(mul_pos (sVal_pos hh) (tVal_pos hh)).le,
    by nlinarith [sVal_pos hh, sVal_lt_one hh, tVal_pos hh, tVal_lt_one hh]⟩

theorem sq_tVal_mem {h : ℝ} (hh : |h| < B.h₀) :
    B.tVal h ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sq_nonneg _, by nlinarith [tVal_pos hh, tVal_lt_one hh]⟩

variable (B)

/-- **The candidate graphon `W_h`** of `thm:singular-endpoint`: the rank-one two-block
graphon `f_h ⊗ f_h` with `f_h = s_h·1_{[0,α_h]} + t_h·1_{(α_h,1]}`. -/
noncomputable def graphon {h : ℝ} (hh : |h| < B.h₀) : Graphon :=
  bipodalGraphon (Set.Icc 0 (B.alph h)) measurableSet_Icc
    (B.sVal h ^ 2) (B.sVal h * B.tVal h) (B.tVal h ^ 2)
    (sq_sVal_mem hh) (cross_mem hh) (sq_tVal_mem hh)

variable {B}

/-- `e(W_h) = (α_h s_h + (1-α_h) t_h)²`, the square of the mean of `f_h`
(`lem:constant-graphon-comparison`). -/
theorem graphon_edgeDensity {h : ℝ} (hh : |h| < B.h₀) :
    (B.graphon hh).edgeDensity = (B.alph h * B.sVal h + (1 - B.alph h) * B.tVal h) ^ 2 := by
  have ha := B.alph_mem h hh
  rw [graphon, bipodalGraphon_edgeDensity, unitμ_Icc_toReal ha.1.le ha.2.le]
  ring

/-- `I_{p_h}(W_h) = α²J(s²) + 2α(1-α)J(st) + (1-α)²J(t²)`, the restriction of the graphon
Lagrangian to the bipodal family (`lem:rank-one-kkt-family`). -/
theorem graphon_Ip {h : ℝ} (hh : |h| < B.h₀) :
    (B.graphon hh).Ip (B.p h)
      = B.alph h ^ 2 * Jp (B.p h) (B.sVal h ^ 2)
        + 2 * B.alph h * (1 - B.alph h) * Jp (B.p h) (B.sVal h * B.tVal h)
        + (1 - B.alph h) ^ 2 * Jp (B.p h) (B.tVal h ^ 2) := by
  have ha := B.alph_mem h hh
  have hp := B.p_mem h hh
  exact Ip_bipodalGraphon_Icc hp.1 hp.2 (sq_sVal_mem hh) (cross_mem hh) (sq_tVal_mem hh)
    ha.1.le ha.2.le

/-- **The integral of an arbitrary function of a two-block bipodal graphon** splits over the
four block cells: `∫∫φ(W) = φ(q₁₁)a² + φ(q₁₂)·2a(1-a) + φ(q₂₂)(1-a)²`.  Same computation as
`bipodalGraphon_entropy`, for a general `φ`; `φ = (·^d)` gives `graphon_Wmoment` and
`φ = Γ_d` gives the block form of `∫Γ_d(W_h)`. -/
theorem bipodalGraphon_integral_comp (φ : ℝ → ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    (q11 q12 q22 : ℝ) (h11 : q11 ∈ Set.Icc (0:ℝ) 1) (h12 : q12 ∈ Set.Icc (0:ℝ) 1)
    (h22 : q22 ∈ Set.Icc (0:ℝ) 1) :
    ∫ z, φ ((bipodalGraphon A hA q11 q12 q22 h11 h12 h22).toFun z.1 z.2) ∂gμ
      = φ q11 * (unitμ A).toReal ^ 2
        + φ q12 * (2 * (unitμ A).toReal * (1 - (unitμ A).toReal))
        + φ q22 * (1 - (unitμ A).toReal) ^ 2 := by
  rw [show gμ = unitμ.prod unitμ from rfl]
  rw [show (fun z : ℝ × ℝ => φ ((bipodalGraphon A hA q11 q12 q22 h11 h12 h22).toFun z.1 z.2))
      = (fun z : ℝ × ℝ => φ q11 * (A.indicator 1 z.1 * A.indicator 1 z.2)
          + φ q12 * (A.indicator 1 z.1 * Aᶜ.indicator 1 z.2)
          + φ q12 * (Aᶜ.indicator 1 z.1 * A.indicator 1 z.2)
          + φ q22 * (Aᶜ.indicator 1 z.1 * Aᶜ.indicator 1 z.2))
    from by
      funext z
      rw [bipodalGraphon_apply]
      exact bipodalValue_comp_indicator_sum φ A q11 q12 q22 z.1 z.2]
  have hiA : Integrable (A.indicator (1 : ℝ → ℝ)) unitμ := (integrable_const 1).indicator hA
  have hiAc : Integrable (Aᶜ.indicator (1 : ℝ → ℝ)) unitμ :=
    (integrable_const 1).indicator hA.compl
  have i1 : Integrable (fun z : ℝ × ℝ => φ q11 * (A.indicator 1 z.1 * A.indicator 1 z.2))
      (unitμ.prod unitμ) := (hiA.mul_prod hiA).const_mul _
  have i2 : Integrable (fun z : ℝ × ℝ => φ q12 * (A.indicator 1 z.1 * Aᶜ.indicator 1 z.2))
      (unitμ.prod unitμ) := (hiA.mul_prod hiAc).const_mul _
  have i3 : Integrable (fun z : ℝ × ℝ => φ q12 * (Aᶜ.indicator 1 z.1 * A.indicator 1 z.2))
      (unitμ.prod unitμ) := (hiAc.mul_prod hiA).const_mul _
  have i4 : Integrable (fun z : ℝ × ℝ => φ q22 * (Aᶜ.indicator 1 z.1 * Aᶜ.indicator 1 z.2))
      (unitμ.prod unitμ) := (hiAc.mul_prod hiAc).const_mul _
  have i12 : Integrable (fun z : ℝ × ℝ => φ q11 * (A.indicator 1 z.1 * A.indicator 1 z.2)
      + φ q12 * (A.indicator 1 z.1 * Aᶜ.indicator 1 z.2)) (unitμ.prod unitμ) := i1.add i2
  have i123 : Integrable (fun z : ℝ × ℝ => φ q11 * (A.indicator 1 z.1 * A.indicator 1 z.2)
      + φ q12 * (A.indicator 1 z.1 * Aᶜ.indicator 1 z.2)
      + φ q12 * (Aᶜ.indicator 1 z.1 * A.indicator 1 z.2)) (unitμ.prod unitμ) := i12.add i3
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2]
  simp only [integral_const_mul, integral_prod_mul]
  rw [integral_indicator_one hA, integral_indicator_one hA.compl]
  simp only [measureReal_def]
  have e3 : (unitμ Aᶜ).toReal = 1 - (unitμ A).toReal := by
    rw [prob_compl_eq_one_sub hA, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  rw [e3]; ring

/-- `∫∫W_h^d = q_h²`: for a rank-one graphon `f ⊗ f` the `d`-th moment is `(∫f^d)²`
(`lem:constant-graphon-comparison`). -/
theorem graphon_Wmoment {h : ℝ} (hh : |h| < B.h₀) :
    (B.graphon hh).Wmoment d = B.qVal h ^ 2 := by
  have ha := B.alph_mem h hh
  have e1 : (B.sVal h ^ 2) ^ d = (B.sVal h ^ d) ^ 2 := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : (B.tVal h ^ 2) ^ d = (B.tVal h ^ d) ^ 2 := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have e3 : (B.sVal h * B.tVal h) ^ d = B.sVal h ^ d * B.tVal h ^ d := mul_pow _ _ _
  show ∫ z, ((B.graphon hh).toFun z.1 z.2) ^ d ∂gμ = _
  rw [graphon, bipodalGraphon_integral_comp (fun x : ℝ => x ^ d),
    unitμ_Icc_toReal ha.1.le ha.2.le]
  rw [e1, e2, e3, qVal]
  ring

/-! ### The `H`-density and the `d`-th moment -/

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- `t(H, W_h) = q_h^{|V(H)|}`: the rank-one identity of `paper/sections/singular.tex`. -/
theorem graphon_tDensity (hreg : ∀ v, H.degree v = d) {h : ℝ} (hh : |h| < B.h₀) :
    (B.graphon hh).tDensity H = B.qVal h ^ Fintype.card V := by
  have ha := B.alph_mem h hh
  rw [graphon, tDensity_rankOne_two_block H hreg (sq_sVal_mem hh) (cross_mem hh)
    (sq_tVal_mem hh) ha.1.le ha.2.le, qVal]

/-- `r_h^m = q_h^v`: the handshake identity `nd = 2m` turns the definition
`r_h = q_h^{2/d}` into the equality of the two feasibility constraints. -/
theorem rVal_pow_card_edges (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d) {h : ℝ}
    (hh : |h| < B.h₀) :
    B.rVal h ^ H.edgeFinset.card = B.qVal h ^ Fintype.card V := by
  have hq : 0 < B.qVal h := qVal_pos hh
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  have hhand : (Fintype.card V : ℝ) * (d : ℝ) = 2 * (H.edgeFinset.card : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (regular_handshake H hreg)
  rw [rVal, show Real.rpow (B.qVal h) (2 / (d : ℝ)) = B.qVal h ^ (2 / (d : ℝ)) from rfl,
    ← Real.rpow_natCast (B.qVal h ^ (2 / (d : ℝ))) H.edgeFinset.card,
    ← Real.rpow_mul hq.le, ← Real.rpow_natCast (B.qVal h) (Fintype.card V)]
  congr 1
  field_simp
  linarith [hhand]

/-- **`t(H, W_h) = r_h^m`**, the feasibility clause of `thm:singular-endpoint`. -/
theorem graphon_tDensity_eq_rVal_pow (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d) {h : ℝ}
    (hh : |h| < B.h₀) :
    (B.graphon hh).tDensity H = B.rVal h ^ H.edgeFinset.card := by
  rw [graphon_tDensity H hreg hh, rVal_pow_card_edges H hd hreg hh]

end KKTFamily

end SingularEndpoint

end UpperTailOptimizers
