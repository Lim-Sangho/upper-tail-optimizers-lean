import UpperTailOptimizers.SingularEndpoint.FirstVariation
import UpperTailOptimizers.SingularEndpoint.Interp4
import UpperTailOptimizers.SingularEndpoint.CostGap
import UpperTailOptimizers.SingularEndpoint.FamilyContinuity

/-!
# The quartic first-variation lower bound (Section 7, `paper/singular_endpoint.tex`)

The **first** of the two lower bounds of `lem:first-variation-bound`: near the coalescing wells the one-point dual potential
`eq:first-variation` dominates the square of the node quadratic,

`Ψ_h(x) ≥ a_ρ Q_h(x)²` for `x ∈ 𝓝_ρ = [u_* - ρ, u_* + ρ]`, with `a_ρ ≥ d³/24`.

`SingularEndpoint/FirstVariation.lean` proves the four contact conditions
`Ψ_h(s_h) = Ψ_h(t_h) = Ψ_h'(s_h) = Ψ_h'(t_h) = 0`, and
`SingularEndpoint/CostGap.lean` proves the collapsed form `eq:endpoint-first-variation`,
`Ψ_0(x) = 2Γ_d(u_* x)`.  What is added here is the *quantitative* half.

## The argument

The paper factors `Ψ_h = Q_h² R_h` by an analytic Weierstrass division joint in `(h, x)`
and reads `R_0(u_*) = d³/12` off the quartic expansion of `eq:endpoint-first-variation`.  As
elsewhere in `SingularEndpoint/` (see `SingularEndpoint/Order4.lean`, `SingularEndpoint/Interp4.lean`) that
division is replaced by an elementary two-node **Hermite remainder**: on a window around
`u_*` the four contact conditions give, for every `x`, an unlocated `ξ` with

`Ψ_h(x) = Ψ_h⁗(ξ)/24 · (x - s_h)²(x - t_h)² = Ψ_h⁗(ξ)/24 · Q_h(x)²`,

and an unlocated `ξ` is harmless because only a *lower* bound is wanted.  The constant then
comes from a single evaluation, `Ψ_0⁗(u_*) = 2d³` (`Psi4_zero_uStar`), together with joint
continuity of `(h, ξ) ↦ Ψ_h⁗(ξ)` at `(0, u_*)`: on a small enough box `Ψ_h⁗ ≥ d³`, which is
the paper's `R_h ≥ d³/24 · 2 = d³/12` up to the factor `24` of the remainder formula.

`Ψ⁗` needs no `p`-dependent continuity: `J_p⁗(u) = 2/u³ + 2/(1-u)³` does not involve `p`
at all, so the only `h`-dependence left in `Ψ_h⁗` sits in the four family scalars
`α_h, s_h, t_h, η_h`, each analytic — hence continuous — at `h = 0`.

**Scope.**  The companion bound `Ψ_h ≥ b_ρ` *off* `𝓝_ρ` on `[0,2]` is not proved here; it is
`KKTFamily.exists_firstVariation_upperGap` in `SingularEndpoint/PsiTilde.lean`.  The reason for the
split is that the paper's `Ψ_h` there uses the continued entropy `J̃` of
`eq:entropy-continuation` ("We suppress the tilde below", `paper/singular_endpoint.tex`),
whereas `KKTFamily.Psi` uses the plain `Jp`, and the two agree only while `x s_h` and
`x t_h` stay in `[0,1]`.  Everything below therefore stays inside a small window around `u_*`,
where they agree.

## Contents

* `KKTFamily.Psi1`, `.Psi2`, `.Psi3`, `.Psi4` — the derivative chain of
  `eq:first-variation`, with `hasDerivAt_Psi'`, `hasDerivAt_Psi1`,
  `hasDerivAt_Psi2`, `hasDerivAt_Psi3`;
* `KKTFamily.Psi1_sVal`, `.Psi1_tVal` — the two slope contacts of
  `SingularEndpoint/FirstVariation.lean` restated as `Ψ_h'(s_h) = Ψ_h'(t_h) = 0`;
* `KKTFamily.Psi4_zero`, `.Psi4_zero_uStar` — `Ψ_0⁗(x) = 2u_*⁴𝓛_*'''(u_* x)` and the
  non-degeneracy value `Ψ_0⁗(u_*) = 2d³`;
* `KKTFamily.exists_Psi4_window`, `.exists_Psi4_lower` — the uniform bound
  `Ψ_h⁗ ≥ d³` on a box around `(0, u_*)`;
* `KKTFamily.exists_firstVariation_lower` — the quartic lower bound
  `Ψ_h(x) ≥ (d³/24) Q_h(x)²` of `lem:first-variation-bound`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

variable {d : ℕ}

/-! ## Preliminaries

The exponents `d - 1`, `d - 2` are natural-number subtractions whose casts to `ℝ` agree with
the real subtractions because `hd : 2 ≤ d` (`cast_sub_one`, `cast_sub_two` of
`SingularEndpoint/Contact.lean`); the exponent `d - 3` does **not**, and is kept as a Nat cast
throughout (see `Psi4`). -/

/-- `J_p⁗` is continuous at every point of `(0,1)`: it is the rational function
`2/z³ + 2/(1-z)³`, with poles only at `0` and `1`.  A local copy of `continuousAt_Jp4`
(`SingularEndpoint/FkktDeriv.lean`), which this file does not import. -/
private theorem continuousAt_Jp4' {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    ContinuousAt Jp4 z := by
  have h1 : (z : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hz0)
  have h2 : ((1 : ℝ) - z) ^ 3 ≠ 0 := pow_ne_zero 3 (by linarith)
  show ContinuousAt (fun u : ℝ => 2 / u ^ 3 + 2 / (1 - u) ^ 3) z
  fun_prop (disch := assumption)

namespace KKTFamily

variable {d : ℕ} {B : KKTFamily d}

/-! ## The derivative chain of the dual potential

`Psi1` is the derivative expression of `hasDerivAt_Psi` (`SingularEndpoint/FirstVariation.lean`)
taken verbatim, so that `hasDerivAt_Psi'` below is that lemma with no bridging.  The three
further derivatives replace `J_p'` successively by `J_p''`, `J_p'''`, `J_p⁗`, each
composition with `x ↦ x s_h` contributing one more factor of `s_h`. -/

/-- `Ψ_h'(x) = 2{α_h s_h J_{p_h}'(x s_h) + (1-α_h) t_h J_{p_h}'(x t_h)} - dη_h x^{d-1}`,
the first display of the proof of `lem:first-variation-bound`. -/
noncomputable def Psi1 (B : KKTFamily d) (h x : ℝ) : ℝ :=
  2 * (B.alph h * (Jp' (B.p h) (x * B.sVal h) * B.sVal h)
      + (1 - B.alph h) * (Jp' (B.p h) (x * B.tVal h) * B.tVal h))
    - B.etaVal h * ((d : ℝ) * x ^ (d - 1))

/-- `Ψ_h''(x) = 2{α_h s_h² J_{p_h}''(x s_h) + (1-α_h) t_h² J_{p_h}''(x t_h)}
- d(d-1)η_h x^{d-2}`. -/
noncomputable def Psi2 (B : KKTFamily d) (h x : ℝ) : ℝ :=
  2 * (B.alph h * (Jp'' (x * B.sVal h) * B.sVal h ^ 2)
      + (1 - B.alph h) * (Jp'' (x * B.tVal h) * B.tVal h ^ 2))
    - B.etaVal h * ((d : ℝ) * ((d : ℝ) - 1) * x ^ (d - 2))

/-- `Ψ_h'''(x) = 2{α_h s_h³ J_{p_h}'''(x s_h) + (1-α_h) t_h³ J_{p_h}'''(x t_h)}
- d(d-1)(d-2)η_h x^{d-3}`. -/
noncomputable def Psi3 (B : KKTFamily d) (h x : ℝ) : ℝ :=
  2 * (B.alph h * (Jp3 (x * B.sVal h) * B.sVal h ^ 3)
      + (1 - B.alph h) * (Jp3 (x * B.tVal h) * B.tVal h ^ 3))
    - B.etaVal h * ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) * x ^ (d - 3))

/-- `Ψ_h⁗(x) = 2{α_h s_h⁴ J_{p_h}⁗(x s_h) + (1-α_h) t_h⁴ J_{p_h}⁗(x t_h)}
- d(d-1)(d-2)(d-3)η_h x^{d-4}`.

**The trailing factor is the cast of the natural-number difference `d - 3`**, exactly as in
`Lstar3` (`SingularEndpoint/Contact.lean`) and `Fkkt4` (`SingularEndpoint/Fkkt4.lean`): differentiating
`x ↦ x^{d-3}` produces `((d-3 : ℕ) : ℝ) x^{d-4}`, and at `d = 2, 3` that coefficient is `0`
whereas `(d:ℝ) - 3` is not.  Writing `(d:ℝ) - 3` here would make `Psi4` false at `d = 2`.
The two leading factors may be honest real subtractions because `hd : 2 ≤ d` makes
`((d-1 : ℕ) : ℝ) = (d:ℝ) - 1` and `((d-2 : ℕ) : ℝ) = (d:ℝ) - 2`. -/
noncomputable def Psi4 (B : KKTFamily d) (h x : ℝ) : ℝ :=
  2 * (B.alph h * (Jp4 (x * B.sVal h) * B.sVal h ^ 4)
      + (1 - B.alph h) * (Jp4 (x * B.tVal h) * B.tVal h ^ 4))
    - B.etaVal h * ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d - 3 : ℕ) : ℝ)
      * x ^ (d - 4))

/-- `hasDerivAt_Psi` (`SingularEndpoint/FirstVariation.lean`) with its derivative expression named:
`Ψ_h' = Psi1`. -/
theorem hasDerivAt_Psi' (hd : 2 ≤ d) {h x : ℝ} (hh : |h| < B.h₀)
    (hs0 : 0 < x * B.sVal h) (hs1 : x * B.sVal h < 1)
    (ht0 : 0 < x * B.tVal h) (ht1 : x * B.tVal h < 1) :
    HasDerivAt (B.Psi h) (B.Psi1 h x) x :=
  hasDerivAt_Psi hd hh hs0 hs1 ht0 ht1

/-- `Ψ_h'' = Psi2`, at a point where both products `x s_h`, `x t_h` are interior. -/
theorem hasDerivAt_Psi1 (hd : 2 ≤ d) {h x : ℝ} (hh : |h| < B.h₀)
    (hs0 : 0 < x * B.sVal h) (hs1 : x * B.sVal h < 1)
    (ht0 : 0 < x * B.tVal h) (ht1 : x * B.tVal h < 1) :
    HasDerivAt (B.Psi1 h) (B.Psi2 h x) x := by
  have hp := B.p_mem h hh
  have e1 : HasDerivAt (fun y : ℝ => Jp' (B.p h) (y * B.sVal h) * B.sVal h)
      (Jp'' (x * B.sVal h) * B.sVal h * B.sVal h) x := by
    have h0 : HasDerivAt (fun y : ℝ => Jp' (B.p h) (y * B.sVal h))
        (Jp'' (x * B.sVal h) * B.sVal h) x := by
      have := (hasDerivAt_Jp' hp.1 hp.2 hs0 hs1).comp x
        ((hasDerivAt_id x).mul_const (B.sVal h))
      simpa [Function.comp_def] using this
    exact h0.mul_const (B.sVal h)
  have e2 : HasDerivAt (fun y : ℝ => Jp' (B.p h) (y * B.tVal h) * B.tVal h)
      (Jp'' (x * B.tVal h) * B.tVal h * B.tVal h) x := by
    have h0 : HasDerivAt (fun y : ℝ => Jp' (B.p h) (y * B.tVal h))
        (Jp'' (x * B.tVal h) * B.tVal h) x := by
      have := (hasDerivAt_Jp' hp.1 hp.2 ht0 ht1).comp x
        ((hasDerivAt_id x).mul_const (B.tVal h))
      simpa [Function.comp_def] using this
    exact h0.mul_const (B.tVal h)
  have e3 : HasDerivAt (fun y : ℝ => B.etaVal h * ((d : ℝ) * y ^ (d - 1)))
      (B.etaVal h * ((d : ℝ) * (((d - 1 : ℕ) : ℝ) * x ^ (d - 1 - 1)))) x :=
    ((hasDerivAt_pow (d - 1) x).const_mul ((d : ℝ))).const_mul (B.etaVal h)
  have e := (((e1.const_mul (B.alph h)).add (e2.const_mul (1 - B.alph h))).const_mul
    (2 : ℝ)).sub e3
  have hval : 2 * (B.alph h * (Jp'' (x * B.sVal h) * B.sVal h * B.sVal h)
        + (1 - B.alph h) * (Jp'' (x * B.tVal h) * B.tVal h * B.tVal h))
      - B.etaVal h * ((d : ℝ) * (((d - 1 : ℕ) : ℝ) * x ^ (d - 1 - 1))) = B.Psi2 h x := by
    rw [Psi2, cast_sub_one hd, show d - 1 - 1 = d - 2 from by omega]
    ring
  rw [hval] at e
  exact e

/-- `Ψ_h''' = Psi3`.  No admissibility of `p_h` is needed: `J_p''` and its derivatives do
not depend on `p`. -/
theorem hasDerivAt_Psi2 (hd : 2 ≤ d) {h x : ℝ}
    (hs0 : 0 < x * B.sVal h) (hs1 : x * B.sVal h < 1)
    (ht0 : 0 < x * B.tVal h) (ht1 : x * B.tVal h < 1) :
    HasDerivAt (B.Psi2 h) (B.Psi3 h x) x := by
  have e1 : HasDerivAt (fun y : ℝ => Jp'' (y * B.sVal h) * B.sVal h ^ 2)
      (Jp3 (x * B.sVal h) * B.sVal h * B.sVal h ^ 2) x := by
    have h0 : HasDerivAt (fun y : ℝ => Jp'' (y * B.sVal h))
        (Jp3 (x * B.sVal h) * B.sVal h) x := by
      have := (hasDerivAt_Jp'' hs0 hs1).comp x ((hasDerivAt_id x).mul_const (B.sVal h))
      simpa [Function.comp_def] using this
    exact h0.mul_const (B.sVal h ^ 2)
  have e2 : HasDerivAt (fun y : ℝ => Jp'' (y * B.tVal h) * B.tVal h ^ 2)
      (Jp3 (x * B.tVal h) * B.tVal h * B.tVal h ^ 2) x := by
    have h0 : HasDerivAt (fun y : ℝ => Jp'' (y * B.tVal h))
        (Jp3 (x * B.tVal h) * B.tVal h) x := by
      have := (hasDerivAt_Jp'' ht0 ht1).comp x ((hasDerivAt_id x).mul_const (B.tVal h))
      simpa [Function.comp_def] using this
    exact h0.mul_const (B.tVal h ^ 2)
  have e3 : HasDerivAt
      (fun y : ℝ => B.etaVal h * ((d : ℝ) * ((d : ℝ) - 1) * y ^ (d - 2)))
      (B.etaVal h * ((d : ℝ) * ((d : ℝ) - 1)
        * (((d - 2 : ℕ) : ℝ) * x ^ (d - 2 - 1)))) x :=
    ((hasDerivAt_pow (d - 2) x).const_mul ((d : ℝ) * ((d : ℝ) - 1))).const_mul (B.etaVal h)
  have e := (((e1.const_mul (B.alph h)).add (e2.const_mul (1 - B.alph h))).const_mul
    (2 : ℝ)).sub e3
  have hval : 2 * (B.alph h * (Jp3 (x * B.sVal h) * B.sVal h * B.sVal h ^ 2)
        + (1 - B.alph h) * (Jp3 (x * B.tVal h) * B.tVal h * B.tVal h ^ 2))
      - B.etaVal h * ((d : ℝ) * ((d : ℝ) - 1)
        * (((d - 2 : ℕ) : ℝ) * x ^ (d - 2 - 1))) = B.Psi3 h x := by
    rw [Psi3, cast_sub_two hd, show d - 2 - 1 = d - 3 from by omega]
    ring
  rw [hval] at e
  exact e

/-- `Ψ_h⁗ = Psi4`.  Here the exponent that comes down is the **cast of the natural-number**
difference `d - 3`, which is why `Psi4` carries `((d-3 : ℕ) : ℝ)` and not `(d:ℝ) - 3`; the
degree bound is therefore not used. -/
theorem hasDerivAt_Psi3 (_hd : 2 ≤ d) {h x : ℝ}
    (hs0 : 0 < x * B.sVal h) (hs1 : x * B.sVal h < 1)
    (ht0 : 0 < x * B.tVal h) (ht1 : x * B.tVal h < 1) :
    HasDerivAt (B.Psi3 h) (B.Psi4 h x) x := by
  have e1 : HasDerivAt (fun y : ℝ => Jp3 (y * B.sVal h) * B.sVal h ^ 3)
      (Jp4 (x * B.sVal h) * B.sVal h * B.sVal h ^ 3) x := by
    have h0 : HasDerivAt (fun y : ℝ => Jp3 (y * B.sVal h))
        (Jp4 (x * B.sVal h) * B.sVal h) x := by
      have := (hasDerivAt_Jp3 hs0 hs1).comp x ((hasDerivAt_id x).mul_const (B.sVal h))
      simpa [Function.comp_def] using this
    exact h0.mul_const (B.sVal h ^ 3)
  have e2 : HasDerivAt (fun y : ℝ => Jp3 (y * B.tVal h) * B.tVal h ^ 3)
      (Jp4 (x * B.tVal h) * B.tVal h * B.tVal h ^ 3) x := by
    have h0 : HasDerivAt (fun y : ℝ => Jp3 (y * B.tVal h))
        (Jp4 (x * B.tVal h) * B.tVal h) x := by
      have := (hasDerivAt_Jp3 ht0 ht1).comp x ((hasDerivAt_id x).mul_const (B.tVal h))
      simpa [Function.comp_def] using this
    exact h0.mul_const (B.tVal h ^ 3)
  have e3 : HasDerivAt
      (fun y : ℝ => B.etaVal h
        * ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) * y ^ (d - 3)))
      (B.etaVal h * ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2)
        * (((d - 3 : ℕ) : ℝ) * x ^ (d - 3 - 1)))) x :=
    ((hasDerivAt_pow (d - 3) x).const_mul
      ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2))).const_mul (B.etaVal h)
  have e := (((e1.const_mul (B.alph h)).add (e2.const_mul (1 - B.alph h))).const_mul
    (2 : ℝ)).sub e3
  have hval : 2 * (B.alph h * (Jp4 (x * B.sVal h) * B.sVal h * B.sVal h ^ 3)
        + (1 - B.alph h) * (Jp4 (x * B.tVal h) * B.tVal h * B.tVal h ^ 3))
      - B.etaVal h * ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2)
        * (((d - 3 : ℕ) : ℝ) * x ^ (d - 3 - 1))) = B.Psi4 h x := by
    rw [Psi4, show d - 3 - 1 = d - 4 from by omega]
    ring
  rw [hval] at e
  exact e

/-! ## The two slope contacts, restated

`Psi_deriv_sVal` and `Psi_deriv_tVal` of `SingularEndpoint/FirstVariation.lean` are stated as the
vanishing of the derivative *expression*; since `Psi1` is that expression verbatim, they are
literally `Ψ_h'(s_h) = 0` and `Ψ_h'(t_h) = 0`. -/

/-- `Ψ_h'(s_h) = 0`. -/
theorem Psi1_sVal (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) : B.Psi1 h (B.sVal h) = 0 :=
  Psi_deriv_sVal hd hh

/-- `Ψ_h'(t_h) = 0`. -/
theorem Psi1_tVal (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) : B.Psi1 h (B.tVal h) = 0 :=
  Psi_deriv_tVal hd hh

/-! ## The fourth derivative at `h = 0` -/

/-- **`Ψ_0⁗(x) = 2u_*⁴ 𝓛_*'''(u_* x)`.**

This is `eq:endpoint-first-variation` differentiated four times: `Ψ_0(x) = 2Γ_d(u_* x)` and
`Γ_d^{(4)} = 𝓛_*'''` (`hasDerivAt_Gam`, `hasDerivAt_Lstar2`), so the chain rule contributes
`u_*⁴`.  The proof below is the direct algebraic verification, which avoids having to
differentiate a composite four times.

The one real step is the correction term.  Matching
`2β_d u_*^d · d(d-1)(d-2)((d-3:ℕ)) x^{d-4}` with
`2u_*⁴ · γ_*(d-1)(d-2)((d-3:ℕ)) (u_* x)^{d-4}` uses `β_d d = γ_*` and
`u_*⁴ u_*^{d-4} = u_*^d`, the latter true only for `d ≥ 4`; for `d ≤ 3` the Nat cast
`((d-3 : ℕ) : ℝ)` is `0` and both correction terms vanish.  This is the same split as in
`Lstar3_rStar` and `Lstar4_rStar`. -/
theorem Psi4_zero (hd : 2 ≤ d) (B : KKTFamily d) (x : ℝ) :
    B.Psi4 0 x = 2 * uStar d ^ 4 * Lstar3 d (uStar d * x) := by
  have hcorr : 2 * betaD d * uStar d ^ d
        * ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d - 3 : ℕ) : ℝ) * x ^ (d - 4))
      = 2 * uStar d ^ 4
        * (gammaStar d * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d - 3 : ℕ) : ℝ)
          * (uStar d * x) ^ (d - 4)) := by
    rcases lt_or_ge d 4 with hlt | hge
    · have hnat : ((d - 3 : ℕ) : ℝ) = 0 := by
        rw [show d - 3 = 0 from by omega]; norm_num
      rw [hnat]; ring
    · have hpow : uStar d ^ d = uStar d ^ 4 * uStar d ^ (d - 4) := by
        rw [← pow_add]; congr 1; omega
      have hmul : (uStar d * x) ^ (d - 4) = uStar d ^ (d - 4) * x ^ (d - 4) := mul_pow _ _ _
      rw [hpow, hmul, ← betaD_mul_d hd]
      ring
  rw [Psi4, sVal_zero, tVal_zero, B.alph_zero, etaVal_zero hd, Lstar3,
    mul_comm x (uStar d)]
  linear_combination -hcorr

/-- **The non-degeneracy value `Ψ_0⁗(u_*) = 2d³`.**

By `Psi4_zero` and `Lstar3_rStar hd : 𝓛_*'''(r_*) = d⁵/(d-1)²` together with
`uStar_sq hd : u_*² = r_*`:

`2u_*⁴ · d⁵/(d-1)² = 2((d-1)/d)² · d⁵/(d-1)² = 2d³`.

This is the paper's `R_0(u_*) = d³/12` multiplied by the `24` of the Hermite remainder. -/
theorem Psi4_zero_uStar (hd : 2 ≤ d) (B : KKTFamily d) :
    B.Psi4 0 (uStar d) = 2 * (d : ℝ) ^ 3 := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by linarith
  have harg : uStar d * uStar d = rStar d := by rw [← uStar_sq hd]; ring
  have hu4 : uStar d ^ 4 = rStar d ^ 2 := by rw [← uStar_sq hd]; ring
  rw [Psi4_zero hd, harg, Lstar3_rStar hd, hu4, rStar_eq]
  field_simp

/-! ## A uniform lower bound on `Ψ_h⁗` near `(0, u_*)`

The map `(h, ξ) ↦ Ψ_h⁗(ξ)` is continuous at `(0, u_*)` — `J_p⁗` does not depend on `p`, so
only continuity of `J_p⁗` on `(0,1)` and of the family scalars at `h = 0` is used — and its
value there is `2d³ > d³`.  A box around `(0, u_*)` on which the strict inequality persists
is extracted with `Metric.eventually_nhds_iff`; the same box is shrunk so that the two
products `ξ s_h`, `ξ t_h` stay interior, which is what the derivative chain needs. -/

/-- Joint continuity of `(h, ξ) ↦ Ψ_h⁗(ξ)` at `(0, u_*)`. -/
private theorem continuousAt_Psi4 (hd : 2 ≤ d) (B : KKTFamily d) :
    ContinuousAt (fun z : ℝ × ℝ => B.Psi4 z.1 z.2) ((0 : ℝ), uStar d) := by
  have hvs : uStar d * B.sVal 0 = rStar d := by rw [sVal_zero, ← uStar_sq hd]; ring
  have hvt : uStar d * B.tVal 0 = rStar d := by rw [tVal_zero, ← uStar_sq hd]; ring
  have hA : ContinuousAt (fun z : ℝ × ℝ => B.alph z.1) ((0 : ℝ), uStar d) :=
    ContinuousAt.comp' (f := fun z : ℝ × ℝ => z.1) (alph_continuousAt B) continuousAt_fst
  have hS : ContinuousAt (fun z : ℝ × ℝ => B.sVal z.1) ((0 : ℝ), uStar d) :=
    ContinuousAt.comp' (f := fun z : ℝ × ℝ => z.1) (sVal_continuousAt B) continuousAt_fst
  have hT : ContinuousAt (fun z : ℝ × ℝ => B.tVal z.1) ((0 : ℝ), uStar d) :=
    ContinuousAt.comp' (f := fun z : ℝ × ℝ => z.1) (tVal_continuousAt B) continuousAt_fst
  have hE : ContinuousAt (fun z : ℝ × ℝ => B.etaVal z.1) ((0 : ℝ), uStar d) :=
    ContinuousAt.comp' (f := fun z : ℝ × ℝ => z.1) (etaVal_continuousAt B) continuousAt_fst
  have hargS : ContinuousAt (fun z : ℝ × ℝ => z.2 * B.sVal z.1) ((0 : ℝ), uStar d) := by
    exact ContinuousAt.mul continuousAt_snd hS
  have hargT : ContinuousAt (fun z : ℝ × ℝ => z.2 * B.tVal z.1) ((0 : ℝ), uStar d) := by
    exact ContinuousAt.mul continuousAt_snd hT
  have hJs : ContinuousAt Jp4 (uStar d * B.sVal 0) := by
    rw [hvs]; exact continuousAt_Jp4' (rStar_pos hd) (rStar_lt_one hd)
  have hJt : ContinuousAt Jp4 (uStar d * B.tVal 0) := by
    rw [hvt]; exact continuousAt_Jp4' (rStar_pos hd) (rStar_lt_one hd)
  have hCs : ContinuousAt (fun z : ℝ × ℝ => Jp4 (z.2 * B.sVal z.1)) ((0 : ℝ), uStar d) :=
    ContinuousAt.comp' (f := fun z : ℝ × ℝ => z.2 * B.sVal z.1) hJs hargS
  have hCt : ContinuousAt (fun z : ℝ × ℝ => Jp4 (z.2 * B.tVal z.1)) ((0 : ℝ), uStar d) :=
    ContinuousAt.comp' (f := fun z : ℝ × ℝ => z.2 * B.tVal z.1) hJt hargT
  have hPow : ContinuousAt (fun z : ℝ × ℝ => z.2 ^ (d - 4)) ((0 : ℝ), uStar d) := by
    exact ContinuousAt.pow continuousAt_snd (d - 4)
  have hbody : ContinuousAt (fun z : ℝ × ℝ =>
      2 * (B.alph z.1 * (Jp4 (z.2 * B.sVal z.1) * B.sVal z.1 ^ 4)
          + (1 - B.alph z.1) * (Jp4 (z.2 * B.tVal z.1) * B.tVal z.1 ^ 4))
        - B.etaVal z.1 * ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ((d - 3 : ℕ) : ℝ)
          * z.2 ^ (d - 4))) ((0 : ℝ), uStar d) := by
    exact (continuousAt_const.mul ((hA.mul (hCs.mul (hS.pow 4))).add
        ((continuousAt_const.sub hA).mul (hCt.mul (hT.pow 4))))).sub
      (hE.mul (continuousAt_const.mul hPow))
  exact hbody

/-- **The working window.**  There are `w, δ > 0` such that on the box
`|h| < δ`, `ξ ∈ [u_* - w, u_* + w]` the fourth derivative of the dual potential is at least
`d³` and both products `ξ s_h`, `ξ t_h` are interior to `(0,1)`.

The first clause is the uniform version of `Psi4_zero_uStar`; the second is what makes the
derivative chain `hasDerivAt_Psi' → … → hasDerivAt_Psi3` applicable, and is also the reason
the statement stays inside a window (off it the paper's `Ψ_h` uses the continued entropy
`J̃` of `eq:entropy-continuation`, which `KKTFamily.Psi` does not). -/
theorem exists_Psi4_window (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ w : ℝ, 0 < w ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      ∀ ξ ∈ Set.Icc (uStar d - w) (uStar d + w),
        (d : ℝ) ^ 3 ≤ B.Psi4 h ξ ∧ 0 < ξ * B.sVal h ∧ ξ * B.sVal h < 1
          ∧ 0 < ξ * B.tVal h ∧ ξ * B.tVal h < 1 := by
  have hvs : uStar d * B.sVal 0 = rStar d := by rw [sVal_zero, ← uStar_sq hd]; ring
  have hvt : uStar d * B.tVal 0 = rStar d := by rw [tVal_zero, ← uStar_sq hd]; ring
  have hr0 : 0 < rStar d := rStar_pos hd
  have hr1 : rStar d < 1 := rStar_lt_one hd
  have hS0 : ContinuousAt (fun z : ℝ × ℝ => B.sVal z.1) ((0 : ℝ), uStar d) :=
    ContinuousAt.comp' (f := fun z : ℝ × ℝ => z.1) (sVal_continuousAt B) continuousAt_fst
  have hT0 : ContinuousAt (fun z : ℝ × ℝ => B.tVal z.1) ((0 : ℝ), uStar d) :=
    ContinuousAt.comp' (f := fun z : ℝ × ℝ => z.1) (tVal_continuousAt B) continuousAt_fst
  have hS : ContinuousAt (fun z : ℝ × ℝ => z.2 * B.sVal z.1) ((0 : ℝ), uStar d) := by
    exact ContinuousAt.mul continuousAt_snd hS0
  have hT : ContinuousAt (fun z : ℝ × ℝ => z.2 * B.tVal z.1) ((0 : ℝ), uStar d) := by
    exact ContinuousAt.mul continuousAt_snd hT0
  have hP := continuousAt_Psi4 hd B
  have hc0 : ContinuousAt (fun _ : ℝ × ℝ => (0 : ℝ)) ((0 : ℝ), uStar d) := continuousAt_const
  have hc1 : ContinuousAt (fun _ : ℝ × ℝ => (1 : ℝ)) ((0 : ℝ), uStar d) := continuousAt_const
  have hcd : ContinuousAt (fun _ : ℝ × ℝ => (d : ℝ) ^ 3) ((0 : ℝ), uStar d) :=
    continuousAt_const
  -- the four strict inequalities hold at the centre of the box
  have hlt : (d : ℝ) ^ 3 < B.Psi4 0 (uStar d) := by
    have hpos : (0 : ℝ) < (d : ℝ) ^ 3 := pow_pos (dpos hd) 3
    rw [Psi4_zero_uStar hd]; linarith
  have e1 : ∀ᶠ z : ℝ × ℝ in 𝓝 ((0 : ℝ), uStar d), (d : ℝ) ^ 3 < B.Psi4 z.1 z.2 :=
    hcd.eventually_lt hP hlt
  have e2 : ∀ᶠ z : ℝ × ℝ in 𝓝 ((0 : ℝ), uStar d), (0 : ℝ) < z.2 * B.sVal z.1 :=
    hc0.eventually_lt hS (by rw [hvs]; exact hr0)
  have e3 : ∀ᶠ z : ℝ × ℝ in 𝓝 ((0 : ℝ), uStar d), z.2 * B.sVal z.1 < 1 :=
    hS.eventually_lt hc1 (by rw [hvs]; exact hr1)
  have e4 : ∀ᶠ z : ℝ × ℝ in 𝓝 ((0 : ℝ), uStar d), (0 : ℝ) < z.2 * B.tVal z.1 :=
    hc0.eventually_lt hT (by rw [hvt]; exact hr0)
  have e5 : ∀ᶠ z : ℝ × ℝ in 𝓝 ((0 : ℝ), uStar d), z.2 * B.tVal z.1 < 1 :=
    hT.eventually_lt hc1 (by rw [hvt]; exact hr1)
  obtain ⟨ε, hε, hball⟩ :=
    Metric.eventually_nhds_iff.mp (e1.and (e2.and (e3.and (e4.and e5))))
  refine ⟨ε / 2, by linarith, ε / 2, by linarith, ?_⟩
  intro h hh ξ hξ
  have hdist : dist ((h, ξ) : ℝ × ℝ) ((0 : ℝ), uStar d) < ε := by
    have hb : |ξ - uStar d| ≤ ε / 2 :=
      abs_le.mpr ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
    have e : dist ((h, ξ) : ℝ × ℝ) ((0 : ℝ), uStar d) = max |h| |ξ - uStar d| := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
    rw [e]
    exact max_lt (by linarith) (by linarith)
  obtain ⟨f1, f2, f3, f4, f5⟩ := hball hdist
  exact ⟨f1.le, f2, f3, f4, f5⟩

/-- **`Ψ_h⁗ ≥ d³` on a box around `(0, u_*)`**, the uniform non-degeneracy behind the
constant `a_ρ ≥ d³/24` of `lem:first-variation-bound`.  A weakening of
`exists_Psi4_window`. -/
theorem exists_Psi4_lower (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ w : ℝ, 0 < w ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → |h| < B.h₀ →
      ∀ ξ ∈ Set.Icc (uStar d - w) (uStar d + w), (d : ℝ) ^ 3 ≤ B.Psi4 h ξ := by
  obtain ⟨w, hw, δ, hδ, hbox⟩ := exists_Psi4_window hd B
  exact ⟨w, hw, δ, hδ, fun h hh _ ξ hξ => (hbox h hh ξ hξ).1⟩

/-! ## The quartic first-variation lower bound -/

/-- **The quartic lower bound of `lem:first-variation-bound`.**

There are a window half-width `w > 0` and a threshold `δ > 0` such that, for every
`0 < h < δ` inside the family window,

`Ψ_h(x) ≥ (d³/24) Q_h(x)²` for all `x ∈ [u_* - w, u_* + w]`,

where `Q_h(x) = (x - s_h)(x - t_h)` is the node quadratic (`KKTFamily.Qh`).  This is
the paper's `Ψ_h ≥ a_ρ Q_h²` on `𝓝_ρ` with the asserted value `a_ρ = d³/24`.

The proof is the two-node Hermite remainder `exists_deriv4_eq_of_two_double_roots` applied
on `[u_* - w, u_* + w]` to the derivative chain `Ψ_h → Ψ_h' → Ψ_h'' → Ψ_h''' → Ψ_h⁗`, whose
four vanishing hypotheses are the contact conditions `Psi_sVal`, `Psi_tVal`, `Psi1_sVal`,
`Psi1_tVal`.  The nodes are distinct because `t_h - s_h = 2h > 0`, and they lie in the
window because `s_h, t_h → u_*`.  The remainder formula turns the uniform bound
`Ψ_h⁗ ≥ d³` of `exists_Psi4_window` into the stated inequality, the unlocated intermediate
point `ξ` being harmless for a lower bound.

The companion bound `Ψ_h ≥ b_ρ` off the window is `exists_firstVariation_upperGap`
(`SingularEndpoint/PsiTilde.lean`), which works with the continued entropy; see the module
docstring. -/
theorem exists_firstVariation_lower (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ w : ℝ, 0 < w ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → |h| < B.h₀ →
      ∀ x ∈ Set.Icc (uStar d - w) (uStar d + w),
        (d : ℝ) ^ 3 / 24 * B.Qh h x ^ 2 ≤ B.Psi h x := by
  obtain ⟨w, hw, δ₀, hδ₀, hbox⟩ := exists_Psi4_window hd B
  -- shrink the threshold so that the two nodes lie in the window
  have hsw : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), |B.sVal h - uStar d| < w := by
    have h := Metric.tendsto_nhds.mp (sVal_continuousAt B) w hw
    simpa [Real.dist_eq, sVal_zero] using h
  have htw : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), |B.tVal h - uStar d| < w := by
    have h := Metric.tendsto_nhds.mp (tVal_continuousAt B) w hw
    simpa [Real.dist_eq, tVal_zero] using h
  obtain ⟨δ₁, hδ₁, hnode⟩ := Metric.eventually_nhds_iff.mp (hsw.and htw)
  refine ⟨w, hw, min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro h hpos hlt hh x hx
  have habs : |h| = h := abs_of_pos hpos
  have hh0 : |h| < δ₀ := by rw [habs]; exact lt_of_lt_of_le hlt (min_le_left _ _)
  have hh1 : dist h (0 : ℝ) < δ₁ := by
    rw [Real.dist_eq, sub_zero, habs]
    exact lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨hns, hnt⟩ := hnode hh1
  -- the two nodes lie in the window and are distinct
  have hsmem : B.sVal h ∈ Set.Icc (uStar d - w) (uStar d + w) := by
    have := abs_lt.mp hns
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have htmem : B.tVal h ∈ Set.Icc (uStar d - w) (uStar d + w) := by
    have := abs_lt.mp hnt
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hpos
  -- the derivative chain on the window
  have hf : ∀ y ∈ Set.Icc (uStar d - w) (uStar d + w),
      HasDerivAt (B.Psi h) (B.Psi1 h y) y := by
    intro y hy
    obtain ⟨-, hs0, hs1, ht0, ht1⟩ := hbox h hh0 y hy
    exact hasDerivAt_Psi' hd hh hs0 hs1 ht0 ht1
  have hf₁ : ∀ y ∈ Set.Icc (uStar d - w) (uStar d + w),
      HasDerivAt (B.Psi1 h) (B.Psi2 h y) y := by
    intro y hy
    obtain ⟨-, hs0, hs1, ht0, ht1⟩ := hbox h hh0 y hy
    exact hasDerivAt_Psi1 hd hh hs0 hs1 ht0 ht1
  have hf₂ : ∀ y ∈ Set.Icc (uStar d - w) (uStar d + w),
      HasDerivAt (B.Psi2 h) (B.Psi3 h y) y := by
    intro y hy
    obtain ⟨-, hs0, hs1, ht0, ht1⟩ := hbox h hh0 y hy
    exact hasDerivAt_Psi2 hd hs0 hs1 ht0 ht1
  have hf₃ : ∀ y ∈ Set.Icc (uStar d - w) (uStar d + w),
      HasDerivAt (B.Psi3 h) (B.Psi4 h y) y := by
    intro y hy
    obtain ⟨-, hs0, hs1, ht0, ht1⟩ := hbox h hh0 y hy
    exact hasDerivAt_Psi3 hd hs0 hs1 ht0 ht1
  -- the Hermite remainder at the two double nodes
  obtain ⟨ξ, hξ, hrem⟩ := exists_deriv4_eq_of_two_double_roots hf hf₁ hf₂ hf₃ hsmem htmem
    hst (Psi_sVal B h) (Psi1_sVal hd hh) (Psi_tVal hd hh) (Psi1_tVal hd hh) hx
  have hP4 : (d : ℝ) ^ 3 ≤ B.Psi4 h ξ := (hbox h hh0 ξ hξ).1
  have hQ : (x - B.sVal h) ^ 2 * (x - B.tVal h) ^ 2 = B.Qh h x ^ 2 := by
    rw [Qh]; ring
  rw [hrem, hQ]
  exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end KKTFamily

end SingularEndpoint

end UpperTailOptimizers
