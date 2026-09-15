import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Family

/-!
# The first-variation dual potential (Section 5, `paper/sections/singular.tex`)

The one-point dual potential `eq:first-variation` of
`sec:auxiliary-lagrangian`,

`Ψ_h(x) = 2{α_h J_{p_h}(x s_h) + (1-α_h) J_{p_h}(x t_h)} - η_h x^d - κ_h`,
`η_h = 2γ_h q_h / d`,

with `κ_h` normalised so that `Ψ_h(s_h) = 0`.  This file proves the **four contact
conditions** established in the paper's prose following `eq:first-variation`,

`Ψ_h(s_h) = Ψ_h(t_h) = Ψ_h'(s_h) = Ψ_h'(t_h) = 0`,

and the closed form of the normalising constant, `κ_h = 2 I_{p_h}(W_h) - η_h q_h`
(the paper defines `κ_h` only implicitly, by `Ψ_h(s_h) = 0`, and does not display this
evaluation).

All four are consequences of the family data alone: the value contacts are exactly
block-weight stationarity `eq:block-proportion-balance`, and the slope contacts are exactly the
three rank-one KKT equations `eq:three-value-kkt`.  The *quantitative* half of
`lem:first-variation-bound` — the first-variation lower bounds `Ψ_h ≥ a Q_h²` near the
wells (the constant `a` is `ρ`-uniform) and `Ψ_h ≥ b_ρ` away from them — is not here.  The
paper gets the first because the four contact conditions force `Ψ_h` to contain the factor
`Q_h²` with a positive quotient near `u_*` (by analytic division, `Ψ_h = Q_h² D_h` with
`D_0(u_*) = d³/12`), and the second from the positivity of `Ψ_0` away from `u_*` and uniform
convergence.  In Lean they are `exists_firstVariation_lower` (`SingularEndpoint/AuxiliaryLagrangian/FirstVariationBound.lean`) and
`exists_firstVariation_upperGap` (`SingularEndpoint/AuxiliaryLagrangian/PsiTilde.lean`), both by a two-node Hermite remainder in
place of the factorisation.

## Contents

* `KKTFamily.etaVal`, `.IpScalar`, `.kappaVal`, `.Psi`, `.Qh` — the objects of
  `eq:first-variation`;
* `KKTFamily.graphon_Ip_eq_IpScalar` — `I_{p_h}(W_h)` in closed form;
* `KKTFamily.Psi_sVal`, `.Psi_tVal` — the two value contacts, the second being
  `eq:block-proportion-balance`;
* `KKTFamily.hasDerivAt_Psi`, `.Psi_deriv_sVal`, `.Psi_deriv_tVal` — the two slope
  contacts, from the KKT equations;
* `KKTFamily.kappaVal_eq` — the closed form of `κ_h`.
-/

namespace UpperTailOptimizers

open Real

variable {d : ℕ}

/-! ## Power bookkeeping

Two identities that turn `x·(x²)^{d-1}` and `y·(xy)^{d-1}` into `x^{d-1}·x^d` and
`x^{d-1}·y^d`.  They are where the rank-one structure enters the slope contacts. -/

private theorem self_mul_sq_pow (hd : 2 ≤ d) (x : ℝ) :
    x * (x * x) ^ (d - 1) = x ^ (d - 1) * x ^ d := by
  have h1 : x * x = x ^ 2 := by ring
  have h2 : 2 * (d - 1) + 1 = (d - 1) + d := by omega
  rw [h1, ← pow_mul, ← pow_succ', ← pow_add, h2]

private theorem mul_cross_pow (hd : 2 ≤ d) (x y : ℝ) :
    y * (x * y) ^ (d - 1) = x ^ (d - 1) * y ^ d := by
  have h2 : (d - 1) + 1 = d := by omega
  rw [mul_pow, ← mul_assoc, mul_comm y (x ^ (d - 1)), mul_assoc, ← pow_succ', h2]

namespace KKTFamily

variable {d : ℕ} {B : KKTFamily d}

/-- `η_h = μ_h v q_h^{v-1} = 2γ_h q_h / d` `eq:first-variation`.  The graph-free
form: `v = 2m/d` and `γ_h = μ_h m q_h^{v-2}` make the two expressions equal, so nothing
below needs `H`. -/
noncomputable def etaVal (B : KKTFamily d) (h : ℝ) : ℝ :=
  2 * B.gam h * B.qVal h / (d : ℝ)

/-- The cost `I_{p_h}(W_h)` in closed form, as a scalar. -/
noncomputable def IpScalar (B : KKTFamily d) (h : ℝ) : ℝ :=
  B.alph h ^ 2 * Jp (B.p h) (B.sVal h ^ 2)
    + 2 * B.alph h * (1 - B.alph h) * Jp (B.p h) (B.sVal h * B.tVal h)
    + (1 - B.alph h) ^ 2 * Jp (B.p h) (B.tVal h ^ 2)

theorem graphon_Ip_eq_IpScalar {h : ℝ} (hh : |h| < B.h₀) :
    (B.graphon hh).Ip (B.p h) = B.IpScalar h :=
  graphon_Ip hh

/-- The normalising constant of `eq:first-variation`, fixed by `Ψ_h(s_h) = 0`. -/
noncomputable def kappaVal (B : KKTFamily d) (h : ℝ) : ℝ :=
  2 * (B.alph h * Jp (B.p h) (B.sVal h ^ 2)
      + (1 - B.alph h) * Jp (B.p h) (B.sVal h * B.tVal h))
    - B.etaVal h * B.sVal h ^ d

/-- **The one-point dual potential** `eq:first-variation`. -/
noncomputable def Psi (B : KKTFamily d) (h x : ℝ) : ℝ :=
  2 * (B.alph h * Jp (B.p h) (x * B.sVal h) + (1 - B.alph h) * Jp (B.p h) (x * B.tVal h))
    - B.etaVal h * x ^ d - B.kappaVal h

/-- `η_h · d = 2γ_h q_h`, the division-free form of `η_h`. -/
theorem etaVal_mul_d (hd : 2 ≤ d) (B : KKTFamily d) (h : ℝ) :
    B.etaVal h * (d : ℝ) = 2 * B.gam h * B.qVal h := by
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  rw [etaVal]
  field_simp

/-- The first-variation quadratic `Q_h(x) = (x - s_h)(x - t_h)` of
`lem:first-variation-bound`. -/
def Qh (B : KKTFamily d) (h x : ℝ) : ℝ := (x - B.sVal h) * (x - B.tVal h)

/-! ## The two value contacts -/

/-- `Ψ_h(s_h) = 0`: this is the choice of `κ_h`. -/
theorem Psi_sVal (B : KKTFamily d) (h : ℝ) : B.Psi h (B.sVal h) = 0 := by
  have e : B.sVal h * B.sVal h = B.sVal h ^ 2 := by ring
  rw [Psi, kappaVal, e]
  ring

/-- The algebraic identity `q_h(s_h^d - t_h^d) = α_h{s_h^{2d} - (s_ht_h)^d}
- (1-α_h){t_h^{2d} - (s_ht_h)^d}` used in `lem:rank-one-kkt-family` and again in
`kappaVal_eq`. -/
theorem qVal_mul_pow_sub (B : KKTFamily d) (h : ℝ) :
    B.qVal h * (B.sVal h ^ d - B.tVal h ^ d)
      = B.alph h * ((B.sVal h ^ 2) ^ d - (B.sVal h * B.tVal h) ^ d)
        - (1 - B.alph h) * ((B.tVal h ^ 2) ^ d - (B.sVal h * B.tVal h) ^ d) := by
  have e1 : (B.sVal h ^ 2) ^ d = B.sVal h ^ d * B.sVal h ^ d := by
    rw [← pow_mul, two_mul, pow_add]
  have e2 : (B.tVal h ^ 2) ^ d = B.tVal h ^ d * B.tVal h ^ d := by
    rw [← pow_mul, two_mul, pow_add]
  have e3 : (B.sVal h * B.tVal h) ^ d = B.sVal h ^ d * B.tVal h ^ d := mul_pow _ _ _
  rw [qVal, e1, e2, e3]
  ring

/-- **`Ψ_h(t_h) = 0`**, the second value contact.  It is exactly block-weight
stationarity `eq:block-proportion-balance`. -/
theorem Psi_tVal (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) : B.Psi h (B.tVal h) = 0 := by
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  have hrow := B.rowBalance h hh
  have hsq : B.u h - h = B.sVal h := rfl
  have htq : B.u h + h = B.tVal h := rfl
  rw [hsq, htq] at hrow
  -- unfold `𝓜` in the row-balance equation
  simp only [Mfun] at hrow
  have hid := qVal_mul_pow_sub B h
  have ets : B.tVal h * B.sVal h = B.sVal h * B.tVal h := mul_comm _ _
  have ett : B.tVal h * B.tVal h = B.tVal h ^ 2 := by ring
  rw [Psi, kappaVal, ets, ett, etaVal]
  linear_combination (-2 : ℝ) * hrow + (2 * B.gam h / (d : ℝ)) * hid

/-! ## The two slope contacts -/

/-- The derivative of `Ψ_h` at a point where both products `x s_h`, `x t_h` are interior. -/
theorem hasDerivAt_Psi (_hd : 2 ≤ d) {h x : ℝ} (hh : |h| < B.h₀)
    (hs0 : 0 < x * B.sVal h) (hs1 : x * B.sVal h < 1)
    (ht0 : 0 < x * B.tVal h) (ht1 : x * B.tVal h < 1) :
    HasDerivAt (B.Psi h)
      (2 * (B.alph h * (Jp' (B.p h) (x * B.sVal h) * B.sVal h)
          + (1 - B.alph h) * (Jp' (B.p h) (x * B.tVal h) * B.tVal h))
        - B.etaVal h * ((d : ℝ) * x ^ (d - 1))) x := by
  have hp := B.p_mem h hh
  have e1 : HasDerivAt (fun y : ℝ => Jp (B.p h) (y * B.sVal h))
      (Jp' (B.p h) (x * B.sVal h) * B.sVal h) x := by
    have := (hasDerivAt_Jp hp.1 hp.2 hs0 hs1).comp x
      ((hasDerivAt_id x).mul_const (B.sVal h))
    simpa [Function.comp_def] using this
  have e2 : HasDerivAt (fun y : ℝ => Jp (B.p h) (y * B.tVal h))
      (Jp' (B.p h) (x * B.tVal h) * B.tVal h) x := by
    have := (hasDerivAt_Jp hp.1 hp.2 ht0 ht1).comp x
      ((hasDerivAt_id x).mul_const (B.tVal h))
    simpa [Function.comp_def] using this
  have e3 : HasDerivAt (fun y : ℝ => B.etaVal h * y ^ d)
      (B.etaVal h * ((d : ℝ) * x ^ (d - 1))) x := (hasDerivAt_pow d x).const_mul _
  exact (((e1.const_mul (B.alph h)).add (e2.const_mul (1 - B.alph h))).const_mul
    (2 : ℝ)).sub e3 |>.sub_const _

/-- **`Ψ_h'(s_h) = 0`**, the first slope contact: the KKT equations at `s_h²` and `s_h t_h`
collapse the bracket to `s_h^{d-1}(2γ_h q_h - dη_h) = 0`. -/
theorem Psi_deriv_sVal (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) :
    2 * (B.alph h * (Jp' (B.p h) (B.sVal h * B.sVal h) * B.sVal h)
        + (1 - B.alph h) * (Jp' (B.p h) (B.sVal h * B.tVal h) * B.tVal h))
      - B.etaVal h * ((d : ℝ) * B.sVal h ^ (d - 1)) = 0 := by
  have hss := B.kkt_ss h hh
  have hst := B.kkt_st h hh
  have e1 : B.u h - h = B.sVal h := rfl
  have e2 : B.u h + h = B.tVal h := rfl
  rw [e1] at hss
  rw [e1, e2] at hst
  simp only [Fkkt, sub_eq_zero] at hss hst
  have hsq : B.sVal h * B.sVal h = B.sVal h ^ 2 := by ring
  have hη : B.etaVal h * ((d : ℝ) * B.sVal h ^ (d - 1))
      = 2 * B.gam h * B.qVal h * B.sVal h ^ (d - 1) := by
    rw [← mul_assoc, etaVal_mul_d hd]
  have p1 : B.sVal h * (B.sVal h ^ 2) ^ (d - 1) = B.sVal h ^ (d - 1) * B.sVal h ^ d := by
    have := self_mul_sq_pow hd (B.sVal h)
    rwa [hsq] at this
  have p2 : B.tVal h * (B.sVal h * B.tVal h) ^ (d - 1)
      = B.sVal h ^ (d - 1) * B.tVal h ^ d := mul_cross_pow hd _ _
  rw [hsq, hss, hst, hη, qVal]
  linear_combination (2 * B.gam h * B.alph h) * p1
    + (2 * B.gam h * (1 - B.alph h)) * p2

/-- **`Ψ_h'(t_h) = 0`**, the second slope contact, from the KKT equations at `s_h t_h` and
`t_h²`. -/
theorem Psi_deriv_tVal (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) :
    2 * (B.alph h * (Jp' (B.p h) (B.tVal h * B.sVal h) * B.sVal h)
        + (1 - B.alph h) * (Jp' (B.p h) (B.tVal h * B.tVal h) * B.tVal h))
      - B.etaVal h * ((d : ℝ) * B.tVal h ^ (d - 1)) = 0 := by
  have hst := B.kkt_st h hh
  have htt := B.kkt_tt h hh
  have e1 : B.u h - h = B.sVal h := rfl
  have e2 : B.u h + h = B.tVal h := rfl
  rw [e1, e2] at hst
  rw [e2] at htt
  simp only [Fkkt, sub_eq_zero] at hst htt
  have hts : B.tVal h * B.sVal h = B.sVal h * B.tVal h := mul_comm _ _
  have htq : B.tVal h * B.tVal h = B.tVal h ^ 2 := by ring
  have hη : B.etaVal h * ((d : ℝ) * B.tVal h ^ (d - 1))
      = 2 * B.gam h * B.qVal h * B.tVal h ^ (d - 1) := by
    rw [← mul_assoc, etaVal_mul_d hd]
  have p1 : B.tVal h * (B.tVal h ^ 2) ^ (d - 1) = B.tVal h ^ (d - 1) * B.tVal h ^ d := by
    have := self_mul_sq_pow hd (B.tVal h)
    rwa [htq] at this
  have p2 : B.sVal h * (B.sVal h * B.tVal h) ^ (d - 1)
      = B.tVal h ^ (d - 1) * B.sVal h ^ d := by
    have := mul_cross_pow hd (B.tVal h) (B.sVal h)
    rwa [mul_comm (B.tVal h) (B.sVal h)] at this
  rw [hts, htq, hst, htt, hη, qVal]
  linear_combination (2 * B.gam h * (1 - B.alph h)) * p1
    + (2 * B.gam h * B.alph h) * p2

/-! ## The normalisation constant -/

/-- **The closed form of the normalising constant**: `κ_h = 2 I_{p_h}(W_h) - η_h q_h`.

The paper defines `κ_h` only implicitly, by `Ψ_h(s_h) = 0` in
`eq:first-variation`, and does not state this evaluation; it follows in one line
from `Ψ_h(s_h) = Ψ_h(t_h) = 0` with `ν_h` supported on `{s_h, t_h}` together with
`𝓙_h(ν_h) = I_{p_h}(W_h)`.  An equivalent right-hand side is
`2I_{p_h}(W_h) - μ_h v q_h^v`, since `η_h = μ_h v q_h^{v-1}`; the graph-free form is what
every consumer uses. -/
theorem kappaVal_eq (hd : 2 ≤ d) {h : ℝ} (hh : |h| < B.h₀) :
    B.kappaVal h = 2 * B.IpScalar h - B.etaVal h * B.qVal h := by
  have _hd : 2 ≤ d := hd
  have hrow := B.rowBalance h hh
  have e1 : B.u h - h = B.sVal h := rfl
  have e2 : B.u h + h = B.tVal h := rfl
  rw [e1, e2] at hrow
  simp only [Mfun] at hrow
  have hid := qVal_mul_pow_sub B h
  simp only [qVal] at hid ⊢
  rw [kappaVal, IpScalar, etaVal]
  simp only [qVal]
  linear_combination (2 * (1 - B.alph h)) * hrow
    - (2 * (1 - B.alph h) * B.gam h / (d : ℝ)) * hid

end KKTFamily

end UpperTailOptimizers
