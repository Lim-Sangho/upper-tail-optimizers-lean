import UpperTailOptimizers.SingularEndpoint.Defs

/-!
# The three-node cubic and its closed-form integrals

This file is pure one-variable calculus; nothing from Section 7
enters it.  It supplies one of the two elementary ingredients replacing the analytic
Weierstrass division behind the increment expansions of `paper/singular_endpoint.tex`.

The three-node Lagrange interpolation remainder writes a `C³` function vanishing at
`z₁ < z₂ < z₃` as `f(z) = (f'''(ξ)/6)·(z - z₁)(z - z₂)(z - z₃)`, with no analyticity
needed.  Integrating that identity over `[z₁, z₂]` and `[z₂, z₃]` therefore requires the
integral of the node cubic `P(z) = (z - z₁)(z - z₂)(z - z₃)` over those two intervals, and
the point of this file is that both are available in closed form: with `a = z₂ - z₁` and
`b = z₃ - z₂`,

`∫_{z₁}^{z₂} P = a³(a + 2b)/12`  and  `∫_{z₂}^{z₃} P = -b³(b + 2a)/12`.

The signs are forced by the factorisation: on `(z₁, z₂)` the three factors are `+, -, -`,
so `P > 0` there, while on `(z₂, z₃)` they are `+, +, -`, so `P < 0`.  Those two sign
statements are what the sandwich estimate consumes, the closed forms being the weights.

## Contents

* `Pcube`, `PcubeAnti` — the node cubic `(z - z₁)(z - z₂)(z - z₃)` and the explicit
  polynomial antiderivative obtained by expanding it in elementary symmetric functions;
* `hasDerivAt_PcubeAnti` — `PcubeAnti` differentiates to `Pcube` at every point;
* `integral_Pcube` — the fundamental theorem of calculus for the pair, on an arbitrary
  oriented interval;
* `integral_Pcube_left`, `integral_Pcube_right` — the two closed forms displayed above;
* `Pcube_pos_of_mem_Ioo_left`, `Pcube_neg_of_mem_Ioo_right` — the two sign statements.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

/-- The node cubic `P(z) = (z - z₁)(z - z₂)(z - z₃)` of three-node interpolation. -/
noncomputable def Pcube (z1 z2 z3 z : ℝ) : ℝ := (z - z1) * (z - z2) * (z - z3)

/-- The explicit polynomial antiderivative of `Pcube z1 z2 z3`, obtained by expanding the
cubic as `z³ - e₁z² + e₂z - e₃` in the elementary symmetric functions of the nodes and
integrating term by term. -/
noncomputable def PcubeAnti (z1 z2 z3 z : ℝ) : ℝ :=
  z ^ 4 / 4 - (z1 + z2 + z3) * z ^ 3 / 3 + (z1 * z2 + z1 * z3 + z2 * z3) * z ^ 2 / 2
    - (z1 * z2 * z3) * z

/-- `PcubeAnti z1 z2 z3` is an antiderivative of `Pcube z1 z2 z3`. -/
theorem hasDerivAt_PcubeAnti (z1 z2 z3 z : ℝ) :
    HasDerivAt (PcubeAnti z1 z2 z3) (Pcube z1 z2 z3 z) z := by
  have h4 : HasDerivAt (fun z : ℝ => z ^ 4) (4 * z ^ 3) z := by
    simpa using hasDerivAt_pow 4 z
  have h3 : HasDerivAt (fun z : ℝ => z ^ 3) (3 * z ^ 2) z := by
    simpa using hasDerivAt_pow 3 z
  have h2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have h1 : HasDerivAt (fun z : ℝ => z) 1 z := hasDerivAt_id' z
  have key : HasDerivAt (PcubeAnti z1 z2 z3)
      (4 * z ^ 3 / 4 - (z1 + z2 + z3) * (3 * z ^ 2) / 3
        + (z1 * z2 + z1 * z3 + z2 * z3) * (2 * z) / 2 - (z1 * z2 * z3) * 1) z :=
    (((h4.div_const 4).sub ((h3.const_mul _).div_const 3)).add
      ((h2.const_mul _).div_const 2)).sub (h1.const_mul _)
  convert key using 1
  simp only [Pcube]
  ring

/-- The fundamental theorem of calculus for the node cubic, on an arbitrary oriented
interval. -/
theorem integral_Pcube (z1 z2 z3 u v : ℝ) :
    ∫ z in u..v, Pcube z1 z2 z3 z = PcubeAnti z1 z2 z3 v - PcubeAnti z1 z2 z3 u := by
  have hcont : Continuous (Pcube z1 z2 z3) := by
    unfold Pcube
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z _ => hasDerivAt_PcubeAnti z1 z2 z3 z) (hcont.intervalIntegrable u v)

/-- Closed form of the node cubic's integral over the left subinterval: with
`a = z₂ - z₁` and `b = z₃ - z₂`, it equals `a³(a + 2b)/12`. -/
theorem integral_Pcube_left (z1 z2 z3 : ℝ) :
    ∫ z in z1..z2, Pcube z1 z2 z3 z = (z2 - z1) ^ 3 * ((z2 - z1) + 2 * (z3 - z2)) / 12 := by
  rw [integral_Pcube]
  simp only [PcubeAnti]
  ring

/-- Closed form of the node cubic's integral over the right subinterval: with
`a = z₂ - z₁` and `b = z₃ - z₂`, it equals `-b³(b + 2a)/12`. -/
theorem integral_Pcube_right (z1 z2 z3 : ℝ) :
    ∫ z in z2..z3, Pcube z1 z2 z3 z
      = -((z3 - z2) ^ 3 * ((z3 - z2) + 2 * (z2 - z1)) / 12) := by
  rw [integral_Pcube]
  simp only [PcubeAnti]
  ring

/-- On the left subinterval `(z₁, z₂)` the node cubic is positive: its factors are
`+, -, -`.

Both node separations are taken as arguments so that the two sign lemmas have the same
shape at their call sites, but only `h23` is used: membership in `(z₁, z₂)` already forces
`z₁ < z₂`. -/
theorem Pcube_pos_of_mem_Ioo_left {z1 z2 z3 z : ℝ} (_h12 : z1 < z2) (h23 : z2 < z3)
    (hz : z ∈ Set.Ioo z1 z2) : 0 < Pcube z1 z2 z3 z := by
  obtain ⟨hlo, hhi⟩ := hz
  have ha : 0 < z - z1 := sub_pos.mpr hlo
  have hb : z - z2 < 0 := sub_neg.mpr hhi
  have hc : z - z3 < 0 := sub_neg.mpr (hhi.trans h23)
  have hab : (z - z1) * (z - z2) < 0 := mul_neg_of_pos_of_neg ha hb
  exact mul_pos_of_neg_of_neg hab hc

/-- On the right subinterval `(z₂, z₃)` the node cubic is negative: its factors are
`+, +, -`.

As in `Pcube_pos_of_mem_Ioo_left`, only one separation is used — here `h12`, since
membership in `(z₂, z₃)` already forces `z₂ < z₃`. -/
theorem Pcube_neg_of_mem_Ioo_right {z1 z2 z3 z : ℝ} (h12 : z1 < z2) (_h23 : z2 < z3)
    (hz : z ∈ Set.Ioo z2 z3) : Pcube z1 z2 z3 z < 0 := by
  obtain ⟨hlo, hhi⟩ := hz
  have ha : 0 < z - z1 := sub_pos.mpr (h12.trans hlo)
  have hb : 0 < z - z2 := sub_pos.mpr hlo
  have hc : z - z3 < 0 := sub_neg.mpr hhi
  exact mul_neg_of_pos_of_neg (mul_pos ha hb) hc

end SingularEndpoint

end UpperTailOptimizers
