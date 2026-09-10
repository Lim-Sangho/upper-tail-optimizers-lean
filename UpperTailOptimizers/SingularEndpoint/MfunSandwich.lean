import UpperTailOptimizers.SingularEndpoint.Sandwich
import UpperTailOptimizers.SingularEndpoint.FkktDeriv
import UpperTailOptimizers.SingularEndpoint.Family

/-!
# The cubic sandwich at `𝓜_{p,γ}` (Section 7, `paper/singular_endpoint.tex`)

`SingularEndpoint/Sandwich.lean` bounds the two increments of an antiderivative of a `C³` function
with three roots; this file instantiates it at the pair `(𝓜_{p,γ}, F_{p,γ})` of
`SingularEndpoint/Family.lean`, whose three roots are exactly the three edge values of a rank-one
KKT point `eq:three-value-kkt`.

The result is the quantitative form of `Mfun_lt_of_root_left` and `Mfun_lt_of_root_right`
(`SingularEndpoint/RowSign.lean`): those give the *signs* of

    A = 𝓜(z₁) - 𝓜(z₂),    B = 𝓜(z₃) - 𝓜(z₂),

which is what makes `α = B/(A+B)` lie in `(0,1)`; the sandwich here gives their *sizes*, in
terms of the node separations `a = z₂ - z₁` and `b = z₃ - z₂` and any two-sided bound on
`F_{p,γ}'''` over `[z₁, z₃]`.  Along the coalescing family `a` and `b` are both `Θ(h)`, so
the cubic factors `a³(a+2b)/12` and `b³(b+2a)/12` are `Θ(h⁴)` — this is where the `h⁴` of
the increment expansions comes from, and the pinching constant is
`F_{p,γ}'''(r_*) = d⁵/(d-1)²` by `Fkkt3_gammaStar_rStar`.

## Contents

* `Mfun_sandwich_left` — two-sided bounds on `𝓜(z₂) - 𝓜(z₁)`;
* `Mfun_sandwich_right` — two-sided bounds on `𝓜(z₃) - 𝓜(z₂)`;
* `node_gap_left`, `node_gap_right`, `cubic_factor_left`, `cubic_factor_right` — the node
  separations `a = 2hs`, `b = 2ht` at a coalescing triple and the resulting explicit `h⁴`
  cubic factors;
* `cubic_constant_left`, `cubic_constant_sum` — the limiting constants `2d³/3` and `4d³/3`
  at `h = 0`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

variable {d : ℕ}

/-- The derivative hypotheses of `SingularEndpoint/Sandwich.lean`, assembled for `F_{p,γ}` and its
antiderivative `𝓜_{p,γ}` on a closed subinterval of `(0,1)`. -/
private theorem sandwich_hyps (hd : 2 ≤ d) {p γ w v : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hw : 0 < w) (hv : v < 1) :
    (∀ x ∈ Set.Icc w v, HasDerivAt (Fkkt d p γ) (Fkkt1 d γ x) x) ∧
      (∀ x ∈ Set.Icc w v, HasDerivAt (Fkkt1 d γ) (Fkkt2 d γ x) x) ∧
      (∀ x ∈ Set.Icc w v, HasDerivAt (Fkkt2 d γ) (Fkkt3 d γ x) x) ∧
      (∀ x ∈ Set.Icc w v, HasDerivAt (Mfun d p γ) (Fkkt d p γ x) x) := by
  have hx : ∀ x ∈ Set.Icc w v, 0 < x ∧ x < 1 := fun x hx =>
    ⟨lt_of_lt_of_le hw hx.1, lt_of_le_of_lt hx.2 hv⟩
  exact ⟨fun x h => hasDerivAt_Fkkt' hd hp0 hp1 (hx x h).1 (hx x h).2,
    fun x h => hasDerivAt_Fkkt1 hd (hx x h).1 (hx x h).2,
    fun x h => hasDerivAt_Fkkt2 hd (hx x h).1 (hx x h).2,
    fun x h => hasDerivAt_Mfun hd hp0 hp1 (hx x h).1 (hx x h).2⟩

/-- **The left increment of `𝓜_{p,γ}`.**

With `a = z₂ - z₁` and `b = z₃ - z₂`, and `m ≤ F_{p,γ}''' ≤ M` on `[z₁, z₃]`,

    m/6 · a³(a+2b)/12  ≤  𝓜(z₂) - 𝓜(z₁)  ≤  M/6 · a³(a+2b)/12.

Negating gives `A = 𝓜(z₁) - 𝓜(z₂)`, which `Mfun_lt_of_root_left` shows is negative. -/
theorem Mfun_sandwich_left (hd : 2 ≤ d) {p γ z₁ z₂ z₃ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h₁ : 0 < z₁) (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃) (h₃ : z₃ < 1)
    (e₁ : Fkkt d p γ z₁ = 0) (e₂ : Fkkt d p γ z₂ = 0) (e₃ : Fkkt d p γ z₃ = 0)
    {m M : ℝ} (hm : ∀ x ∈ Set.Icc z₁ z₃, m ≤ Fkkt3 d γ x)
    (hM : ∀ x ∈ Set.Icc z₁ z₃, Fkkt3 d γ x ≤ M) :
    m / 6 * ((z₂ - z₁) ^ 3 * ((z₂ - z₁) + 2 * (z₃ - z₂)) / 12)
        ≤ Mfun d p γ z₂ - Mfun d p γ z₁ ∧
      Mfun d p γ z₂ - Mfun d p γ z₁
        ≤ M / 6 * ((z₂ - z₁) ^ 3 * ((z₂ - z₁) + 2 * (z₃ - z₂)) / 12) := by
  obtain ⟨hf, hf₁, hf₂, hF⟩ := sandwich_hyps hd (γ := γ) hp0 hp1 h₁ h₃
  exact increment_sandwich_left hf hf₁ hf₂ hF ⟨le_rfl, (h₁₂.trans h₂₃).le⟩
    ⟨h₁₂.le, h₂₃.le⟩ ⟨(h₁₂.trans h₂₃).le, le_rfl⟩ h₁₂ h₂₃ e₁ e₂ e₃ hm hM

/-- **The right increment of `𝓜_{p,γ}`.**

    M/6 · (-b³(b+2a)/12)  ≤  𝓜(z₃) - 𝓜(z₂)  ≤  m/6 · (-b³(b+2a)/12),

with `m` and `M` exchanged because the node cubic is negative on `(z₂, z₃)`.  This increment
is `B` of `eq:block-proportion-formula`. -/
theorem Mfun_sandwich_right (hd : 2 ≤ d) {p γ z₁ z₂ z₃ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h₁ : 0 < z₁) (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃) (h₃ : z₃ < 1)
    (e₁ : Fkkt d p γ z₁ = 0) (e₂ : Fkkt d p γ z₂ = 0) (e₃ : Fkkt d p γ z₃ = 0)
    {m M : ℝ} (hm : ∀ x ∈ Set.Icc z₁ z₃, m ≤ Fkkt3 d γ x)
    (hM : ∀ x ∈ Set.Icc z₁ z₃, Fkkt3 d γ x ≤ M) :
    M / 6 * (-((z₃ - z₂) ^ 3 * ((z₃ - z₂) + 2 * (z₂ - z₁)) / 12))
        ≤ Mfun d p γ z₃ - Mfun d p γ z₂ ∧
      Mfun d p γ z₃ - Mfun d p γ z₂
        ≤ m / 6 * (-((z₃ - z₂) ^ 3 * ((z₃ - z₂) + 2 * (z₂ - z₁)) / 12)) := by
  obtain ⟨hf, hf₁, hf₂, hF⟩ := sandwich_hyps hd (γ := γ) hp0 hp1 h₁ h₃
  exact increment_sandwich_right hf hf₁ hf₂ hF ⟨le_rfl, (h₁₂.trans h₂₃).le⟩
    ⟨h₁₂.le, h₂₃.le⟩ ⟨(h₁₂.trans h₂₃).le, le_rfl⟩ h₁₂ h₂₃ e₁ e₂ e₃ hm hM

/-! ## The node separations along a coalescing triple

For the family the three nodes are `s²`, `st`, `t²` with `s = u - h` and `t = u + h`, so the
separations factor through the half-gap: `a = 2hs` and `b = 2ht`.  These two identities are
what turn the cubic factors above into explicit multiples of `h⁴`. -/

/-- `st - s² = (t - s)·s`, i.e. `a = 2hs` when `s = u - h`, `t = u + h`. -/
theorem node_gap_left (u h : ℝ) :
    (u - h) * (u + h) - (u - h) ^ 2 = 2 * h * (u - h) := by ring

/-- `t² - st = (t - s)·t`, i.e. `b = 2ht`. -/
theorem node_gap_right (u h : ℝ) :
    (u + h) ^ 2 - (u - h) * (u + h) = 2 * h * (u + h) := by ring

/-- The left cubic factor at the coalescing nodes: `a³(a+2b)/12 = 4h⁴s³(s+2t)/3`. -/
theorem cubic_factor_left (u h : ℝ) :
    ((u - h) * (u + h) - (u - h) ^ 2) ^ 3 *
        (((u - h) * (u + h) - (u - h) ^ 2) + 2 * ((u + h) ^ 2 - (u - h) * (u + h))) / 12
      = 4 * h ^ 4 * (u - h) ^ 3 * ((u - h) + 2 * (u + h)) / 3 := by
  rw [node_gap_left, node_gap_right]; ring

/-- The right cubic factor at the coalescing nodes: `b³(b+2a)/12 = 4h⁴t³(t+2s)/3`. -/
theorem cubic_factor_right (u h : ℝ) :
    ((u + h) ^ 2 - (u - h) * (u + h)) ^ 3 *
        (((u + h) ^ 2 - (u - h) * (u + h)) + 2 * ((u - h) * (u + h) - (u - h) ^ 2)) / 12
      = 4 * h ^ 4 * (u + h) ^ 3 * ((u + h) + 2 * (u - h)) / 3 := by
  rw [node_gap_left, node_gap_right]; ring

/-! ## The limiting constants

At `h = 0` the two nodes merge at `u_*`, and pinching `m` and `M` onto the non-degeneracy
constant `F'''(r_*) = d⁵/(d-1)²` of `Fkkt3_gammaStar_rStar` turns the bounds above into the
paper's coefficients.  These three identities are what make the route to
the increment expansions land on the paper's numbers rather than merely on the right
*order*: `A ≈ -2d³h⁴/3`, `B ≈ -2d³h⁴/3`, `A + B ≈ -4d³h⁴/3`. -/

/-- `K/6 · 4u_*³(u_* + 2u_*)/3 = 2d³/3`, with `K = d⁵/(d-1)²`.

This is the `h⁴` coefficient of `𝓜(z₂) - 𝓜(z₁)`, so `A = 𝓜(z₁) - 𝓜(z₂)` has coefficient
`-2d³/3` — the paper's increment expansions. -/
theorem cubic_constant_left (hd : 2 ≤ d) :
    (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 6 * (4 * uStar d ^ 3 * (uStar d + 2 * uStar d) / 3)
      = 2 * (d : ℝ) ^ 3 / 3 := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hd1 : (d : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h4 : uStar d ^ 4 = ((d : ℝ) - 1) ^ 2 / (d : ℝ) ^ 2 := by
    have hsq : uStar d ^ 4 = (uStar d ^ 2) ^ 2 := by ring
    rw [hsq, uStar_sq hd, rStar_eq, div_pow]
  have hstep : 4 * uStar d ^ 3 * (uStar d + 2 * uStar d) / 3 = 4 * uStar d ^ 4 := by ring
  rw [hstep, h4]
  field_simp
  ring

/-- The right factor `4h⁴t³(t+2s)/3` becomes the same expression at `h = 0`, where `s = t`,
so `A + B` has coefficient `-4d³/3` — the denominator expansion of
the increment expansions, from which `α_0 = 1/2`. -/
theorem cubic_constant_sum (hd : 2 ≤ d) :
    (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 6 * (4 * uStar d ^ 3 * (uStar d + 2 * uStar d) / 3) +
        (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 6 * (4 * uStar d ^ 3 * (uStar d + 2 * uStar d) / 3)
      = 4 * (d : ℝ) ^ 3 / 3 := by
  rw [cubic_constant_left hd]; ring

end SingularEndpoint

end UpperTailOptimizers
