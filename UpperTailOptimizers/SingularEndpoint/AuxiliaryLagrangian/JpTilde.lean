import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.Continuation
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.Identities

/-!
# The continued entropy `J̃_{p_*}` and its modulus (Section 5, `paper/sections/singular.tex`)

The one-dimensional law problem of `sec:auxiliary-lagrangian` pairs a
probability measure on `[0,2]` with itself, so the entropy density is evaluated at products
`x y` ranging over `[0,4]`.  Since `J_{p_*}` has a graphon meaning only on `[0,1]`, the
paper replaces it by the real continuation `eq:entropy-continuation`,

```
J̃_{p_*}(z) := J_{p_*}(r_*) + β_d (z^d - r_*^d) + Γ̃_d(z),   0 ≤ z ≤ 4,
```

built from the continued gap `Γ̃_d` of `SingularEndpoint/AuxiliaryLagrangian/Continuation.lean`.  Two properties are
what the law argument uses, and both are proved here: the continuation *agrees* with
`J_{p_*}` on `[0,1]` (`JpTilde_of_le_one`), so nothing is lost where the original is
defined; and it satisfies the logarithmic modulus of continuity

```
|J̃_{p_*}(z) - J̃_{p_*}(z')| ≤ C_d |z - z'| (1 + log⁺(1/|z - z'|))     (z, z' ∈ [0,4]),
```

which supplies the only regularity that the frozen-tail pairing step in the Lean proof of
`lem:auxiliary-lagrangian-bound` needs.  The paper does not display this
quantitative modulus: `lem:continuation-kernel-bounds` records the `1/2`-Hölder bound
`|J̃_{p_h}(z) - J̃_{p_h}(z')| ≤ C_d|z - z'|^{1/2}` on `[0,4]`, together with uniform bounds.
The explicit `τ(1 + log⁺(1/τ))` modulus proved here is stronger, and implies that Hölder bound
for `J̃_{p_*}` on `[0,4]`.

One route to the modulus integrates
`|ℓ_* - ℓ(z)| ≤ C(1 + |log z| + |log(1-z)|)` over an interval of length `τ`, quoting
`∫₀^τ |log| = τ(1 + log(1/τ))`.  Here the same
bound is obtained *without any integration*, from the two elementary inequalities

```
(a-b) log(a-b) ≤ a log a - b log b ≤ a - b        (0 ≤ b ≤ a ≤ 1)
```

(`sub_mul_log_le`, superadditivity of `x log x`; and `mul_log_sub_le`, which is
`log(a/b) ≤ a/b - 1` after multiplying by `b`).  Writing
`J_p(u) = u log u + (1-u) log(1-u) - u log p - (1-u) log(1-p)` reduces the `[0,1]` half of
the modulus to those two inequalities applied to `u log u` and to its reflection.  Above
`1` the continuation is the polynomial `J_{p_*}(1) + β_d(u^d - 1) + (u-1)^2`
(`JpTilde_of_one_le`), hence Lipschitz on `[1,4]`; the halves concatenate across `z = 1`
because `τ ↦ τ(1 + log⁺(1/τ))` is nondecreasing, which is itself a corollary of
`mul_log_sub_le`.

`log⁺(1/τ)` is written `max 0 (Real.log (1 / τ))`, which is `Real.posLog (1/τ)` by
`Real.posLog_def`; the explicit `max` is kept in the public statements so that they read
without the scoped `log⁺` notation.

## Contents

* `JpTilde` — the continued entropy `J̃_{p_*}` of `eq:entropy-continuation`, with its two
  family formulas `JpTilde_of_le_one` and `JpTilde_of_one_le`;
* `continuousOn_JpTilde` — `J̃_{p_*}` is continuous on `[0,4]`;
* `exists_JpTilde_modulus_Icc_zero_one` — the logarithmic modulus on `[0,1]`;
* `exists_JpTilde_lipschitzOn_Icc_one_four` — the plain Lipschitz bound on `[1,4]`;
* `exists_JpTilde_modulus` — **the logarithmic modulus** on the whole of `[0,4]`.
-/

namespace UpperTailOptimizers

open Real

variable {d : ℕ}

/-! ## The continued entropy -/

/-- The **continued entropy** `J̃_{p_*}` of `eq:entropy-continuation`:
`J̃_{p_*}(z) = J_{p_*}(r_*) + β_d (z^d - r_*^d) + Γ̃_d(z)` for `0 ≤ z ≤ 4`.

It is not an extension of `J_{p_*}` by a formula — only the singular endpoint gap is continued — but
it *does* agree with `J_{p_*}` on `[0,1]`, which is `JpTilde_of_le_one`. -/
noncomputable def JpTilde (d : ℕ) (u : ℝ) : ℝ :=
  Jp (pStar d) (rStar d) + betaD d * (u ^ d - rStar d ^ d) + GamTilde d u

/-- **The continuation agrees with `J_{p_*}` on `[0,1]`.**  This is the point of
`eq:entropy-continuation`: it is the singular endpoint identity
`eq:endpoint-supporting-gap` read backwards, since `Γ̃_d = Γ_d` below `1`. -/
theorem JpTilde_of_le_one {u : ℝ} (hu : u ≤ 1) : JpTilde d u = Jp (pStar d) u := by
  rw [JpTilde, GamTilde_of_le_one hu]
  exact (Jp_pStar_eq_gam d u).symm

/-- Above `1` the continuation of `eq:entropy-continuation` is the polynomial
`J_{p_*}(1) + β_d (u^d - 1) + (u-1)^2`: the constant `J_{p_*}(r_*) - β_d r_*^d` and the
value `Γ_d(1)` recombine into `J_{p_*}(1) - β_d`.  This is what makes `J̃_{p_*}` Lipschitz
on `[1,4]`. -/
theorem JpTilde_of_one_le {u : ℝ} (hu : 1 ≤ u) :
    JpTilde d u = Jp (pStar d) 1 + betaD d * (u ^ d - 1) + (u - 1) ^ 2 := by
  rcases eq_or_lt_of_le hu with h | h
  · rw [← h, JpTilde_of_le_one le_rfl, one_pow]
    ring
  · rw [JpTilde, GamTilde_of_one_lt h, Gam, one_pow]
    ring

/-- `J̃_{p_*}` is continuous on `[0,4]`, as asserted after `eq:entropy-continuation`: it is
a polynomial plus the continuous `Γ̃_d`. -/
theorem continuousOn_JpTilde (hd : 2 ≤ d) : ContinuousOn (JpTilde d) (Set.Icc 0 4) := by
  unfold JpTilde
  exact (continuousOn_const.add
    (continuousOn_const.mul ((continuousOn_pow d).sub continuousOn_const))).add
      (continuousOn_GamTilde hd)

/-! ## The modulus `ω(τ) = τ (1 + log⁺(1/τ))`

The right-hand side of the logarithmic modulus bound, without the constant.  Only four facts
about it are needed: it vanishes at `0`, it dominates the identity, it is nondecreasing,
and it equals `τ - τ log τ` on `[0,1]`. -/

/-- The modulus `ω(τ) = τ (1 + log⁺(1/τ))` of `exists_JpTilde_modulus`. -/
private noncomputable def logMod (τ : ℝ) : ℝ := τ * (1 + max 0 (Real.log (1 / τ)))

private theorem logMod_nonneg {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ logMod τ := by
  have h : (0 : ℝ) ≤ max 0 (Real.log (1 / τ)) := le_max_left _ _
  exact mul_nonneg hτ (by linarith)

/-- `τ ≤ ω(τ)`: the modulus is at least the identity, so a Lipschitz bound implies a
modulus bound. -/
private theorem self_le_logMod {τ : ℝ} (hτ : 0 ≤ τ) : τ ≤ logMod τ := by
  have h : (0 : ℝ) ≤ max 0 (Real.log (1 / τ)) := le_max_left _ _
  have : 0 ≤ τ * max 0 (Real.log (1 / τ)) := mul_nonneg hτ h
  unfold logMod
  nlinarith

/-- On `[0,1]` the modulus is `ω(τ) = τ - τ log τ` (also at `τ = 0`, where Lean's
`log 0 = 0`). -/
private theorem logMod_eq_of_le_one {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    logMod τ = τ - τ * Real.log τ := by
  have hlog : Real.log τ ≤ 0 := Real.log_nonpos hτ0 hτ1
  unfold logMod
  rw [one_div, Real.log_inv, max_eq_right (by linarith : (0 : ℝ) ≤ -Real.log τ)]
  ring

/-- Above `1` the positive part kills the logarithm and `ω(τ) = τ`. -/
private theorem logMod_eq_of_one_le {τ : ℝ} (hτ : 1 ≤ τ) : logMod τ = τ := by
  have hlog : (0 : ℝ) ≤ Real.log τ := Real.log_nonneg hτ
  unfold logMod
  rw [one_div, Real.log_inv, max_eq_left (by linarith : -Real.log τ ≤ (0 : ℝ))]
  ring

/-! ## The two elementary inequalities for `x log x` -/

/-- `a log a - b log b ≤ a - b` for `0 ≤ b ≤ a ≤ 1`.

Split as `(a-b) log a + b (log a - log b)`: the first summand is `≤ 0` because `log a ≤ 0`,
and the second is `b log(a/b) ≤ b (a/b - 1) = a - b` by `Real.log_le_sub_one_of_pos`. -/
private theorem mul_log_sub_le {a b : ℝ} (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    a * Real.log a - b * Real.log b ≤ a - b := by
  have ha0 : 0 ≤ a := le_trans hb0 hba
  have hla : Real.log a ≤ 0 := Real.log_nonpos ha0 ha1
  rcases eq_or_lt_of_le hb0 with hb | hb0'
  · rw [← hb]
    simp only [zero_mul, sub_zero, Real.log_zero]
    nlinarith [mul_nonneg ha0 (neg_nonneg.mpr hla)]
  · have hapos : 0 < a := lt_of_lt_of_le hb0' hba
    have h1 : (a - b) * Real.log a ≤ 0 := by nlinarith
    have hdiv : Real.log a - Real.log b ≤ a / b - 1 := by
      rw [← Real.log_div (ne_of_gt hapos) (ne_of_gt hb0')]
      exact Real.log_le_sub_one_of_pos (div_pos hapos hb0')
    have h2 : b * (Real.log a - Real.log b) ≤ b * (a / b - 1) :=
      mul_le_mul_of_nonneg_left hdiv hb0'.le
    have h3 : b * (a / b - 1) = a - b := by field_simp
    rw [h3] at h2
    linarith

/-- `(a-b) log(a-b) ≤ a log a - b log b` for `0 ≤ b ≤ a ≤ 1`: superadditivity of
`x ↦ x log x`, proved by replacing both logarithms on the left by the larger `log a`.

The hypothesis `a ≤ 1` is not needed (superadditivity holds for all `0 ≤ b ≤ a`); it is
kept so that the lemma pairs with `mul_log_sub_le`, where it is essential. -/
private theorem sub_mul_log_le {a b : ℝ} (hb0 : 0 ≤ b) (hba : b ≤ a) (_ha1 : a ≤ 1) :
    (a - b) * Real.log (a - b) ≤ a * Real.log a - b * Real.log b := by
  have hτ0 : (0 : ℝ) ≤ a - b := by linarith
  have hτa : a - b ≤ a := by linarith
  have h1 : (a - b) * Real.log (a - b) ≤ (a - b) * Real.log a := by
    rcases eq_or_lt_of_le hτ0 with h | h
    · rw [← h]; simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log h hτa) hτ0
  have h2 : b * Real.log b ≤ b * Real.log a := by
    rcases eq_or_lt_of_le hb0 with h | h
    · rw [← h]; simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log h hba) hb0
  have h3 : (a - b) * Real.log a + b * Real.log a = a * Real.log a := by ring
  linarith

/-- The two-sided form: `|a log a - b log b| ≤ ω(a - b)` for `0 ≤ b ≤ a ≤ 1`. -/
private theorem abs_mul_log_sub_le {a b : ℝ} (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    |a * Real.log a - b * Real.log b| ≤ logMod (a - b) := by
  have hτ0 : (0 : ℝ) ≤ a - b := by linarith
  have hτ1 : a - b ≤ 1 := by linarith
  have hlog : Real.log (a - b) ≤ 0 := Real.log_nonpos hτ0 hτ1
  have hneg : (a - b) * Real.log (a - b) ≤ 0 := by nlinarith
  have hB := mul_log_sub_le hb0 hba ha1
  have hA := sub_mul_log_le hb0 hba ha1
  rw [logMod_eq_of_le_one hτ0 hτ1, abs_le]
  constructor <;> linarith

/-- The reflected form: `|(1-a) log(1-a) - (1-b) log(1-b)| ≤ ω(a - b)`, obtained from
`abs_mul_log_sub_le` at the reflected pair `1-a ≤ 1-b`. -/
private theorem abs_one_sub_mul_log_sub_le {a b : ℝ} (hb0 : 0 ≤ b) (hba : b ≤ a)
    (ha1 : a ≤ 1) :
    |(1 - a) * Real.log (1 - a) - (1 - b) * Real.log (1 - b)| ≤ logMod (a - b) := by
  have h := abs_mul_log_sub_le (a := 1 - b) (b := 1 - a) (by linarith) (by linarith)
    (by linarith)
  have he : (1 - b) - (1 - a) = a - b := by ring
  rw [he] at h
  rwa [abs_sub_comm]

/-! ## The modulus is nondecreasing -/

/-- `ω` is nondecreasing on `[0,∞)`.  On `[0,1]` this is exactly `mul_log_sub_le` read as
`a - a log a ≤ b - b log b`; above `1` the modulus is the identity; and the two ranges are
joined through `ω(1) = 1`. -/
private theorem logMod_mono {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) : logMod a ≤ logMod b := by
  have hb0 : 0 ≤ b := le_trans ha0 hab
  rcases le_total b 1 with hb1 | hb1
  · have ha1 : a ≤ 1 := le_trans hab hb1
    rw [logMod_eq_of_le_one ha0 ha1, logMod_eq_of_le_one hb0 hb1]
    have := mul_log_sub_le ha0 hab hb1
    linarith
  · rcases le_total a 1 with ha1 | ha1
    · have h1 : logMod a ≤ 1 := by
        rw [logMod_eq_of_le_one ha0 ha1]
        have h := mul_log_sub_le ha0 ha1 le_rfl
        rw [Real.log_one, mul_zero] at h
        linarith
      rw [logMod_eq_of_one_le hb1]
      linarith
    · rw [logMod_eq_of_one_le ha1, logMod_eq_of_one_le (le_trans ha1 hab)]
      exact hab

/-! ## The `[0,1]` half of the logarithmic modulus -/

/-- `x log(x/y) = x log x - x log y` for `x ≥ 0`, `y > 0` — including `x = 0`, where both
sides vanish under Lean's `log 0 = 0`. -/
private theorem mul_log_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x * Real.log (x / y) = x * Real.log x - x * Real.log y := by
  rcases eq_or_lt_of_le hx with h | hx0
  · rw [← h]; ring
  · rw [Real.log_div (ne_of_gt hx0) (ne_of_gt hy)]; ring

/-- The entropy split into its two `x log x` pieces and an affine remainder:
`J_p(u) = u log u + (1-u) log(1-u) - u log p - (1-u) log(1-p)` on `[0,1]`. -/
private theorem Jp_eq_mul_log {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    Jp p u = u * Real.log u + (1 - u) * Real.log (1 - u)
      - u * Real.log p - (1 - u) * Real.log (1 - p) := by
  rw [Jp, mul_log_div hu0 hp0,
    mul_log_div (by linarith : (0 : ℝ) ≤ 1 - u) (by linarith : (0 : ℝ) < 1 - p)]
  ring

/-- The scalar modulus for `J_p` on `[0,1]`, with the explicit constant
`2 + |log p| + |log(1-p)|`: the two `x log x` pieces each contribute `ω(a-b)`, and the
affine remainder contributes `(a-b)(|log p| + |log(1-p)|) ≤ ω(a-b)(|log p| + |log(1-p)|)`. -/
private theorem abs_Jp_sub_le_logMod {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {a b : ℝ} (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    |Jp p a - Jp p b| ≤ (2 + |Real.log p| + |Real.log (1 - p)|) * logMod (a - b) := by
  have ha0 : 0 ≤ a := le_trans hb0 hba
  have hb1 : b ≤ 1 := le_trans hba ha1
  have hτ0 : (0 : ℝ) ≤ a - b := by linarith
  have hτlog : a - b ≤ logMod (a - b) := self_le_logMod hτ0
  have hdec : Jp p a - Jp p b
      = (a * Real.log a - b * Real.log b)
        + ((1 - a) * Real.log (1 - a) - (1 - b) * Real.log (1 - b))
        - (a - b) * Real.log p + (a - b) * Real.log (1 - p) := by
    rw [Jp_eq_mul_log hp0 hp1 ha0 ha1, Jp_eq_mul_log hp0 hp1 hb0 hb1]
    ring
  have h3 : |(a - b) * Real.log p| ≤ logMod (a - b) * |Real.log p| := by
    rw [abs_mul, abs_of_nonneg hτ0]
    exact mul_le_mul_of_nonneg_right hτlog (abs_nonneg _)
  have h4 : |(a - b) * Real.log (1 - p)| ≤ logMod (a - b) * |Real.log (1 - p)| := by
    rw [abs_mul, abs_of_nonneg hτ0]
    exact mul_le_mul_of_nonneg_right hτlog (abs_nonneg _)
  obtain ⟨h1l, h1r⟩ := abs_le.mp (abs_mul_log_sub_le hb0 hba ha1)
  obtain ⟨h2l, h2r⟩ := abs_le.mp (abs_one_sub_mul_log_sub_le hb0 hba ha1)
  obtain ⟨h3l, h3r⟩ := abs_le.mp h3
  obtain ⟨h4l, h4r⟩ := abs_le.mp h4
  rw [hdec, abs_le]
  constructor <;> linarith

/-- **The logarithmic modulus on `[0,1]`.**  There is `C > 0` with
`|J̃_{p_*}(z) - J̃_{p_*}(z')| ≤ C |z - z'| (1 + log⁺(1/|z - z'|))` for `z, z' ∈ [0,1]`.

Below `1` the continuation *is* `J_{p_*}`, so this is the scalar estimate
`abs_Jp_sub_le_logMod` at `p = p_*`. -/
theorem exists_JpTilde_modulus_Icc_zero_one (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Icc (0 : ℝ) 1, ∀ z' ∈ Set.Icc (0 : ℝ) 1,
      |JpTilde d z - JpTilde d z'|
        ≤ C * |z - z'| * (1 + max 0 (Real.log (1 / |z - z'|))) := by
  have hp0 := pStar_pos hd
  have hp1 := pStar_lt_one hd
  refine ⟨2 + |Real.log (pStar d)| + |Real.log (1 - pStar d)|, by positivity, ?_⟩
  have key : ∀ a b : ℝ, 0 ≤ b → b ≤ a → a ≤ 1 →
      |JpTilde d a - JpTilde d b|
        ≤ (2 + |Real.log (pStar d)| + |Real.log (1 - pStar d)|)
            * |a - b| * (1 + max 0 (Real.log (1 / |a - b|))) := by
    intro a b hb0 hba ha1
    have h := abs_Jp_sub_le_logMod hp0 hp1 hb0 hba ha1
    unfold logMod at h
    rw [JpTilde_of_le_one ha1, JpTilde_of_le_one (le_trans hba ha1),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b), mul_assoc]
    exact h
  intro z hz z' hz'
  rcases le_total z' z with h | h
  · exact key z z' hz'.1 h hz.2
  · rw [abs_sub_comm (JpTilde d z) (JpTilde d z'), abs_sub_comm z z']
    exact key z' z hz.1 h hz'.2

/-! ## The `[1,4]` half: a plain Lipschitz bound -/

/-- `|x^n - y^n| ≤ n M^n |x - y|` on `[0,M]` for `M ≥ 1`, by induction on `n` through
`x^{n+1} - y^{n+1} = x (x^n - y^n) + (x - y) y^n`.

`NonexceptionalEndpoint/QuadraticGrowth/PowBounds.lean` has the `M = 1` case (`abs_pow_sub_pow_le`); here the
arguments live in `[1,4]`, so a version with a general bound is needed. -/
private theorem abs_pow_sub_pow_le_of_le {M : ℝ} (hM : 1 ≤ M) :
    ∀ (n : ℕ) {x y : ℝ}, 0 ≤ x → x ≤ M → 0 ≤ y → y ≤ M →
      |x ^ n - y ^ n| ≤ n * M ^ n * |x - y| := by
  intro n
  induction n with
  | zero => intro x y _ _ _ _; simp
  | succ n ih =>
    intro x y hx0 hxM hy0 hyM
    have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
    have hMn : (0 : ℝ) ≤ M ^ n := pow_nonneg hM0 n
    have ht : (0 : ℝ) ≤ |x - y| := abs_nonneg _
    have h1 := ih hx0 hxM hy0 hyM
    have hxa : |x| ≤ M := by rwa [abs_of_nonneg hx0]
    have hya : |y ^ n| ≤ M ^ n := by
      rw [abs_of_nonneg (pow_nonneg hy0 n)]
      exact pow_le_pow_left₀ hy0 hyM n
    have hstep : |x ^ (n + 1) - y ^ (n + 1)|
        ≤ M * ((n : ℝ) * M ^ n * |x - y|) + |x - y| * M ^ n := by
      have hkey : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by
        ring
      calc |x ^ (n + 1) - y ^ (n + 1)|
          = |x * (x ^ n - y ^ n) + (x - y) * y ^ n| := by rw [hkey]
        _ ≤ |x * (x ^ n - y ^ n)| + |(x - y) * y ^ n| := abs_add_le _ _
        _ = |x| * |x ^ n - y ^ n| + |x - y| * |y ^ n| := by rw [abs_mul, abs_mul]
        _ ≤ M * ((n : ℝ) * M ^ n * |x - y|) + |x - y| * M ^ n :=
            add_le_add (mul_le_mul hxa h1 (abs_nonneg _) hM0)
              (mul_le_mul_of_nonneg_left hya ht)
    refine le_trans hstep ?_
    have hpow : M ^ (n + 1) = M ^ n * M := pow_succ M n
    push_cast
    rw [hpow]
    nlinarith [mul_nonneg (mul_nonneg ht hMn) (sub_nonneg.mpr hM)]

/-- **The `[1,4]` half of the logarithmic modulus.**  On `[1,4]` the continuation is the
polynomial of `JpTilde_of_one_le`, hence Lipschitz: `L = β_d d 4^d + 6` works. -/
theorem exists_JpTilde_lipschitzOn_Icc_one_four (hd : 2 ≤ d) :
    ∃ L : ℝ, 0 < L ∧ ∀ z ∈ Set.Icc (1 : ℝ) 4, ∀ z' ∈ Set.Icc (1 : ℝ) 4,
      |JpTilde d z - JpTilde d z'| ≤ L * |z - z'| := by
  have hb : 0 < betaD d := betaD_pos hd
  have hd0 : (0 : ℝ) < (d : ℝ) := dpos hd
  have h4 : (0 : ℝ) < 4 ^ d := by positivity
  refine ⟨betaD d * ((d : ℝ) * 4 ^ d) + 6, by nlinarith [mul_pos hb (mul_pos hd0 h4)], ?_⟩
  intro z hz z' hz'
  have hpow : |z ^ d - z' ^ d| ≤ (d : ℝ) * 4 ^ d * |z - z'| :=
    abs_pow_sub_pow_le_of_le (by norm_num : (1 : ℝ) ≤ 4) d (by linarith [hz.1]) hz.2
      (by linarith [hz'.1]) hz'.2
  have hq : |(z - z') * (z + z' - 2)| ≤ 6 * |z - z'| := by
    have habs : |z + z' - 2| ≤ 6 := by
      rw [abs_le]
      exact ⟨by linarith [hz.1, hz'.1], by linarith [hz.2, hz'.2]⟩
    rw [abs_mul]
    calc |z - z'| * |z + z' - 2| ≤ |z - z'| * 6 :=
          mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      _ = 6 * |z - z'| := by ring
  have hdiff : JpTilde d z - JpTilde d z'
      = betaD d * (z ^ d - z' ^ d) + (z - z') * (z + z' - 2) := by
    rw [JpTilde_of_one_le hz.1, JpTilde_of_one_le hz'.1]
    ring
  rw [hdiff]
  calc |betaD d * (z ^ d - z' ^ d) + (z - z') * (z + z' - 2)|
      ≤ |betaD d * (z ^ d - z' ^ d)| + |(z - z') * (z + z' - 2)| := abs_add_le _ _
    _ = betaD d * |z ^ d - z' ^ d| + |(z - z') * (z + z' - 2)| := by
        rw [abs_mul, abs_of_pos hb]
    _ ≤ betaD d * ((d : ℝ) * 4 ^ d * |z - z'|) + 6 * |z - z'| :=
        add_le_add (mul_le_mul_of_nonneg_left hpow hb.le) hq
    _ = (betaD d * ((d : ℝ) * 4 ^ d) + 6) * |z - z'| := by ring

/-! ## The logarithmic modulus -/

/-- **The logarithmic modulus**.  There is `C_d > 0`
such that

`|J̃_{p_*}(z) - J̃_{p_*}(z')| ≤ C_d |z - z'| (1 + log⁺(1/|z - z'|))`   for `z, z' ∈ [0,4]`,

where `log⁺ t = max 0 (log t)`.  This is the only regularity of the continued entropy that
the frozen-tail pairing step in the proof of `lem:auxiliary-lagrangian-bound` uses.

The two halves `exists_JpTilde_modulus_Icc_zero_one` and
`exists_JpTilde_lipschitzOn_Icc_one_four` concatenate across `z = 1` by the triangle
inequality: the Lipschitz half is absorbed because `τ ≤ ω(τ)`, and both pieces are absorbed
into `ω(|z - z'|)` because `ω` is nondecreasing (`logMod_mono`). -/
theorem exists_JpTilde_modulus (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Icc (0 : ℝ) 4, ∀ z' ∈ Set.Icc (0 : ℝ) 4,
      |JpTilde d z - JpTilde d z'|
        ≤ C * |z - z'| * (1 + max 0 (Real.log (1 / |z - z'|))) := by
  obtain ⟨C₁, hC₁, hmod⟩ := exists_JpTilde_modulus_Icc_zero_one hd
  obtain ⟨L, hL, hlip⟩ := exists_JpTilde_lipschitzOn_Icc_one_four hd
  refine ⟨C₁ + L, by linarith, ?_⟩
  have key : ∀ a b : ℝ, 0 ≤ b → b ≤ a → a ≤ 4 →
      |JpTilde d a - JpTilde d b| ≤ (C₁ + L) * logMod (a - b) := by
    intro a b hb0 hba ha4
    have hτ0 : (0 : ℝ) ≤ a - b := by linarith
    have hm0 : 0 ≤ logMod (a - b) := logMod_nonneg hτ0
    rcases le_total a 1 with ha1 | ha1
    · -- both endpoints below `1`
      have h := hmod a ⟨by linarith, ha1⟩ b ⟨hb0, by linarith⟩
      rw [abs_of_nonneg hτ0] at h
      have he : C₁ * (a - b) * (1 + max 0 (Real.log (1 / (a - b)))) = C₁ * logMod (a - b) := by
        unfold logMod; ring
      rw [he] at h
      have hgrow : C₁ * logMod (a - b) ≤ (C₁ + L) * logMod (a - b) :=
        mul_le_mul_of_nonneg_right (by linarith) hm0
      linarith
    · rcases le_total 1 b with hb1 | hb1
      · -- both endpoints above `1`
        have h := hlip a ⟨le_trans hb1 hba, ha4⟩ b ⟨hb1, by linarith⟩
        rw [abs_of_nonneg hτ0] at h
        have h1 : L * (a - b) ≤ L * logMod (a - b) :=
          mul_le_mul_of_nonneg_left (self_le_logMod hτ0) hL.le
        have h2 : L * logMod (a - b) ≤ (C₁ + L) * logMod (a - b) :=
          mul_le_mul_of_nonneg_right (by linarith) hm0
        linarith
      · -- `b ≤ 1 ≤ a`: split at the matching point
        have h1 := hmod 1 ⟨zero_le_one, le_rfl⟩ b ⟨hb0, hb1⟩
        have h2 := hlip a ⟨ha1, ha4⟩ 1 ⟨le_rfl, by norm_num⟩
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - b)] at h1
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - 1)] at h2
        have he : C₁ * (1 - b) * (1 + max 0 (Real.log (1 / (1 - b))))
            = C₁ * logMod (1 - b) := by unfold logMod; ring
        rw [he] at h1
        have hstep1 : |JpTilde d 1 - JpTilde d b| ≤ C₁ * logMod (a - b) := by
          have := mul_le_mul_of_nonneg_left
            (logMod_mono (by linarith : (0 : ℝ) ≤ 1 - b) (by linarith : (1 : ℝ) - b ≤ a - b))
            hC₁.le
          linarith
        have hstep2 : |JpTilde d a - JpTilde d 1| ≤ L * logMod (a - b) := by
          have hle : a - 1 ≤ logMod (a - b) :=
            le_trans (by linarith) (self_le_logMod hτ0)
          have := mul_le_mul_of_nonneg_left hle hL.le
          linarith
        have htri := abs_sub_le (JpTilde d a) (JpTilde d 1) (JpTilde d b)
        linarith
  have final : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 4 → b ∈ Set.Icc (0 : ℝ) 4 → b ≤ a →
      |JpTilde d a - JpTilde d b|
        ≤ (C₁ + L) * |a - b| * (1 + max 0 (Real.log (1 / |a - b|))) := by
    intro a b ha hb hba
    have h := key a b hb.1 hba ha.2
    unfold logMod at h
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b), mul_assoc]
    exact h
  intro z hz z' hz'
  rcases le_total z' z with h | h
  · exact final z z' hz hz' h
  · rw [abs_sub_comm (JpTilde d z) (JpTilde d z'), abs_sub_comm z z']
    exact final z' z hz' hz h

end UpperTailOptimizers
