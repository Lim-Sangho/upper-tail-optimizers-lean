import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.EdgeGap
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.Expansions

/-!
# The multiplier expansion `μ_h` (Section 5, `paper/sections/singular.tex`)

The paper defines the multiplier `μ_h := \frac{γ_h}{m q_h^{v-2}}` (`rmk:rank-one-family-universality`)
but states no expansion for it.  This file proves, as an additional result,

  `μ_h = \frac{1}{m r_*^m}\left[1 + \frac{d²}{3}
  \left(2 + \frac{(v-2)(4d-1)}{d-1}\right)h² + O_{d,m}(h⁴)\right]`,

with `v = 2m/d`.  The four entries of `eq:rank-one-parameter-expansions` are `Ucoeff_eq`,
`Lcoeff_eq` (`SingularEndpoint/ConstantGraphonComparison/Expansions.lean`), `tendsto_alph_slope`
(`SingularEndpoint/ConstantGraphonComparison/Order5.lean`) and `tendsto_rVal_coeff` (`SingularEndpoint/ConstantGraphonComparison/EdgeGap.lean`);
`Gcoeff_eq` and `tendsto_qVal_coeff` give the expansions of `γ_h` and `q_h` from the proof in
`app:rank-one-parameter-expansions`.

## No graph layer is involved

`μ_h` is not a field of `KKTFamily`, and it need not be: the graph `H` enters `μ_h`
**only** through the two numbers `m = e(H)` and `v = |V(H)|`, and only through the single
relation `v = 2m/d` that `d`-regularity forces.  So `KKTFamily.muVal` takes `m` as a plain
real parameter and substitutes `2m/d` for `v`; the results below hold for every real `m > 0`,
of which the `m = e(H)` of a `d`-regular `H` is one instance.  No `H`, no `SimpleGraph`, and no
new structure field.

## The mechanism

`μ_h` is a quotient of two family quantities whose `h²` coefficients are already known, so
nothing new is analysed — only divided:

  `\frac{μ_h}{μ_0} = \frac{γ_h}{γ_*}\left(\frac{q_h}{q_*}\right)^{-(v-2)}`,
  `\frac{γ_h}{γ_*} = 1 + \frac{2d²}{3}h² + O(h⁴)`,
  `\frac{q_h}{q_*} = 1 - \frac{d²(4d-1)}{3(d-1)}h² + O(h⁴)`.

Two elementary steps carry this.

* **The value at `h = 0`.**  `q_*^{v-2} = u_*^{d(v-2)} = u_*^{2m-2d} = r_*^{m-d}`, so
  `μ_0 = γ_* r_*^{d-m}/m = r_*^{-d}r_*^{d-m}/m = 1/(m r_*^m)` by `γ_* r_*^d = 1`.
* **The `h²` coefficient.**  The only genuinely new limit is that of
  `(q_h^{v-2} - q_*^{v-2})/h²`.  It is the chain rule at a point the family may hit
  repeatedly, so `slopeFill` — the difference quotient of `x ↦ x^{v-2}` at `q_*` with its
  removable singularity filled by the derivative — is used instead of composing punctured
  limits: `slopeFill` is continuous at `q_*` and satisfies
  `slopeFill(x)·(x - q_*) = x^{v-2} - q_*^{v-2}` identically, so the limit follows from
  `tendsto_qVal_coeff` with no side condition on `q_h ≠ q_*`.

`Real.rpow` is used throughout, since `v - 2 = 2m/d - 2` and `m` are real; only `q_h > 0`
(`qVal_pos`, on the family window) and `m ≠ 0` are needed.

## Contents

* `KKTFamily.muVal` — `μ_h = γ_h/(m q_h^{2m/d-2})`;
* `KKTFamily.muVal_zero` — `μ_0 = 1/(m r_*^m)`;
* `tendsto_muVal_coeff` — the `h²` coefficient of `μ_h`;
* `tendsto_muVal_coeff_rStar` — the same, with `μ_0` written out as `1/(m r_*^m)`.
-/

namespace UpperTailOptimizers

open Filter Topology

variable {d : ℕ}

/-! ## A difference quotient with its removable singularity filled -/

/-- The **filled difference quotient** of `f` at `a`: the slope `x ↦ (f x - f a)/(x - a)`,
given the value `c` at `x = a`.

Taking `c = f'(a)` makes it continuous at `a` (`tendsto_slopeFill`) while keeping the exact
factorisation `f x - f a = slopeFill f a c x · (x - a)` (`slopeFill_mul`) at every `x`.  That
is what lets a chain rule be applied along a family that may repeatedly return to `a`, where
composing with the punctured limit `Tendsto (slope f a) (𝓝[≠] a)` is not available. -/
private noncomputable def slopeFill (f : ℝ → ℝ) (a c : ℝ) : ℝ → ℝ :=
  fun x => if x = a then c else (f x - f a) / (x - a)

/-- The exact factorisation `f x - f a = slopeFill f a c x · (x - a)`, valid at every `x`
including `x = a`, where both sides vanish. -/
private theorem slopeFill_mul (f : ℝ → ℝ) (a c x : ℝ) :
    slopeFill f a c x * (x - a) = f x - f a := by
  by_cases hx : x = a
  · simp [slopeFill, hx]
  · have hxa : x - a ≠ 0 := sub_ne_zero.mpr hx
    simp only [slopeFill, if_neg hx]
    field_simp

/-- **`slopeFill f a f'(a)` is continuous at `a`.**  Off `a` it is Mathlib's `slope f a`,
which tends to `f'(a)` by `hasDerivAt_iff_tendsto_slope`; at `a` it is the constant `f'(a)`.
The two filters recombine by `𝓝[≠] a ⊔ pure a = 𝓝 a`. -/
private theorem tendsto_slopeFill {f : ℝ → ℝ} {a c : ℝ} (hf : HasDerivAt f c a) :
    Tendsto (slopeFill f a c) (𝓝 a) (𝓝 c) := by
  have h1 : Tendsto (slopeFill f a c) (𝓝[≠] a) (𝓝 c) := by
    refine (hasDerivAt_iff_tendsto_slope.mp hf).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxa : x ≠ a := hx
    simp only [slopeFill, if_neg hxa]
    rw [_root_.slope_def_field]
  have h2 : Tendsto (slopeFill f a c) (pure a) (𝓝 c) := by
    have h := tendsto_pure_nhds (slopeFill f a c) a
    rwa [show slopeFill f a c a = c from by simp [slopeFill]] at h
  have h := h1.sup h2
  rwa [nhdsNE_sup_pure] at h

/-! ## The multiplier `μ_h` -/

namespace KKTFamily

/-- **The scalar multiplier `μ_h = γ_h/(m q_h^{v-2})`** of `lem:rank-one-kkt-family`,
with the exponent `v - 2` written out as `2m/d - 2` through the `d`-regularity relation
`v = 2m/d`.

`m` is a plain real parameter: for a `d`-regular `H` it is `e(H)`, but nothing below uses
more than `m > 0`.  The power is `Real.rpow`, the exponent being real. -/
noncomputable def muVal (B : KKTFamily d) (m h : ℝ) : ℝ :=
  B.gam h / (m * B.qVal h ^ (2 * m / (d : ℝ) - 2))

/-- **The value of the multiplier at `h = 0`**:
`μ_0 = 1/(m r_*^m)`.

`q_0^{v-2} = (u_*^d)^{2m/d-2} = u_*^{2m-2d} = r_*^{m-d}` because `u_*² = r_*`, and
`γ_* = r_*^{-d}` by `gammaStar_mul_rStar_pow`; the two powers of `r_*` combine to `r_*^{-m}`.
No hypothesis on `m` is needed: at `m = 0` both sides are Lean's `1/0 = 0`. -/
theorem muVal_zero (B : KKTFamily d) (hd : 2 ≤ d) (m : ℝ) :
    B.muVal m 0 = 1 / (m * rStar d ^ m) := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hdne : (d : ℝ) ≠ 0 := by linarith
  have hu : (0 : ℝ) ≤ uStar d := uStar_nonneg hd
  have hr : (0 : ℝ) < rStar d := rStar_pos hd
  have hexp : ((d : ℕ) : ℝ) * (2 * m / (d : ℝ) - 2) = 2 * (m - (d : ℝ)) := by field_simp
  have hq : (uStar d ^ d : ℝ) ^ (2 * m / (d : ℝ) - 2) = rStar d ^ (m - (d : ℝ)) := by
    rw [← Real.rpow_natCast (uStar d) d, ← Real.rpow_mul hu, hexp, Real.rpow_mul hu,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, uStar_sq hd]
  have hprod : (rStar d ^ d : ℝ) * rStar d ^ (m - (d : ℝ)) = rStar d ^ m := by
    rw [← Real.rpow_natCast (rStar d) d, ← Real.rpow_add hr]
    congr 1
    ring
  have hgam : gammaStar d = (rStar d ^ d : ℝ)⁻¹ :=
    (inv_eq_of_mul_eq_one_left (gammaStar_mul_rStar_pow hd)).symm
  rw [muVal, B.gam_zero, B.qVal_zero, hq, ← hprod, hgam]
  ring

end KKTFamily

variable (B : KKTFamily d)

/-- **The `h²` rate of `q_h^e` for a real exponent `e`.**

  `\frac{q_h^e - q_*^e}{h²} \to -e\,q_*^e\,\frac{d²(4d-1)}{3(d-1)}`.

This is `tendsto_qVal_coeff` composed with the derivative of `x ↦ x^e` at `q_* = u_*^d > 0`.
The composition is done through `slopeFill`, not through the punctured slope limit, because
`q_h = q_*` is not excluded at any particular `h`.  The constant is
`e q_*^{e-1}·(-\frac{d(4d-1)}{3}u_*^{d-2})` simplified by `q_*^{e-1} = q_*^e/q_*` and
`u_*^d = u_*^{d-2}r_*`, `r_* = (d-1)/d`. -/
private theorem tendsto_qVal_rpow_coeff (hd : 2 ≤ d) (e : ℝ) :
    Tendsto (fun h : ℝ => (B.qVal h ^ e - (uStar d ^ d : ℝ) ^ e) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-(e * (uStar d ^ d : ℝ) ^ e
        * ((d : ℝ) ^ 2 * (4 * (d : ℝ) - 1) / (3 * ((d : ℝ) - 1)))))) := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hq0 : (0 : ℝ) < uStar d ^ d := pow_pos (uStar_pos hd) d
  have hderiv : HasDerivAt (fun x : ℝ => x ^ e) (e * (uStar d ^ d : ℝ) ^ (e - 1))
      (uStar d ^ d) := Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hq0))
  have hcomp : Tendsto (fun h : ℝ =>
      slopeFill (fun x : ℝ => x ^ e) (uStar d ^ d) (e * (uStar d ^ d : ℝ) ^ (e - 1)) (B.qVal h))
      (𝓝[≠] (0 : ℝ)) (𝓝 (e * (uStar d ^ d : ℝ) ^ (e - 1))) :=
    (tendsto_slopeFill hderiv).comp (tendsto_qVal B)
  have hmul := hcomp.mul (tendsto_qVal_coeff B hd)
  have hval : e * (uStar d ^ d : ℝ) ^ (e - 1)
      * -((d : ℝ) * (4 * (d : ℝ) - 1) / 3 * uStar d ^ (d - 2))
      = -(e * (uStar d ^ d : ℝ) ^ e
        * ((d : ℝ) ^ 2 * (4 * (d : ℝ) - 1) / (3 * ((d : ℝ) - 1)))) := by
    have hsub : (uStar d ^ d : ℝ) ^ (e - 1) = (uStar d ^ d : ℝ) ^ e / (uStar d ^ d) := by
      rw [Real.rpow_sub hq0, Real.rpow_one]
    obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, (uStar d ^ d : ℝ) ^ e = Q := ⟨_, rfl⟩
    have hpow : (uStar d : ℝ) ^ d = uStar d ^ (d - 2) * rStar d := by
      rw [← uStar_sq hd, ← pow_add, show d - 2 + 2 = d from by omega]
    have hune : (uStar d : ℝ) ^ (d - 2) ≠ 0 := pow_ne_zero _ (uStar_ne_zero hd)
    have hdne : (d : ℝ) ≠ 0 := by linarith
    have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
    rw [hsub, hQ, hpow, rStar_eq]
    field_simp
  rw [hval] at hmul
  refine hmul.congr fun h => ?_
  rw [← mul_div_assoc]
  congr 1
  exact slopeFill_mul _ _ _ _

/-- The rational identity behind the `μ` coefficient, with the power `q_*^{v-2}` held as an
opaque `Q`: dividing the `γ` and `q` rates gives
`\frac{γ_*·\frac{2d²}{3}·Q + γ_*eQ\frac{d²(4d-1)}{3(d-1)}}{mQ²}
  = \frac{γ_*}{mQ}·\frac{d²}{3}\left(2 + \frac{e(4d-1)}{d-1}\right)`. -/
private theorem muVal_coeff_algebra (hd : 2 ≤ d) {Q e g m : ℝ} (hQ : Q ≠ 0) (hm : m ≠ 0) :
    (g * (2 * (d : ℝ) ^ 2 / 3) * Q
        - g * -(e * Q * ((d : ℝ) ^ 2 * (4 * (d : ℝ) - 1) / (3 * ((d : ℝ) - 1))))) / (m * Q * Q)
      = g / (m * Q) * ((d : ℝ) ^ 2 / 3)
        * (2 + e * (4 * (d : ℝ) - 1) / ((d : ℝ) - 1)) := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The pointwise rewriting of the increment of `μ_h` as a single quotient,

  `\frac{A}{mX} - \frac{g}{mY}
    = \frac{(A-g)Y - g(X-Y)}{mXY}`,   divided throughout by `h²`.

The two powers `X = q_h^{v-2}` and `Y = q_*^{v-2}` are held as opaque atoms: `field_simp`
normalises inside a `Real.rpow` exponent, which would desynchronise them from their
nonvanishing hypotheses if the identity were proved in place. -/
private theorem muVal_diff_eq {A g X Y m h : ℝ} (hX : X ≠ 0) (hY : Y ≠ 0) (hm : m ≠ 0)
    (hh : h ≠ 0) :
    ((A - g) / h ^ 2 * Y - g * ((X - Y) / h ^ 2)) / (m * X * Y)
      = (A / (m * X) - g / (m * Y)) / h ^ 2 := by
  field_simp
  ring

/-- **The `h²` coefficient of the multiplier `μ_h`**:

  `\frac{μ_h - μ_0}{h²} \to μ_0·\frac{d²}{3}
    \left(2 + \frac{(v-2)(4d-1)}{d-1}\right)`,   `v = 2m/d`.

Everything is a quotient of the two rates already proved: `Gcoeff_eq` supplies
`γ_h - γ_* = \frac{2d^{d+2}}{3(d-1)^d}h² + o(h²)`, whose ratio to `γ_* = (d/(d-1))^d` is the
clean `\frac{2d²}{3}`, and `tendsto_qVal_rpow_coeff` supplies the `q_h^{v-2}` rate.  Writing
`μ_h - μ_0 = \frac{(γ_h-γ_*)q_*^{v-2} - γ_*(q_h^{v-2}-q_*^{v-2})}{m q_h^{v-2}q_*^{v-2}}`
turns the statement into `Filter.Tendsto.div`. -/
theorem tendsto_muVal_coeff (hd : 2 ≤ d) {m : ℝ} (hm : 0 < m) :
    Tendsto (fun h : ℝ => (B.muVal m h - B.muVal m 0) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (B.muVal m 0 * ((d : ℝ) ^ 2 / 3)
        * (2 + (2 * m / (d : ℝ) - 2) * (4 * (d : ℝ) - 1) / ((d : ℝ) - 1)))) := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hmne : m ≠ 0 := ne_of_gt hm
  have hq0 : (0 : ℝ) < uStar d ^ d := pow_pos (uStar_pos hd) d
  have hQ0 : (0 : ℝ) < (uStar d ^ d : ℝ) ^ (2 * m / (d : ℝ) - 2) :=
    Real.rpow_pos_of_pos hq0 _
  have hQ0ne : (uStar d ^ d : ℝ) ^ (2 * m / (d : ℝ) - 2) ≠ 0 := ne_of_gt hQ0
  -- `μ_0` written out
  have hmu0 : B.muVal m 0
      = gammaStar d / (m * (uStar d ^ d : ℝ) ^ (2 * m / (d : ℝ) - 2)) := by
    rw [KKTFamily.muVal, B.gam_zero, B.qVal_zero]
  -- `Gcoeff = γ_*·2d²/3`
  have hGgam : Gcoeff B = gammaStar d * (2 * (d : ℝ) ^ 2 / 3) := by
    have hdd : ((d : ℝ) - 1) ^ d ≠ 0 := pow_ne_zero _ (by linarith : ((d : ℝ) - 1) ≠ 0)
    rw [Gcoeff_eq B hd, gammaStar, div_pow, pow_add]
    field_simp
  -- numerator and denominator
  have hnum := ((tendsto_gam_coeff B).mul
      (tendsto_const_nhds (x := (uStar d ^ d : ℝ) ^ (2 * m / (d : ℝ) - 2)))).sub
    ((tendsto_qVal_rpow_coeff B hd (2 * m / (d : ℝ) - 2)).const_mul (gammaStar d))
  have hQ : Tendsto (fun h : ℝ => B.qVal h ^ (2 * m / (d : ℝ) - 2)) (𝓝[≠] (0 : ℝ))
      (𝓝 ((uStar d ^ d : ℝ) ^ (2 * m / (d : ℝ) - 2))) := by
    have hc : ContinuousAt (fun x : ℝ => x ^ (2 * m / (d : ℝ) - 2)) (uStar d ^ d) :=
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hq0))).continuousAt
    exact hc.tendsto.comp (tendsto_qVal B)
  have hden := ((tendsto_const_nhds (x := m)).mul hQ).mul
    (tendsto_const_nhds (x := (uStar d ^ d : ℝ) ^ (2 * m / (d : ℝ) - 2)))
  have hDne : m * (uStar d ^ d : ℝ) ^ (2 * m / (d : ℝ) - 2)
      * (uStar d ^ d : ℝ) ^ (2 * m / (d : ℝ) - 2) ≠ 0 := by positivity
  have hdiv := hnum.div hden hDne
  rw [hGgam, muVal_coeff_algebra hd hQ0ne hmne] at hdiv
  rw [hmu0]
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_window B] with h hh hw
  have hhne : h ≠ 0 := hh
  have hXne : (B.qVal h : ℝ) ^ (2 * m / (d : ℝ) - 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (KKTFamily.qVal_pos hw) _)
  simp only [Pi.div_apply]
  rw [KKTFamily.muVal]
  exact muVal_diff_eq hXne hQ0ne hmne hhne

/-- **The `h²` coefficient of `μ_h`, with `μ_0` written out**:

  `μ_h = \frac{1}{m r_*^m}\left[1 + \frac{d²}{3}
    \left(2 + \frac{(v-2)(4d-1)}{d-1}\right)h² + o(h²)\right]`,   `v = 2m/d`.

`tendsto_muVal_coeff` with `μ_0` evaluated by `muVal_zero`. -/
theorem tendsto_muVal_coeff_rStar (hd : 2 ≤ d) {m : ℝ} (hm : 0 < m) :
    Tendsto (fun h : ℝ => (B.muVal m h - 1 / (m * rStar d ^ m)) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (1 / (m * rStar d ^ m) * ((d : ℝ) ^ 2 / 3)
        * (2 + (2 * m / (d : ℝ) - 2) * (4 * (d : ℝ) - 1) / ((d : ℝ) - 1)))) := by
  have h := tendsto_muVal_coeff B hd hm
  rwa [B.muVal_zero hd m] at h

end UpperTailOptimizers
