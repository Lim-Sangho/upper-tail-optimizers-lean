import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilyBase
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Jacobian3

/-!
# The base-point Jacobian of the family system (Section 5, `paper/sections/singular.tex`)

`SingularEndpoint/RankOneStationaryFamily/FamilyBase.lean` and `SingularEndpoint/RankOneStationaryFamily/FamilyAnalytic.lean` supply two of the three
hypotheses of the analytic implicit function theorem behind
`lem:rank-one-kkt-family`: the vanishing `F(z₀, 0) = 0` and the joint analyticity
of `F`.  **This file supplies the third one**, the invertibility of the `(u, ℓ, γ)`-Jacobian
at the base point, in the shape

  `HasStrictFDerivAt (fun z => Fsys d z 0) (jac3 a b c e hb hc) (zBase d)`

with `jac3` the `3 × 3` continuous linear equivalence of `SingularEndpoint/RankOneStationaryFamily/Jacobian3.lean`.

The computation is *elementary*, not analytic.  At `h = 0` every `logSlope` argument of
`SingularEndpoint/RankOneStationaryFamily/FamilySystem.lean` carries a factor `h`, so it is identically `logSlope 0 = 1` as
a function of `z = (u, ℓ, γ)`, and the restricted system is the explicit map `Gfun` below.
Writing `𝓛_*` for the rank-one KKT function of `eq:kkt-quartic-expansion` and `w = u²`, the
three components are `𝓛(w)`, `4u·𝓛′(w)` and `4𝓛′(w) + 4w·𝓛″(w)`, so their `u`-derivatives
are `2u·𝓛′(w)`, `4𝓛′(w) + 8u²·𝓛″(w)` and `16u·𝓛″(w) + 8u³·𝓛‴(w)`.  At the base point the
first two vanish by the contact identities `Lstar1_rStar`, `Lstar2_rStar`, which is exactly
the pattern of zeros of `jac3`, and the surviving corner entry is
`c = 8u_*³·Γ_d^{(4)}(r_*) ≠ 0` by `Lstar3_rStar`.

The `h = 0` values of `E₂` and `E₃` are `Esys2_zero'` and `Esys3_zero'`
(`SingularEndpoint/RankOneStationaryFamily/FamilySystem.lean`) — the hypothesis-free forms, which is what a statement about
all of `ℝ × ℝ × ℝ` needs.  Their hypothesis-carrying siblings `Esys2_zero`, `Esys3_zero`
are the same fact under the (unused) hypotheses `0 < u` and `u² < 1`.

## Contents

* `Gfun` — the restriction of the family system of `lem:rank-one-kkt-family` to
  `h = 0`, written out as an elementary map `ℝ × ℝ × ℝ → ℝ × ℝ × ℝ`;
* `Fsys_zero_eq` — `Fsys d z 0 = Gfun d z`;
* `hasStrictDerivAt_ell` — the log-odds has strict derivative `-J_p''` on `(0,1)`;
* `exists_hasStrictFDerivAt_Fsys` — the hypothesis `hL` of the analytic implicit function
  theorem: the base-point derivative of `z ↦ Fsys d z 0` is a `jac3` with the two
  determinant entries nonzero.
-/

namespace UpperTailOptimizers

open Real

variable {d : ℕ}

/-! ## The system at `h = 0`

The exponents `d - 1`, `d - 2` are natural-number subtractions; their casts to `ℝ` agree
with the real subtractions only above the truncation point, which is what `cast_sub_one` and
`cast_sub_two` of `SingularEndpoint/RankOneStationaryFamily/Contact.lean` record. -/

/-- **The family system of `lem:rank-one-kkt-family` at `h = 0`**, written out.

Every `logSlope` argument of `Esys2`, `Esys3` carries a factor `h`, so at `h = 0` the whole
system is the elementary map

  `G₁ = ℓ - ell(u²) - γ(u²)^{d-1}`,
  `G₂ = 4u/(1-u²) + 4/u - 4γu(d-1)(u²)^{d-2}`,
  `G₃ = 4/(1-u²)² - 4γ((d-1)(u²)^{d-2} + u(d-1)u^{d-2}(d-2)u^{d-3})`,

in the coordinates `z = (u, ℓ, γ)`.  Abstractly `G₁ = 𝓛(u²)`, `G₂ = 4u·𝓛′(u²)` and
`G₃ = 4𝓛′(u²) + 4u²·𝓛″(u²)`. -/
noncomputable def Gfun (d : ℕ) (z : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (z.2.1 - ell (z.1 ^ 2) - z.2.2 * (z.1 ^ 2) ^ (d - 1),
    4 * z.1 / (1 - z.1 ^ 2) + 4 / z.1
      - 4 * z.2.2 * z.1 * (((d - 1 : ℕ) : ℝ) * (z.1 ^ 2) ^ (d - 2)),
    4 / (1 - z.1 ^ 2) ^ 2
      - 4 * z.2.2 * (((d - 1 : ℕ) : ℝ) * (z.1 ^ 2) ^ (d - 2)
          + z.1 * (((d - 1 : ℕ) : ℝ) * z.1 ^ (d - 2)) * (((d - 2 : ℕ) : ℝ) * z.1 ^ (d - 3))))

/-- **The `h = 0` restriction of the family system is `Gfun`.**  The first component is
`Esys1` with `(u - 0)(u + 0) = u²`, the other two are `Esys2_zero` and `Esys3_zero`. -/
theorem Fsys_zero_eq (hd : 2 ≤ d) (z : ℝ × ℝ × ℝ) : Fsys d z 0 = Gfun d z := by
  have _hd : 2 ≤ d := hd
  have h1 : (z.1 - 0) * (z.1 + 0) = z.1 ^ 2 := by ring
  simp only [Fsys, Esys1, Lell, h1, Esys2_zero', Esys3_zero', Gfun]

/-! ## A differentiation-friendly form

`Gfun` is written the way `Esys2_zero`, `Esys3_zero` produce it.  For the derivative
computation it is convenient to (i) isolate the multiplier `γ` as a single factor, so that
each component is `φ(u) - γ·ψ(u)` with `φ`, `ψ` functions of one variable, and (ii) trade
the truncated-exponent product `u·u^{d-2}·u^{d-3}` for `u²·(u²)^{d-3}`. -/

/-- The truncated-exponent identity behind the mixed term of `E₃`: it holds for every `x`,
the case `d = 2` because both `((d-2 : ℕ) : ℝ)` and `(d : ℝ) - 2` vanish there. -/
private theorem mixed_pow_eq (hd : 2 ≤ d) (x : ℝ) :
    x * (((d - 1 : ℕ) : ℝ) * x ^ (d - 2)) * (((d - 2 : ℕ) : ℝ) * x ^ (d - 3))
      = x ^ 2 * (((d : ℝ) - 1) * ((d : ℝ) - 2) * (x ^ 2) ^ (d - 3)) := by
  rcases eq_or_lt_of_le hd with hd2 | hd3
  · rw [← hd2]; norm_num
  · have hd3' : 3 ≤ d := hd3
    have e1 : x ^ (d - 2) * x ^ (d - 3) = (x ^ 2) ^ (d - 3) * x := by
      rw [← pow_add, ← pow_mul, ← pow_succ]
      congr 1
      omega
    rw [cast_sub_one hd, cast_sub_two hd]
    linear_combination ((d : ℝ) - 1) * ((d : ℝ) - 2) * x * e1

/-- `Gfun` with the multiplier `γ = z.2.2` isolated and the truncated exponents merged. -/
private noncomputable def Gaux (d : ℕ) (z : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (z.2.1 - ell (z.1 ^ 2) - z.2.2 * (z.1 ^ 2) ^ (d - 1),
    (4 * z.1 / (1 - z.1 ^ 2) + 4 / z.1)
      - z.2.2 * (4 * z.1 * (((d : ℝ) - 1) * (z.1 ^ 2) ^ (d - 2))),
    4 / (1 - z.1 ^ 2) ^ 2
      - z.2.2 * (4 * (((d : ℝ) - 1) * (z.1 ^ 2) ^ (d - 2)
          + z.1 ^ 2 * (((d : ℝ) - 1) * ((d : ℝ) - 2) * (z.1 ^ 2) ^ (d - 3)))))

private theorem Gfun_eq_Gaux (hd : 2 ≤ d) (z : ℝ × ℝ × ℝ) : Gfun d z = Gaux d z := by
  simp only [Gfun, Gaux, Prod.mk.injEq]
  refine ⟨trivial, ?_, ?_⟩
  · rw [cast_sub_one hd]; ring
  · rw [mixed_pow_eq hd z.1, cast_sub_one hd]; ring

/-! ## The one-variable derivatives

Each component of `Gaux` has the shape `φ(u) - γ·ψ(u)`, so the whole `(u, ℓ, γ)`-derivative
is assembled from six one-variable derivatives.  The three `φ`-derivatives are written in
terms of `J_p''`, `J_p'''`, `J_p''''`, and the three `ψ`-derivatives in the matching
polynomial shape, so that the differences `φ' - γ_*·ψ'` are literally `𝓛_*′`, `𝓛_*″`,
`𝓛_*‴` at `r_*`. -/

/-- **The derivative of the log-odds**: `ℓ′(z) = -1/(z(1-z)) = -J_p''(z)` on `(0,1)`.
`ell z = log((1-z)/z)`, so this is the quotient rule followed by `Real.log`. -/
theorem hasStrictDerivAt_ell {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasStrictDerivAt ell (-Jp'' z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz0
  have h1 : (0 : ℝ) < 1 - z := by linarith
  have h1ne : (1 : ℝ) - z ≠ 0 := ne_of_gt h1
  have hq := ((hasStrictDerivAt_const z (1 : ℝ)).sub (hasStrictDerivAt_id z)).div
    (hasStrictDerivAt_id z) hzne
  refine (hq.log (ne_of_gt (div_pos h1 hz0))).congr_deriv ?_
  simp only [Pi.sub_apply, Pi.div_apply, id_eq]
  rw [Jp'']
  field_simp
  ring

/-- `d/du ell(u²) = -2u·J_p''(u²)`. -/
private theorem hasStrictDerivAt_phi1 {x : ℝ} (hx0 : 0 < x) (hx1 : x ^ 2 < 1) :
    HasStrictDerivAt (fun y : ℝ => ell (y ^ 2)) (-(2 * x * Jp'' (x ^ 2))) x := by
  have hx2 : (0 : ℝ) < x ^ 2 := pow_pos hx0 2
  -- `HasStrictDerivAt` unfolds to `HasStrictFDerivAt`, so dot notation would resolve
  -- `comp_of_eq` to the `FDeriv` version; the chain rule has to be written in prefix form.
  refine (HasStrictDerivAt.comp_of_eq x (hasStrictDerivAt_ell hx2 hx1)
    (hasStrictDerivAt_pow 2 x) rfl).congr_deriv ?_
  push_cast
  ring

/-- `d/du (u²)^{d-1} = 2u(d-1)(u²)^{d-2}`. -/
private theorem hasStrictDerivAt_psi1 (hd : 2 ≤ d) (x : ℝ) :
    HasStrictDerivAt (fun y : ℝ => (y ^ 2) ^ (d - 1))
      (2 * x * (((d : ℝ) - 1) * (x ^ 2) ^ (d - 2))) x := by
  refine ((hasStrictDerivAt_pow 2 x).pow (d - 1)).congr_deriv ?_
  rw [show d - 1 - 1 = d - 2 from by omega, cast_sub_one hd]
  push_cast
  ring

/-- `d/du (4u/(1-u²) + 4/u) = 4J_p''(u²) + 8u²J_p'''(u²)`. -/
private theorem hasStrictDerivAt_phi2 {x : ℝ} (hx0 : 0 < x) (hx1 : x ^ 2 < 1) :
    HasStrictDerivAt (fun y : ℝ => 4 * y / (1 - y ^ 2) + 4 / y)
      (4 * Jp'' (x ^ 2) + 8 * x ^ 2 * Jp3 (x ^ 2)) x := by
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hden : (1 : ℝ) - x ^ 2 ≠ 0 := by
    have : (0 : ℝ) < 1 - x ^ 2 := by linarith
    exact ne_of_gt this
  have hnum := (hasStrictDerivAt_const x (4 : ℝ)).mul (hasStrictDerivAt_id x)
  have hd1 := (hasStrictDerivAt_const x (1 : ℝ)).sub (hasStrictDerivAt_pow 2 x)
  have h1 := hnum.div hd1 hden
  have h2 := (hasStrictDerivAt_const x (4 : ℝ)).div (hasStrictDerivAt_id x) hxne
  refine (h1.add h2).congr_deriv ?_
  simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
  rw [Jp'', Jp3]
  push_cast
  field_simp
  ring

/-- `d/du (4u(d-1)(u²)^{d-2}) = 4(d-1)(u²)^{d-2} + 8u²(d-1)(d-2)(u²)^{d-3}`. -/
private theorem hasStrictDerivAt_psi2 (hd : 2 ≤ d) (x : ℝ) :
    HasStrictDerivAt (fun y : ℝ => 4 * y * (((d : ℝ) - 1) * (y ^ 2) ^ (d - 2)))
      (4 * (((d : ℝ) - 1) * (x ^ 2) ^ (d - 2))
        + 8 * x ^ 2 * (((d : ℝ) - 1) * ((d : ℝ) - 2) * (x ^ 2) ^ (d - 3))) x := by
  have hA := (hasStrictDerivAt_const x (4 : ℝ)).mul (hasStrictDerivAt_id x)
  have hB := ((hasStrictDerivAt_pow 2 x).pow (d - 2)).const_mul ((d : ℝ) - 1)
  refine (hA.mul hB).congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
  rw [show d - 2 - 1 = d - 3 from by omega, cast_sub_two hd]
  push_cast
  ring

/-- `d/du (4/(1-u²)²) = 16u·J_p'''(u²) + 8u³·J_p''''(u²)`. -/
private theorem hasStrictDerivAt_phi3 {x : ℝ} (hx0 : 0 < x) (hx1 : x ^ 2 < 1) :
    HasStrictDerivAt (fun y : ℝ => 4 / (1 - y ^ 2) ^ 2)
      (16 * x * Jp3 (x ^ 2) + 8 * x * x ^ 2 * Jp4 (x ^ 2)) x := by
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hpos : (0 : ℝ) < 1 - x ^ 2 := by linarith
  have hden : ((1 : ℝ) - x ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hpos)
  have hd1 := ((hasStrictDerivAt_const x (1 : ℝ)).sub (hasStrictDerivAt_pow 2 x)).pow 2
  refine ((hasStrictDerivAt_const x (4 : ℝ)).div hd1 hden).congr_deriv ?_
  simp only [Pi.sub_apply, Pi.pow_apply]
  rw [Jp3, Jp4]
  push_cast
  field_simp
  ring

/-- `d/du (4((d-1)(u²)^{d-2} + u²(d-1)(d-2)(u²)^{d-3}))
      = 16u(d-1)(d-2)(u²)^{d-3} + 8u³(d-1)(d-2)(d-3)(u²)^{d-4}`,
the last coefficient being the cast of the **natural-number** difference `d - 3`, exactly as
in `Lstar3`. -/
private theorem hasStrictDerivAt_psi3 (hd : 2 ≤ d) (x : ℝ) :
    HasStrictDerivAt
      (fun y : ℝ => 4 * (((d : ℝ) - 1) * (y ^ 2) ^ (d - 2)
        + y ^ 2 * (((d : ℝ) - 1) * ((d : ℝ) - 2) * (y ^ 2) ^ (d - 3))))
      (16 * x * (((d : ℝ) - 1) * ((d : ℝ) - 2) * (x ^ 2) ^ (d - 3))
        + 8 * x * x ^ 2 * (((d : ℝ) - 1) * ((d : ℝ) - 2) * (((d - 3 : ℕ) : ℝ))
            * (x ^ 2) ^ (d - 4))) x := by
  have hA := ((hasStrictDerivAt_pow 2 x).pow (d - 2)).const_mul ((d : ℝ) - 1)
  have hB := ((hasStrictDerivAt_pow 2 x).pow (d - 3)).const_mul
    (((d : ℝ) - 1) * ((d : ℝ) - 2))
  have hC := (hasStrictDerivAt_pow 2 x).mul hB
  refine ((hA.add hC).const_mul (4 : ℝ)).congr_deriv ?_
  simp only [Pi.pow_apply]
  rw [show d - 2 - 1 = d - 3 from by omega, show d - 3 - 1 = d - 4 from by omega,
    cast_sub_two hd]
  push_cast
  ring

/-! ## The three coordinate projections -/

/-- The projection `z ↦ u`. -/
private def prU : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

/-- The projection `z ↦ ℓ`. -/
private def prL : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The projection `z ↦ γ`. -/
private def prG : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

private theorem prU_apply (v : ℝ × ℝ × ℝ) : prU v = v.1 := rfl
private theorem prL_apply (v : ℝ × ℝ × ℝ) : prL v = v.2.1 := rfl
private theorem prG_apply (v : ℝ × ℝ × ℝ) : prG v = v.2.2 := rfl

private theorem hasStrictFDerivAt_prU (z : ℝ × ℝ × ℝ) :
    HasStrictFDerivAt (fun v : ℝ × ℝ × ℝ => v.1) prU z :=
  prU.hasStrictFDerivAt

private theorem hasStrictFDerivAt_prL (z : ℝ × ℝ × ℝ) :
    HasStrictFDerivAt (fun v : ℝ × ℝ × ℝ => v.2.1) prL z :=
  prL.hasStrictFDerivAt

private theorem hasStrictFDerivAt_prG (z : ℝ × ℝ × ℝ) :
    HasStrictFDerivAt (fun v : ℝ × ℝ × ℝ => v.2.2) prG z :=
  prG.hasStrictFDerivAt

/-- A one-variable derivative in `u` lifted to `ℝ × ℝ × ℝ`. -/
private theorem liftU {φ : ℝ → ℝ} {q x : ℝ} {z : ℝ × ℝ × ℝ}
    (h : HasStrictDerivAt φ q x) (hx : x = z.1) :
    HasStrictFDerivAt (fun v : ℝ × ℝ × ℝ => φ v.1) (q • prU) z :=
  h.comp_hasStrictFDerivAt_of_eq z (hasStrictFDerivAt_prU z) hx

/-! ## The Jacobian at the base point -/

/-- **The base-point derivative of the family system is a `jac3`.**

This is the hypothesis `hL` of the analytic implicit function theorem for
`lem:rank-one-kkt-family`: at `(u_*, ℓ_*, γ_*)` the map `z ↦ F(z, 0)` is strictly
differentiable with derivative

```
[ 0   1   a ]
[ 0   0   b ]
[ c   0   e ]
```

The two zeros in the first column and the zero in the second row are the contact identities
`Lstar1_rStar` and `Lstar2_rStar`; the corner entry is `c = 8u_*³·Γ_d^{(4)}(r_*)`, nonzero by
`Lstar3_rStar`, and `b = -4u_*(d-1)r_*^{d-2} ≠ 0`.  The four entries are existentially
quantified because only `b ≠ 0` and `c ≠ 0` — the determinant `-bc` — are needed
downstream. -/
theorem exists_hasStrictFDerivAt_Fsys (hd : 2 ≤ d) :
    ∃ a b c e : ℝ, ∃ hb : b ≠ 0, ∃ hc : c ≠ 0,
      HasStrictFDerivAt (fun z : ℝ × ℝ × ℝ => Fsys d z 0)
        (jac3 a b c e hb hc : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ)) (zBase d) := by
  have h1d : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hu0 : 0 < uStar d := uStar_pos hd
  have husq : uStar d ^ 2 = rStar d := uStar_sq hd
  have hu1 : uStar d ^ 2 < 1 := by rw [husq]; exact rStar_lt_one hd
  have hw0 : (0 : ℝ) < uStar d ^ 2 := pow_pos hu0 2
  -- the two nonvanishing entries
  have hbpos : (0 : ℝ) < 4 * uStar d * (((d : ℝ) - 1) * (uStar d ^ 2) ^ (d - 2)) := by
    have h2 : (0 : ℝ) < (uStar d ^ 2) ^ (d - 2) := pow_pos hw0 _
    have h3 : (0 : ℝ) < 4 * uStar d := by linarith
    exact mul_pos h3 (mul_pos (by linarith) h2)
  have hb : -(4 * uStar d * (((d : ℝ) - 1) * (uStar d ^ 2) ^ (d - 2))) ≠ 0 := by
    simpa using ne_of_gt hbpos
  have hcpos : (0 : ℝ) < 8 * uStar d ^ 3 * ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2) := by
    have h2 : (0 : ℝ) < uStar d ^ 3 := pow_pos hu0 3
    have h3 : (0 : ℝ) < (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 := by
      apply div_pos (by positivity) (by nlinarith)
    nlinarith
  have hc : (8 : ℝ) * uStar d ^ 3 * ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2) ≠ 0 := ne_of_gt hcpos
  -- the three contact identities in the form the coefficient computations need
  have hLs1 : Jp'' (uStar d ^ 2)
      - gammaStar d * ((d : ℝ) - 1) * (uStar d ^ 2) ^ (d - 2) = 0 := by
    have h := Lstar1_rStar hd
    rw [Lstar1] at h
    rw [husq]
    exact h
  have hLs2 : Jp3 (uStar d ^ 2)
      - gammaStar d * ((d : ℝ) - 1) * ((d : ℝ) - 2) * (uStar d ^ 2) ^ (d - 3) = 0 := by
    have h := Lstar2_rStar hd
    rw [Lstar2] at h
    rw [husq]
    exact h
  have hLs3 : Jp4 (uStar d ^ 2)
      - gammaStar d * ((d : ℝ) - 1) * ((d : ℝ) - 2) * (((d - 3 : ℕ) : ℝ))
        * (uStar d ^ 2) ^ (d - 4) = (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 := by
    have h := Lstar3_rStar hd
    rw [Lstar3] at h
    rw [husq]
    exact h
  refine ⟨-((uStar d ^ 2) ^ (d - 1)),
    -(4 * uStar d * (((d : ℝ) - 1) * (uStar d ^ 2) ^ (d - 2))),
    8 * uStar d ^ 3 * ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2),
    -(4 * (((d : ℝ) - 1) * (uStar d ^ 2) ^ (d - 2)
      + uStar d ^ 2 * (((d : ℝ) - 1) * ((d : ℝ) - 2) * (uStar d ^ 2) ^ (d - 3)))),
    hb, hc, ?_⟩
  have hGeq : (fun z : ℝ × ℝ × ℝ => Fsys d z 0) = fun z : ℝ × ℝ × ℝ => Gaux d z := by
    funext z
    rw [Fsys_zero_eq hd z, Gfun_eq_Gaux hd z]
  rw [hGeq]
  -- component 1
  have hcomp1 : HasStrictFDerivAt (fun z : ℝ × ℝ × ℝ => (Gaux d z).1)
      (prL + (-((uStar d ^ 2) ^ (d - 1))) • prG) (zBase d) := by
    refine (((hasStrictFDerivAt_prL (zBase d)).sub
      (liftU (hasStrictDerivAt_phi1 hu0 hu1) rfl)).sub
      ((hasStrictFDerivAt_prG (zBase d)).mul
        (liftU (hasStrictDerivAt_psi1 hd (uStar d)) rfl))).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [zBase, add_apply, sub_apply,
      smul_apply, smul_eq_mul, prU_apply, prL_apply, prG_apply]
    linear_combination (2 * uStar d * v.1) * hLs1
  -- component 2
  have hcomp2 : HasStrictFDerivAt (fun z : ℝ × ℝ × ℝ => (Gaux d z).2.1)
      ((-(4 * uStar d * (((d : ℝ) - 1) * (uStar d ^ 2) ^ (d - 2)))) • prG) (zBase d) := by
    refine ((liftU (hasStrictDerivAt_phi2 hu0 hu1) rfl).sub
      ((hasStrictFDerivAt_prG (zBase d)).mul
        (liftU (hasStrictDerivAt_psi2 hd (uStar d)) rfl))).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [zBase, add_apply, sub_apply,
      smul_apply, smul_eq_mul, prU_apply, prG_apply]
    linear_combination (4 * v.1) * hLs1 + (8 * uStar d ^ 2 * v.1) * hLs2
  -- component 3
  have hcomp3 : HasStrictFDerivAt (fun z : ℝ × ℝ × ℝ => (Gaux d z).2.2)
      ((8 * uStar d ^ 3 * ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2)) • prU
        + (-(4 * (((d : ℝ) - 1) * (uStar d ^ 2) ^ (d - 2)
            + uStar d ^ 2 * (((d : ℝ) - 1) * ((d : ℝ) - 2)
              * (uStar d ^ 2) ^ (d - 3))))) • prG) (zBase d) := by
    refine ((liftU (hasStrictDerivAt_phi3 hu0 hu1) rfl).sub
      ((hasStrictFDerivAt_prG (zBase d)).mul
        (liftU (hasStrictDerivAt_psi3 hd (uStar d)) rfl))).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [zBase, add_apply, sub_apply,
      smul_apply, smul_eq_mul, prU_apply, prG_apply]
    linear_combination (16 * uStar d * v.1) * hLs2 + (8 * uStar d ^ 3 * v.1) * hLs3
  refine (hcomp1.prodMk (hcomp2.prodMk hcomp3)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.prod_apply, jac3_coe, add_apply,
    smul_apply, smul_eq_mul, prU_apply, prL_apply, prG_apply]

end UpperTailOptimizers
