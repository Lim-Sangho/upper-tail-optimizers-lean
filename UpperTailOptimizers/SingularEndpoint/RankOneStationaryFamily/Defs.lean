import UpperTailOptimizers.LZBoundary.PhiConvex

/-!
# The singular regular endpoint: scalar objects (Section 5, `paper/sections/singular.tex`)

This file introduces the scalar objects of `sec:singular-endpoint`, Section 5 of
`paper/paper.tex` (`paper/sections/singular.tex` and the subsection files it inputs), together
with the elementary arithmetic facts about them.

Section 5 treats the density excluded from `thm:nonexceptional-endpoint`, namely `r_* = (d-1)/d`, at
which the two scalar contact points of Section 3 coalesce.  The section's `r_*` is the
number the rest of the development calls `rStar d`; its `u_* = √r_*` is **new**, and is
called `uStar d` here to keep the two apart.  Likewise the section's `p_*` is the
development's `pStar d`.

## Contents

* `rStar`, `uStar` — the exceptional density `r_* = (d-1)/d` and factor value `u_* = √r_*`;
* `ell`, `ellStar` — the log-odds `ℓ(z) = log((1-z)/z)` and its singular endpoint value
  `ℓ_* = ℓ(p_*) = d/(d-1) - log(d-1)`;
* `gammaStar`, `betaD` — the singular endpoint multiplier `γ_* = (d/(d-1))^d = r_*^{-d}` and
  `β_d = γ_*/d`;
* `Jp3`, `Jp4`, `Jp5` — the third, fourth and fifth derivatives of `J_p` (which do not
  depend on `p`), with their `HasDerivAt` chain;
* `Fkkt` — the rank-one scalar KKT function `F_{p,γ}(z) = J_p'(z) - γ z^{d-1}` of
  `eq:rank-one-kkt`, and `Lstar = F_{p_*,γ_*}`
  `eq:kkt-quartic-expansion`;
* `Gam`, `Rd` — the singular endpoint supporting gap `Γ_d` `eq:endpoint-supporting-gap` and the
  convexity defect `R_d` (not named in the paper, which uses the unnormalised quantity
  `z^d - r_*^d - d r_*^{d-1}(z - r_*)` in the proof of `lem:localization-rank-one`);
* `gd` — the diagonal divided slope `g_d(z) = 1/((d-1)z^{d-1}(1-z))` of
  `lem:rank-one-kkt-family`.

Nothing here depends on the graph `H`; the objects that do live in `SingularEndpoint/RankOneStationaryFamily/RankOne.lean`
and above.
-/

namespace UpperTailOptimizers

open Real

variable {d : ℕ}

/-! ## The singular endpoint constants -/

/-- The **singular endpoint factor value** `u_* = √r_*` of `sec:singular-endpoint`.  The rank-one
graphons of Section 5 are `f ⊗ f` with `f` two-valued around `u_*`, so that the three edge
values `s², st, t²` all collapse to the exceptional density `r_* = u_*²` (`rStar`,
`LZBoundary/Phi.lean`). -/
noncomputable def uStar (d : ℕ) : ℝ := Real.sqrt (rStar d)

/-- The log-odds `ℓ(z) = log((1-z)/z)`.  It is related to `J_p'` by
`J_p'(z) = ℓ(p) - ℓ(z)` (`Jp'_eq_ell_sub`). -/
noncomputable def ell (z : ℝ) : ℝ := Real.log ((1 - z) / z)

/-- The singular endpoint log-odds `ℓ_* = ℓ(p_*) = d/(d-1) - log(d-1)`. -/
noncomputable def ellStar (d : ℕ) : ℝ := (d : ℝ) / ((d : ℝ) - 1) - Real.log ((d : ℝ) - 1)

/-- The singular endpoint scalar multiplier `γ_* = (d/(d-1))^d = r_*^{-d}`. -/
noncomputable def gammaStar (d : ℕ) : ℝ := ((d : ℝ) / ((d : ℝ) - 1)) ^ d

/-- `β_d = γ_*/d = d^{d-1}/(d-1)^d`, the slope of the singular endpoint supporting line in the
`x = u^d` coordinate. -/
noncomputable def betaD (d : ℕ) : ℝ := gammaStar d / (d : ℝ)

/-! ## Basic arithmetic -/

theorem rStar_eq (d : ℕ) : rStar d = ((d : ℝ) - 1) / (d : ℝ) := rfl

theorem rStar_ne_zero (hd : 2 ≤ d) : rStar d ≠ 0 := ne_of_gt (rStar_pos hd)

theorem one_sub_rStar (hd : 2 ≤ d) : 1 - rStar d = 1 / (d : ℝ) := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  rw [rStar_eq]
  field_simp
  ring

theorem uStar_pos (hd : 2 ≤ d) : 0 < uStar d := Real.sqrt_pos.mpr (rStar_pos hd)

theorem uStar_nonneg (hd : 2 ≤ d) : 0 ≤ uStar d := (uStar_pos hd).le

/-- `u_*² = r_*`. -/
@[simp] theorem uStar_sq (hd : 2 ≤ d) : uStar d ^ 2 = rStar d :=
  Real.sq_sqrt (rStar_pos hd).le

theorem uStar_lt_one (hd : 2 ≤ d) : uStar d < 1 := by
  have h := rStar_lt_one hd
  nlinarith [uStar_sq hd, uStar_pos hd]

theorem uStar_ne_zero (hd : 2 ≤ d) : uStar d ≠ 0 := ne_of_gt (uStar_pos hd)

theorem gammaStar_pos (hd : 2 ≤ d) : 0 < gammaStar d := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  exact pow_pos (div_pos (by linarith) (by linarith)) d

/-- `γ_* r_*^d = 1`: the singular endpoint multiplier is `r_*^{-d}`. -/
theorem gammaStar_mul_rStar_pow (hd : 2 ≤ d) : gammaStar d * rStar d ^ d = 1 := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : ((d : ℝ) - 1) ≠ 0 := by linarith
  have hdd : (d : ℝ) ≠ 0 := by linarith
  rw [gammaStar, rStar_eq, ← mul_pow]
  have hone : (d : ℝ) / ((d : ℝ) - 1) * (((d : ℝ) - 1) / (d : ℝ)) = 1 := by field_simp
  rw [hone, one_pow]

theorem betaD_pos (hd : 2 ≤ d) : 0 < betaD d :=
  div_pos (gammaStar_pos hd) (dpos hd)

/-- `β_d · d = γ_*`. -/
theorem betaD_mul_d (hd : 2 ≤ d) : betaD d * (d : ℝ) = gammaStar d := by
  have hdd : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  rw [betaD]
  field_simp

/-! ## The higher derivatives of `J_p`

`J_p''(u) = 1/(u(1-u)) = 1/u + 1/(1-u)`, so the higher derivatives are `p`-free. -/

/-- The third derivative `J_p'''(u) = -1/u² + 1/(1-u)²`. -/
noncomputable def Jp3 (u : ℝ) : ℝ := -(1 / u ^ 2) + 1 / (1 - u) ^ 2

/-- The fourth derivative `J_p''''(u) = 2/u³ + 2/(1-u)³`. -/
noncomputable def Jp4 (u : ℝ) : ℝ := 2 / u ^ 3 + 2 / (1 - u) ^ 3

/-- The fifth derivative `J_p^{(5)}(u) = -6/u⁴ + 6/(1-u)⁴`. -/
noncomputable def Jp5 (u : ℝ) : ℝ := -(6 / u ^ 4) + 6 / (1 - u) ^ 4

/-- `J_p''(u) = 1/u + 1/(1-u)` on `(0,1)`: the partial-fraction form used to differentiate
it repeatedly. -/
theorem Jp''_eq_add {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Jp'' u = 1 / u ^ 1 + 1 / (1 - u) ^ 1 := by
  have h1 : u ≠ 0 := ne_of_gt hu0
  have h2 : (1 : ℝ) - u ≠ 0 := by linarith
  rw [Jp'']
  field_simp
  ring

/-- Derivative of `x ↦ 1/x^n` away from the origin. -/
private theorem hasDerivAt_one_div_pow (n : ℕ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun x : ℝ => 1 / x ^ n) (-((n : ℝ) * u ^ (n - 1)) / (u ^ n) ^ 2) u := by
  have hp : HasDerivAt (fun x : ℝ => x ^ n) ((n : ℝ) * u ^ (n - 1)) u := hasDerivAt_pow n u
  have h : HasDerivAt (fun x : ℝ => (x ^ n)⁻¹) (-((n : ℝ) * u ^ (n - 1)) / (u ^ n) ^ 2) u :=
    hp.inv (pow_ne_zero n hu)
  simpa only [one_div] using h

/-- Derivative of `x ↦ 1/(1-x)^n` away from `x = 1`. -/
private theorem hasDerivAt_one_div_one_sub_pow (n : ℕ) {u : ℝ} (hu : (1 : ℝ) - u ≠ 0) :
    HasDerivAt (fun x : ℝ => 1 / (1 - x) ^ n)
      (-((n : ℝ) * (1 - u) ^ (n - 1) * (-1)) / ((1 - u) ^ n) ^ 2) u := by
  have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub (1 : ℝ)
  have hp : HasDerivAt (fun x : ℝ => (1 - x) ^ n) ((n : ℝ) * (1 - u) ^ (n - 1) * (-1)) u :=
    hsub.pow n
  have h : HasDerivAt (fun x : ℝ => ((1 - x) ^ n)⁻¹)
      (-((n : ℝ) * (1 - u) ^ (n - 1) * (-1)) / ((1 - u) ^ n) ^ 2) u :=
    hp.inv (pow_ne_zero n hu)
  simpa only [one_div] using h

theorem hasDerivAt_Jp'' {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt Jp'' (Jp3 u) u := by
  have h1 : u ≠ 0 := ne_of_gt hu0
  have h2 : (1 : ℝ) - u ≠ 0 := by linarith
  have e := (hasDerivAt_one_div_pow 1 h1).add (hasDerivAt_one_div_one_sub_pow 1 h2)
  have hval : -(((1 : ℕ) : ℝ) * u ^ (1 - 1)) / (u ^ 1) ^ 2
      + -(((1 : ℕ) : ℝ) * (1 - u) ^ (1 - 1) * (-1)) / ((1 - u) ^ 1) ^ 2 = Jp3 u := by
    rw [Jp3]; norm_num [neg_div]
  rw [hval] at e
  refine e.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hu0 hu1] with x hx using Jp''_eq_add hx.1 hx.2

theorem hasDerivAt_Jp3 {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt Jp3 (Jp4 u) u := by
  have h1 : u ≠ 0 := ne_of_gt hu0
  have h2 : (1 : ℝ) - u ≠ 0 := by linarith
  have e := ((hasDerivAt_one_div_pow 2 h1).neg).add (hasDerivAt_one_div_one_sub_pow 2 h2)
  have hval : -(-(((2 : ℕ) : ℝ) * u ^ (2 - 1)) / (u ^ 2) ^ 2)
      + -(((2 : ℕ) : ℝ) * (1 - u) ^ (2 - 1) * (-1)) / ((1 - u) ^ 2) ^ 2 = Jp4 u := by
    rw [Jp4]; field_simp; ring
  rw [hval] at e
  exact e

theorem hasDerivAt_Jp4 {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt Jp4 (Jp5 u) u := by
  have h1 : u ≠ 0 := ne_of_gt hu0
  have h2 : (1 : ℝ) - u ≠ 0 := by linarith
  have e := ((hasDerivAt_one_div_pow 3 h1).const_mul (2 : ℝ)).add
    ((hasDerivAt_one_div_one_sub_pow 3 h2).const_mul (2 : ℝ))
  have hval : (2 : ℝ) * (-(((3 : ℕ) : ℝ) * u ^ (3 - 1)) / (u ^ 3) ^ 2)
      + (2 : ℝ) * (-(((3 : ℕ) : ℝ) * (1 - u) ^ (3 - 1) * (-1)) / ((1 - u) ^ 3) ^ 2)
      = Jp5 u := by
    rw [Jp5]; field_simp; ring
  rw [hval] at e
  refine e.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, Jp4]
  ring

/-! ## The rank-one scalar KKT function, and the singular endpoint gap -/

/-- The **rank-one scalar KKT function** `F_{p,γ}(z) = J_p'(z) - γ z^{d-1}` of
`lem:stationary-rank-one-bipodality`.  Equation `eq:rank-one-kkt` says that
`F_{p,γ}(f(x)f(y)) = 0` a.e. at a *rank-one KKT point*, the term Section 5 defines at
`eq:graphon-stationarity`.  Most of Section 5 takes this scalar equation as its hypothesis;
`kkt_scalar_of_stationary` (`SingularEndpoint/RankOneStationaryFamily/StationaryReduction.lean`) derives it from the
variational condition itself. -/
noncomputable def Fkkt (d : ℕ) (p γ z : ℝ) : ℝ := Jp' p z - γ * z ^ (d - 1)

/-- `𝓛_*(z) = J_{p_*}'(z) - γ_* z^{d-1}`; the function whose first three Taylor coefficients at
`r_*` vanish.  The paper calls it `𝓛_0` — it is `𝓛_h` of
`eq:kkt-parameter-shift` at `h = 0` — and states its expansion at `r_*` as
`eq:kkt-quartic-expansion`.  The Lean name is kept as `Lstar`, matching `pStar`/`gammaStar`. -/
noncomputable def Lstar (d : ℕ) (z : ℝ) : ℝ := Fkkt d (pStar d) (gammaStar d) z

/-- The **singular endpoint supporting gap**
`Γ_d(z) = J_{p_*}(z) - J_{p_*}(r_*) - β_d (z^d - r_*^d)` `eq:endpoint-supporting-gap`:
the difference between `J_{p_*}` and its supporting function at `r_*`. -/
noncomputable def Gam (d : ℕ) (z : ℝ) : ℝ :=
  Jp (pStar d) z - Jp (pStar d) (rStar d) - betaD d * (z ^ d - rStar d ^ d)

/-- The **convexity defect** `R_d(u) = (u^d - r_*^d - d r_*^{d-1}(u - r_*))/(d r_*^{d-1})`.
The paper does not name it: the proof of `lem:localization-rank-one` bounds the numerator by
`0 ≤ z^d - r_*^d - d r_*^{d-1}(z - r_*) ≤ C_dΓ_d(z)^{1/2}` (the Lean's `R_d² ≤ C_dΓ_d`) and
integrates it into a lower bound for `e(W) - e(W_h)`, which the Lean derives from the
edge/moment identity `e(W) - r_* = (∫W^d - r_*^d)/(d r_*^{d-1}) - ∫R_d(W)`.  It is the Jensen gap
that converts a `d`-th moment constraint into an edge-density statement. -/
noncomputable def Rd (d : ℕ) (u : ℝ) : ℝ :=
  (u ^ d - rStar d ^ d - (d : ℝ) * rStar d ^ (d - 1) * (u - rStar d))
    / ((d : ℝ) * rStar d ^ (d - 1))

/-- The diagonal divided slope `g_d(z) = 1/((d-1) z^{d-1}(1-z))` of
`lem:rank-one-kkt-family`: the common value at `x = y = z` of
`D(x,y) = (ℓ(y)-ℓ(x))/(x^{d-1}-y^{d-1})`. -/
noncomputable def gd (d : ℕ) (z : ℝ) : ℝ :=
  1 / (((d : ℝ) - 1) * z ^ (d - 1) * (1 - z))

/-! ## `ℓ` and `J_p'` -/

/-- `J_p'(z) = ℓ(p) - ℓ(z)`, the form in which the KKT equations of
`eq:three-value-kkt` are written. -/
theorem Jp'_eq_ell_sub {p z : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    Jp' p z = ell p - ell z := by
  have hp' : (0 : ℝ) < 1 - p := by linarith
  have hz' : (0 : ℝ) < 1 - z := by linarith
  rw [Jp', ell, ell, Real.log_div (ne_of_gt hp') (ne_of_gt hp0),
    Real.log_div (ne_of_gt hz') (ne_of_gt hz0),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (ne_of_gt hz0) (ne_of_gt hp'), Real.log_mul (ne_of_gt hz') (ne_of_gt hp0)]
  ring

/-- `ℓ(r_*) = -log(d-1)`. -/
theorem ell_rStar (hd : 2 ≤ d) : ell (rStar d) = -Real.log ((d : ℝ) - 1) := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by linarith
  have hstep : (1 - rStar d) / rStar d = ((d : ℝ) - 1)⁻¹ := by
    rw [one_sub_rStar hd, rStar_eq]
    field_simp
  rw [ell, hstep, Real.log_inv]

end UpperTailOptimizers
