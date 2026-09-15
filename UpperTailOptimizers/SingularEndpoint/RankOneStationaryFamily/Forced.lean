import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Contact

/-!
# The singular endpoint values are forced (Section 5, `paper/sections/singular.tex`)

`sec:singular-endpoint` opens by displaying the distinguished point

```
r_* = (d-1)/d,   p_* = (d-1)/((d-1) + exp(d/(d-1))),
```

and `sec:rank-one-stationary-family` sets `γ_* = (d/(d-1))^d = r_*^{-d}`.  This file proves a
converse that the paper does not state: *these values are forced whenever the two factor
values in such an analytic family coalesce at an interior point*.

Coalescence means that the three roots `s²`, `st`, `t²` of `eq:three-value-kkt`
merge at a common interior value `w`.  In the limit, the rank-one scalar KKT function
`F_{p,γ}(z) = J_p'(z) - γ z^{d-1}` of `eq:rank-one-kkt` therefore has a
**triple zero** at `w`, which is exactly the system
`eq:endpoint-entropy-derivatives`.  The content of this file is the converse of
`SingularEndpoint/RankOneStationaryFamily/Contact.lean`: a triple zero can only sit at `(w, p, γ) = (r_*, p_*, γ_*)`.

The key computation is `triple_zero_abscissa`.  Eliminating `γ` between the second and the
third contact equations turns them into `w · J^{(3)}(w) = (d-2) · J''(w)`, that is
`(2w-1)/(w(1-w)²) = (d-2)/(w(1-w))`, i.e. `d·w = d-1`.

## Contents

* `ell_strictAntiOn`, `ell_injOn` — the log-odds `ℓ(z) = log((1-z)/z)` is strictly
  decreasing, hence injective, on `(0,1)`;
* `triple_zero_abscissa` — the last two contact equations force `w = r_*`;
* `triple_zero_multiplier` — the second contact equation then forces `γ = γ_*`;
* `triple_zero_density` — the first contact equation then forces `p = p_*`;
* `triple_contact_forced` — the assembled statement.
-/

namespace UpperTailOptimizers

open Real

variable {d : ℕ}

/-! ## Strict monotonicity of the log-odds -/

/-- The log-odds `ℓ(z) = log((1-z)/z)` is strictly decreasing on `(0,1)`.

No calculus is needed: `z ↦ (1-z)/z` is positive and strictly decreasing there, and
`Real.log` is strictly increasing on the positives. -/
theorem ell_strictAntiOn : StrictAntiOn ell (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := hx.1
  have hy0 : (0 : ℝ) < y := hy.1
  have hy1 : y < 1 := hy.2
  have hpos : (0 : ℝ) < (1 - y) / y := div_pos (by linarith) hy0
  have hlt : (1 - y) / y < (1 - x) / x := by
    rw [div_lt_div_iff₀ hy0 hx0]
    nlinarith
  exact Real.log_lt_log hpos hlt

/-- The log-odds is injective on `(0,1)`. -/
theorem ell_injOn : Set.InjOn ell (Set.Ioo (0 : ℝ) 1) :=
  ell_strictAntiOn.injOn

/-! ## The forced abscissa -/

/-- **The forced abscissa.**  If the rank-one KKT function `F_{p,γ}` has a zero of order at
least three at an interior point `w` — so that the second and third equations of
`eq:endpoint-entropy-derivatives` hold at `w` with multiplier `γ` — then `w = r_*`.

Only the last two contact equations are used; the density `p` never enters, since
`J_p''` and `J_p^{(3)}` do not depend on `p`.  Eliminating `γ` gives
`w · J^{(3)}(w) = (d-2) · J''(w)`, that is `2w - 1 = (d-2)(1-w)`, i.e. `d·w = d-1`. -/
theorem triple_zero_abscissa (hd : 2 ≤ d) {g w : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    (h1 : Jp'' w - g * ((d : ℝ) - 1) * w ^ (d - 2) = 0)
    (h2 : Jp3 w - g * ((d : ℝ) - 1) * ((d : ℝ) - 2) * w ^ (d - 3) = 0) :
    w = rStar d := by
  have h1lt : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hwne : w ≠ 0 := ne_of_gt hw0
  have hw1' : (1 : ℝ) - w ≠ 0 := by linarith
  rcases eq_or_lt_of_le hd with hd2 | hd3
  · -- `d = 2`: the factor `(d:ℝ) - 2` vanishes, so `J^{(3)}(w) = 0` forces `w = 1/2`.
    have hdeq : (d : ℝ) = 2 := by rw [← hd2]; norm_num
    rw [hdeq] at h2
    norm_num [Jp3] at h2
    rw [rStar_eq, hdeq]
    have hsq : w ^ 2 ≠ 0 := pow_ne_zero 2 hwne
    have hsq' : ((1 : ℝ) - w) ^ 2 ≠ 0 := pow_ne_zero 2 hw1'
    field_simp at h2
    nlinarith [h2]
  · -- `3 ≤ d`: multiply the third equation by `w` and substitute the second.
    have hd3' : 3 ≤ d := hd3
    have hpow : w * w ^ (d - 3) = w ^ (d - 2) := by
      rw [show d - 2 = (d - 3) + 1 from by omega, pow_succ]
      ring
    -- `w · J^{(3)}(w) = (d-2) · J''(w)`
    have hkey : w * Jp3 w = ((d : ℝ) - 2) * Jp'' w := by
      have h2' : Jp3 w = g * ((d : ℝ) - 1) * ((d : ℝ) - 2) * w ^ (d - 3) := by linarith
      have e2 : w * Jp3 w
          = ((d : ℝ) - 2) * (g * ((d : ℝ) - 1) * w ^ (d - 2)) := by
        rw [h2', ← hpow]; ring
      rw [e2]
      have : g * ((d : ℝ) - 1) * w ^ (d - 2) = Jp'' w := by linarith
      rw [this]
    rw [Jp3, Jp''] at hkey
    rw [rStar_eq]
    have hmul : w * ((d : ℝ)) = (d : ℝ) - 1 := by
      field_simp at hkey
      nlinarith [hkey]
    field_simp
    linarith [hmul]

/-! ## The forced multiplier and the forced density -/

/-- **The forced multiplier.**  Once the abscissa is `r_*`, the second contact equation
determines the multiplier: `γ = γ_*`.

`triple_contact_two` says that the same equation holds with `γ := γ_*`, so the two differ
by the nonzero factor `(d-1) r_*^{d-2}`. -/
theorem triple_zero_multiplier (hd : 2 ≤ d) {g : ℝ}
    (h1 : Jp'' (rStar d) - g * ((d : ℝ) - 1) * rStar d ^ (d - 2) = 0) :
    g = gammaStar d := by
  have h1lt : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hfac : ((d : ℝ) - 1) * rStar d ^ (d - 2) ≠ 0 :=
    ne_of_gt (mul_pos (by linarith) (pow_pos (rStar_pos hd) _))
  have htwo := triple_contact_two hd
  have hzero : (g - gammaStar d) * (((d : ℝ) - 1) * rStar d ^ (d - 2)) = 0 := by
    rw [htwo] at h1; ring_nf; ring_nf at h1; linarith
  rcases mul_eq_zero.mp hzero with h | h
  · linarith [sub_eq_zero.mp h]
  · exact absurd h hfac

/-- **The forced ambient density.**  Once the abscissa is `r_*` and the multiplier is `γ_*`,
the first contact equation `F_{p,γ_*}(r_*) = 0` determines the density: `p = p_*`.

Indeed `J_p'(r_*) = ℓ(p) - ℓ(r_*)` by `Jp'_eq_ell_sub`, so the equation reads
`ℓ(p) = γ_* r_*^{d-1} + ℓ(r_*)`; `triple_contact_one` says `p_*` satisfies the same
equation, and `ell_injOn` finishes. -/
theorem triple_zero_density (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h0 : Fkkt d p (gammaStar d) (rStar d) = 0) : p = pStar d := by
  have hr0 : (0 : ℝ) < rStar d := rStar_pos hd
  have hr1 : rStar d < 1 := rStar_lt_one hd
  have hps0 : (0 : ℝ) < pStar d := pStar_pos hd
  have hps1 : pStar d < 1 := pStar_lt_one hd
  have hone := triple_contact_one hd
  have heq : Jp' p (rStar d) = Jp' (pStar d) (rStar d) := by
    rw [hone]
    rw [Fkkt] at h0
    linarith
  rw [Jp'_eq_ell_sub hp0 hp1 hr0 hr1, Jp'_eq_ell_sub hps0 hps1 hr0 hr1] at heq
  exact ell_injOn ⟨hp0, hp1⟩ ⟨hps0, hps1⟩ (by linarith)

/-! ## The assembled claim -/

/-- **The singular endpoint values are forced** (a converse not stated in the paper).

If the rank-one scalar KKT function `F_{p,γ}(z) = J_p'(z) - γ z^{d-1}` of
`eq:rank-one-kkt` has a **triple zero** at an interior point `w` — the
limiting form of `eq:three-value-kkt` when the two factor values of a coalescing
rank-one stationary family merge — then necessarily

```
w = r_*,   γ = γ_*,   p = p_*.
```

This is the converse of the triple-contact identities of `SingularEndpoint/RankOneStationaryFamily/Contact.lean`: those
say the displayed point *is* a triple contact, this says it is the *only* one. -/
theorem triple_contact_forced (hd : 2 ≤ d) {p g w : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hw0 : 0 < w) (hw1 : w < 1)
    (h0 : Fkkt d p g w = 0)
    (h1 : Jp'' w - g * ((d : ℝ) - 1) * w ^ (d - 2) = 0)
    (h2 : Jp3 w - g * ((d : ℝ) - 1) * ((d : ℝ) - 2) * w ^ (d - 3) = 0) :
    w = rStar d ∧ g = gammaStar d ∧ p = pStar d := by
  have hw : w = rStar d := triple_zero_abscissa hd hw0 hw1 h1 h2
  subst hw
  have hg : g = gammaStar d := triple_zero_multiplier hd h1
  subst hg
  exact ⟨rfl, rfl, triple_zero_density hd hp0 hp1 h0⟩

end UpperTailOptimizers
