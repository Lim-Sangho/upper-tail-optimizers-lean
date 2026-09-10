import UpperTailOptimizers.SingularEndpoint.Quartic
import UpperTailOptimizers.SingularEndpoint.FkktDeriv

/-!
# The exact quartic order of `Γ_d` at `r_*` (Section 7, `paper/singular_endpoint.tex`)

`SingularEndpoint/Quartic.lean` extracts from the contact identities
`eq:endpoint-entropy-derivatives` the *one-sided* consequence
`Γ_d(u) ≥ c_d |u - r_*|^4`, which is all the localization argument needs.  Section 7 needs
more: the averaged-gap display in the proof of `lem:constant-graphon-comparison`

```
∫ Γ_d(W_h) = d³h⁴/3 + O_d(h⁶)
```

is obtained by evaluating `Γ_d` at three nodes `s_h², s_h t_h, t_h²` that all collapse onto
`r_*` at rate `h`, so what is required is the exact leading coefficient, i.e. the *limit*

```
Γ_d(z) / (z - r_*)⁴  →  Γ_d⁽⁴⁾(r_*) / 24 = d⁵/(d-1)² / 24 .
```

This file supplies that limit.  The route is the two-sided version of the argument already
used in `SingularEndpoint/Quartic.lean`: `Γ_d, Γ_d', Γ_d'', Γ_d'''` all vanish at `r_*`
(`Gam_rStar`, `Lstar_rStar`, `Lstar1_rStar`, `Lstar2_rStar`) while
`Γ_d⁽⁴⁾ = 𝓛_*'''` is continuous at `r_*` with value `K = d⁵/(d-1)²` (`Lstar3_rStar`), so on
a small window `K - ε ≤ Γ_d⁽⁴⁾ ≤ K + ε` and the fourth-order Taylor bounds pinch the
quotient between `(K ∓ ε)/24`.  The ε/pinching idiom is the one of `SingularEndpoint/Order4.lean`.

Only the lower Taylor bound `quartic_lower_of_deriv4_ge` was available; its upper companion
`quartic_upper_of_deriv4_le` is obtained here by negating all the data, so no Taylor
argument is repeated.

## Contents

* `quartic_upper_of_deriv4_le` — the upper companion of `quartic_lower_of_deriv4_ge`;
* `tendsto_Gam_div_pow_four` — the two-sided limit `Γ_d(z)/(z - r_*)⁴ → K/24`;
* `Gam_le_of_near` — a plain quartic *upper* bound `Γ_d(z) ≤ C (z - r_*)⁴` on a fixed
  neighbourhood of `r_*`, used to show that the middle node contributes nothing.
-/

namespace UpperTailOptimizers

/-! ## A generic quartic upper bound -/

/-- **Fourth-order Taylor upper bound.**  If `f` is four times differentiable on `[a,b]`,
its fourth derivative is bounded *above* by `M`, and `f` together with its first three
derivatives vanishes at an interior point `c`, then `f x ≤ (M/24)(x-c)⁴` on `[a,b]`.

This is `quartic_lower_of_deriv4_ge` applied to `-f`, whose derivatives are `-f₁, …, -f₄`
and whose fourth derivative is bounded below by `-M`; nothing is reproved. -/
theorem quartic_upper_of_deriv4_le {f f1 f2 f3 f4 : ℝ → ℝ} {c M a b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x ∈ Set.Icc a b, HasDerivAt f1 (f2 x) x)
    (hf2 : ∀ x ∈ Set.Icc a b, HasDerivAt f2 (f3 x) x)
    (hf3 : ∀ x ∈ Set.Icc a b, HasDerivAt f3 (f4 x) x)
    (hle : ∀ x ∈ Set.Icc a b, f4 x ≤ M)
    (hfc : f c = 0) (h1c : f1 c = 0) (h2c : f2 c = 0) (h3c : f3 c = 0) :
    ∀ x ∈ Set.Icc a b, f x ≤ M / 24 * (x - c) ^ 4 := by
  have hneg := quartic_lower_of_deriv4_ge (f := fun y => -f y) (f1 := fun y => -f1 y)
    (f2 := fun y => -f2 y) (f3 := fun y => -f3 y) (f4 := fun y => -f4 y) (c := c) (m := -M)
    hac hcb (fun x hx => (hf x hx).neg) (fun x hx => (hf1 x hx).neg)
    (fun x hx => (hf2 x hx).neg) (fun x hx => (hf3 x hx).neg)
    (fun x hx => neg_le_neg (hle x hx)) (by simp [hfc]) (by simp [h1c]) (by simp [h2c])
    (by simp [h3c])
  intro x hx
  have h := hneg x hx
  linarith

namespace SingularEndpoint

open Filter Topology

variable {d : ℕ}

/-! ## The fourth derivative near `r_*` -/

/-- `Γ_d⁽⁴⁾ = 𝓛_*'''` is continuous at `r_*`.

`Lstar3_eq` identifies `𝓛_*'''` with `F_{p,γ_*}'''`, and `continuousAt_Fkkt3` gives joint
continuity in `(γ, z)`; composing with `z ↦ (γ_*, z)` freezes the first coordinate. -/
private theorem continuousAt_Lstar3_rStar (hd : 2 ≤ d) : ContinuousAt (Lstar3 d) (rStar d) := by
  have hpair : ContinuousAt (fun z : ℝ => ((gammaStar d, z) : ℝ × ℝ)) (rStar d) := by fun_prop
  have hjoint := continuousAt_Fkkt3 d (γ := gammaStar d) (rStar_pos hd) (rStar_lt_one hd)
  -- `Lstar3_eq` is definitional, and so is the `∘` of `ContinuousAt.comp`.
  exact hjoint.comp hpair

/-- A closed window `[r_* - δ, r_* + δ] ⊆ (0,1)` on which `Γ_d⁽⁴⁾ = 𝓛_*'''` stays within `ε`
of its singular endpoint value `K = d⁵/(d-1)²` (`Lstar3_rStar`). -/
private theorem exists_lstar3_band (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ 0 < rStar d - δ ∧ rStar d + δ < 1 ∧
      ∀ x ∈ Set.Icc (rStar d - δ) (rStar d + δ),
        (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 - ε ≤ Lstar3 d x ∧
          Lstar3 d x ≤ (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 + ε := by
  have hr0 := rStar_pos hd
  have hr1 := rStar_lt_one hd
  have hcont := continuousAt_Lstar3_rStar hd
  have hval := Lstar3_rStar hd
  have hA : ∀ᶠ z in 𝓝 (rStar d), (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 - ε ≤ Lstar3 d z :=
    hcont.eventually (eventually_ge_nhds (by rw [hval]; linarith))
  have hB : ∀ᶠ z in 𝓝 (rStar d), Lstar3 d z ≤ (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 + ε :=
    hcont.eventually (eventually_le_nhds (by rw [hval]; linarith))
  have hI : ∀ᶠ z in 𝓝 (rStar d), z ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhds hr0 hr1
  have hev : ∀ᶠ z in 𝓝 (rStar d), (0 < z ∧ z < 1) ∧
      ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 - ε ≤ Lstar3 d z ∧
        Lstar3 d z ≤ (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 + ε) := by
    filter_upwards [hA, hB, hI] with z h1 h2 h3 using ⟨⟨h3.1, h3.2⟩, h1, h2⟩
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hkey : ∀ x ∈ Set.Icc (rStar d - η / 2) (rStar d + η / 2), (0 < x ∧ x < 1) ∧
      ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 - ε ≤ Lstar3 d x ∧
        Lstar3 d x ≤ (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 + ε) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    refine hball ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  exact ⟨η / 2, by linarith, (hkey _ ⟨le_rfl, by linarith⟩).1.1,
    (hkey _ ⟨by linarith, le_rfl⟩).1.2, fun x hx => (hkey x hx).2⟩

/-- The two Taylor bounds on a window around `r_*`: for every `ε > 0` there is a
`δ > 0` with

```
(K - ε)/24 · (z - r_*)⁴  ≤  Γ_d(z)  ≤  (K + ε)/24 · (z - r_*)⁴,     K = d⁵/(d-1)²,
```

for all `z ∈ [r_* - δ, r_* + δ]`.  This is `quartic_lower_of_deriv4_ge` and
`quartic_upper_of_deriv4_le` applied to `f = Γ_d` with derivatives `𝓛_*, 𝓛_*', 𝓛_*'', 𝓛_*'''`
on the band produced by `exists_lstar3_band`. -/
private theorem exists_gam_quartic_band (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Set.Icc (rStar d - δ) (rStar d + δ),
      ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 - ε) / 24 * (z - rStar d) ^ 4 ≤ Gam d z ∧
        Gam d z ≤ ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 + ε) / 24 * (z - rStar d) ^ 4 := by
  obtain ⟨δ, hδ, hlo, hhi, hL3⟩ := exists_lstar3_band hd hε
  have hmem : ∀ x ∈ Set.Icc (rStar d - δ) (rStar d + δ), 0 < x ∧ x < 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hlow := quartic_lower_of_deriv4_ge (f := Gam d) (f1 := Lstar d) (f2 := Lstar1 d)
    (f3 := Lstar2 d) (f4 := Lstar3 d) (c := rStar d)
    (m := (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 - ε) (by linarith) (by linarith)
    (fun x hx => hasDerivAt_Gam hd (hmem x hx).1 (hmem x hx).2)
    (fun x hx => hasDerivAt_Lstar hd (hmem x hx).1 (hmem x hx).2)
    (fun x hx => hasDerivAt_Lstar1 hd (hmem x hx).1 (hmem x hx).2)
    (fun x hx => hasDerivAt_Lstar2 hd (hmem x hx).1 (hmem x hx).2)
    (fun x hx => (hL3 x hx).1) (Gam_rStar hd) (Lstar_rStar hd) (Lstar1_rStar hd)
    (Lstar2_rStar hd)
  have hupp := quartic_upper_of_deriv4_le (f := Gam d) (f1 := Lstar d) (f2 := Lstar1 d)
    (f3 := Lstar2 d) (f4 := Lstar3 d) (c := rStar d)
    (M := (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 + ε) (by linarith) (by linarith)
    (fun x hx => hasDerivAt_Gam hd (hmem x hx).1 (hmem x hx).2)
    (fun x hx => hasDerivAt_Lstar hd (hmem x hx).1 (hmem x hx).2)
    (fun x hx => hasDerivAt_Lstar1 hd (hmem x hx).1 (hmem x hx).2)
    (fun x hx => hasDerivAt_Lstar2 hd (hmem x hx).1 (hmem x hx).2)
    (fun x hx => (hL3 x hx).2) (Gam_rStar hd) (Lstar_rStar hd) (Lstar1_rStar hd)
    (Lstar2_rStar hd)
  exact ⟨δ, hδ, fun z hz => ⟨hlow z hz, hupp z hz⟩⟩

/-! ## The two-sided quartic limit -/

/-- **`Γ_d` vanishes to order exactly four at `r_*`.**

```
Γ_d(z) / (z - r_*)⁴  →  d⁵/(d-1)² / 24        as `z → r_*`, `z ≠ r_*`.
```

The numerator `d⁵/(d-1)² = Γ_d⁽⁴⁾(r_*)` is `Lstar3_rStar`.  Feeding `z = s_h², s_h t_h,
t_h²` into this limit and using the node rates `(s_h² - r_*)/h → -2u_*`,
`(t_h² - r_*)/h → +2u_*` is what produces the constant `d³/3` of the averaged-gap display
in the proof of `lem:constant-graphon-comparison`. -/
theorem tendsto_Gam_div_pow_four (hd : 2 ≤ d) :
    Tendsto (fun z : ℝ => Gam d z / (z - rStar d) ^ 4) (𝓝[≠] (rStar d))
      (𝓝 ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 24)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hband⟩ := exists_gam_quartic_band hd hε
  have hIcc : Set.Icc (rStar d - δ) (rStar d + δ) ∈ 𝓝[≠] (rStar d) :=
    nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith))
  filter_upwards [self_mem_nhdsWithin, hIcc] with z hzne hzmem
  have hne : z - rStar d ≠ 0 := sub_ne_zero.mpr hzne
  have hpos : 0 < (z - rStar d) ^ 4 := by positivity
  obtain ⟨hl, hu⟩ := hband z hzmem
  have hl' : ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 - ε) / 24 ≤ Gam d z / (z - rStar d) ^ 4 :=
    (le_div_iff₀ hpos).mpr hl
  have hu' : Gam d z / (z - rStar d) ^ 4 ≤ ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 + ε) / 24 :=
    (div_le_iff₀ hpos).mpr hu
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-! ## A quartic upper bound near `r_*` -/

/-- **A plain quartic majorant near `r_*`.**

The chosen shape: there are a constant `C > 0` and a radius `δ > 0` such that

```
Γ_d(z) ≤ C · (z - r_*)⁴        for all `z ∈ [r_* - δ, r_* + δ]`,
```

with `C` and `δ` existentially quantified (no `z ≠ r_*` is required, and the inequality is
trivially true at `z = r_*` since both sides vanish).

This is the middle-node estimate of the averaged-gap evaluation in the proof of
`lem:constant-graphon-comparison`.  There the argument is
`s_h t_h`, which satisfies `(s_h t_h - r_*)/h → 0` but may coincide with `r_*` at isolated
values of `h`; squeezing `Γ_d(s_h t_h)` between `0` (`Gam_nonneg`) and
`C (s_h t_h - r_*)⁴` therefore avoids a non-vanishing hypothesis that need not hold, and
shows the middle block contributes `o(h⁴)`. -/
theorem Gam_le_of_near (hd : 2 ≤ d) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ z ∈ Set.Icc (rStar d - δ) (rStar d + δ), Gam d z ≤ C * (z - rStar d) ^ 4 := by
  obtain ⟨δ, hδ, hband⟩ := exists_gam_quartic_band hd (ε := 1) one_pos
  exact ⟨((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 + 1) / 24, δ, by positivity, hδ,
    fun z hz => (hband z hz).2⟩

end SingularEndpoint

end UpperTailOptimizers
