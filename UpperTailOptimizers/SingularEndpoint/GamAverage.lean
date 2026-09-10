import UpperTailOptimizers.SingularEndpoint.GamQuartic
import UpperTailOptimizers.SingularEndpoint.FamilyRates
import UpperTailOptimizers.SingularEndpoint.CostGap

/-!
# The averaged gap along the coalescing family (Section 7, `paper/singular_endpoint.tex`)

The proof of `lem:constant-graphon-comparison` in `paper/singular_endpoint.tex` evaluates the averaged
supporting gap of the candidate `W_h`,

```
∫ Γ_d(W_h) = d³h⁴/3 + O_d(h⁶) ,
```

an unlabelled display, one of
the two halves of that cost-gap lemma.  This file proves the limit form

```
∫ Γ_d(W_h) / h⁴  →  d³/3      as `h → 0`, `h ≠ 0`,
```

i.e. the displayed identity without its `O(h⁶)` refinement, which would need the family
expansions `eq:rank-one-parameter-expansions` that `KKTFamily` deliberately omits.

The two inputs are already isolated:

* `tendsto_Gam_div_pow_four` (`SingularEndpoint/GamQuartic.lean`) — `Γ_d` vanishes to order exactly
  four at `r_*`, with `Γ_d(z)/(z - r_*)⁴ → K/24`, `K = d⁵/(d-1)²`; and its companion
  `Gam_le_of_near`, a plain quartic majorant on a fixed window;
* `tendsto_sVal_sq_rate`, `tendsto_tVal_sq_rate`, `tendsto_sVal_mul_tVal_rate`,
  `tendsto_alph` (`SingularEndpoint/FamilyRates.lean`) — the three node rates `-2u_*`, `+2u_*`, `0`
  and the block weight limit `1/2`.

Given those, the block form `gamInt_graphon` of the integral is a sum of three terms and each
is treated separately.

* **Outer nodes.**  `Γ_d(s_h²)/h⁴ = [Γ_d(z)/(z - r_*)⁴]_{z = s_h²} · [(s_h² - r_*)/h]⁴`.  The
  first factor is `tendsto_Gam_div_pow_four` composed with `h ↦ s_h²`, which is legitimate
  because the rate `-2u_*` is *nonzero*, so `s_h² ≠ r_*` eventually and the composition lands
  in the punctured neighbourhood.  The limit is `K/24 · (2u_*)⁴ = 2d³/3` by
  `quartic_leading_const`, since `u_*⁴ = r_*² = (d-1)²/d²`.
* **Middle node.**  Here the rate is `0`, so `s_h t_h` may hit `r_*` at isolated `h` and no
  composition is available.  Instead `Γ_d(s_h t_h)/h⁴` is squeezed between `0` (`Gam_nonneg`)
  and `C·((s_h t_h - r_*)/h)⁴ → 0` (`Gam_le_of_near`): the middle block contributes nothing.
* **Assembly.**  With `α_h → 1/2` the total is `(1/4 + 1/4)·(2d³/3) = d³/3`.

## Contents

* `quartic_leading_const` — the arithmetic `K/24 · L⁴ = 2d³/3` whenever `L² = 4r_*`;
* `tendsto_Gam_sVal_sq`, `tendsto_Gam_tVal_sq` — the outer node limits `2d³/3`;
* `tendsto_Gam_cross` — the middle node limit `0`;
* `tendsto_gamInt_block` — **the averaged-gap evaluation** of the proof of
  `lem:constant-graphon-comparison`, in the block form of `gamInt_graphon`;
* `tendsto_gamInt_graphon` — the same limit read back on `∫Γ_d(W_h)`;
* `tendsto_node_of_rate` — a node with a finite rate at `0` converges;
* `eventually_abs_lt_h₀` — the parameter is eventually inside the family window.  The last
  two are shared with `SingularEndpoint/GamRVal.lean`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

variable {d : ℕ}

/-! ## The leading constant -/

/-- **The leading constant of the averaged-gap evaluation** in the proof of
`lem:constant-graphon-comparison`.

For any `L` with `L² = 4r_*` — both outer rates `∓2u_*` qualify, since `u_*² = r_*` —

```
Γ_d⁽⁴⁾(r_*)/24 · L⁴ = (d⁵/(d-1)²)/24 · 16r_*² = 2d³/3 ,
```

using `r_* = (d-1)/d`.  This is the only arithmetic in the file. -/
theorem quartic_leading_const (hd : 2 ≤ d) {L : ℝ} (hL : L ^ 2 = 4 * rStar d) :
    (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 24 * L ^ 4 = 2 * (d : ℝ) ^ 3 / 3 := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hd1 : (d : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h1)
  have h4 : L ^ 4 = 16 * (((d : ℝ) - 1) / (d : ℝ)) ^ 2 := by
    have hsq : L ^ 4 = (L ^ 2) ^ 2 := by ring
    rw [hsq, hL, rStar_eq]
    ring
  rw [h4]
  field_simp
  ring

/-! ## Reading a node off its rate -/

/-- A node with a finite rate converges: if `(f h - c)/h` has a limit as `h → 0`, `h ≠ 0`,
then `f h → c`, because `f h - c = h · (f h - c)/h`. -/
theorem tendsto_node_of_rate {f : ℝ → ℝ} {L c : ℝ}
    (hf : Tendsto (fun x : ℝ => (f x - c) / x) (𝓝[≠] (0 : ℝ)) (𝓝 L)) :
    Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 c) := by
  have hid : Tendsto (fun x : ℝ => x) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hprod := hid.mul hf
  rw [zero_mul] at hprod
  have hsub : Tendsto (fun x : ℝ => f x - c) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxne : x ≠ 0 := hx
    field_simp
  have hadd := hsub.add_const c
  rw [zero_add] at hadd
  exact hadd.congr fun x => by ring

/-- A node with a *nonzero* rate eventually avoids its limit: if `(f h - c)/h → L ≠ 0` then
`f h ≠ c` for all small `h ≠ 0`.  This is what lets the outer nodes be fed into the punctured
limit `tendsto_Gam_div_pow_four`. -/
private theorem eventually_node_ne {f : ℝ → ℝ} {L c : ℝ} (hL : L ≠ 0)
    (hf : Tendsto (fun x : ℝ => (f x - c) / x) (𝓝[≠] (0 : ℝ)) (𝓝 L)) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ), f x ≠ c := by
  filter_upwards [hf.eventually_ne hL] with x hx hfx
  exact hx (by rw [hfx, sub_self, zero_div])

/-! ## The outer nodes -/

/-- **The generic outer-node limit.**  If a node `f` approaches `r_*` at a nonzero rate `L`,
then `Γ_d(f h)/h⁴ → (K/24)·L⁴` with `K = d⁵/(d-1)²`.

The factorisation is `Γ_d(f h)/h⁴ = [Γ_d(z)/(z - r_*)⁴]_{z = f h} · [(f h - r_*)/h]⁴`, valid
once `f h ≠ r_*` and `h ≠ 0`; the first factor converges by `tendsto_Gam_div_pow_four`
composed with `f`, which lands in `𝓝[≠] r_*` by `eventually_node_ne`. -/
private theorem tendsto_Gam_node_div (hd : 2 ≤ d) {f : ℝ → ℝ} {L : ℝ} (hL : L ≠ 0)
    (hf : Tendsto (fun x : ℝ => (f x - rStar d) / x) (𝓝[≠] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun x : ℝ => Gam d (f x) / x ^ 4) (𝓝[≠] (0 : ℝ))
      (𝓝 ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 / 24 * L ^ 4)) := by
  have hne := eventually_node_ne hL hf
  have hpunc : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝[≠] (rStar d)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f (tendsto_node_of_rate hf) hne
  have hmul := ((tendsto_Gam_div_pow_four hd).comp hpunc).mul (hf.pow 4)
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hne] with x hx hfx
  have hxne : x ≠ 0 := hx
  have hzne : f x - rStar d ≠ 0 := sub_ne_zero.mpr hfx
  simp only [Function.comp_apply]
  field_simp

/-- **The lower outer node**: `Γ_d(s_h²)/h⁴ → 2d³/3`.  The rate is `-2u_* ≠ 0`
(`tendsto_sVal_sq_rate`, `uStar_pos`) and `(-2u_*)² = 4r_*`. -/
theorem tendsto_Gam_sVal_sq (hd : 2 ≤ d) (B : KKTFamily d) :
    Tendsto (fun h : ℝ => Gam d (B.sVal h ^ 2) / h ^ 4) (𝓝[≠] (0 : ℝ))
      (𝓝 (2 * (d : ℝ) ^ 3 / 3)) := by
  have hu : 0 < uStar d := uStar_pos hd
  have hL : -(2 * uStar d) ≠ 0 := by intro h; nlinarith
  have hsq : (-(2 * uStar d)) ^ 2 = 4 * rStar d := by rw [← uStar_sq hd]; ring
  have h := tendsto_Gam_node_div hd hL (tendsto_sVal_sq_rate hd B)
  rwa [quartic_leading_const hd hsq] at h

/-- **The upper outer node**: `Γ_d(t_h²)/h⁴ → 2d³/3`.  Same as `tendsto_Gam_sVal_sq` with the
rate `+2u_*`; the fourth power erases the sign. -/
theorem tendsto_Gam_tVal_sq (hd : 2 ≤ d) (B : KKTFamily d) :
    Tendsto (fun h : ℝ => Gam d (B.tVal h ^ 2) / h ^ 4) (𝓝[≠] (0 : ℝ))
      (𝓝 (2 * (d : ℝ) ^ 3 / 3)) := by
  have hu : 0 < uStar d := uStar_pos hd
  have hL : 2 * uStar d ≠ 0 := by intro h; nlinarith
  have hsq : (2 * uStar d) ^ 2 = 4 * rStar d := by rw [← uStar_sq hd]; ring
  have h := tendsto_Gam_node_div hd hL (tendsto_tVal_sq_rate hd B)
  rwa [quartic_leading_const hd hsq] at h

/-! ## The middle node -/

/-- The parameter is eventually inside the family's window `(-h₀, h₀)`, so the family's
admissibility lemmas apply. -/
theorem eventually_abs_lt_h₀ (B : KKTFamily d) :
    ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < B.h₀ := by
  refine eventually_nhdsWithin_of_eventually_nhds ?_
  have hmem : Set.Ioo (-B.h₀) B.h₀ ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [B.h₀_pos]) B.h₀_pos
  filter_upwards [hmem] with h hh
  rw [abs_lt]
  exact ⟨hh.1, hh.2⟩

/-- **The middle node contributes nothing**: `Γ_d(s_h t_h)/h⁴ → 0`.

The cross rate `(s_h t_h - r_*)/h → 0` vanishes, so the node may coincide with `r_*` at
isolated `h` and `tendsto_Gam_div_pow_four` cannot be composed with it.  Squeezing avoids the
issue: `0 ≤ Γ_d(s_h t_h) ≤ C(s_h t_h - r_*)⁴` by `Gam_nonneg` and `Gam_le_of_near`, and after
dividing by `h⁴ > 0` the majorant is `C·((s_h t_h - r_*)/h)⁴ → C·0⁴ = 0`. -/
theorem tendsto_Gam_cross (hd : 2 ≤ d) (B : KKTFamily d) :
    Tendsto (fun h : ℝ => Gam d (B.sVal h * B.tVal h) / h ^ 4) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, δ, _hC, hδ, hband⟩ := Gam_le_of_near hd
  have hrate := tendsto_sVal_mul_tVal_rate hd B
  have hnode : Tendsto (fun h : ℝ => B.sVal h * B.tVal h) (𝓝[≠] (0 : ℝ)) (𝓝 (rStar d)) :=
    tendsto_node_of_rate hrate
  have hIcc : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      B.sVal h * B.tVal h ∈ Set.Icc (rStar d - δ) (rStar d + δ) :=
    hnode (Icc_mem_nhds (by linarith) (by linarith))
  have hmaj : Tendsto (fun h : ℝ => C * ((B.sVal h * B.tVal h - rStar d) / h) ^ 4)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h := (hrate.pow 4).const_mul C
    rwa [show (0 : ℝ) ^ 4 = 0 from by ring, mul_zero] at h
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [self_mem_nhdsWithin, eventually_abs_lt_h₀ B] with h hx hb
    have hxne : h ≠ 0 := hx
    have hpos : (0 : ℝ) < h ^ 4 := by positivity
    exact div_nonneg
      (Gam_nonneg hd (KKTFamily.cross_mem hb).1 (KKTFamily.cross_mem hb).2) hpos.le
  · filter_upwards [self_mem_nhdsWithin, hIcc] with h hx hmem
    have hxne : h ≠ 0 := hx
    have hpos : (0 : ℝ) < h ^ 4 := by positivity
    have hrw : C * ((B.sVal h * B.tVal h - rStar d) / h) ^ 4
        = C * (B.sVal h * B.tVal h - rStar d) ^ 4 / h ^ 4 := by
      rw [div_pow, mul_div_assoc]
    rw [hrw]
    gcongr
    exact hband _ hmem

/-! ## The average -/

/-- **The averaged-gap evaluation** of the proof of `lem:constant-graphon-comparison`, in the block
form of `gamInt_graphon`:

```
(α_h² Γ_d(s_h²) + 2α_h(1-α_h) Γ_d(s_h t_h) + (1-α_h)² Γ_d(t_h²)) / h⁴  →  d³/3 .
```

The three block coefficients converge to `1/4`, `1/2`, `1/4` by `tendsto_alph`, and the three
quotients to `2d³/3`, `0`, `2d³/3`, so the total is `(1/4 + 1/4)·2d³/3 = d³/3`.  This is the
`O_d(h⁶)`-free content of the paper's expansion; the remainder term would need the family
expansions `eq:rank-one-parameter-expansions`. -/
theorem tendsto_gamInt_block (hd : 2 ≤ d) (B : KKTFamily d) :
    Tendsto (fun h : ℝ =>
        (B.alph h ^ 2 * Gam d (B.sVal h ^ 2)
          + 2 * B.alph h * (1 - B.alph h) * Gam d (B.sVal h * B.tVal h)
          + (1 - B.alph h) ^ 2 * Gam d (B.tVal h ^ 2)) / h ^ 4)
      (𝓝[≠] (0 : ℝ)) (𝓝 ((d : ℝ) ^ 3 / 3)) := by
  have halph : Tendsto B.alph (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) :=
    (tendsto_alph B).mono_left nhdsWithin_le_nhds
  have hbeta : Tendsto (fun h : ℝ => 1 - B.alph h) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
    have h : Tendsto (fun h : ℝ => (1 : ℝ) - B.alph h) (𝓝[≠] (0 : ℝ))
        (𝓝 ((1 : ℝ) - 1 / 2)) := tendsto_const_nhds.sub halph
    rwa [show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num] at h
  have h1 : Tendsto (fun h : ℝ => B.alph h ^ 2 * (Gam d (B.sVal h ^ 2) / h ^ 4))
      (𝓝[≠] (0 : ℝ)) (𝓝 ((1 / 2 : ℝ) ^ 2 * (2 * (d : ℝ) ^ 3 / 3))) :=
    (halph.pow 2).mul (tendsto_Gam_sVal_sq hd B)
  have h2 : Tendsto (fun h : ℝ =>
      2 * B.alph h * (1 - B.alph h) * (Gam d (B.sVal h * B.tVal h) / h ^ 4))
      (𝓝[≠] (0 : ℝ)) (𝓝 (2 * (1 / 2 : ℝ) * (1 / 2 : ℝ) * 0)) :=
    ((halph.const_mul 2).mul hbeta).mul (tendsto_Gam_cross hd B)
  have h3 : Tendsto (fun h : ℝ => (1 - B.alph h) ^ 2 * (Gam d (B.tVal h ^ 2) / h ^ 4))
      (𝓝[≠] (0 : ℝ)) (𝓝 ((1 / 2 : ℝ) ^ 2 * (2 * (d : ℝ) ^ 3 / 3))) :=
    (hbeta.pow 2).mul (tendsto_Gam_tVal_sq hd B)
  have hsum := (h1.add h2).add h3
  rw [show (1 / 2 : ℝ) ^ 2 * (2 * (d : ℝ) ^ 3 / 3) + 2 * (1 / 2 : ℝ) * (1 / 2 : ℝ) * 0
      + (1 / 2 : ℝ) ^ 2 * (2 * (d : ℝ) ^ 3 / 3) = (d : ℝ) ^ 3 / 3 from by ring] at hsum
  exact hsum.congr fun h => by ring

/-- **The averaged-gap evaluation on the integral itself**: `∫Γ_d(W_h)/h⁴ → d³/3`
(proof of `lem:constant-graphon-comparison`).

`W_h = B.graphon hh` depends on a proof `hh : |h| < h₀`, so `h ↦ ∫Γ_d(W_h)` is not literally
a function of `h`.  The statement is therefore made for *any* `F` that represents the
integral where the latter is defined — which is all a caller needs, and is exactly how the
cost gap `cost_gap_eq` will be read along the family. -/
theorem tendsto_gamInt_graphon (hd : 2 ≤ d) (B : KKTFamily d) {F : ℝ → ℝ}
    (hF : ∀ (h : ℝ) (hh : |h| < B.h₀), F h = GamInt d (B.graphon hh)) :
    Tendsto (fun h : ℝ => F h / h ^ 4) (𝓝[≠] (0 : ℝ)) (𝓝 ((d : ℝ) ^ 3 / 3)) := by
  refine (tendsto_gamInt_block hd B).congr' ?_
  filter_upwards [eventually_abs_lt_h₀ B] with h hb
  rw [hF h hb, KKTFamily.gamInt_graphon hb]

end SingularEndpoint

end UpperTailOptimizers
