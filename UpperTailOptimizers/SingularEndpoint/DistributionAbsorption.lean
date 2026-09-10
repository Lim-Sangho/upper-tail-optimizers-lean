import UpperTailOptimizers.SingularEndpoint.DistributionQuant

/-!
# The Young absorption of `lem:auxiliary-lagrangian-bound` (Section 7)

`SingularEndpoint/DistributionQuant.lean` stops one step short of the refined form of `eq:auxiliary-lagrangian-bound`: it
assembles the gap bound `KKTFamily.distributionGap_lower_of_bounds`, in which the mixed and
tail losses of the quadratic form are still carried as the two explicit error terms

`C_m = C_ρL_hε_ρ(ε_ρ + |Δ_h(ν)| + A_ρ^{3/16})`,   `C_t = Cε_ρ²`,   `L_h = 1 + log(1/h)`,

and leaves the Young absorption that turns those two into `ζ(h)ε_ρ` undone.  **This file is that paragraph**, and the two conclusions
it yields: the refined form and the lemma-level statement `eq:auxiliary-lagrangian-bound`.

## The three analytic steps

The exponents `16/3` and `16/13` are conjugate, `3/16 + 13/16 = 1`.  Written with the
splitting constant left to be *derived* rather than guessed, the paper's display is

* `exists_absorption_mixed` — for `C, a > 0`,
  `C·L·ε·A^{3/16} ≤ (a/8)A + C'(Lε)^{16/13}` with `C'` depending only on `C` and `a`.
  The constant is produced by two-weight AM–GM (`Real.geom_mean_le_arith_mean2_weighted`)
  at the points `s·A` and `t·(Lε)^{16/13}` with `s = 2a/3` and
  `t = (C/s^{3/16})^{16/13}`, which is exactly the choice making `(3/16)s = a/8` and
  `s^{3/16}t^{13/16} = C`.  Both `A = 0` and `ε = 0` are covered: nothing in the argument
  divides by them.
* `rpow_mixed_eq`, `rpow_mixed_le` — the residue `(Lε)^{16/13} = L^{16/13}ε^{3/13}ε`, and
  under `ε ≤ Kh⁴` the bound `(Lε)^{16/13} ≤ L^{16/13}(Kh⁴)^{3/13}ε`, which is what turns the
  residue into a *multiple of `ε`* — the form the tail mass is measured in.
* `zeta`, `tendsto_zeta`, `exists_zeta_le` — the paper's
  `ζ(h) = C_{ρ,K}(L_h^{16/13}h^{12/13} + L_hh⁴)`, here written in the equivalent shape
  `C(L_h^{16/13}(Kh⁴)^{3/13} + L_hh⁴)` (note `h^{12/13} = (h⁴)^{3/13}`), together with
  `ζ(h) → 0` as `h ↓ 0` and the `ε`-form actually consumed, "decrease `h_{ρ,K}` once more so
  that `ζ(h) ≤ b_ρ/2`".  Both summands vanish because any positive power of `h` beats
  `log(1/h)` (`Real.tendsto_log_mul_rpow_nhdsGT_zero`).

## The two conclusions

* `KKTFamily.exists_distributionGap_refined` — the refined form of `eq:auxiliary-lagrangian-bound`, obtained by
  feeding `exists_abs_mixedQuad_le` and `exists_abs_tailQuad_le` into
  `distributionGap_lower_of_bounds` and then absorbing.  The coefficient
  of `A_ρ` is the paper's `a_ρ/2 = d³/48`: `distributionGap_lower_of_bounds` leaves `d³/32`, and
  the Young step spends `a_ρ/8 = d³/192` of it.
* `KKTFamily.exists_distributionGap` — `eq:auxiliary-lagrangian-bound`, from the refined bound by
  `exists_firstVariation_upperGap` (`Ψ_h ≥ b_ρ` on `T_ρ`) and `exists_zeta_le` at `b_ρ/2`.

## What is assumed, and what is not done

The hypotheses `hCorner`, `hu0`, `hud` of `SingularEndpoint/DistributionQuant.lean` — the two clauses of
`lem:central-kernel-bound` proved in `SingularEndpoint/KernelError.lean`
(`exists_kernelTheta_error`, `exists_u0_window`, `exists_ud_window`), which sits above this
file — are carried unchanged; they are *hypotheses*, not axioms, and nothing here weakens
them.  `SingularEndpoint/DistributionFinal.lean` discharges them, through the package of
`SingularEndpoint/DistributionWindow.lean`.  The first-variation bound `hTW` is carried in the same way
(`exists_firstVariation_lower_PsiT` produces its window radius `w` *after* `ρ` is fixed, so it cannot
be discharged inside a statement that quantifies `ρ` first).

The uniqueness clause of `sec:endpoint-optimality-proof`,
which reads `ν = ν_h` off `eq:auxiliary-lagrangian-bound` for an exact minimiser, is not here; it is
`KKTFamily.distribution_unique` in `SingularEndpoint/DistributionUnique.lean`.

## Contents

* `exists_absorption_mixed` — the Young step, with the splitting constant derived;
* `rpow_mixed_eq`, `rpow_mixed_le` — the residue as a multiple of `ε`;
* `zeta`, `tendsto_zeta`, `exists_zeta_le` — the vanishing loss function;
* `KKTFamily.exists_distributionGap_refined` — the refined form of `eq:auxiliary-lagrangian-bound`;
* `KKTFamily.exists_distributionGap` — `eq:auxiliary-lagrangian-bound`;
* `tendsto_logInv_mul_rpow` — `(1 + log(1/h))·h^r → 0` as `h ↓ 0` for every `r > 0`, shared
  with `SingularEndpoint/GraphonComparisonMaster.lean`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-! ## The Young step -/

/-- **Two-weight AM–GM in the shape the Young step needs**: weights `3/16` and `13/16` at the
points `s·A` and `t·Y`.  This is `Real.geom_mean_le_arith_mean2_weighted` with the two
`Real.mul_rpow` splittings already performed, so that the scaling constants `s` and `t` appear
only through `s^{3/16}t^{13/16}`. -/
private theorem absorption_two_weight {s t A Y : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hA : 0 ≤ A)
    (hY : 0 ≤ Y) :
    s ^ (3 / 16 : ℝ) * t ^ (13 / 16 : ℝ) * (A ^ (3 / 16 : ℝ) * Y ^ (13 / 16 : ℝ))
      ≤ 3 / 16 * (s * A) + 13 / 16 * (t * Y) := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 3 / 16) (w₂ := 13 / 16)
    (p₁ := s * A) (p₂ := t * Y) (by norm_num) (by norm_num) (mul_nonneg hs hA)
    (mul_nonneg ht hY) (by norm_num)
  rw [Real.mul_rpow hs hA, Real.mul_rpow ht hY] at h
  calc s ^ (3 / 16 : ℝ) * t ^ (13 / 16 : ℝ) * (A ^ (3 / 16 : ℝ) * Y ^ (13 / 16 : ℝ))
      = s ^ (3 / 16 : ℝ) * A ^ (3 / 16 : ℝ) * (t ^ (13 / 16 : ℝ) * Y ^ (13 / 16 : ℝ)) := by
        ring
    _ ≤ 3 / 16 * (s * A) + 13 / 16 * (t * Y) := h

/-- **The Young step of `paper/singular_endpoint.tex`.**  With the conjugate exponents
`16/3` and `16/13`,

`C·L·ε·A^{3/16} ≤ (a/8)·A + C'·(L·ε)^{16/13}`,

for every `L, ε, A ≥ 0`, with `C'` depending only on `C` and `a`.

The splitting constant is *not* the obvious one and is derived rather than guessed: applying
`absorption_two_weight` at `s·A` and `t·(Lε)^{16/13}` gives
`s^{3/16}t^{13/16}·A^{3/16}(Lε) ≤ (3/16)sA + (13/16)t(Lε)^{16/13}`, so the two requirements
are `(3/16)s = a/8` and `s^{3/16}t^{13/16} = C`, i.e. `s = 2a/3` and
`t = (C/s^{3/16})^{16/13}`.  Then `C' = (13/16)t + 1`, the `+1` only to make it positive when
`C = 0`.  Neither `A = 0` nor `ε = 0` is excluded. -/
theorem exists_absorption_mixed {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ L eps A : ℝ, 0 ≤ L → 0 ≤ eps → 0 ≤ A →
      C * L * eps * A ^ (3 / 16 : ℝ) ≤ a / 8 * A + C' * (L * eps) ^ (16 / 13 : ℝ) := by
  have hs : (0 : ℝ) < 2 * a / 3 := by linarith
  have hs3 : (0 : ℝ) < (2 * a / 3) ^ (3 / 16 : ℝ) := Real.rpow_pos_of_pos hs _
  have hq : (0 : ℝ) ≤ C / (2 * a / 3) ^ (3 / 16 : ℝ) := div_nonneg hC hs3.le
  have ht : (0 : ℝ) ≤ (C / (2 * a / 3) ^ (3 / 16 : ℝ)) ^ (16 / 13 : ℝ) := Real.rpow_nonneg hq _
  refine ⟨13 / 16 * (C / (2 * a / 3) ^ (3 / 16 : ℝ)) ^ (16 / 13 : ℝ) + 1, by linarith, ?_⟩
  intro L eps A hL heps hA
  have hLe : (0 : ℝ) ≤ L * eps := mul_nonneg hL heps
  have hY : (0 : ℝ) ≤ (L * eps) ^ (16 / 13 : ℝ) := Real.rpow_nonneg hLe _
  have hkey := absorption_two_weight (s := 2 * a / 3)
    (t := (C / (2 * a / 3) ^ (3 / 16 : ℝ)) ^ (16 / 13 : ℝ)) (A := A)
    (Y := (L * eps) ^ (16 / 13 : ℝ)) hs.le ht hA hY
  have hYe : ((L * eps) ^ (16 / 13 : ℝ)) ^ (13 / 16 : ℝ) = L * eps := by
    rw [← Real.rpow_mul hLe, show (16 / 13 : ℝ) * (13 / 16) = 1 by norm_num, Real.rpow_one]
  have hte : ((C / (2 * a / 3) ^ (3 / 16 : ℝ)) ^ (16 / 13 : ℝ)) ^ (13 / 16 : ℝ)
      = C / (2 * a / 3) ^ (3 / 16 : ℝ) := by
    rw [← Real.rpow_mul hq, show (16 / 13 : ℝ) * (13 / 16) = 1 by norm_num, Real.rpow_one]
  have hprod : (2 * a / 3) ^ (3 / 16 : ℝ) * (C / (2 * a / 3) ^ (3 / 16 : ℝ)) = C := by
    rw [mul_comm, div_mul_cancel₀ C (ne_of_gt hs3)]
  rw [hte, hYe, hprod] at hkey
  linarith [hkey, hY]

/-! ## The residue as a multiple of `ε` -/

/-- **The residue split** of `paper/singular_endpoint.tex`:
`(Lε)^{16/13} = L^{16/13}ε^{3/13}ε`.  The exponent bookkeeping is `16/13 = 3/13 + 1`, and
`Real.rpow_add'` needs only `ε ≥ 0` because that sum is nonzero. -/
theorem rpow_mixed_eq {L eps : ℝ} (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    (L * eps) ^ (16 / 13 : ℝ) = L ^ (16 / 13 : ℝ) * eps ^ (3 / 13 : ℝ) * eps := by
  have hne : (3 / 13 : ℝ) + 1 ≠ 0 := by norm_num
  have he : eps ^ (16 / 13 : ℝ) = eps ^ (3 / 13 : ℝ) * eps := by
    rw [show (16 / 13 : ℝ) = 3 / 13 + 1 by norm_num, Real.rpow_add' heps hne, Real.rpow_one]
  rw [Real.mul_rpow hL heps, he, ← mul_assoc]

/-- **The residue as a multiple of the tail mass**: under
the localisation hypothesis `ε ≤ Kh⁴` of `eq:graphon-comparison-estimates`,

`(Lε)^{16/13} ≤ L^{16/13}(Kh⁴)^{3/13}·ε`.

Only `ε^{3/13} ≤ (Kh⁴)^{3/13}` is used, so `ε = 0` is again harmless. -/
theorem rpow_mixed_le {L eps K h : ℝ} (hL : 0 ≤ L) (heps : 0 ≤ eps) (_hKh : 0 ≤ K * h ^ 4)
    (hb : eps ≤ K * h ^ 4) :
    (L * eps) ^ (16 / 13 : ℝ) ≤ L ^ (16 / 13 : ℝ) * (K * h ^ 4) ^ (3 / 13 : ℝ) * eps := by
  rw [rpow_mixed_eq hL heps]
  have hmono : eps ^ (3 / 13 : ℝ) ≤ (K * h ^ 4) ^ (3 / 13 : ℝ) :=
    Real.rpow_le_rpow heps hb (by norm_num)
  have hLn : (0 : ℝ) ≤ L ^ (16 / 13 : ℝ) := Real.rpow_nonneg hL _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hLn) heps

/-! ## The vanishing loss function `ζ` -/

/-- **The paper's `ζ(h) = C_{ρ,K}(L_h^{16/13}h^{12/13} + L_hh⁴)`**, with `L_h = 1 + log(1/h)`, written with `h^{12/13}` in
the form `(Kh⁴)^{3/13}` in which the Young residue delivers it (`rpow_mixed_le`).  The two
shapes agree up to the constant `K^{3/13}`, and this one is the one actually consumed. -/
noncomputable def zeta (C K h : ℝ) : ℝ :=
  C * ((1 + Real.log (1 / h)) ^ (16 / 13 : ℝ) * (K * h ^ 4) ^ (3 / 13 : ℝ)
        + (1 + Real.log (1 / h)) * h ^ 4)

/-- `(1 + log(1/h))·h^r → 0` as `h ↓ 0`, for every `r > 0`: any positive power of `h` beats
`log(1/h)`.  After `log(1/h) = -log h` the statement is the difference of `h^r → 0` and
`Real.tendsto_log_mul_rpow_nhdsGT_zero`. -/
theorem tendsto_logInv_mul_rpow {r : ℝ} (hr : 0 < r) :
    Filter.Tendsto (fun h : ℝ => (1 + Real.log (1 / h)) * h ^ r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hc : Filter.Tendsto (fun x : ℝ => x ^ r) (nhds 0) (nhds ((0 : ℝ) ^ r)) :=
    (Real.continuousAt_rpow_const 0 r (Or.inr hr.le)).tendsto
  rw [Real.zero_rpow (ne_of_gt hr)] at hc
  have h1 : Filter.Tendsto (fun x : ℝ => x ^ r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    hc.mono_left nhdsWithin_le_nhds
  have h2 := tendsto_log_mul_rpow_nhdsGT_zero hr
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  refine Filter.Tendsto.congr ?_ h3
  intro x
  show x ^ r - Real.log x * x ^ r = (1 + Real.log (1 / x)) * x ^ r
  rw [one_div, Real.log_inv]
  ring

/-- The natural-power instance of `tendsto_logInv_mul_rpow` at `r = 4`, which is the exponent
`ζ` carries in its second summand. -/
private theorem tendsto_logInv_mul_pow_four :
    Filter.Tendsto (fun h : ℝ => (1 + Real.log (1 / h)) * h ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  refine Filter.Tendsto.congr ?_ (tendsto_logInv_mul_rpow (r := 4) (by norm_num))
  intro x
  show (1 + Real.log (1 / x)) * x ^ (4 : ℝ) = (1 + Real.log (1 / x)) * x ^ 4
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `(h⁴)^{3/13} = h^{12/13}`: the identification of the paper's `h^{12/13}` with the shape
`rpow_mixed_le` produces. -/
private theorem pow_four_rpow {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 4) ^ (3 / 13 : ℝ) = x ^ (12 / 13 : ℝ) := by
  rw [show x ^ 4 = x ^ ((4 : ℕ) : ℝ) from (Real.rpow_natCast x 4).symm, ← Real.rpow_mul hx]
  norm_num

/-- `(h^{3/4})^{16/13} = h^{12/13}`: the exponent that makes the first summand of `ζ` a pure
`16/13`-power of a vanishing quantity. -/
private theorem rpow_three_quarters_pow {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (3 / 4 : ℝ)) ^ (16 / 13 : ℝ) = x ^ (12 / 13 : ℝ) := by
  rw [← Real.rpow_mul hx]
  norm_num

/-- The first summand of `ζ` vanishes as `h ↓ 0`.  On `(0,1)` it is exactly
`K^{3/13}·((1 + log(1/h))h^{3/4})^{16/13}`, a fixed power of a quantity that tends to `0` by
`tendsto_logInv_mul_rpow`; the exponent `3/4` is chosen so that `(3/4)(16/13) = 12/13`. -/
private theorem tendsto_zetaOne {K : ℝ} (hK : 0 ≤ K) :
    Filter.Tendsto
      (fun h : ℝ => (1 + Real.log (1 / h)) ^ (16 / 13 : ℝ) * (K * h ^ 4) ^ (3 / 13 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hg : Filter.Tendsto (fun h : ℝ => (1 + Real.log (1 / h)) * h ^ (3 / 4 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := tendsto_logInv_mul_rpow (by norm_num)
  have hg16 : Filter.Tendsto
      (fun h : ℝ => ((1 + Real.log (1 / h)) * h ^ (3 / 4 : ℝ)) ^ (16 / 13 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hr := hg.rpow_const (Or.inr (show (0 : ℝ) ≤ 16 / 13 by norm_num))
    rwa [Real.zero_rpow (show (16 / 13 : ℝ) ≠ 0 by norm_num)] at hr
  have hmul := hg16.const_mul (K ^ (3 / 13 : ℝ))
  rw [mul_zero] at hmul
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio 1, isOpen_Iio, Set.mem_Iio.mpr (by norm_num), fun x hx => ⟨hx.2, hx.1⟩⟩
  have heq : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      K ^ (3 / 13 : ℝ) * ((1 + Real.log (1 / x)) * x ^ (3 / 4 : ℝ)) ^ (16 / 13 : ℝ)
        = (1 + Real.log (1 / x)) ^ (16 / 13 : ℝ) * (K * x ^ 4) ^ (3 / 13 : ℝ) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1.le
    have hL : (0 : ℝ) ≤ 1 + Real.log (1 / x) := by
      have := Real.log_nonneg (one_le_one_div hx.1 hx.2.le)
      linarith
    have hxr : (0 : ℝ) ≤ x ^ (3 / 4 : ℝ) := Real.rpow_nonneg hx0 _
    have hx4 : (0 : ℝ) ≤ x ^ 4 := pow_nonneg hx0 4
    rw [Real.mul_rpow hL hxr, rpow_three_quarters_pow hx0, Real.mul_rpow hK hx4,
      pow_four_rpow hx0]
    ring
  refine hmul.congr' ?_
  filter_upwards [hmem] with x hx
  exact heq x hx

/-- **`ζ(h) → 0` as `h ↓ 0`**.  Both summands vanish
because any positive power of `h` beats `log(1/h)`. -/
theorem tendsto_zeta (C : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    Filter.Tendsto (zeta C K) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h3 := ((tendsto_zetaOne hK).add tendsto_logInv_mul_pow_four).const_mul C
  rw [add_zero, mul_zero] at h3
  exact h3

/-- **The `ε`-form of `tendsto_zeta` actually consumed** — the paper's "decreasing `h_{ρ,K}`
once more so that `ζ(h) ≤ b_ρ/2`". -/
theorem exists_zeta_le (C : ℝ) {K : ℝ} (hK : 0 ≤ K) {b : ℝ} (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → zeta C K h ≤ b := by
  obtain ⟨δ, hδ, hprop⟩ := Metric.tendsto_nhdsWithin_nhds.mp (tendsto_zeta C hK) b hb
  refine ⟨δ, hδ, fun h hh0 hhδ => ?_⟩
  have hmem : h ∈ Set.Ioi (0 : ℝ) := hh0
  have hdist : dist h (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
    exact hhδ
  have hval := hprop hmem hdist
  rw [Real.dist_eq, sub_zero] at hval
  exact le_trans (le_abs_self _) hval.le

/-! ## The absorption, as pure arithmetic -/

/-- **The absorption of `paper/singular_endpoint.tex`, stripped of all measure theory.**
Given the gap bound of `KKTFamily.distributionGap_lower_of_bounds` — written here with `A`
for `A_ρ`, `P` for the retained tail integral `∫_{T_ρ}Ψ̃_hdν`, `eps` for `ε_ρ`, `Delta` for
`Δ_h(ν)` and `G` for the Lagrangian gap — and the two hypotheses `eq:graphon-comparison-estimates`,
there are `C_z` and `M` depending only on `dd = d³`, `C_q`, `C_{m,0}`, `C_{t,0}`, `K` and
`E = 1 + 2^d` such that the mixed and pure-tail losses collapse into `ζ(h)ε_ρ + MΔ²`.

The four absorptions are the paper's: `ε² ≤ Kh⁴ε` and `ε|Δ| ≤ Kh⁴ε` for the two elementary
mixed terms, `exists_absorption_mixed` followed by `rpow_mixed_le` for the `A^{3/16}` term, and
`(Eε + |Δ|)² ≤ 2E²ε² + 2Δ²` for the polynomial part of the central estimate — the only term
that is *not* proportional to `ε` and hence the source of the retained `MΔ²`.  The `A`-budget
spent by the Young step is `dd/192 = a_ρ/8`, which the drop from `dd/32` to `dd/48` pays for
with `dd/96` to spare. -/
private theorem exists_absorb_arith {dd Cq Cm0 Ct0 K E : ℝ} (hdd : 0 < dd) (hCq : 0 ≤ Cq)
    (hCm0 : 0 ≤ Cm0) (hCt0 : 0 ≤ Ct0) (hK : 1 ≤ K) :
    ∃ Cz : ℝ, 0 < Cz ∧ ∃ M : ℝ, 0 < M ∧
      ∀ A P eps Delta h G : ℝ, 0 ≤ A → 0 ≤ eps → 0 < h → h ≤ 1 →
        eps ≤ K * h ^ 4 → |Delta| ≤ K * h ^ 4 →
        dd / 32 * A + P - Cq * (E * eps + |Delta|) ^ 2
            - (2 * (Cm0 * (1 + Real.log (1 / h)) * (eps + |Delta| + A ^ (3 / 16 : ℝ)) * eps)
              + Ct0 * eps ^ 2) ≤ G →
        dd / 48 * A + P - zeta Cz K h * eps - M * Delta ^ 2 ≤ G := by
  obtain ⟨C', hC'0, hC'⟩ := exists_absorption_mixed (C := 2 * Cm0) (a := dd / 24) (by linarith)
    (by linarith)
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK
  have hSnn : (0 : ℝ) ≤ 4 * Cm0 * K + Ct0 * K + 2 * Cq * E ^ 2 * K :=
    add_nonneg (add_nonneg (mul_nonneg (by linarith) hKpos.le) (mul_nonneg hCt0 hKpos.le))
      (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg E)) hKpos.le)
  obtain ⟨Cz, hCzdef⟩ : ∃ x : ℝ, x = C' + (4 * Cm0 * K + Ct0 * K + 2 * Cq * E ^ 2 * K) + 1 :=
    ⟨_, rfl⟩
  have hCzC : C' ≤ Cz := by rw [hCzdef]; linarith
  have hCzS : 4 * Cm0 * K + Ct0 * K + 2 * Cq * E ^ 2 * K ≤ Cz := by rw [hCzdef]; linarith
  refine ⟨Cz, by rw [hCzdef]; linarith, 2 * Cq + 1, by linarith, ?_⟩
  intro A P eps Delta h G hA heps hh0 hh1 hepsb hDb hgap
  simp only [zeta]
  have hLog : (0 : ℝ) ≤ Real.log (1 / h) := Real.log_nonneg (one_le_one_div hh0 hh1)
  have hL0 : (0 : ℝ) ≤ 1 + Real.log (1 / h) := by linarith
  have hKh : (0 : ℝ) ≤ K * h ^ 4 := le_trans heps hepsb
  have hh4 : (0 : ℝ) ≤ h ^ 4 := pow_nonneg hh0.le 4
  have hyoung := hC' (1 + Real.log (1 / h)) eps A hL0 heps hA
  have hp2 := rpow_mixed_le hL0 heps hKh hepsb
  -- Opaque names for the five transcendental atoms, so that the linear arithmetic below
  -- never sees a logarithm or an `rpow` and stays inside the default heartbeat budget.
  obtain ⟨R1, hR1⟩ : ∃ x : ℝ,
      x = (1 + Real.log (1 / h)) ^ (16 / 13 : ℝ) * (K * h ^ 4) ^ (3 / 13 : ℝ) := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ x : ℝ, x = ((1 + Real.log (1 / h)) * eps) ^ (16 / 13 : ℝ) := ⟨_, rfl⟩
  obtain ⟨A16, hA16⟩ : ∃ x : ℝ, x = A ^ (3 / 16 : ℝ) := ⟨_, rfl⟩
  obtain ⟨R2, hR2⟩ : ∃ x : ℝ, x = h ^ 4 := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ x : ℝ, x = 1 + Real.log (1 / h) := ⟨_, rfl⟩
  have hR1nn : (0 : ℝ) ≤ R1 := by
    rw [hR1]
    exact mul_nonneg (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hKh _)
  have hR2nn : (0 : ℝ) ≤ R2 := by rw [hR2]; exact hh4
  have hL1 : (1 : ℝ) ≤ L := by rw [hLd]; linarith
  have hL0' : (0 : ℝ) ≤ L := by linarith
  have hepsb' : eps ≤ K * R2 := by rw [hR2]; exact hepsb
  have hDb' : |Delta| ≤ K * R2 := by rw [hR2]; exact hDb
  rw [← hR1, ← hR2, ← hLd]
  rw [← hA16, ← hLd] at hgap
  rw [← hA16, ← hYd, ← hLd] at hyoung
  rw [← hYd, ← hR1] at hp2
  -- the Young residue, absorbed into the first summand of `ζ`
  have hR1e : (0 : ℝ) ≤ R1 * eps := mul_nonneg hR1nn heps
  have hLR2e : (0 : ℝ) ≤ L * R2 * eps := mul_nonneg (mul_nonneg hL0' hR2nn) heps
  have hzeta1 : C' * Y ≤ Cz * (R1 * eps) :=
    le_trans (mul_le_mul_of_nonneg_left hp2 hC'0.le) (mul_le_mul_of_nonneg_right hCzC hR1e)
  have hzeta2 : (4 * Cm0 * K + Ct0 * K + 2 * Cq * E ^ 2 * K) * (L * R2 * eps)
      ≤ Cz * (L * R2 * eps) := mul_le_mul_of_nonneg_right hCzS hLR2e
  -- the elementary `ε ≤ Kh⁴` absorptions
  have he1 : eps * eps ≤ K * R2 * eps := mul_le_mul_of_nonneg_right hepsb' heps
  have he2 : |Delta| * eps ≤ K * R2 * eps := mul_le_mul_of_nonneg_right hDb' heps
  have h2Cm0L : (0 : ℝ) ≤ 2 * Cm0 * L := mul_nonneg (by linarith) hL0'
  have ha1 : 2 * Cm0 * L * (eps * eps) ≤ 2 * Cm0 * L * (K * R2 * eps) :=
    mul_le_mul_of_nonneg_left he1 h2Cm0L
  have ha2 : 2 * Cm0 * L * (|Delta| * eps) ≤ 2 * Cm0 * L * (K * R2 * eps) :=
    mul_le_mul_of_nonneg_left he2 h2Cm0L
  have ha3 : Ct0 * (eps * eps) ≤ Ct0 * (K * R2 * eps) := mul_le_mul_of_nonneg_left he1 hCt0
  have ha4 : 2 * Cq * E ^ 2 * (eps * eps) ≤ 2 * Cq * E ^ 2 * (K * R2 * eps) :=
    mul_le_mul_of_nonneg_left he1 (mul_nonneg (by linarith) (sq_nonneg E))
  -- the polynomial part of the central estimate
  have hsq : (E * eps + |Delta|) ^ 2 ≤ 2 * (E * eps) ^ 2 + 2 * Delta ^ 2 := by
    nlinarith [sq_nonneg (E * eps - |Delta|), sq_abs Delta]
  have hsq2 : Cq * (E * eps + |Delta|) ^ 2 ≤ Cq * (2 * (E * eps) ^ 2 + 2 * Delta ^ 2) :=
    mul_le_mul_of_nonneg_left hsq hCq
  have hD2 : (0 : ℝ) ≤ Delta ^ 2 := sq_nonneg Delta
  have hddA : (0 : ℝ) ≤ dd * A := mul_nonneg hdd.le hA
  -- upgrading `h⁴` to `L_h h⁴` in the two summands that carry no logarithm
  have hLh : R2 ≤ L * R2 := by linarith [mul_nonneg (sub_nonneg.mpr hL1) hR2nn]
  have hg1 : Ct0 * K * eps * R2 ≤ Ct0 * K * eps * (L * R2) :=
    mul_le_mul_of_nonneg_left hLh (mul_nonneg (mul_nonneg hCt0 hKpos.le) heps)
  have hg2 : 2 * Cq * E ^ 2 * K * eps * R2 ≤ 2 * Cq * E ^ 2 * K * eps * (L * R2) :=
    mul_le_mul_of_nonneg_left hLh
      (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg E)) hKpos.le) heps)
  linarith only [hgap, hyoung, hzeta1, hzeta2, ha1, ha2, ha3, ha4, hsq2, hg1, hg2, hddA, hD2]

namespace KKTFamily

/-! ## The refined and lemma-level forms of `eq:auxiliary-lagrangian-bound` -/

/-- **The refined form of `eq:auxiliary-lagrangian-bound`**


The paper displays the gap bound once, as `eq:auxiliary-lagrangian-bound`; the
constant-explicit refinement below appears only inside the proof, and its tail term is the
linear `b_ρ·ε_ρ(ν)` coming from the tail floor of `lem:first-variation-bound`.  The
Lean keeps the sharper `∫_{T_ρ}Ψ̃_h dν - ζ(h)ε_ρ`, which is stronger and has no counterpart in
the paper — `ζ` does not occur in it.  With `A_ρ = ∫_{𝓝_ρ}Q_h²dν`, `ε_ρ = ν(T_ρ)` and `Δ = Δ_h(ν)`, under the two
hypotheses `eq:graphon-comparison-estimates` — `ε_ρ ≤ Kh⁴` and `|Δ| ≤ Kh⁴` —

`𝒥_h(ν) - 𝒥_h(ν_h) - η_hΔ ≥ (d³/48)A_ρ + ∫_{T_ρ}Ψ̃_hdν - ζ(h)ε_ρ - MΔ²`,

with `d³/48 = a_ρ/2` and `ζ` the vanishing loss function of `zeta`/`tendsto_zeta`.  The tail
integral `∫_{T_ρ}Ψ̃_hdν` is kept intact, as the paper insists: it is consumed only in
`exists_distributionGap`, and in `lem:graphon-lagrangian-bound` it is passed on to the rare rows.

This is `distributionGap_lower_of_bounds` with `exists_abs_mixedQuad_le` and
`exists_abs_tailQuad_le` substituted and `exists_absorb_arith` applied.  The three
hypotheses `hu0`, `hud`, `hCorner` are the unformalised clauses of
`lem:central-kernel-bound` that `SingularEndpoint/DistributionQuant.lean` already carries, and
`hTW` is the first-variation bound `exists_firstVariation_lower_PsiT` (kept as a hypothesis because its
window radius is produced only after `ρ` is chosen). -/
theorem exists_distributionGap_refined (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2) {Cu Cp K : ℝ} (hCu : 0 ≤ Cu)
    (hCp : 0 ≤ Cp) (hK : 1 ≤ K) :
    ∃ Cz : ℝ, 0 < Cz ∧ ∃ M : ℝ, 0 < M ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ h : ℝ, 0 < h → h < δ₀ → h ≤ 1 → |h| < B.h₀ →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ (d : ℝ) ^ 3 / 192 →
        |B.kp00 h| ≤ Cp → |B.kpd0 h| ≤ Cp → |B.kp0d h| ≤ Cp → |B.kpdd h| ≤ Cp →
        (∀ x ∈ centralWindow d ρ, |B.u0 h x| ≤ Cu) →
        (∀ x ∈ centralWindow d ρ, |B.ud h x| ≤ Cu) →
        (∀ x ∈ centralWindow d ρ, ∀ y ∈ centralWindow d ρ,
          |B.kernelTheta h x y - (d : ℝ) ^ 3 / 4| ≤ δ) →
        (∀ x ∈ centralWindow d ρ, (d : ℝ) ^ 3 / 24 * B.Qh h x ^ 2 ≤ B.PsiT h x) →
        B.sVal h ∈ centralWindow d ρ → B.tVal h ∈ centralWindow d ρ →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
          (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal ≤ K * h ^ 4 →
          |(∫ x, x ^ d ∂ν) - B.qVal h| ≤ K * h ^ 4 →
          (d : ℝ) ^ 3 / 48 * (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
              + (∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.PsiT h x ∂ν)
              - zeta Cz K h * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
              - M * ((∫ x, x ^ d ∂ν) - B.qVal h) ^ 2
            ≤ B.distributionJ h ν - B.distributionJ h (B.distributionMeasure h)
                - B.etaVal h * ((∫ x, x ^ d ∂ν) - B.qVal h) := by
  obtain ⟨Cm0, hCm0, δm, hδm, hmix⟩ := exists_abs_mixedQuad_le hd B hρ0
  obtain ⟨Ct0, hCt0, δt, hδt, htail⟩ := exists_abs_tailQuad_le hd B
  obtain ⟨_CJ, _hCJ, δj, hδj, hJ⟩ := exists_abs_JpTildeH_le hd B
  have hdR : (0 : ℝ) < (d : ℝ) := by
    have hdn : (0 : ℕ) < d := lt_of_lt_of_le (by norm_num) hd
    exact_mod_cast hdn
  have hdd : (0 : ℝ) < (d : ℝ) ^ 3 := pow_pos hdR 3
  obtain ⟨Cz, hCz, M, hM, habs⟩ := exists_absorb_arith (dd := (d : ℝ) ^ 3)
    (Cq := Cp + 192 * Cu ^ 2 / (d : ℝ) ^ 3) (Cm0 := Cm0) (Ct0 := Ct0) (K := K)
    (E := 1 + 2 ^ d) hdd (add_nonneg hCp (by positivity)) hCm0.le hCt0.le hK
  refine ⟨Cz, hCz, M, hM, min (min δm δt) δj, lt_min (lt_min hδm hδt) hδj, ?_⟩
  intro h hh0 hhδ hh1 hhb δ hδ hδ8 h00 hd0 h0d hddc hu0 hud hCorner hTW hs ht ν hνp hν
    hepsb hDb
  have := hνp
  have habsh : |h| = h := abs_of_pos hh0
  have hhm : h < δm := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hht : |h| < δt := by
    rw [habsh]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hhj : |h| < δj := by
    rw [habsh]
    exact lt_of_lt_of_le hhδ (min_le_right _ _)
  have hmain := distributionGap_lower_of_bounds hd B hhb hh0 hρu hρ1 hν hs ht hδ hδ8 hCu hCp h00
    hd0 h0d hddc hu0 hud hCorner hTW (hJ h hhj) (hmix h hh0 hhm hhb ν hνp hν)
    (htail h hht ρ ν hνp hν)
  have hA0 : (0 : ℝ) ≤ ∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν :=
    setIntegral_nonneg (measurableSet_centralWindow d ρ) fun x _ => sq_nonneg _
  exact habs (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
    (∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.PsiT h x ∂ν)
    (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal ((∫ x, x ^ d ∂ν) - B.qVal h) h
    (B.distributionJ h ν - B.distributionJ h (B.distributionMeasure h)
      - B.etaVal h * ((∫ x, x ^ d ∂ν) - B.qVal h))
    hA0 ENNReal.toReal_nonneg hh0 hh1 hepsb hDb hmain

/-- **`eq:auxiliary-lagrangian-bound`**:

`𝒥_h(ν) - 𝒥_h(ν_h) - η_hΔ ≥ M⁻¹[∫_{𝓝_ρ}Q_h²dν + ν(T_ρ)] - MΔ²`.

The refined bound `exists_distributionGap_refined` is combined with the companion first-variation bound
`exists_firstVariation_upperGap` — `Ψ_h ≥ b_ρ` on the tail, so `∫_{T_ρ}Ψ̃_hdν ≥ b_ρε_ρ` — after
`exists_zeta_le` has shrunk the window so that `ζ(h) ≤ b_ρ/2`, leaving `(b_ρ/2)ε_ρ`.  The
constant is `M = M₀ + 48/d³ + 2/b_ρ`, which dominates both reciprocals at once.

The hypotheses are those of `exists_distributionGap_refined`; in particular the Lagrangian gap is
taken in the linearised form `η_hΔ_h(ν)` of `eq:first-variation`
(`distributionJ_sub_eq`), not in the form `μ_h{m_d(ν)^v - q_h^v}`, the two differing by
`O(Δ_h(ν)²)`. -/
theorem exists_distributionGap (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2) {Cu Cp K : ℝ} (hCu : 0 ≤ Cu)
    (hCp : 0 ≤ Cp) (hK : 1 ≤ K) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ h : ℝ, 0 < h → h < δ₀ → h ≤ 1 → |h| < B.h₀ →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ (d : ℝ) ^ 3 / 192 →
        |B.kp00 h| ≤ Cp → |B.kpd0 h| ≤ Cp → |B.kp0d h| ≤ Cp → |B.kpdd h| ≤ Cp →
        (∀ x ∈ centralWindow d ρ, |B.u0 h x| ≤ Cu) →
        (∀ x ∈ centralWindow d ρ, |B.ud h x| ≤ Cu) →
        (∀ x ∈ centralWindow d ρ, ∀ y ∈ centralWindow d ρ,
          |B.kernelTheta h x y - (d : ℝ) ^ 3 / 4| ≤ δ) →
        (∀ x ∈ centralWindow d ρ, (d : ℝ) ^ 3 / 24 * B.Qh h x ^ 2 ≤ B.PsiT h x) →
        B.sVal h ∈ centralWindow d ρ → B.tVal h ∈ centralWindow d ρ →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
          (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal ≤ K * h ^ 4 →
          |(∫ x, x ^ d ∂ν) - B.qVal h| ≤ K * h ^ 4 →
          M⁻¹ * ((∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
                  + (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal)
              - M * ((∫ x, x ^ d ∂ν) - B.qVal h) ^ 2
            ≤ B.distributionJ h ν - B.distributionJ h (B.distributionMeasure h)
                - B.etaVal h * ((∫ x, x ^ d ∂ν) - B.qVal h) := by
  obtain ⟨Cz, hCz, M₀, hM₀, δ₁, hδ₁, href⟩ :=
    exists_distributionGap_refined hd B hρ0 hρu hρ1 hCu hCp hK
  obtain ⟨b, hb, δ₂, hδ₂, hlow⟩ := exists_firstVariation_upperGap hd B hρ0
  obtain ⟨δ₃, hδ₃, hzle⟩ := exists_zeta_le Cz (le_trans zero_le_one hK)
    (show (0 : ℝ) < b / 2 by linarith)
  have hdR : (0 : ℝ) < (d : ℝ) := by
    have hdn : (0 : ℕ) < d := lt_of_lt_of_le (by norm_num) hd
    exact_mod_cast hdn
  have hdd : (0 : ℝ) < (d : ℝ) ^ 3 := pow_pos hdR 3
  have hp1 : (0 : ℝ) < 48 / (d : ℝ) ^ 3 := div_pos (by norm_num) hdd
  have hp2 : (0 : ℝ) < 2 / b := div_pos (by norm_num) hb
  have hMpos : (0 : ℝ) < M₀ + 48 / (d : ℝ) ^ 3 + 2 / b := by linarith
  have hM1 : (M₀ + 48 / (d : ℝ) ^ 3 + 2 / b)⁻¹ ≤ (d : ℝ) ^ 3 / 48 := by
    have hstep := one_div_le_one_div_of_le hp1 (show 48 / (d : ℝ) ^ 3
      ≤ M₀ + 48 / (d : ℝ) ^ 3 + 2 / b by linarith)
    rw [one_div_div] at hstep
    rw [inv_eq_one_div]
    exact hstep
  have hM2 : (M₀ + 48 / (d : ℝ) ^ 3 + 2 / b)⁻¹ ≤ b / 2 := by
    have hstep := one_div_le_one_div_of_le hp2 (show 2 / b
      ≤ M₀ + 48 / (d : ℝ) ^ 3 + 2 / b by linarith)
    rw [one_div_div] at hstep
    rw [inv_eq_one_div]
    exact hstep
  have hM3 : M₀ ≤ M₀ + 48 / (d : ℝ) ^ 3 + 2 / b := by linarith
  refine ⟨M₀ + 48 / (d : ℝ) ^ 3 + 2 / b, hMpos, min (min δ₁ δ₂) δ₃,
    lt_min (lt_min hδ₁ hδ₂) hδ₃, ?_⟩
  intro h hh0 hhδ hh1 hhb δ hδ hδ8 h00 hd0 h0d hddc hu0 hud hCorner hTW hs ht ν hνp hν
    hepsb hDb
  have := hνp
  have habsh : |h| = h := abs_of_pos hh0
  have hh1' : h < δ₁ := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hh2' : |h| < δ₂ := by
    rw [habsh]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hh3' : h < δ₃ := lt_of_lt_of_le hhδ (min_le_right _ _)
  have hmain := href h hh0 hh1' hh1 hhb δ hδ hδ8 h00 hd0 h0d hddc hu0 hud hCorner hTW hs ht
    ν hνp hν hepsb hDb
  -- the tail integral dominates `b_ρ ε_ρ`
  have hmT : MeasurableSet (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ) :=
    measurableSet_Icc.diff (measurableSet_centralWindow d ρ)
  have hiIcc : IntegrableOn (B.PsiT h) (Set.Icc (0 : ℝ) 2) ν :=
    integrableOn_of_continuousOn hν (continuousOn_PsiT hd B hhb) isCompact_Icc
  have hiT : IntegrableOn (B.PsiT h) (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ) ν :=
    hiIcc.mono_set Set.sdiff_subset
  have hgapT : ∀ x ∈ Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, b ≤ B.PsiT h x := by
    intro x hx
    refine hlow h hh2' hhb x hx.1 ?_
    have hx2 : x ∉ Set.Icc (uStar d - ρ) (uStar d + ρ) := hx.2
    rw [Set.mem_Icc, not_and_or] at hx2
    rcases hx2 with hc | hc
    · push Not at hc
      rw [abs_of_nonpos (by linarith)]
      linarith
    · push Not at hc
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hPT : b * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
      ≤ ∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.PsiT h x ∂ν := by
    have hge := setIntegral_ge_of_const_le_real (μ := ν) (c := b) (f := B.PsiT h) hmT
      (measure_ne_top ν _) hgapT hiT
    simpa [measureReal_def] using hge
  -- the loss function is at most `b_ρ/2`
  have hz := hzle h hh0 hh3'
  have heps0 : (0 : ℝ) ≤ (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal :=
    ENNReal.toReal_nonneg
  have hzmul : zeta Cz K h * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
      ≤ b / 2 * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal :=
    mul_le_mul_of_nonneg_right hz heps0
  have hA0 : (0 : ℝ) ≤ ∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν :=
    setIntegral_nonneg (measurableSet_centralWindow d ρ) fun x _ => sq_nonneg _
  have hsplit1 : (M₀ + 48 / (d : ℝ) ^ 3 + 2 / b)⁻¹
        * (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
      ≤ (d : ℝ) ^ 3 / 48 * (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν) :=
    mul_le_mul_of_nonneg_right hM1 hA0
  have hsplit2 : (M₀ + 48 / (d : ℝ) ^ 3 + 2 / b)⁻¹
        * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
      ≤ b / 2 * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal :=
    mul_le_mul_of_nonneg_right hM2 heps0
  have hsplit3 : M₀ * ((∫ x, x ^ d ∂ν) - B.qVal h) ^ 2
      ≤ (M₀ + 48 / (d : ℝ) ^ 3 + 2 / b) * ((∫ x, x ^ d ∂ν) - B.qVal h) ^ 2 :=
    mul_le_mul_of_nonneg_right hM3 (sq_nonneg _)
  linarith [hmain, hPT, hzmul, hsplit1, hsplit2, hsplit3]

end KKTFamily

end SingularEndpoint

end UpperTailOptimizers
