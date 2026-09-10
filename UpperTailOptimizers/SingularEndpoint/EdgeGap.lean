import UpperTailOptimizers.SingularEndpoint.Order5
import UpperTailOptimizers.SingularEndpoint.GamRVal

/-!
# The singular endpoint edge gap (Section 7, `paper/singular_endpoint.tex`)

The **singular endpoint edge gap** — the second bracket of the exact cost gap
`eq:constant-comparison-identity` —

  `e(W_h) - r_h = -(d-1)h² + O_d(h⁴)`.

In the paper this display is unlabelled: it sits
inside the proof of `lem:constant-graphon-comparison`, which also dropped the auxiliary abbreviations
`U₂`, `a₁` and the explicit coefficient computation reproduced below.

This file proves it, together with the two derived expansions of
`eq:rank-one-parameter-expansions` it passes through:

  `q_h = u_*^d - \frac{d(4d-1)}{3}u_*^{d-2}h² + o(h²)`,   `r_h = r_* - \frac{2(4d-1)}{3}h² + o(h²)`.

Everything is a consequence of the three quadratic coefficients of
`SingularEndpoint/Expansions.lean` and the block-weight slope of `SingularEndpoint/Order5.lean`; no new
analysis is involved.  The one combinatorial ingredient is the **second difference of a
power**,

  `\frac{s_h^d + t_h^d - 2u_h^d}{h²} \to d(d-1)u_*^{d-2}`,

which is exact: `t_h - u_h = h` and `s_h - u_h = -h`, so the two geometric-sum
factorisations of `x^d - y^d` combine into `∑_{j<d}\frac{t_h^j - s_h^j}{h}u_h^{d-1-j}` with
no remainder, and each summand has the rate `2j u_*^{j-1}` of `tendsto_pow_diff_rate`.

The arithmetic that produces the clean `-(d-1)`:

  `2u_*U₂ - 4u_*a₁ + \frac{2(4d-1)}{3}
     = \frac{5-3d}{3} - \frac{8d}{3} + \frac{8d-2}{3} = 1 - d`.

## Contents

* `sum_range_cast` — `∑_{j<n} j = n(n-1)/2` over `ℝ`;
* `tendsto_pow_second_diff` — the second difference of `x ↦ x^d` along the family;
* `tendsto_qVal_coeff`, `tendsto_rVal_coeff` — the `q` and `r` lines of
  `eq:rank-one-parameter-expansions`;
* `tendsto_edge_gap` — the edge gap, and `graphon_edge_gap`, its reading on the
  candidate graphon.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology Finset

variable {d : ℕ}

/-- `∑_{j<n} j = n(n-1)/2`, over `ℝ`. -/
theorem sum_range_cast (n : ℕ) : (∑ j ∈ range n, (j : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

variable (B : KKTFamily d)

/-! ## The second difference of a power -/

/-- **The second difference of `x ↦ x^d` at the family midpoint.**

  `\frac{s_h^d + t_h^d - 2u_h^d}{h²} \to d(d-1)u_*^{d-2}`.

The identity behind it is exact: `t_h^d - u_h^d = h·∑_{j<d}t_h^j u_h^{d-1-j}` and
`s_h^d - u_h^d = -h·∑_{j<d}s_h^j u_h^{d-1-j}`, so the second difference divided by `h²` is
`∑_{j<d}\frac{t_h^j - s_h^j}{h}u_h^{d-1-j}` on the nose. -/
theorem tendsto_pow_second_diff (hd : 2 ≤ d) :
    Tendsto (fun h : ℝ => (B.sVal h ^ d + B.tVal h ^ d - 2 * B.u h ^ d) / h ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 ((d : ℝ) * ((d : ℝ) - 1) * uStar d ^ (d - 2))) := by
  have hterm : Tendsto (fun h : ℝ =>
      ∑ j ∈ range d, ((B.tVal h ^ j - B.sVal h ^ j) / h) * B.u h ^ (d - 1 - j))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∑ j ∈ range d, (2 * (j : ℝ) * uStar d ^ (j - 1)) * uStar d ^ (d - 1 - j))) := by
    refine tendsto_finsetSum _ fun j _ => ?_
    exact (tendsto_pow_diff_rate B j).mul ((tendsto_u_punctured B).pow (d - 1 - j))
  have hval : (∑ j ∈ range d, (2 * (j : ℝ) * uStar d ^ (j - 1)) * uStar d ^ (d - 1 - j))
      = (d : ℝ) * ((d : ℝ) - 1) * uStar d ^ (d - 2) := by
    have hcongr : ∀ j ∈ range d,
        (2 * (j : ℝ) * uStar d ^ (j - 1)) * uStar d ^ (d - 1 - j)
          = 2 * uStar d ^ (d - 2) * (j : ℝ) := by
      intro j hj
      have hjd : j < d := mem_range.mp hj
      rcases Nat.eq_zero_or_pos j with rfl | hj1
      · simp
      · rw [mul_assoc, ← pow_add, show j - 1 + (d - 1 - j) = d - 2 from by omega]
        ring
    rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum, sum_range_cast]
    have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
    field_simp
  rw [hval] at hterm
  refine hterm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := hh
  have e1 := pow_sub_pow_eq (B.tVal h) (B.u h) d
  have e2 := pow_sub_pow_eq (B.sVal h) (B.u h) d
  have ht : B.tVal h - B.u h = h := by rw [KKTFamily.tVal]; ring
  have hs : B.sVal h - B.u h = -h := by rw [KKTFamily.sVal]; ring
  rw [ht] at e1
  rw [hs] at e2
  have hsplit : (∑ j ∈ range d, ((B.tVal h ^ j - B.sVal h ^ j) / h) * B.u h ^ (d - 1 - j))
      = ((∑ j ∈ range d, B.tVal h ^ j * B.u h ^ (d - 1 - j))
        - ∑ j ∈ range d, B.sVal h ^ j * B.u h ^ (d - 1 - j)) / h := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by field_simp
  have ht1 : (∑ j ∈ range d, B.tVal h ^ j * B.u h ^ (d - 1 - j))
      = (B.tVal h ^ d - B.u h ^ d) / h := by
    rw [eq_div_iff hne]; linear_combination -e1
  have hs1 : (∑ j ∈ range d, B.sVal h ^ j * B.u h ^ (d - 1 - j))
      = (B.u h ^ d - B.sVal h ^ d) / h := by
    rw [eq_div_iff hne]; linear_combination e2
  rw [hsplit, ht1, hs1]
  field_simp
  ring

/-! ## The `q` and `r` coefficients -/

/-- **`eq:rank-one-parameter-expansions`, the `q` line**:

  `q_h = u_*^d - \frac{d(4d-1)}{3}u_*^{d-2}h² + o(h²)`.

`q_h - u_*^d` splits as `\frac{s^d + t^d - 2u^d}{2} + (u^d - u_*^d) - (α_h-\frac12)(t^d-s^d)`,
whose three rates are `\frac{d(d-1)}{2}u_*^{d-2}`, `du_*^{d-1}U₂` and `2da₁u_*^{d-1}`. -/
theorem tendsto_qVal_coeff (hd : 2 ≤ d) :
    Tendsto (fun h : ℝ => (B.qVal h - uStar d ^ d) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-((d : ℝ) * (4 * (d : ℝ) - 1) / 3 * uStar d ^ (d - 2)))) := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hune : uStar d ≠ 0 := ne_of_gt (uStar_pos hd)
  have hsq : uStar d ^ 2 = rStar d := uStar_sq hd
  -- the three rates
  have hA := (tendsto_pow_second_diff B hd).div_const (2 : ℝ)
  have hB : Tendsto (fun h : ℝ => (B.u h ^ d - uStar d ^ d) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (Ucoeff B * ((d : ℝ) * uStar d ^ (d - 1)))) := by
    have hg := tendsto_geom_sum₂ (f := B.u) (g := fun _ : ℝ => uStar d) d
      (tendsto_u_punctured B) tendsto_const_nhds
    have h := (tendsto_u_coeff B).mul hg
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ≠ 0 := hh
    rw [pow_sub_pow_eq (B.u h) (uStar d) d]
    field_simp
  have hC := (tendsto_alph_slope B hd).mul (tendsto_pow_diff_rate B d)
  have hsum := (hA.add hB).sub hC
  have hval : (d : ℝ) * ((d : ℝ) - 1) * uStar d ^ (d - 2) / 2
      + Ucoeff B * ((d : ℝ) * uStar d ^ (d - 1))
      - 2 * (d : ℝ) ^ 2 * uStar d / (3 * ((d : ℝ) - 1)) * (2 * (d : ℝ) * uStar d ^ (d - 1))
      = -((d : ℝ) * (4 * (d : ℝ) - 1) / 3 * uStar d ^ (d - 2)) := by
    have hd0 : (d : ℝ) ≠ 0 := by linarith
    have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
    have hpow1 : uStar d ^ (d - 1) = uStar d * uStar d ^ (d - 2) := by
      rw [← pow_succ', show d - 2 + 1 = d - 1 from by omega]
    have hsq' : uStar d * uStar d = ((d : ℝ) - 1) / (d : ℝ) := by
      rw [← sq, hsq, rStar_eq]
    have key1 : Ucoeff B * ((d : ℝ) * uStar d ^ (d - 1))
        = (5 - 3 * (d : ℝ)) * (d : ℝ) / 6 * uStar d ^ (d - 2) := by
      rw [Ucoeff_eq B hd, hpow1]; field_simp
    have key2 : 2 * (d : ℝ) ^ 2 * uStar d / (3 * ((d : ℝ) - 1))
        * (2 * (d : ℝ) * uStar d ^ (d - 1)) = 4 * (d : ℝ) ^ 2 / 3 * uStar d ^ (d - 2) := by
      rw [hpow1, show 2 * (d : ℝ) ^ 2 * uStar d / (3 * ((d : ℝ) - 1))
          * (2 * (d : ℝ) * (uStar d * uStar d ^ (d - 2)))
          = 4 * (d : ℝ) ^ 3 / (3 * ((d : ℝ) - 1)) * (uStar d * uStar d) * uStar d ^ (d - 2) from
        by ring, hsq']
      field_simp
    rw [key1, key2]
    field_simp
    ring
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := hh
  rw [KKTFamily.qVal]
  field_simp
  ring

/-- **`eq:rank-one-parameter-expansions`, the `r` line**: `r_h = r_* - \frac{2(4d-1)}{3}h² + o(h²)`.

Obtained from `r_h^d = q_h²` (`rVal_pow_d`) by dividing the geometric-sum factorisation of
`r_h^d - r_*^d` by its non-vanishing cofactor `∑_{j<d}r_h^j r_*^{d-1-j} \to d r_*^{d-1}`. -/
theorem tendsto_rVal_coeff (hd : 2 ≤ d) :
    Tendsto (fun h : ℝ => (B.rVal h - rStar d) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-(2 * (4 * (d : ℝ) - 1) / 3))) := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hune : uStar d ≠ 0 := ne_of_gt (uStar_pos hd)
  have hrpos : (0 : ℝ) < rStar d := rStar_pos hd
  have hsq : uStar d ^ 2 = rStar d := uStar_sq hd
  -- the numerator `(r_h^d - r_*^d)/h²`
  have hq := tendsto_qVal_coeff B hd
  have hqv : Tendsto B.qVal (𝓝[≠] (0 : ℝ)) (𝓝 (uStar d ^ d)) := tendsto_qVal B
  have hnum : Tendsto (fun h : ℝ => (B.rVal h ^ d - rStar d ^ d) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-((d : ℝ) * (4 * (d : ℝ) - 1) / 3 * uStar d ^ (d - 2)) * (2 * uStar d ^ d))) := by
    have h := hq.mul (hqv.add (tendsto_const_nhds (x := uStar d ^ d)))
    rw [show uStar d ^ d + uStar d ^ d = 2 * uStar d ^ d from by ring] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin, eventually_window B] with h hh hw
    have hne : h ≠ 0 := hh
    have hrd := KKTFamily.rVal_pow_d hd hw
    have hsd : rStar d ^ d = uStar d ^ d * uStar d ^ d := by
      rw [← pow_add, ← two_mul, pow_mul, hsq]
    rw [hrd, hsd]
    field_simp
    ring
  -- the cofactor
  have hcof := tendsto_geom_sum₂ (f := B.rVal) (g := fun _ : ℝ => rStar d) d
    (tendsto_rVal hd B) tendsto_const_nhds
  have hcofne : (d : ℝ) * rStar d ^ (d - 1) ≠ 0 := by positivity
  have hdiv := hnum.div hcof hcofne
  have hval : -((d : ℝ) * (4 * (d : ℝ) - 1) / 3 * uStar d ^ (d - 2)) * (2 * uStar d ^ d)
      / ((d : ℝ) * rStar d ^ (d - 1)) = -(2 * (4 * (d : ℝ) - 1) / 3) := by
    have e1 : uStar d ^ d = uStar d ^ (d - 2) * rStar d := by
      rw [← hsq, ← pow_add, show d - 2 + 2 = d from by omega]
    have e2 : rStar d ^ (d - 1) = uStar d ^ (d - 2) * uStar d ^ (d - 2) * rStar d := by
      rw [← pow_add, ← hsq, ← pow_mul, ← pow_add,
        show d - 2 + (d - 2) + 2 = 2 * (d - 1) from by omega, mul_comm 2 (d - 1), pow_mul]
    rw [e1, e2]
    have hune2 : uStar d ^ (d - 2) ≠ 0 := pow_ne_zero _ hune
    have hd0 : (d : ℝ) ≠ 0 := by linarith
    field_simp
  rw [hval] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_window B] with h hh hw
  have hne : h ≠ 0 := hh
  have hrv : (0 : ℝ) < B.rVal h := KKTFamily.rVal_pos hd hw
  have hSne : (∑ i ∈ range d, B.rVal h ^ i * rStar d ^ (d - 1 - i)) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun i _ => by positivity)
      ⟨0, mem_range.mpr (by omega : 0 < d)⟩)
  simp only [Pi.div_apply]
  rw [pow_sub_pow_eq (B.rVal h) (rStar d) d]
  field_simp

/-! ## The edge gap -/

/-- **The singular endpoint edge gap** (unlabelled in the proof of `lem:constant-graphon-comparison`):
`\frac{e(W_h) - r_h}{h²} \to -(d-1)`.

`e(W_h) = \{α_h s_h + (1-α_h)t_h\}² = \{u_h - 2h(α_h - \frac12)\}²`, so the rate of
`e(W_h) - r_*` is `2u_*(U₂ - 2a₁)`, and adding `\frac{2(4d-1)}{3}` from `tendsto_rVal_coeff`
gives `\frac{5-3d}{3} - \frac{8d}{3} + \frac{8d-2}{3} = 1-d`. -/
theorem tendsto_edge_gap (hd : 2 ≤ d) :
    Tendsto (fun h : ℝ =>
        ((B.alph h * B.sVal h + (1 - B.alph h) * B.tVal h) ^ 2 - B.rVal h) / h ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (-((d : ℝ) - 1))) := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hune : uStar d ≠ 0 := ne_of_gt (uStar_pos hd)
  have hsq : uStar d ^ 2 = rStar d := uStar_sq hd
  -- the midpoint rate
  have hmid : Tendsto (fun h : ℝ =>
      ((B.alph h * B.sVal h + (1 - B.alph h) * B.tVal h) - uStar d) / h ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (Ucoeff B - 2 * (2 * (d : ℝ) ^ 2 * uStar d / (3 * ((d : ℝ) - 1))))) := by
    have h := (tendsto_u_coeff B).sub ((tendsto_alph_slope B hd).const_mul (2 : ℝ))
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ≠ 0 := hh
    rw [KKTFamily.sVal, KKTFamily.tVal]
    field_simp
    ring
  have hsum : Tendsto (fun h : ℝ =>
      (B.alph h * B.sVal h + (1 - B.alph h) * B.tVal h) + uStar d) (𝓝[≠] (0 : ℝ))
      (𝓝 (2 * uStar d)) := by
    have halph : Tendsto B.alph (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) :=
      (tendsto_alph B).mono_left nhdsWithin_le_nhds
    have h := ((halph.mul (tendsto_sVal B)).add
      ((tendsto_const_nhds (x := (1 : ℝ)) |>.sub halph).mul (tendsto_tVal B))).add
      (tendsto_const_nhds (x := uStar d))
    rw [show (1 / 2 : ℝ) * uStar d + (1 - 1 / 2) * uStar d + uStar d = 2 * uStar d from by ring] at h
    exact h
  have hedge := (hmid.mul hsum).sub (tendsto_rVal_coeff B hd)
  have hval : (Ucoeff B - 2 * (2 * (d : ℝ) ^ 2 * uStar d / (3 * ((d : ℝ) - 1)))) * (2 * uStar d)
      - -(2 * (4 * (d : ℝ) - 1) / 3) = -((d : ℝ) - 1) := by
    have hd0 : (d : ℝ) ≠ 0 := by linarith
    have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
    have hsq' : uStar d * uStar d = ((d : ℝ) - 1) / (d : ℝ) := by
      rw [← sq, hsq, rStar_eq]
    have e1 : (5 - 3 * (d : ℝ)) / (6 * uStar d) * (2 * uStar d) = (5 - 3 * (d : ℝ)) / 3 := by
      field_simp; ring
    have e2 : 2 * (2 * (d : ℝ) ^ 2 * uStar d / (3 * ((d : ℝ) - 1))) * (2 * uStar d)
        = 8 * (d : ℝ) / 3 := by
      rw [show 2 * (2 * (d : ℝ) ^ 2 * uStar d / (3 * ((d : ℝ) - 1))) * (2 * uStar d)
          = 8 * (d : ℝ) ^ 2 / (3 * ((d : ℝ) - 1)) * (uStar d * uStar d) from by ring, hsq']
      field_simp
    rw [Ucoeff_eq B hd, sub_mul, e1, e2]
    field_simp
    ring
  rw [hval] at hedge
  refine hedge.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := hh
  have hr : rStar d = uStar d ^ 2 := hsq.symm
  rw [hr]
  field_simp
  ring

/-- The edge gap read on the candidate graphon itself, via `graphon_edgeDensity`. -/
theorem graphon_edge_gap (hd : 2 ≤ d) {F : ℝ → ℝ}
    (hF : ∀ (h : ℝ) (hh : |h| < B.h₀), F h = (B.graphon hh).edgeDensity) :
    Tendsto (fun h : ℝ => (F h - B.rVal h) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-((d : ℝ) - 1))) := by
  refine (tendsto_edge_gap B hd).congr' ?_
  filter_upwards [eventually_window B] with h hw
  rw [hF h hw, KKTFamily.graphon_edgeDensity hw]

end SingularEndpoint

end UpperTailOptimizers
