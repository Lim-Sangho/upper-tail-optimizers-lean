import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.FamilyQuadratic

/-!
# The trapezoid remainder (Section 5, `paper/sections/singular.tex`)

Section 5 computes the `h⁵` coefficient of the increment at the contacts
`B_h - A_h = 𝓜_h(t_h²) - 𝓜_h(s_h²)`, and that coefficient is what pins the block-weight slope
`a₁ = α'(0) = 2d²u_*/(3(d-1))` of `eq:rank-one-parameter-expansions`.  The increment is an
integral of `𝓜_h'` across the outer pair of nodes, and the two nodes sit at distance `2h`
apart *exactly* (`t_h - s_h = 2h`).  Comparing that integral against its trapezoid-rule value
therefore costs an exact power of `h`, not merely an estimate — the algebraic content of the
comparison is the identity proved here.

For the model integrand `z ↦ z^{d-1}` the comparison reads

  `\frac{x^{d-1}+y^{d-1}}{2}(x-y) - \frac{x^d - y^d}{d}
     = \frac{(x-y)^3}{2d}\sum_{j<d}
        \Bigl(\sum_{i<j}x^iy^{j-1-i}\Bigr)\Bigl(\sum_{i<d-1-j}x^iy^{d-1-j-1-i}\Bigr)`,

the *trapezoid error* on the left and an **exact** factor `(x-y)^3` on the right.  No `O(·)`
and no mean-value point: the cofactor is a named double geometric sum, so it can be evaluated
in a limit, which is precisely what distinguishes the `h⁵` order from the `h⁴` order of
`SingularEndpoint/RankOneStationaryFamily/Order4.lean` (compare the discussion in `SingularEndpoint/ConstantGraphonComparison/TaylorTail.lean`).

Two further facts finish the evaluation.  The cofactor's combinatorial weight is
`∑_{j<d} j(d-1-j) = d(d-1)(d-2)/6`, and when the two arguments run to a common limit `c` the
cofactor itself converges to `d(d-1)(d-2)/6 · c^{d-3}` — the `tendsto_geom_sum₂` helper of
`SingularEndpoint/ConstantGraphonComparison/FamilyQuadratic.lean` applied to each of the two inner sums.

Everything in this file is pure algebra, finite combinatorics and elementary limits: no
family, no graphon, no entropy.

## Contents

* `trapezoid_error_eq` — the trapezoid identity, with its exact `(x-y)^3`;
* `sum_range_mul_compl` — `∑_{j<d} j(d-1-j) = d(d-1)(d-2)/6`, valid for every `d`;
* `tendsto_trapezoid_sum` — the cofactor tends to `d(d-1)(d-2)/6 · c^{d-3}`.

That is the whole interface; the three private helpers below are used nowhere else.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

/-! ## The trapezoid identity -/

/-- **Step A.**  Pairing the two power differences across the range,

  `∑_{j<d} (x^j - y^j)(x^{d-1-j} - y^{d-1-j})
     = d(x^{d-1} + y^{d-1}) - 2∑_{j<d} x^j y^{d-1-j}`.

The diagonal products collapse because `j + (d-1-j) = d-1` for `j < d`, and the two mixed
sums agree by reflecting the index (`Finset.sum_range_reflect`). -/
private theorem sum_pow_diff_prod (d : ℕ) (x y : ℝ) :
    ∑ j ∈ Finset.range d, (x ^ j - y ^ j) * (x ^ (d - 1 - j) - y ^ (d - 1 - j))
      = (d : ℝ) * (x ^ (d - 1) + y ^ (d - 1))
        - 2 * ∑ j ∈ Finset.range d, x ^ j * y ^ (d - 1 - j) := by
  have hrefl : ∑ j ∈ Finset.range d, y ^ j * x ^ (d - 1 - j)
      = ∑ j ∈ Finset.range d, x ^ j * y ^ (d - 1 - j) := by
    have h := Finset.sum_range_reflect (fun j => x ^ j * y ^ (d - 1 - j)) d
    rw [← h]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < d := Finset.mem_range.mp hj
    have h1 : d - 1 - (d - 1 - j) = j := by omega
    simp only [h1]
    ring
  have hexp : ∀ j ∈ Finset.range d, (x ^ j - y ^ j) * (x ^ (d - 1 - j) - y ^ (d - 1 - j))
      = (x ^ (d - 1) + y ^ (d - 1)) - x ^ j * y ^ (d - 1 - j) - y ^ j * x ^ (d - 1 - j) := by
    intro j hj
    have hj' : j < d := Finset.mem_range.mp hj
    have hadd : j + (d - 1 - j) = d - 1 := by omega
    have hx : x ^ j * x ^ (d - 1 - j) = x ^ (d - 1) := by rw [← pow_add, hadd]
    have hy : y ^ j * y ^ (d - 1 - j) = y ^ (d - 1) := by rw [← pow_add, hadd]
    rw [show (x ^ j - y ^ j) * (x ^ (d - 1 - j) - y ^ (d - 1 - j))
        = x ^ j * x ^ (d - 1 - j) + y ^ j * y ^ (d - 1 - j)
          - x ^ j * y ^ (d - 1 - j) - y ^ j * x ^ (d - 1 - j) from by ring, hx, hy]
  rw [Finset.sum_congr rfl hexp]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hrefl]
  ring

/-- **The trapezoid identity.**  The trapezoid-rule error for `∫_y^x z^{d-1}\,dz`,

  `\frac{x^{d-1}+y^{d-1}}{2}(x-y) - \frac{x^d-y^d}{d}`,

carries an exact factor `(x-y)^3`:

  `= \frac{(x-y)^3}{2d}\sum_{j<d}
      \Bigl(\sum_{i<j}x^iy^{j-1-i}\Bigr)\Bigl(\sum_{i<d-1-j}x^iy^{d-1-j-1-i}\Bigr)`.

The hypothesis `1 ≤ d` is needed: at `d = 0` the left-hand side is `x - y` (Lean's `x/0 = 0`
swallows the second term) while the right-hand side is `0`.

Section 5 uses this at `x = t_h`, `y = s_h`, where `x - y = 2h` exactly, so the cubic factor
is exactly `8h³` and the whole error is `h³` times a convergent cofactor
(`tendsto_trapezoid_sum`). -/
theorem trapezoid_error_eq (d : ℕ) (hd : 1 ≤ d) (x y : ℝ) :
    (x ^ (d - 1) + y ^ (d - 1)) * (x - y) / 2 - (x ^ d - y ^ d) / (d : ℝ)
      = (x - y) ^ 3 / (2 * (d : ℝ))
        * ∑ j ∈ Finset.range d,
            (∑ i ∈ Finset.range j, x ^ i * y ^ (j - 1 - i))
              * (∑ i ∈ Finset.range (d - 1 - j), x ^ i * y ^ (d - 1 - j - 1 - i)) := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ j ∈ Finset.range d,
      (∑ i ∈ Finset.range j, x ^ i * y ^ (j - 1 - i))
        * (∑ i ∈ Finset.range (d - 1 - j), x ^ i * y ^ (d - 1 - j - 1 - i)) := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ∑ j ∈ Finset.range d, x ^ j * y ^ (d - 1 - j) := ⟨_, rfl⟩
  have hS : (x - y) ^ 2 * S = (d : ℝ) * (x ^ (d - 1) + y ^ (d - 1)) - 2 * P := by
    rw [hSdef, hPdef, ← sum_pow_diff_prod d x y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_sub_pow_eq x y j, pow_sub_pow_eq x y (d - 1 - j)]
    ring
  rw [← hSdef, pow_sub_pow_eq x y d, ← hPdef,
    show (x - y) ^ 3 / (2 * (d : ℝ)) * S = (x - y) / (2 * (d : ℝ)) * ((x - y) ^ 2 * S) from
      by ring, hS]
  field_simp

/-! ## The combinatorial weight -/

/-- Gauss's sum over `ℝ`: `∑_{j<d} j = d(d-1)/2`. -/
private theorem sum_range_cast_id (d : ℕ) :
    (∑ j ∈ Finset.range d, (j : ℝ)) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  induction d with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The square pyramid over `ℝ`: `∑_{j<d} j² = d(d-1)(2d-1)/6`. -/
private theorem sum_range_cast_sq (d : ℕ) :
    (∑ j ∈ Finset.range d, (j : ℝ) ^ 2) = (d : ℝ) * ((d : ℝ) - 1) * (2 * (d : ℝ) - 1) / 6 := by
  induction d with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **The combinatorial weight of the trapezoid cofactor**:

  `∑_{j<d} j·(d-1-j) = d(d-1)(d-2)/6`,

with `d - 1 - j` the *natural* subtraction.  True for every `d`, including `d = 0, 1, 2`,
where both sides vanish.  It is the sum of the products of the two inner geometric sums'
lengths, and `tendsto_trapezoid_sum` is exactly this weight times `c^{d-3}`. -/
theorem sum_range_mul_compl (d : ℕ) :
    (∑ j ∈ Finset.range d, (j : ℝ) * ((d - 1 - j : ℕ) : ℝ))
      = (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) / 6 := by
  have hcast : ∀ j ∈ Finset.range d, (j : ℝ) * ((d - 1 - j : ℕ) : ℝ)
      = ((d : ℝ) - 1) * (j : ℝ) - (j : ℝ) ^ 2 := by
    intro j hj
    have hj' : j < d := Finset.mem_range.mp hj
    rw [Nat.cast_sub (by omega : j ≤ d - 1), Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    ring
  rw [Finset.sum_congr rfl hcast, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_range_cast_id, sum_range_cast_sq]
  ring

/-! ## The limit of the cofactor -/

/-- **The trapezoid cofactor in the limit.**  If `x h` and `y h` both tend to `c` as
`h → 0`, `h ≠ 0`, then

  `∑_{j<d}\Bigl(∑_{i<j}x^iy^{j-1-i}\Bigr)\Bigl(∑_{i<d-1-j}x^iy^{d-1-j-1-i}\Bigr)
     →  \frac{d(d-1)(d-2)}{6}\,c^{d-3}`.

Each inner sum is handled by `tendsto_geom_sum₂` (`SingularEndpoint/ConstantGraphonComparison/FamilyQuadratic.lean`), giving the
limit `∑_{j<d} (j c^{j-1})((d-1-j) c^{d-1-j-1})`; the exponents add to `d-3` on the range
`1 ≤ j ≤ d-2`, and off that range one of the two integer factors is `0`, so the whole sum is
`c^{d-3}·∑_{j<d} j(d-1-j)` and `sum_range_mul_compl` finishes.

Applied along the family with `x = t_h`, `y = s_h` and `c = u_*`, this converts
`trapezoid_error_eq` into the `h³`-rate statement Section 5's `h⁵` bookkeeping consumes. -/
theorem tendsto_trapezoid_sum {x y : ℝ → ℝ} {c : ℝ} (d : ℕ)
    (hx : Tendsto x (𝓝[≠] (0 : ℝ)) (𝓝 c))
    (hy : Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝 c)) :
    Tendsto (fun h : ℝ => ∑ j ∈ Finset.range d,
        (∑ i ∈ Finset.range j, x h ^ i * y h ^ (j - 1 - i))
          * (∑ i ∈ Finset.range (d - 1 - j), x h ^ i * y h ^ (d - 1 - j - 1 - i)))
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) / 6 * c ^ (d - 3))) := by
  have hterms : ∀ j ∈ Finset.range d,
      ((j : ℝ) * c ^ (j - 1)) * (((d - 1 - j : ℕ) : ℝ) * c ^ (d - 1 - j - 1))
        = c ^ (d - 3) * ((j : ℝ) * ((d - 1 - j : ℕ) : ℝ)) := by
    intro j hj
    have hj' : j < d := Finset.mem_range.mp hj
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · simp [hj0]
    · by_cases hjd : j + 1 < d
      · have hpow : (j - 1) + (d - 1 - j - 1) = d - 3 := by omega
        rw [show ((j : ℝ) * c ^ (j - 1)) * (((d - 1 - j : ℕ) : ℝ) * c ^ (d - 1 - j - 1))
            = (j : ℝ) * ((d - 1 - j : ℕ) : ℝ) * (c ^ (j - 1) * c ^ (d - 1 - j - 1)) from
          by ring, ← pow_add, hpow]
        ring
      · have hzero : d - 1 - j = 0 := by omega
        rw [hzero]
        simp
  have hval : ∑ j ∈ Finset.range d,
      ((j : ℝ) * c ^ (j - 1)) * (((d - 1 - j : ℕ) : ℝ) * c ^ (d - 1 - j - 1))
        = (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) / 6 * c ^ (d - 3) := by
    rw [Finset.sum_congr rfl hterms, ← Finset.mul_sum, sum_range_mul_compl]
    ring
  rw [← hval]
  exact tendsto_finsetSum _ fun j _ =>
    (tendsto_geom_sum₂ j hx hy).mul (tendsto_geom_sum₂ (d - 1 - j) hx hy)

end SingularEndpoint

end UpperTailOptimizers
