import Mathlib

/-!
# Elementary power-function inequalities (Section 4.2 toolkit)

Quantitative facts about `x ↦ x^k` on `[0,1]` used throughout Section 4.2
("The quadratic cost of an edge-density deficit", `sec:nonexceptional-quadratic-growth`) of
`paper/paper.tex`:

* `pow_sub_pow_eq` — the factorisation `x^k - y^k = (x-y) ∑_{i<k} x^i y^{k-1-i}`;
* `abs_pow_sub_pow_le` — the Lipschitz bound `|x^k - y^k| ≤ k |x-y|` on `[0,1]`;
* `pow_sub_pow_ge` — the reverse bound `y^{k-1} |x-y| ≤ |x^k - y^k|` for `x,y ≥ 0`;
* `pow_taylor_abs_le` — the first-order Taylor bound
  `|x^k - y^k - k y^{k-1} (x-y)| ≤ k² (x-y)²` on `[0,1]`;
* `pow_convex_gap_ge` / `pow_convex_gap_pos` — the strict-convexity gap
  `s^d - r^d - d r^{d-1}(s-r) ≥ r^{d-2} (s-r)²`, the quantity `d r^{d-1} D_d(r,s)`
  of the paper.

All the constants are explicit, so the lemmas can be instantiated uniformly over
compact parameter sets without any compactness argument.
-/

namespace UpperTailOptimizers

open Finset

/-- The factorisation `x^k - y^k = (x - y) · ∑_{i<k} x^i y^{k-1-i}`. -/
theorem pow_sub_pow_eq (x y : ℝ) (k : ℕ) :
    x ^ k - y ^ k = (x - y) * ∑ i ∈ range k, x ^ i * y ^ (k - 1 - i) := by
  rw [mul_comm]
  exact ((Commute.all x y).geom_sum₂_mul k).symm

/-- Each geometric-sum term is bounded by `1` on `[0,1]`, so the sum is at most `k`. -/
theorem geom_sum₂_le_card {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (k : ℕ) : ∑ i ∈ range k, x ^ i * y ^ (k - 1 - i) ≤ k := by
  calc ∑ i ∈ range k, x ^ i * y ^ (k - 1 - i)
      ≤ ∑ _i ∈ range k, (1:ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hx1 : x ^ i ≤ 1 := pow_le_one₀ hx.1 hx.2
        have hy1 : y ^ (k - 1 - i) ≤ 1 := pow_le_one₀ hy.1 hy.2
        calc x ^ i * y ^ (k - 1 - i) ≤ 1 * 1 :=
              mul_le_mul hx1 hy1 (pow_nonneg hy.1 _) zero_le_one
          _ = 1 := one_mul 1
    _ = k := by simp

/-- The geometric sum is nonnegative for `x, y ≥ 0`. -/
theorem geom_sum₂_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    0 ≤ ∑ i ∈ range k, x ^ i * y ^ (k - 1 - i) :=
  Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg hx i) (pow_nonneg hy _)

/-- **Lipschitz bound for powers on `[0,1]`**: `|x^k - y^k| ≤ k·|x - y|`. -/
theorem abs_pow_sub_pow_le {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (k : ℕ) : |x ^ k - y ^ k| ≤ k * |x - y| := by
  rw [pow_sub_pow_eq, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [abs_of_nonneg (geom_sum₂_nonneg hx.1 hy.1 k)]
  exact geom_sum₂_le_card hx hy k

/-- **Reverse Lipschitz bound**: `y^{k-1}·|x - y| ≤ |x^k - y^k|` for `x, y ≥ 0`, `1 ≤ k`. -/
theorem pow_sub_pow_ge {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {k : ℕ} (hk : 1 ≤ k) :
    y ^ (k - 1) * |x - y| ≤ |x ^ k - y ^ k| := by
  rw [pow_sub_pow_eq, abs_mul, mul_comm (y ^ (k - 1)) (|x - y|)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_of_nonneg (geom_sum₂_nonneg hx hy k)]
  have h0 : (0:ℕ) ∈ range k := Finset.mem_range.mpr hk
  calc y ^ (k - 1) = x ^ 0 * y ^ (k - 1 - 0) := by
        rw [pow_zero, one_mul]
        congr 1
    _ ≤ ∑ i ∈ range k, x ^ i * y ^ (k - 1 - i) :=
        Finset.single_le_sum (f := fun i => x ^ i * y ^ (k - 1 - i))
          (fun i _ => mul_nonneg (pow_nonneg hx i) (pow_nonneg hy _)) h0

/-- **First-order Taylor bound for powers on `[0,1]`**:
`|x^k - y^k - k·y^{k-1}·(x-y)| ≤ k²·(x-y)²`. -/
theorem pow_taylor_abs_le {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (k : ℕ) : |x ^ k - y ^ k - k * y ^ (k - 1) * (x - y)| ≤ k ^ 2 * (x - y) ^ 2 := by
  have hky : (k:ℝ) * y ^ (k - 1) = ∑ i ∈ range k, y ^ i * y ^ (k - 1 - i) :=
    (geom_sum₂_self y k).symm
  have hkey : x ^ k - y ^ k - k * y ^ (k - 1) * (x - y)
      = (x - y) * ∑ i ∈ range k, (x ^ i - y ^ i) * y ^ (k - 1 - i) := by
    rw [pow_sub_pow_eq, hky]
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1
    funext i
    ring
  rw [hkey, abs_mul]
  have hsum : |∑ i ∈ range k, (x ^ i - y ^ i) * y ^ (k - 1 - i)| ≤ k ^ 2 * |x - y| := by
    calc |∑ i ∈ range k, (x ^ i - y ^ i) * y ^ (k - 1 - i)|
        ≤ ∑ i ∈ range k, |(x ^ i - y ^ i) * y ^ (k - 1 - i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range k, (k:ℝ) * |x - y| := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [abs_mul]
          have h1 : |x ^ i - y ^ i| ≤ i * |x - y| := abs_pow_sub_pow_le hx hy i
          have h2 : |y ^ (k - 1 - i)| ≤ 1 := by
            rw [abs_of_nonneg (pow_nonneg hy.1 _)]
            exact pow_le_one₀ hy.1 hy.2
          calc |x ^ i - y ^ i| * |y ^ (k - 1 - i)|
              ≤ (i * |x - y|) * 1 :=
                mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
            _ = i * |x - y| := mul_one _
            _ ≤ k * |x - y| := by
                have : (i:ℝ) ≤ k := by
                  exact_mod_cast (Finset.mem_range.mp hi).le
                exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ = k * ((k:ℝ) * |x - y|) := by rw [Finset.sum_const, Finset.card_range]; simp
      _ = k ^ 2 * |x - y| := by ring
  calc |x - y| * |∑ i ∈ range k, (x ^ i - y ^ i) * y ^ (k - 1 - i)|
      ≤ |x - y| * (k ^ 2 * |x - y|) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = k ^ 2 * (|x - y| * |x - y|) := by ring
    _ = k ^ 2 * (x - y) ^ 2 := by rw [← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]

/-- The strict-convexity gap of `u ↦ u^d` as a double geometric sum:
`s^d - r^d - d·r^{d-1}·(s-r) = (s-r)² · T` with
`T = ∑_{i<d} (∑_{j<i} s^j r^{i-1-j}) r^{d-1-i}`. -/
theorem pow_convex_gap_eq (r s : ℝ) (d : ℕ) :
    s ^ d - r ^ d - d * r ^ (d - 1) * (s - r)
      = (s - r) ^ 2 * ∑ i ∈ range d, (∑ j ∈ range i, s ^ j * r ^ (i - 1 - j)) * r ^ (d - 1 - i) := by
  have hdr : (d:ℝ) * r ^ (d - 1) = ∑ i ∈ range d, r ^ i * r ^ (d - 1 - i) :=
    (geom_sum₂_self r d).symm
  have h1 : s ^ d - r ^ d - d * r ^ (d - 1) * (s - r)
      = (s - r) * ∑ i ∈ range d, (s ^ i - r ^ i) * r ^ (d - 1 - i) := by
    rw [pow_sub_pow_eq s r d, hdr]
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1
    funext i
    ring
  rw [h1]
  have h2 : ∀ i ∈ range d, (s ^ i - r ^ i) * r ^ (d - 1 - i)
      = (s - r) * ((∑ j ∈ range i, s ^ j * r ^ (i - 1 - j)) * r ^ (d - 1 - i)) := by
    intro i _
    rw [pow_sub_pow_eq s r i]
    ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  ring

/-- **Lower bound on the convexity gap**: for `0 ≤ r, s` and `2 ≤ d`,
`r^{d-2}·(s-r)² ≤ s^d - r^d - d·r^{d-1}·(s-r)`. -/
theorem pow_convex_gap_ge {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) {d : ℕ} (hd : 2 ≤ d) :
    r ^ (d - 2) * (s - r) ^ 2 ≤ s ^ d - r ^ d - d * r ^ (d - 1) * (s - r) := by
  rw [pow_convex_gap_eq]
  rw [mul_comm (r ^ (d - 2)) ((s - r) ^ 2)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  -- the `i = d-1` term already dominates `r^{d-2}`
  have hmem : d - 1 ∈ range d := Finset.mem_range.mpr (by omega)
  have hterm : r ^ (d - 2)
      ≤ (∑ j ∈ range (d - 1), s ^ j * r ^ (d - 1 - 1 - j)) * r ^ (d - 1 - (d - 1)) := by
    have h0 : (0:ℕ) ∈ range (d - 1) := Finset.mem_range.mpr (by omega)
    have hsingle : s ^ 0 * r ^ (d - 1 - 1 - 0) ≤ ∑ j ∈ range (d - 1), s ^ j * r ^ (d - 1 - 1 - j) :=
      Finset.single_le_sum (f := fun j => s ^ j * r ^ (d - 1 - 1 - j))
        (fun j _ => mul_nonneg (pow_nonneg hs j) (pow_nonneg hr _)) h0
    have heq : s ^ 0 * r ^ (d - 1 - 1 - 0) = r ^ (d - 2) := by
      rw [pow_zero, one_mul]
      congr 1
    have hlast : d - 1 - (d - 1) = 0 := by omega
    rw [hlast, pow_zero, mul_one]
    rw [heq] at hsingle
    exact hsingle
  refine le_trans hterm ?_
  refine Finset.single_le_sum
    (f := fun i => (∑ j ∈ range i, s ^ j * r ^ (i - 1 - j)) * r ^ (d - 1 - i))
    (fun i _ => ?_) hmem
  exact mul_nonneg
    (Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg hs j) (pow_nonneg hr _))
    (pow_nonneg hr _)

/-- **Strict positivity of the convexity gap**: for `0 < r`, `0 ≤ s`, `s ≠ r`, `2 ≤ d`,
`0 < s^d - r^d - d·r^{d-1}·(s-r)`.  This is `d·r^{d-1}·D_d(r,s)` of the paper. -/
theorem pow_convex_gap_pos {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (hrs : s ≠ r) {d : ℕ}
    (hd : 2 ≤ d) : 0 < s ^ d - r ^ d - d * r ^ (d - 1) * (s - r) := by
  have h := pow_convex_gap_ge hr.le hs hd
  have hpos : 0 < r ^ (d - 2) * (s - r) ^ 2 := by
    have h1 : 0 < r ^ (d - 2) := pow_pos hr _
    have h2 : 0 < (s - r) ^ 2 := by
      have : s - r ≠ 0 := sub_ne_zero.mpr hrs
      positivity
    positivity
  linarith

end UpperTailOptimizers
