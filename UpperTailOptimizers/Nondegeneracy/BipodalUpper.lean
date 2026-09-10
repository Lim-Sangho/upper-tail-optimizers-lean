import UpperTailOptimizers.Nondegeneracy.TDensityExpansion
import UpperTailOptimizers.Nondegeneracy.ArcBounds

/-!
# The matching quadratic upper bound (`lem:bipodal-quadratic-bound` of `paper/bipodal_optimizer.tex`): scalar toolkit

**`lem:bipodal-quadratic-bound` (quadratic upper bound).**  Uniformly for `r` in a compact subarc `K` of a
Lubetzky–Zhao boundary arc: for every small `δ > 0` there is a bipodal graphon `V_δ` with
`e(V_δ) = r - δ`, `t(H, V_δ) = r^m`, and `I_{pc(r)}(V_δ) ≤ J_{pc(r)}(r) + C' δ²`.

The construction is the paper's: a small block of size `c` with internal density
`a = 1/2`, cross density `s = sm(r)` (the second contact), and large-block density `q`
adjusted to meet the constraints.  The formalisation replaces the paper's analytic
implicit function theorem and its patching argument by a **quantitative one-variable
solve**: the edge constraint determines `q = qSolve a s r δ c` explicitly, and the
`H`-density constraint `tBip = r^m` is solved for `c` by the intermediate value
theorem, using the linearisation

`tBip - r^m ≈ m r^{m-1}(q - r) + n c (s^d r^{m-d} - r^m)`

with explicit error constants (`tBip_linearization`).  All estimates carry explicit
constants, so the resulting `C'` and `δ₀` are uniform over `K` with no compactness
patching.  This file contains the scalar helpers and the `I_p` formula for the
two-block graphon; the headline theorem `quadratic_upper` follows in
`Nondegeneracy/QuadraticUpper.lean`.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set

/-! ### The explicit solution of the edge constraint -/

/-- The large-block density solving the edge constraint
`a c² + 2c(1-c) s + (1-c)² q = r - δ` for `q`. -/
noncomputable def qSolve (a s r δ c : ℝ) : ℝ :=
  (r - δ - c ^ 2 * a - 2 * c * (1 - c) * s) / (1 - c) ^ 2

/-- `qSolve` satisfies the edge constraint (in the block form of
`bipodalGraphon_edgeDensity`). -/
theorem qSolve_edge {c : ℝ} (a s r δ : ℝ) (hc : c ≠ 1) :
    a * c ^ 2 + s * (2 * c * (1 - c)) + qSolve a s r δ c * (1 - c) ^ 2 = r - δ := by
  have h1c : (1 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  unfold qSolve
  field_simp
  ring

/-- `qSolve` at `c = 0` is `r - δ`. -/
theorem qSolve_zero (a s r δ : ℝ) : qSolve a s r δ 0 = r - δ := by
  unfold qSolve
  norm_num

/-- The deviation of `qSolve` from `r`, exactly. -/
theorem qSolve_sub_eq {c : ℝ} (a s r δ : ℝ) (hc : c ≠ 1) :
    qSolve a s r δ c - r
      = (2 * c * (r - s) - δ + c ^ 2 * (2 * s - a - r)) / (1 - c) ^ 2 := by
  have h1c : (1 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  unfold qSolve
  field_simp
  ring

/-- Crude deviation bound: `|qSolve - r| ≤ 16 c + 4 δ` on the box
`c ∈ [0, 1/2]`, `δ ≥ 0`, `a, s, r ∈ [0,1]`. -/
theorem qSolve_dev_bound {a s r δ c : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hs : s ∈ Set.Icc (0:ℝ) 1) (hr : r ∈ Set.Icc (0:ℝ) 1)
    (hc0 : 0 ≤ c) (hc2 : c ≤ 1/2) (hδ0 : 0 ≤ δ) :
    |qSolve a s r δ c - r| ≤ 16 * c + 4 * δ := by
  have hc1 : c ≠ 1 := by intro h; rw [h] at hc2; norm_num at hc2
  rw [qSolve_sub_eq a s r δ hc1, abs_div]
  have hden : (1/4 : ℝ) ≤ (1 - c) ^ 2 := by nlinarith
  have hdenpos : (0:ℝ) < (1 - c) ^ 2 := by nlinarith
  have hnum : |2 * c * (r - s) - δ + c ^ 2 * (2 * s - a - r)| ≤ 4 * c + δ := by
    have hrs : |r - s| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hr.1, hs.2], by linarith [hr.2, hs.1]⟩
    have h1 : |2 * c * (r - s) - δ| ≤ 2 * c + δ := by
      calc |2 * c * (r - s) - δ| ≤ |2 * c * (r - s)| + |δ| := abs_sub _ _
        _ = 2 * c * |r - s| + δ := by
            rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * c), abs_of_nonneg hδ0]
        _ ≤ 2 * c + δ := by nlinarith
    have h2 : |c ^ 2 * (2 * s - a - r)| ≤ 2 * c ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg c)]
      have h2sar : |2 * s - a - r| ≤ 2 :=
        abs_le.mpr ⟨by linarith [hs.1, ha.2, hr.2], by linarith [hs.2, ha.1, hr.1]⟩
      nlinarith [sq_nonneg c]
    calc |2 * c * (r - s) - δ + c ^ 2 * (2 * s - a - r)|
        ≤ |2 * c * (r - s) - δ| + |c ^ 2 * (2 * s - a - r)| := abs_add_le _ _
      _ ≤ (2 * c + δ) + 2 * c ^ 2 := add_le_add h1 h2
      _ ≤ 4 * c + δ := by nlinarith
  rw [abs_of_pos hdenpos, div_le_iff₀ hdenpos]
  calc |2 * c * (r - s) - δ + c ^ 2 * (2 * s - a - r)| ≤ 4 * c + δ := hnum
    _ ≤ (16 * c + 4 * δ) * (1 - c) ^ 2 := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 16 * c + 4 * δ)
          (by linarith : (0:ℝ) ≤ (1 - c) ^ 2 - 1/4)]

/-- First-order bound: `|qSolve - r - (2c(r-s) - δ)| ≤ 28 (c² + δ²)` on the box. -/
theorem qSolve_linear_bound {a s r δ c : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hs : s ∈ Set.Icc (0:ℝ) 1) (hr : r ∈ Set.Icc (0:ℝ) 1)
    (hc0 : 0 ≤ c) (hc2 : c ≤ 1/2) (hδ0 : 0 ≤ δ) :
    |qSolve a s r δ c - r - (2 * c * (r - s) - δ)| ≤ 28 * (c ^ 2 + δ ^ 2) := by
  have hc1 : c ≠ 1 := by intro h; rw [h] at hc2; norm_num at hc2
  have h1c : (1 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  have hident : qSolve a s r δ c - r - (2 * c * (r - s) - δ)
      = (c ^ 2 * (2 * s - a - r) + (2 * c * (r - s) - δ) * (2 * c - c ^ 2))
        / (1 - c) ^ 2 := by
    unfold qSolve
    field_simp
    ring
  rw [hident, abs_div]
  have hden : (1/4 : ℝ) ≤ (1 - c) ^ 2 := by nlinarith
  have hdenpos : (0:ℝ) < (1 - c) ^ 2 := by nlinarith
  have hnum : |c ^ 2 * (2 * s - a - r) + (2 * c * (r - s) - δ) * (2 * c - c ^ 2)|
      ≤ 7 * (c ^ 2 + δ ^ 2) := by
    have hrs : |r - s| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hr.1, hs.2], by linarith [hr.2, hs.1]⟩
    have h1 : |c ^ 2 * (2 * s - a - r)| ≤ 2 * c ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg c)]
      have h2sar : |2 * s - a - r| ≤ 2 :=
        abs_le.mpr ⟨by linarith [hs.1, ha.2, hr.2], by linarith [hs.2, ha.1, hr.1]⟩
      nlinarith [sq_nonneg c]
    have h2 : |(2 * c * (r - s) - δ) * (2 * c - c ^ 2)| ≤ (2 * c + δ) * (2 * c) := by
      rw [abs_mul]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) (by linarith)
      · calc |2 * c * (r - s) - δ| ≤ |2 * c * (r - s)| + |δ| := abs_sub _ _
          _ = 2 * c * |r - s| + δ := by
              rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * c), abs_of_nonneg hδ0]
          _ ≤ 2 * c + δ := by nlinarith
      · rw [abs_of_nonneg (by nlinarith : (0:ℝ) ≤ 2 * c - c ^ 2)]
        nlinarith
    calc |c ^ 2 * (2 * s - a - r) + (2 * c * (r - s) - δ) * (2 * c - c ^ 2)|
        ≤ |c ^ 2 * (2 * s - a - r)| + |(2 * c * (r - s) - δ) * (2 * c - c ^ 2)| :=
          abs_add_le _ _
      _ ≤ 2 * c ^ 2 + (2 * c + δ) * (2 * c) := add_le_add h1 h2
      _ ≤ 7 * (c ^ 2 + δ ^ 2) := by nlinarith [two_mul_le_add_sq c δ]
  rw [abs_of_pos hdenpos, div_le_iff₀ hdenpos]
  calc |c ^ 2 * (2 * s - a - r) + (2 * c * (r - s) - δ) * (2 * c - c ^ 2)|
      ≤ 7 * (c ^ 2 + δ ^ 2) := hnum
    _ ≤ 28 * (c ^ 2 + δ ^ 2) * (1 - c) ^ 2 := by
        nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ c ^ 2 + δ ^ 2)
          (by linarith : (0:ℝ) ≤ (1 - c) ^ 2 - 1/4)]

/-- Squares of quantities bounded by `16c + 4δ` are `O(c² + δ²)` (with constant `512`). -/
theorem abs_le_sq_bound {x c δ : ℝ} (_hc : 0 ≤ c) (_hδ : 0 ≤ δ) (h : |x| ≤ 16 * c + 4 * δ) :
    x ^ 2 ≤ 512 * (c ^ 2 + δ ^ 2) := by
  have hsq := mul_self_le_mul_self (abs_nonneg x) h
  have habs2 : |x| * |x| = x ^ 2 := by
    rw [← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]
  nlinarith [two_mul_le_add_sq c δ]

/-- `c`-multiples of quantities bounded by `16c + 4δ` are `O(c² + δ²)` (constant `18`). -/
theorem abs_le_mul_bound {x c δ : ℝ} (hc : 0 ≤ c) (_hδ : 0 ≤ δ) (h : |x| ≤ 16 * c + 4 * δ) :
    c * |x| ≤ 18 * (c ^ 2 + δ ^ 2) := by
  have h1 := mul_le_mul_of_nonneg_left h hc
  nlinarith [two_mul_le_add_sq c δ]

/-! ### The relative-entropy formula for the two-block graphon -/

/-- **`I_p` of the two-block bipodal graphon**:
`I_p(V) = c² J_p(a) + 2c(1-c) J_p(s) + (1-c)² J_p(q)` for the block `A = [0,c]`. -/
theorem Ip_bipodalGraphon_Icc {p a s q c : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1) (hq : q ∈ Set.Icc (0:ℝ) 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (bipodalGraphon (Set.Icc 0 c) measurableSet_Icc a s q ha hs hq).Ip p
      = c ^ 2 * Jp p a + 2 * c * (1 - c) * Jp p s + (1 - c) ^ 2 * Jp p q := by
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  rw [Graphon.Ip_eq_entropy _ hp0 hp1, bipodalGraphon_entropy, bipodalGraphon_edgeDensity,
    unitμ_Icc_toReal hc0 hc1, Real.log_div h1p (ne_of_gt hp0),
    Jp_eq_entIntegrand hp0 hp1 ha.1 ha.2, Jp_eq_entIntegrand hp0 hp1 hs.1 hs.2,
    Jp_eq_entIntegrand hp0 hp1 hq.1 hq.2]
  simp only [entIntegrand_eq_neg_shannonH]
  ring

/-- `qSolve` is continuous on `[0, 1/2]`-type boxes (away from `c = 1`). -/
theorem continuousOn_qSolve (a s r δ : ℝ) {S : Set ℝ} (hS : ∀ x ∈ S, x ≤ 1/2) :
    ContinuousOn (fun c => qSolve a s r δ c) S := by
  simp only [qSolve]
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    exact pow_ne_zero 2 (by linarith [hS x hx])

/-! ### The linearisation of the `H`-density polynomial -/

/-- **Linearisation of `tBip` at `(c, q) = (0, r)`** with explicit error constants:
the error is at most `m² (q-r)² + 2nm c |q-r| + (2n² + 2^n) c²`. -/
theorem tBip_linearization {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d)
    {a s q r c : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (hq : q ∈ Set.Icc (0:ℝ) 1) (hr : r ∈ Set.Icc (0:ℝ) 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    |tBip H a s q c - r ^ H.edgeFinset.card
      - ((H.edgeFinset.card : ℝ) * r ^ (H.edgeFinset.card - 1) * (q - r)
        + (Fintype.card V : ℝ) * c
          * (s ^ d * r ^ (H.edgeFinset.card - d) - r ^ H.edgeFinset.card))|
      ≤ (H.edgeFinset.card : ℝ) ^ 2 * (q - r) ^ 2
        + 2 * (Fintype.card V : ℝ) * (H.edgeFinset.card : ℝ) * c * |q - r|
        + (2 * (Fintype.card V : ℝ) ^ 2 + 2 ^ (Fintype.card V)) * c ^ 2 := by
  set n := Fintype.card V with hn
  set m := H.edgeFinset.card with hm
  have h1c : (1 - c) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have h1mem : (1 : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  -- the five error terms
  have hPb : |q ^ m - r ^ m - (m : ℝ) * r ^ (m - 1) * (q - r)| ≤ (m : ℝ) ^ 2 * (q - r) ^ 2 :=
    pow_taylor_abs_le hq hr m
  have hQb : |q ^ m - r ^ m| ≤ (m : ℝ) * |q - r| := abs_pow_sub_pow_le hq hr m
  have hAb : |(1 - c) ^ n - (1 - (n : ℝ) * c)| ≤ (n : ℝ) ^ 2 * c ^ 2 := by
    have h := pow_taylor_abs_le h1c h1mem n
    rw [one_pow, one_pow] at h
    have he1 : (1 - c) ^ n - 1 - (n : ℝ) * 1 * ((1 - c) - 1)
        = (1 - c) ^ n - (1 - (n : ℝ) * c) := by ring
    have he2 : ((1 : ℝ) - c - 1) ^ 2 = c ^ 2 := by ring
    rwa [he1, he2] at h
  have hBb : |(1 - c) ^ (n - 1) - 1| ≤ (n : ℝ) * c := by
    have h := abs_pow_sub_pow_le h1c h1mem (n - 1)
    rw [one_pow] at h
    have he : |(1 : ℝ) - c - 1| = c := by
      rw [show (1 : ℝ) - c - 1 = -c by ring, abs_neg, abs_of_nonneg hc0]
    rw [he] at h
    refine le_trans h ?_
    have : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.sub_le n 1
    exact mul_le_mul_of_nonneg_right this hc0
  have hSb : |q ^ (m - d) - r ^ (m - d)| ≤ (m : ℝ) * |q - r| := by
    refine le_trans (abs_pow_sub_pow_le hq hr (m - d)) ?_
    have : ((m - d : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.sub_le m d
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hRb0 : 0 ≤ tBipRem H a s q c := tBipRem_nonneg H ha hs hq hc0 hc1
  have hRb1 : tBipRem H a s q c ≤ 2 ^ n * c ^ 2 := tBipRem_le H ha hs hq hc0 hc1
  have hqm : |q ^ m| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hq.1 m)]
    exact pow_le_one₀ hq.1 hq.2
  have hsqm : |s ^ d * q ^ (m - d)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hs.1 d), abs_of_nonneg (pow_nonneg hq.1 (m - d))]
    calc s ^ d * q ^ (m - d) ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ hs.1 hs.2) (pow_le_one₀ hq.1 hq.2)
            (pow_nonneg hq.1 _) zero_le_one
      _ = 1 := one_mul 1
  have hsd : |s ^ d| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hs.1 d)]
    exact pow_le_one₀ hs.1 hs.2
  -- the exact decomposition of the linearisation error
  rw [tBip_expansion H hreg]
  have hident : (1 - c) ^ n * q ^ m
      + (n : ℝ) * c * (1 - c) ^ (n - 1) * (s ^ d * q ^ (m - d)) + tBipRem H a s q c
      - r ^ m - ((m : ℝ) * r ^ (m - 1) * (q - r)
        + (n : ℝ) * c * (s ^ d * r ^ (m - d) - r ^ m))
      = (q ^ m - r ^ m - (m : ℝ) * r ^ (m - 1) * (q - r))
        + (-(n : ℝ) * c) * (q ^ m - r ^ m)
        + ((1 - c) ^ n - (1 - (n : ℝ) * c)) * q ^ m
        + ((n : ℝ) * c * ((1 - c) ^ (n - 1) - 1)) * (s ^ d * q ^ (m - d))
        + ((n : ℝ) * c * s ^ d) * (q ^ (m - d) - r ^ (m - d))
        + tBipRem H a s q c := by
    ring
  rw [hident]
  -- triangle inequality over the six terms
  have habs : |(q ^ m - r ^ m - (m : ℝ) * r ^ (m - 1) * (q - r))
        + (-(n : ℝ) * c) * (q ^ m - r ^ m)
        + ((1 - c) ^ n - (1 - (n : ℝ) * c)) * q ^ m
        + ((n : ℝ) * c * ((1 - c) ^ (n - 1) - 1)) * (s ^ d * q ^ (m - d))
        + ((n : ℝ) * c * s ^ d) * (q ^ (m - d) - r ^ (m - d))
        + tBipRem H a s q c|
      ≤ |q ^ m - r ^ m - (m : ℝ) * r ^ (m - 1) * (q - r)|
        + |(-(n : ℝ) * c) * (q ^ m - r ^ m)|
        + |((1 - c) ^ n - (1 - (n : ℝ) * c)) * q ^ m|
        + |((n : ℝ) * c * ((1 - c) ^ (n - 1) - 1)) * (s ^ d * q ^ (m - d))|
        + |((n : ℝ) * c * s ^ d) * (q ^ (m - d) - r ^ (m - d))|
        + |tBipRem H a s q c| := by
    calc _ ≤ |(q ^ m - r ^ m - (m : ℝ) * r ^ (m - 1) * (q - r))
        + (-(n : ℝ) * c) * (q ^ m - r ^ m)
        + ((1 - c) ^ n - (1 - (n : ℝ) * c)) * q ^ m
        + ((n : ℝ) * c * ((1 - c) ^ (n - 1) - 1)) * (s ^ d * q ^ (m - d))
        + ((n : ℝ) * c * s ^ d) * (q ^ (m - d) - r ^ (m - d))|
        + |tBipRem H a s q c| := abs_add_le _ _
      _ ≤ (|(q ^ m - r ^ m - (m : ℝ) * r ^ (m - 1) * (q - r))
        + (-(n : ℝ) * c) * (q ^ m - r ^ m)
        + ((1 - c) ^ n - (1 - (n : ℝ) * c)) * q ^ m
        + ((n : ℝ) * c * ((1 - c) ^ (n - 1) - 1)) * (s ^ d * q ^ (m - d))|
        + |((n : ℝ) * c * s ^ d) * (q ^ (m - d) - r ^ (m - d))|)
        + |tBipRem H a s q c| := by
          gcongr
          exact abs_add_le _ _
      _ ≤ ((|(q ^ m - r ^ m - (m : ℝ) * r ^ (m - 1) * (q - r))
        + (-(n : ℝ) * c) * (q ^ m - r ^ m)
        + ((1 - c) ^ n - (1 - (n : ℝ) * c)) * q ^ m|
        + |((n : ℝ) * c * ((1 - c) ^ (n - 1) - 1)) * (s ^ d * q ^ (m - d))|)
        + |((n : ℝ) * c * s ^ d) * (q ^ (m - d) - r ^ (m - d))|)
        + |tBipRem H a s q c| := by
          gcongr
          exact abs_add_le _ _
      _ ≤ (((|(q ^ m - r ^ m - (m : ℝ) * r ^ (m - 1) * (q - r))
        + (-(n : ℝ) * c) * (q ^ m - r ^ m)|
        + |((1 - c) ^ n - (1 - (n : ℝ) * c)) * q ^ m|)
        + |((n : ℝ) * c * ((1 - c) ^ (n - 1) - 1)) * (s ^ d * q ^ (m - d))|)
        + |((n : ℝ) * c * s ^ d) * (q ^ (m - d) - r ^ (m - d))|)
        + |tBipRem H a s q c| := by
          gcongr
          exact abs_add_le _ _
      _ ≤ _ := by
          have := abs_add_le (q ^ m - r ^ m - (m : ℝ) * r ^ (m - 1) * (q - r))
            ((-(n : ℝ) * c) * (q ^ m - r ^ m))
          gcongr
  refine le_trans habs ?_
  -- bound each of the six terms
  have hb2 : |(-(n : ℝ) * c) * (q ^ m - r ^ m)| ≤ (n : ℝ) * c * ((m : ℝ) * |q - r|) := by
    rw [abs_mul]
    refine mul_le_mul ?_ hQb (abs_nonneg _) (by positivity)
    rw [abs_mul, abs_neg, abs_of_nonneg (by exact_mod_cast Nat.zero_le n : (0:ℝ) ≤ (n:ℝ)),
      abs_of_nonneg hc0]
  have hb3 : |((1 - c) ^ n - (1 - (n : ℝ) * c)) * q ^ m| ≤ (n : ℝ) ^ 2 * c ^ 2 := by
    rw [abs_mul]
    calc |(1 - c) ^ n - (1 - (n : ℝ) * c)| * |q ^ m|
        ≤ ((n : ℝ) ^ 2 * c ^ 2) * 1 := mul_le_mul hAb hqm (abs_nonneg _) (by positivity)
      _ = (n : ℝ) ^ 2 * c ^ 2 := mul_one _
  have hb4 : |((n : ℝ) * c * ((1 - c) ^ (n - 1) - 1)) * (s ^ d * q ^ (m - d))|
      ≤ (n : ℝ) ^ 2 * c ^ 2 := by
    rw [abs_mul, abs_mul]
    have hnc : |(n : ℝ) * c| = (n : ℝ) * c := by
      rw [abs_mul, abs_of_nonneg (by exact_mod_cast Nat.zero_le n : (0:ℝ) ≤ (n:ℝ)),
        abs_of_nonneg hc0]
    rw [hnc]
    calc (n : ℝ) * c * |(1 - c) ^ (n - 1) - 1| * |s ^ d * q ^ (m - d)|
        ≤ ((n : ℝ) * c * ((n : ℝ) * c)) * 1 := by
          refine mul_le_mul ?_ hsqm (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hBb (by positivity)
      _ = (n : ℝ) ^ 2 * c ^ 2 := by ring
  have hb5 : |((n : ℝ) * c * s ^ d) * (q ^ (m - d) - r ^ (m - d))|
      ≤ (n : ℝ) * c * ((m : ℝ) * |q - r|) := by
    rw [abs_mul]
    refine mul_le_mul ?_ hSb (abs_nonneg _) (by positivity)
    rw [abs_mul]
    calc |(n : ℝ) * c| * |s ^ d| ≤ |(n : ℝ) * c| * 1 :=
          mul_le_mul_of_nonneg_left hsd (abs_nonneg _)
      _ = (n : ℝ) * c := by
          rw [mul_one, abs_mul,
            abs_of_nonneg (by exact_mod_cast Nat.zero_le n : (0:ℝ) ≤ (n:ℝ)),
            abs_of_nonneg hc0]
  have hb6 : |tBipRem H a s q c| ≤ 2 ^ n * c ^ 2 := by
    rw [abs_of_nonneg hRb0]
    exact hRb1
  calc |q ^ m - r ^ m - (m : ℝ) * r ^ (m - 1) * (q - r)|
        + |(-(n : ℝ) * c) * (q ^ m - r ^ m)|
        + |((1 - c) ^ n - (1 - (n : ℝ) * c)) * q ^ m|
        + |((n : ℝ) * c * ((1 - c) ^ (n - 1) - 1)) * (s ^ d * q ^ (m - d))|
        + |((n : ℝ) * c * s ^ d) * (q ^ (m - d) - r ^ (m - d))|
        + |tBipRem H a s q c|
      ≤ (m : ℝ) ^ 2 * (q - r) ^ 2 + (n : ℝ) * c * ((m : ℝ) * |q - r|)
        + (n : ℝ) ^ 2 * c ^ 2 + (n : ℝ) ^ 2 * c ^ 2
        + (n : ℝ) * c * ((m : ℝ) * |q - r|) + 2 ^ n * c ^ 2 := by
        gcongr
    _ = (m : ℝ) ^ 2 * (q - r) ^ 2 + 2 * (n : ℝ) * (m : ℝ) * c * |q - r|
        + (2 * (n : ℝ) ^ 2 + 2 ^ n) * c ^ 2 := by ring

end UpperTailOptimizers
