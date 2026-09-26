import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.Reduced

/-!
# The quadratic cofactor of the moment remainder

The merge step works with the second-order Taylor remainder
`Dfun d ε z = z^d - ε^d - d ε^{d-1}(z-ε)` of
`Preliminaries/KRRSAnalyticExtension/Reduced.lean` after the substitution `z = ε + u`.  The
binomial theorem makes the two lowest-order terms cancel, so the remainder carries an explicit
factor `u^2`; this file isolates the resulting cofactor and records the data the merge needs
about it.

## Contents

* `polyP` — the cofactor `∑_{j < d-1} C(d,j+2) ε^{d-2-j} u^j`, together with `Dfun_shift`:
  `Dfun d ε (ε+u) = u^2 * polyP d ε u`.
* `polyP1` — the `u`-derivative of `polyP` (`hasDerivAt_polyP`).  Both are polynomials, hence
  jointly analytic in `(ε,u)`: `analyticAt_polyP`, `analyticAt_polyP1`.
* `polyP_zero`, `polyP1_zero`, `deriv_polyP1_zero` — the three values at `u = 0`, namely
  `C(d,2) ε^{d-2}`, `C(d,3) ε^{d-3}` and `2 C(d,4) ε^{d-4}`.

The natural-number subtractions follow the convention of `Reduced.lean`: for `d = 2, 3` the
binomial coefficients `C(d,3)`, `C(d,4)` vanish, so the truncated exponents `ε^{d-3}`,
`ε^{d-4}` occurring in the last two statements multiply zero and are harmless.
-/

namespace UpperTailOptimizers

/-- The quadratic cofactor of the moment remainder: `Dfun d ε (ε+u) = u² · polyP d ε u`. -/
noncomputable def polyP (d : ℕ) (ε u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d - 1), (Nat.choose d (j + 2) : ℝ) * ε ^ (d - 2 - j) * u ^ j

/-- The binomial expansion of `(ε+u)^d` with its constant and linear terms split off. -/
private theorem add_pow_split {d : ℕ} (hd : 2 ≤ d) (ε u : ℝ) :
    (ε + u) ^ d = ε ^ d + (d : ℝ) * ε ^ (d - 1) * u
      + ∑ j ∈ Finset.range (d - 1),
          (Nat.choose d (j + 2) : ℝ) * ε ^ (d - 2 - j) * u ^ (j + 2) := by
  have hrange : d + 1 = d - 1 + 1 + 1 := by omega
  rw [add_comm ε u, add_pow, hrange, Finset.sum_range_succ', Finset.sum_range_succ']
  have hterm : ∀ j ∈ Finset.range (d - 1),
      u ^ (j + 1 + 1) * ε ^ (d - (j + 1 + 1)) * (Nat.choose d (j + 1 + 1) : ℝ)
        = (Nat.choose d (j + 2) : ℝ) * ε ^ (d - 2 - j) * u ^ (j + 2) := by
    intro j _
    have h1 : j + 1 + 1 = j + 2 := rfl
    have h2 : d - (j + 2) = d - 2 - j := by omega
    rw [h1, h2]
    ring
  rw [Finset.sum_congr rfl hterm]
  simp [Nat.choose_one_right]
  ring

/-- The shift identity. -/
theorem Dfun_shift {d : ℕ} (hd : 2 ≤ d) (ε u : ℝ) :
    Dfun d ε (ε + u) = u ^ 2 * polyP d ε u := by
  have hsum : u ^ 2 * polyP d ε u
      = ∑ j ∈ Finset.range (d - 1),
          (Nat.choose d (j + 2) : ℝ) * ε ^ (d - 2 - j) * u ^ (j + 2) := by
    unfold polyP
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, Dfun, add_pow_split hd ε u]
  ring

/-- `polyP` is jointly analytic (it is a polynomial). -/
theorem analyticAt_polyP (d : ℕ) (q : ℝ × ℝ) :
    AnalyticAt ℝ (fun w : ℝ × ℝ => polyP d w.1 w.2) q := by
  unfold polyP
  refine Finset.analyticAt_fun_sum _ fun j _ => ?_
  exact (analyticAt_const.mul (analyticAt_fst.pow _)).mul (analyticAt_snd.pow _)

/-- The `u`-derivative of `polyP`, again a polynomial. -/
noncomputable def polyP1 (d : ℕ) (ε u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d - 1), (j : ℝ) * (Nat.choose d (j + 2) : ℝ) * ε ^ (d - 2 - j) * u ^ (j - 1)

/-- `polyP1` is the `u`-derivative of `polyP`. -/
theorem hasDerivAt_polyP {d : ℕ} (ε u : ℝ) :
    HasDerivAt (fun y : ℝ => polyP d ε y) (polyP1 d ε u) u := by
  unfold polyP polyP1
  refine HasDerivAt.fun_sum fun j _ => ?_
  exact ((hasDerivAt_pow j u).const_mul
    ((Nat.choose d (j + 2) : ℝ) * ε ^ (d - 2 - j))).congr_deriv (by ring)

/-- `polyP1` is jointly analytic (it is a polynomial). -/
theorem analyticAt_polyP1 (d : ℕ) (q : ℝ × ℝ) :
    AnalyticAt ℝ (fun w : ℝ × ℝ => polyP1 d w.1 w.2) q := by
  unfold polyP1
  refine Finset.analyticAt_fun_sum _ fun j _ => ?_
  exact (analyticAt_const.mul (analyticAt_fst.pow _)).mul (analyticAt_snd.pow _)

/-- Values at `u = 0`, in terms of binomial coefficients. -/
theorem polyP_zero {d : ℕ} (hd : 2 ≤ d) (ε : ℝ) :
    polyP d ε 0 = (Nat.choose d 2 : ℝ) * ε ^ (d - 2) := by
  unfold polyP
  have hr : d - 1 = d - 2 + 1 := by omega
  rw [hr, Finset.sum_range_succ']
  simp

/-- The value of `polyP1` at `u = 0`; only the term `j = 1` survives. -/
theorem polyP1_zero {d : ℕ} (hd : 2 ≤ d) (ε : ℝ) :
    polyP1 d ε 0 = (Nat.choose d 3 : ℝ) * ε ^ (d - 3) := by
  unfold polyP1
  rw [Finset.sum_eq_single 1]
  · have h2 : d - 2 - 1 = d - 3 := by omega
    rw [h2]
    norm_num
  · intro j _ hne
    rcases Nat.eq_zero_or_pos j with hz | hpos
    · simp [hz]
    · have hne0 : j - 1 ≠ 0 := by omega
      simp [zero_pow hne0]
  · intro hmem
    have hd2 : d = 2 := by
      simp only [Finset.mem_range, not_lt] at hmem
      omega
    subst hd2
    norm_num

/-- The second `u`-derivative of `polyP` in the form needed at `u = 0`. -/
private theorem hasDerivAt_polyP1 (d : ℕ) (ε u : ℝ) :
    HasDerivAt (fun y : ℝ => polyP1 d ε y)
      (∑ j ∈ Finset.range (d - 1), (j : ℝ) * (Nat.choose d (j + 2) : ℝ) * ε ^ (d - 2 - j) *
        (((j - 1 : ℕ) : ℝ) * u ^ (j - 1 - 1))) u := by
  unfold polyP1
  refine HasDerivAt.fun_sum fun j _ => ?_
  exact (hasDerivAt_pow (j - 1) u).const_mul
    ((j : ℝ) * (Nat.choose d (j + 2) : ℝ) * ε ^ (d - 2 - j))

/-- The second `u`-derivative of `polyP` at `0`. -/
theorem deriv_polyP1_zero {d : ℕ} (hd : 2 ≤ d) (ε : ℝ) :
    deriv (fun y : ℝ => polyP1 d ε y) 0 = 2 * (Nat.choose d 4 : ℝ) * ε ^ (d - 4) := by
  rw [(hasDerivAt_polyP1 d ε 0).deriv, Finset.sum_eq_single 2]
  · have h2 : d - 2 - 2 = d - 4 := by omega
    rw [h2]
    norm_num
  · intro j _ hne
    match j, hne with
    | 0, _ => simp
    | 1, _ => simp
    | (n + 3), _ => simp
  · intro hmem
    have hd4 : d < 4 := by
      simp only [Finset.mem_range, not_lt] at hmem
      omega
    rw [Nat.choose_eq_zero_of_lt hd4]
    norm_num

end UpperTailOptimizers
