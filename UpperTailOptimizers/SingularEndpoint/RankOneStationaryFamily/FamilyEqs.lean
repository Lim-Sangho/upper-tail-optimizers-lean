import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.LogSlope
import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.PowBounds

/-!
# Exact division by `h` in the family equations (Section 5, `paper/sections/singular.tex`)

The three rank-one KKT equations `eq:three-value-kkt` of
`lem:rank-one-kkt-family` read, with `s = u - h` and `t = u + h`,

  `𝓛(s²) = 0`,  `𝓛(s t) = 0`,  `𝓛(t²) = 0`,   where `𝓛(z) = ℓ_h - ℓ(z) - γ_h z^{d-1}`.

At `h = 0` the three roots `s², s t, t²` merge, so the system degenerates.  The paper's proof
eliminates `ℓ_h`, equates the two divided slopes across `s², s t, t²` and writes their
difference as `A(u,h) = hB(u,h)`.  The formalisation instead replaces the system by the
equivalent system

  `G₁ := 𝓛(s t)`,  `G₂ := 𝓛(t²) - 𝓛(s²)`,  `G₃ := 𝓛(t²) + 𝓛(s²) - 2𝓛(s t)`,

whose last two members vanish identically at `h = 0`, and divides `G₂` by `h` and `G₃`
by `h²`.  **This file performs both divisions exactly**, with no analytic-division machinery
at all: each of `G₂`, `G₃` splits into a logarithmic half and a polynomial half, and each
half factors in closed form.

* the logarithmic halves factor through two elementary identities for `ℓ(z) = log((1-z)/z)`,
  `ell_sub_ell_eq` and `ell_add_ell_sub_two_eq`, whose right-hand sides are `log(1 - X)` with
  `X` an explicit multiple of `h` resp. `h²`; rewriting with `log_one_sub_eq` of
  `SingularEndpoint/RankOneStationaryFamily/LogSlope.lean` then pulls out the factor `h` resp. `h²` syntactically
  (`ell_sub_ell_factored`, `ell_add_ell_sub_two_factored`);
* the polynomial halves factor through the geometric-sum identity `pow_sub_pow_eq`
  (`pow_sub_pow_factored`, `pow_add_pow_sub_two_factored`).

Everything here is an identity between real numbers under mild positivity hypotheses; no
limit, derivative or power series occurs.

## Contents

* `Lell`, `Lell_eq_Fkkt` — the scalar KKT function of `eq:three-value-kkt` in
  log-odds coordinates, and its agreement with `Fkkt` of
  `eq:rank-one-kkt`;
* `ell_sub_ell_eq`, `ell_add_ell_sub_two_eq` — the two closed-form logarithm identities;
* `ell_sub_ell_factored`, `ell_add_ell_sub_two_factored` — the same identities with the
  factor `h` resp. `h²` extracted, through `logSlope`;
* `pow_sub_pow_factored`, `pow_add_pow_sub_two_factored` — the corresponding exact
  factorisations of the polynomial halves `z ↦ z^{d-1}`.
-/

namespace UpperTailOptimizers

open Real

variable {d : ℕ} {p s t u h z : ℝ}

/-! ## The KKT function in log-odds coordinates -/

/-- The scalar KKT function of `eq:three-value-kkt` written in **log-odds
coordinates**: `𝓛(z) = ℓ_h - ℓ(z) - γ_h z^{d-1}`, with the value `ℓ_h = ℓ(p_h)` carried as
the free parameter `lv` and the multiplier `γ_h` as `g`.

Unlike `Fkkt` this is defined for every real `z` without reference to `p`, which is what
makes the exact divisions below purely algebraic. -/
noncomputable def Lell (d : ℕ) (lv g z : ℝ) : ℝ := lv - ell z - g * z ^ (d - 1)

/-- `Lell` is the rank-one scalar KKT function `Fkkt` of
`eq:rank-one-kkt`, once the free value `lv` is taken to be `ℓ(p)`.  This is
the passage from `eq:rank-one-kkt` to `eq:three-value-kkt` in the
proof of `lem:rank-one-kkt-family`. -/
theorem Lell_eq_Fkkt (hp0 : 0 < p) (hp1 : p < 1) (hz0 : 0 < z) (hz1 : z < 1) (g : ℝ) :
    Lell d (ell p) g z = Fkkt d p g z := by
  rw [Lell, Fkkt, Jp'_eq_ell_sub hp0 hp1 hz0 hz1]

/-! ## The two closed-form logarithm identities

Both are elementary consequences of `ℓ(z) = log(1-z) - log z`.  They are stated for a pair
`0 < s < 1`, `0 < t < 1` together with the singular endpoint coordinates `u`, `h` of
`lem:rank-one-kkt-family`, recorded as the hypotheses `s + t = 2u` and
`t - s = 2h` (so `s = u - h` and `t = u + h`). -/

/-- **Identity (A)**, the exact form of the divided difference `𝓛(t²) - 𝓛(s²)` of
`eq:three-value-kkt` on its logarithmic half:

  `ℓ(t²) - ℓ(s²) = log(1 - 4uh/(1-s²)) + 2 log(1 - 2h/t)`.

The first summand comes from `(1-t²)/(1-s²) = 1 - 4uh/(1-s²)`, which holds because
`t² - s² = 4uh`; the second from `s/t = 1 - 2h/t`.  Both arguments are visibly `1 - O(h)`,
which is what makes the division by `h` of `ell_sub_ell_factored` exact. -/
theorem ell_sub_ell_eq (hs : 0 < s) (ht : 0 < t) (hs1 : s ^ 2 < 1) (ht1 : t ^ 2 < 1)
    (hu : s + t = 2 * u) (hh : t - s = 2 * h) :
    ell (t ^ 2) - ell (s ^ 2)
      = Real.log (1 - 4 * u * h / (1 - s ^ 2)) + 2 * Real.log (1 - 2 * h / t) := by
  have hs2 : (0 : ℝ) < 1 - s ^ 2 := by linarith
  have ht2 : (0 : ℝ) < 1 - t ^ 2 := by linarith
  have hsq : (0 : ℝ) < s ^ 2 := by positivity
  have htq : (0 : ℝ) < t ^ 2 := by positivity
  have hA : (1 : ℝ) - 4 * u * h / (1 - s ^ 2) = (1 - t ^ 2) / (1 - s ^ 2) := by
    field_simp
    linear_combination (t - s) * hu + 2 * u * hh
  have hB : (1 : ℝ) - 2 * h / t = s / t := by
    field_simp
    linarith
  have e1 : ell (t ^ 2) = Real.log (1 - t ^ 2) - 2 * Real.log t := by
    rw [ell, Real.log_div ht2.ne' htq.ne', Real.log_pow]
    push_cast
    ring
  have e2 : ell (s ^ 2) = Real.log (1 - s ^ 2) - 2 * Real.log s := by
    rw [ell, Real.log_div hs2.ne' hsq.ne', Real.log_pow]
    push_cast
    ring
  rw [hA, hB, Real.log_div ht2.ne' hs2.ne', Real.log_div hs.ne' ht.ne', e1, e2]
  ring

/-- **Identity (B)**, the exact form of the second divided difference
`𝓛(t²) + 𝓛(s²) - 2𝓛(st)` of `eq:three-value-kkt` on its logarithmic half:

  `ℓ(t²) + ℓ(s²) - 2 ℓ(st) = log(1 - 4h²/(1-st)²)`.

The `log z` parts cancel exactly (`log t² + log s² - 2 log(st) = 0`), and the surviving part
is governed by the polynomial identity `(1-s²)(1-t²) = (1-st)² - 4h²`.  The argument is
visibly `1 - O(h²)`, which is what makes the division by `h²` of
`ell_add_ell_sub_two_factored` exact. -/
theorem ell_add_ell_sub_two_eq (hs : 0 < s) (ht : 0 < t) (hs1 : s ^ 2 < 1) (ht1 : t ^ 2 < 1)
    (hst : s * t < 1) (hh : t - s = 2 * h) :
    ell (t ^ 2) + ell (s ^ 2) - 2 * ell (s * t)
      = Real.log (1 - 4 * h ^ 2 / (1 - s * t) ^ 2) := by
  have hs2 : (0 : ℝ) < 1 - s ^ 2 := by linarith
  have ht2 : (0 : ℝ) < 1 - t ^ 2 := by linarith
  have hst2 : (0 : ℝ) < 1 - s * t := by linarith
  have hsq : (0 : ℝ) < s ^ 2 := by positivity
  have htq : (0 : ℝ) < t ^ 2 := by positivity
  have hC : (1 : ℝ) - 4 * h ^ 2 / (1 - s * t) ^ 2
      = ((1 - s ^ 2) * (1 - t ^ 2)) / (1 - s * t) ^ 2 := by
    field_simp
    linear_combination (t - s + 2 * h) * hh
  have e1 : ell (t ^ 2) = Real.log (1 - t ^ 2) - 2 * Real.log t := by
    rw [ell, Real.log_div ht2.ne' htq.ne', Real.log_pow]
    push_cast
    ring
  have e2 : ell (s ^ 2) = Real.log (1 - s ^ 2) - 2 * Real.log s := by
    rw [ell, Real.log_div hs2.ne' hsq.ne', Real.log_pow]
    push_cast
    ring
  have e3 : ell (s * t) = Real.log (1 - s * t) - (Real.log s + Real.log t) := by
    rw [ell, Real.log_div hst2.ne' (mul_pos hs ht).ne', Real.log_mul hs.ne' ht.ne']
  rw [hC, Real.log_div (by positivity) (by positivity), Real.log_mul hs2.ne' ht2.ne',
    Real.log_pow, e1, e2, e3]
  push_cast
  ring

/-! ## The factored forms: the divisions by `h` and by `h²`

Rewriting each `log (1 - X)` above by `log_one_sub_eq`, `log(1 - X) = -X · logSlope X`,
makes the factor `h` resp. `h²` appear syntactically, so it can be cancelled by `ring`
alone.  Since `logSlope` is analytic at `0` (`analyticAt_logSlope`), the right-hand sides are
analytic through `h = 0`.  This plays the role of the analytic extension of the divided
slopes in the proof of `lem:rank-one-kkt-family` ("Although each slope appears as `0/0` at
`h = 0`, both extend analytically"); here the logarithmic and polynomial differences are
divided by `h` resp. `h²` separately, rather than by one another. -/

/-- **Identity (A′)**: the divided difference of `ell_sub_ell_eq` with its factor of `h`
extracted,

  `ℓ(t²) - ℓ(s²) = -h · ( (4u/(1-s²))·logSlope(4uh/(1-s²)) + (4/t)·logSlope(2h/t) )`.

The division of `G₂ = 𝓛(t²) - 𝓛(s²)` by `h` in the formal construction of the family of
`lem:rank-one-kkt-family`, on the logarithmic half. -/
theorem ell_sub_ell_factored (hs : 0 < s) (ht : 0 < t) (hs1 : s ^ 2 < 1) (ht1 : t ^ 2 < 1)
    (hu : s + t = 2 * u) (hh : t - s = 2 * h) :
    ell (t ^ 2) - ell (s ^ 2)
      = -h * ((4 * u / (1 - s ^ 2)) * logSlope (4 * u * h / (1 - s ^ 2))
              + (4 / t) * logSlope (2 * h / t)) := by
  rw [ell_sub_ell_eq hs ht hs1 ht1 hu hh, log_one_sub_eq, log_one_sub_eq]
  ring

/-- **Identity (B′)**: the second divided difference of `ell_add_ell_sub_two_eq` with its
factor of `h²` extracted,

  `ℓ(t²) + ℓ(s²) - 2 ℓ(st) = -h² · (4/(1-st)²)·logSlope(4h²/(1-st)²)`.

The division of `G₃ = 𝓛(t²) + 𝓛(s²) - 2𝓛(st)` by `h²` in the formal construction of the
family of `lem:rank-one-kkt-family`, on the logarithmic half. -/
theorem ell_add_ell_sub_two_factored (hs : 0 < s) (ht : 0 < t) (hs1 : s ^ 2 < 1)
    (ht1 : t ^ 2 < 1) (hst : s * t < 1) (hh : t - s = 2 * h) :
    ell (t ^ 2) + ell (s ^ 2) - 2 * ell (s * t)
      = -h ^ 2 * ((4 / (1 - s * t) ^ 2) * logSlope (4 * h ^ 2 / (1 - s * t) ^ 2)) := by
  rw [ell_add_ell_sub_two_eq hs ht hs1 ht1 hst hh, log_one_sub_eq]
  ring

/-! ## The polynomial halves

The same two divisions on the half `z ↦ γ z^{d-1}` of `eq:three-value-kkt`.  Here no
analysis at all is needed: the geometric-sum factorisation `pow_sub_pow_eq` produces the
factors `t² - s² = 4uh` and `t - s = 2h` explicitly. -/

/-- **Division of the polynomial half of `G₂` by `h`**:

  `(t²)^{d-1} - (s²)^{d-1} = 4uh · ∑_{i<d-1} (t²)^i (s²)^{d-2-i}`.

Immediate from `pow_sub_pow_eq` together with `t² - s² = (t-s)(t+s) = 4uh`. -/
theorem pow_sub_pow_factored (_hd : 2 ≤ d) (hu : s + t = 2 * u) (hh : t - s = 2 * h) :
    (t ^ 2) ^ (d - 1) - (s ^ 2) ^ (d - 1)
      = 4 * u * h * ∑ i ∈ Finset.range (d - 1), (t ^ 2) ^ i * (s ^ 2) ^ (d - 1 - 1 - i) := by
  have hts : t ^ 2 - s ^ 2 = 4 * u * h := by
    linear_combination (t - s) * hu + 2 * u * hh
  rw [pow_sub_pow_eq, hts]

/-- **Division of the polynomial half of `G₃` by `h²`**:

  `(t²)^{d-1} + (s²)^{d-1} - 2(st)^{d-1} = 4h² · (Σ₁ + s·Σ₃·Σ₄)`,

where `Σ₁ = ∑_{i<d-1} (t²)^i (st)^{d-2-i}`, `Σ₃ = ∑_{i<d-1} s^{d-2-i} t^i` and
`Σ₄ = ∑_{j<d-2} t^j s^{d-3-j}`.

Proved by three applications of `pow_sub_pow_eq`: the telescoping
`(t²)^{d-1} - (st)^{d-1} = t(t-s)Σ₁` and `(st)^{d-1} - (s²)^{d-1} = s(t-s)Σ₂`, the termwise
factorisation `Σ₁ - Σ₂ = (t^{d-2} - s^{d-2})Σ₃`, and `t^{d-2} - s^{d-2} = (t-s)Σ₄`.  At
`d = 2` the last sum is empty and the identity degenerates to `(t-s)² = 4h²`. -/
theorem pow_add_pow_sub_two_factored (_hd : 2 ≤ d) (hh : t - s = 2 * h) :
    (t ^ 2) ^ (d - 1) + (s ^ 2) ^ (d - 1) - 2 * (s * t) ^ (d - 1)
      = 4 * h ^ 2 *
          ((∑ i ∈ Finset.range (d - 1), (t ^ 2) ^ i * (s * t) ^ (d - 1 - 1 - i))
            + s * (∑ i ∈ Finset.range (d - 1), s ^ (d - 1 - 1 - i) * t ^ i)
                * ∑ j ∈ Finset.range (d - 2), t ^ j * s ^ (d - 2 - 1 - j)) := by
  have hd2 : d - 2 = d - 1 - 1 := by omega
  rw [hd2]
  generalize d - 1 = k
  have e1 : (t ^ 2) ^ k - (s * t) ^ k
      = (t ^ 2 - s * t) * ∑ i ∈ Finset.range k, (t ^ 2) ^ i * (s * t) ^ (k - 1 - i) :=
    pow_sub_pow_eq _ _ k
  have e2 : (s * t) ^ k - (s ^ 2) ^ k
      = (s * t - s ^ 2) * ∑ i ∈ Finset.range k, (s * t) ^ i * (s ^ 2) ^ (k - 1 - i) :=
    pow_sub_pow_eq _ _ k
  have e4 : t ^ (k - 1) - s ^ (k - 1)
      = (t - s) * ∑ j ∈ Finset.range (k - 1), t ^ j * s ^ (k - 1 - 1 - j) :=
    pow_sub_pow_eq _ _ (k - 1)
  have e3 : (∑ i ∈ Finset.range k, (t ^ 2) ^ i * (s * t) ^ (k - 1 - i))
        - ∑ i ∈ Finset.range k, (s * t) ^ i * (s ^ 2) ^ (k - 1 - i)
      = (t ^ (k - 1) - s ^ (k - 1)) * ∑ i ∈ Finset.range k, s ^ (k - 1 - i) * t ^ i := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i < k := Finset.mem_range.mp hi
    obtain ⟨m, hm⟩ : ∃ m, k - 1 = i + m := ⟨k - 1 - i, by omega⟩
    rw [hm, Nat.add_sub_cancel_left]
    ring
  linear_combination e1 - e2 + s * (t - s) * e3
    + s * (t - s) * (∑ i ∈ Finset.range k, s ^ (k - 1 - i) * t ^ i) * e4
    + (t - s + 2 * h)
        * ((∑ i ∈ Finset.range k, (t ^ 2) ^ i * (s * t) ^ (k - 1 - i))
            + s * (∑ i ∈ Finset.range k, s ^ (k - 1 - i) * t ^ i)
                * ∑ j ∈ Finset.range (k - 1), t ^ j * s ^ (k - 1 - 1 - j)) * hh

end UpperTailOptimizers
