import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilyEqs

/-!
# The desingularized family system (Section 5, `paper/sections/singular.tex`)

The three rank-one KKT equations `eq:three-value-kkt` of
`lem:rank-one-kkt-family` read, with `s = u - h` and `t = u + h`,

  `𝓛(s²) = 0`,  `𝓛(s t) = 0`,  `𝓛(t²) = 0`,   where `𝓛(z) = ℓ_h - ℓ(z) - γ_h z^{d-1}`
                                              (`Lell` of `SingularEndpoint/RankOneStationaryFamily/FamilyEqs.lean`).

At `h = 0` the three roots merge and the system degenerates.  The paper's proof of
`lem:rank-one-kkt-family` equates the two divided slopes and divides their difference by `h`,
`A(u,h) = hB(u,h)`; the formalisation instead replaces the system by

  `G₁ = 𝓛(s t)`,  `G₂ = 𝓛(t²) - 𝓛(s²)`,  `G₃ = 𝓛(t²) + 𝓛(s²) - 2𝓛(s t)`,

whose last two members vanish identically at `h = 0`, and then divides `G₂` by `h` and `G₃`
by `h²`.  (The paper's "analytic Weierstrass division" is a different step, the factorisation
of `𝓜_h'` in `app:rank-one-kkt-family`.)

**This file writes the quotients down.**  `Esys1`, `Esys2`, `Esys3` are `G₁`, `G₂/h`,
`G₃/h²` *as closed-form expressions*: every division has already been carried out exactly in
`SingularEndpoint/RankOneStationaryFamily/FamilyEqs.lean`, through `logSlope` on the logarithmic halves and through the
geometric-sum identity on the polynomial halves.  Nothing here is a limit or a quotient of
functions; the two factorisation theorems `Lell_sub_eq_mul` and `Lell_add_sub_two_eq_mul`
are algebraic identities valid for every `h`, and `lell_three_eq_iff` records that for
`h ≠ 0` the desingularized system `(E₁, E₂, E₃) = 0` has exactly the same solutions as
`eq:three-value-kkt`.

The values at `h = 0` (`Esys2_zero`, `Esys3_zero`) are the entries `4u·𝓛′(u²)` and
`4𝓛′(u²) + 4u²·𝓛″(u²)` of the base point of the implicit function theorem, written out with
`ℓ′(z) = -1/(z(1-z))` already expanded in the variable `u`.  The natural-number casts
`((d-1 : ℕ) : ℝ)`, `((d-2 : ℕ) : ℝ)` are deliberate: at `d = 2` the truncated subtractions
`d - 2` and `d - 3` are *not* `d - 2` and `d - 3` over `ℝ`, and the formulas below are the
ones that are true for every `d ≥ 2`.

## Contents

* `Esys1`, `Esys2`, `Esys3` — the three components of the desingularized system of
  `lem:rank-one-kkt-family`;
* `Lell_sub_eq_mul`, `Lell_add_sub_two_eq_mul` — the exact factorisations
  `G₂ = h·E₂` and `G₃ = h²·E₃`;
* `lell_three_eq_iff` — for `h ≠ 0` the desingularized system is equivalent to
  `eq:three-value-kkt`;
* `Esys2_zero`, `Esys3_zero` — the values of `E₂` and `E₃` at `h = 0`, with the
  hypothesis-free forms `Esys2_zero'`, `Esys3_zero'` that `SingularEndpoint/RankOneStationaryFamily/FamilyDeriv.lean` uses.
-/

namespace UpperTailOptimizers

open Real

variable {d : ℕ} {lv g u h : ℝ}

/-! ## The three components -/

/-- `E₁`, the first component of the desingularized system of
`lem:rank-one-kkt-family`: the middle equation of `eq:three-value-kkt`
itself, `𝓛(s_h t_h) = 0`, written with `s_h = u - h` and `t_h = u + h` substituted. -/
noncomputable def Esys1 (d : ℕ) (lv g u h : ℝ) : ℝ := Lell d lv g ((u - h) * (u + h))

/-- `E₂ = G₂/h`, the second component of the desingularized system of
`lem:rank-one-kkt-family`, in closed form:

  `E₂ = (4u/(1-s²))·logSlope(4uh/(1-s²)) + (4/t)·logSlope(2h/t)
        - 4γu·∑_{i<d-1} (t²)^i (s²)^{d-2-i}`,

with `s = u - h`, `t = u + h`.  The division of `G₂ = 𝓛(t²) - 𝓛(s²)` by `h` is already
performed here — see `Lell_sub_eq_mul`.  Note that `E₂` does not involve `ℓ_h`, which
cancels in the difference. -/
noncomputable def Esys2 (d : ℕ) (g u h : ℝ) : ℝ :=
  (4 * u / (1 - (u - h) ^ 2)) * logSlope (4 * u * h / (1 - (u - h) ^ 2))
    + (4 / (u + h)) * logSlope (2 * h / (u + h))
    - 4 * g * u * ∑ i ∈ Finset.range (d - 1), ((u + h) ^ 2) ^ i * ((u - h) ^ 2) ^ (d - 1 - 1 - i)

/-- `E₃ = G₃/h²`, the third component of the desingularized system of
`lem:rank-one-kkt-family`, in closed form:

  `E₃ = (4/(1-st)²)·logSlope(4h²/(1-st)²)
        - 4γ·(∑_{i<d-1} (t²)^i (st)^{d-2-i} + s·(∑_{i<d-1} s^{d-2-i} t^i)·(∑_{j<d-2} t^j s^{d-3-j}))`,

with `s = u - h`, `t = u + h`.  The division of `G₃ = 𝓛(t²) + 𝓛(s²) - 2𝓛(st)` by `h²` is
already performed here — see `Lell_add_sub_two_eq_mul`.  Like `E₂`, it does not involve
`ℓ_h`. -/
noncomputable def Esys3 (d : ℕ) (g u h : ℝ) : ℝ :=
  (4 / (1 - (u - h) * (u + h)) ^ 2) * logSlope (4 * h ^ 2 / (1 - (u - h) * (u + h)) ^ 2)
    - 4 * g *
        ((∑ i ∈ Finset.range (d - 1), ((u + h) ^ 2) ^ i * ((u - h) * (u + h)) ^ (d - 1 - 1 - i))
          + (u - h) * (∑ i ∈ Finset.range (d - 1), (u - h) ^ (d - 1 - 1 - i) * (u + h) ^ i)
              * ∑ j ∈ Finset.range (d - 2), (u + h) ^ j * (u - h) ^ (d - 2 - 1 - j))

/-! ## The two exact factorisations

Both are pure algebra on top of the four factorisations of `SingularEndpoint/RankOneStationaryFamily/FamilyEqs.lean`: the
logarithmic halves come from `ell_sub_ell_factored` and `ell_add_ell_sub_two_factored`, the
polynomial halves from `pow_sub_pow_factored` and `pow_add_pow_sub_two_factored`, and `ring`
does the rest.  They hold for *every* `h`, in particular at `h = 0` where both sides
vanish. -/

/-- **Division of `G₂` by `h`** in `lem:rank-one-kkt-family`:

  `𝓛(t²) - 𝓛(s²) = h · E₂`,   `s = u - h`, `t = u + h`.

The factor `h` is extracted syntactically, so no analytic division is involved. -/
theorem Lell_sub_eq_mul (hd : 2 ≤ d) (hs : 0 < u - h) (ht : 0 < u + h)
    (hs1 : (u - h) ^ 2 < 1) (ht1 : (u + h) ^ 2 < 1) (_hst : (u - h) * (u + h) < 1) :
    Lell d lv g ((u + h) ^ 2) - Lell d lv g ((u - h) ^ 2) = h * Esys2 d g u h := by
  have hA := ell_sub_ell_factored (s := u - h) (t := u + h) (u := u) (h := h)
    hs ht hs1 ht1 (by ring) (by ring)
  have hB := pow_sub_pow_factored (d := d) (s := u - h) (t := u + h) (u := u) (h := h)
    hd (by ring) (by ring)
  simp only [Lell, Esys2]
  linear_combination -hA - g * hB

/-- **Division of `G₃` by `h²`** in `lem:rank-one-kkt-family`:

  `𝓛(t²) + 𝓛(s²) - 2𝓛(st) = h² · E₃`,   `s = u - h`, `t = u + h`.

The factor `h²` is extracted syntactically, so no analytic division is involved. -/
theorem Lell_add_sub_two_eq_mul (hd : 2 ≤ d) (hs : 0 < u - h) (ht : 0 < u + h)
    (hs1 : (u - h) ^ 2 < 1) (ht1 : (u + h) ^ 2 < 1) (hst : (u - h) * (u + h) < 1) :
    Lell d lv g ((u + h) ^ 2) + Lell d lv g ((u - h) ^ 2)
        - 2 * Lell d lv g ((u - h) * (u + h))
      = h ^ 2 * Esys3 d g u h := by
  have hA := ell_add_ell_sub_two_factored (s := u - h) (t := u + h) (h := h)
    hs ht hs1 ht1 hst (by ring)
  have hB := pow_add_pow_sub_two_factored (d := d) (s := u - h) (t := u + h) (h := h)
    hd (by ring)
  simp only [Lell, Esys3]
  linear_combination -hA - g * hB

/-! ## Equivalence with the original system -/

/-- **The desingularization is faithful**: for `h ≠ 0` the system `(E₁, E₂, E₃) = 0` has
exactly the solutions of `eq:three-value-kkt`.

Forward, `h` and `h²` are cancelled from `Lell_sub_eq_mul` and `Lell_add_sub_two_eq_mul`.
Backward, `E₁ = 0` gives the middle root, and then the same two identities give
`𝓛(t²) - 𝓛(s²) = 0` and `𝓛(t²) + 𝓛(s²) = 0`, so both outer values vanish. -/
theorem lell_three_eq_iff (hd : 2 ≤ d) (hne : h ≠ 0) (hs : 0 < u - h) (ht : 0 < u + h)
    (hs1 : (u - h) ^ 2 < 1) (ht1 : (u + h) ^ 2 < 1) (hst : (u - h) * (u + h) < 1) :
    (Lell d lv g ((u - h) ^ 2) = 0 ∧ Lell d lv g ((u - h) * (u + h)) = 0
        ∧ Lell d lv g ((u + h) ^ 2) = 0)
      ↔ (Esys1 d lv g u h = 0 ∧ Esys2 d g u h = 0 ∧ Esys3 d g u h = 0) := by
  have h2 : Lell d lv g ((u + h) ^ 2) - Lell d lv g ((u - h) ^ 2) = h * Esys2 d g u h :=
    Lell_sub_eq_mul hd hs ht hs1 ht1 hst
  have h3 : Lell d lv g ((u + h) ^ 2) + Lell d lv g ((u - h) ^ 2)
      - 2 * Lell d lv g ((u - h) * (u + h)) = h ^ 2 * Esys3 d g u h :=
    Lell_add_sub_two_eq_mul hd hs ht hs1 ht1 hst
  simp only [Esys1]
  constructor
  · rintro ⟨hA, hB, hC⟩
    refine ⟨hB, ?_, ?_⟩
    · have hz : h * Esys2 d g u h = 0 := by rw [← h2, hA, hC]; ring
      exact (mul_eq_zero.mp hz).resolve_left hne
    · have hz : h ^ 2 * Esys3 d g u h = 0 := by rw [← h3, hA, hB, hC]; ring
      exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hne)
  · rintro ⟨hB, hE2, hE3⟩
    rw [hE2, mul_zero] at h2
    rw [hE3, mul_zero, hB] at h3
    exact ⟨by linarith, hB, by linarith⟩

/-! ## The values at `h = 0`

At `h = 0` every `logSlope` argument vanishes, so `logSlope_zero` replaces it by `1`, and
each of the three geometric sums has all of its terms equal, so it collapses to a constant
sum.  What comes out is `E₂(u, 0) = 4u·𝓛′(u²)` and `E₃(u, 0) = 4𝓛′(u²) + 4u²·𝓛″(u²)` with
`ℓ′` expanded — the base point of the implicit function theorem in
`lem:rank-one-kkt-family`. -/

/-- The value of `E₂` at `h = 0` for *every* `u`.  `SingularEndpoint/RankOneStationaryFamily/FamilyDeriv.lean` consumes exactly
this hypothesis-free form, `Fsys_zero_eq` being a statement about all of `ℝ × ℝ × ℝ`: at
`h = 0` every `logSlope` argument vanishes and the geometric sum collapses whatever `u` is. -/
theorem Esys2_zero' (g u : ℝ) :
    Esys2 d g u 0
      = 4 * u / (1 - u ^ 2) + 4 / u - 4 * g * u * (((d - 1 : ℕ) : ℝ) * (u ^ 2) ^ (d - 2)) := by
  have key : ∀ i ∈ Finset.range (d - 1),
      ((u + 0) ^ 2) ^ i * ((u - 0) ^ 2) ^ (d - 1 - 1 - i) = (u ^ 2) ^ (d - 2) := by
    intro i hi
    have hik : i < d - 1 := Finset.mem_range.mp hi
    have he : i + (d - 1 - 1 - i) = d - 2 := by omega
    rw [add_zero, sub_zero, ← pow_add, he]
  have hsum : ∑ i ∈ Finset.range (d - 1), ((u + 0) ^ 2) ^ i * ((u - 0) ^ 2) ^ (d - 1 - 1 - i)
      = ((d - 1 : ℕ) : ℝ) * (u ^ 2) ^ (d - 2) := by
    calc ∑ i ∈ Finset.range (d - 1), ((u + 0) ^ 2) ^ i * ((u - 0) ^ 2) ^ (d - 1 - 1 - i)
        = ∑ _i ∈ Finset.range (d - 1), (u ^ 2) ^ (d - 2) := Finset.sum_congr rfl key
      _ = ((d - 1 : ℕ) : ℝ) * (u ^ 2) ^ (d - 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have harg1 : 4 * u * (0 : ℝ) / (1 - (u - 0) ^ 2) = 0 := by norm_num
  have harg2 : 2 * (0 : ℝ) / (u + 0) = 0 := by norm_num
  rw [Esys2, hsum, harg1, harg2, logSlope_zero]
  simp only [sub_zero, add_zero, mul_one]

/-- The value of `E₂` at `h = 0`, i.e. `4u·𝓛′(u²)` of `lem:rank-one-kkt-family`:

  `E₂(u, 0) = 4u/(1-u²) + 4/u - 4γu·(d-1)(u²)^{d-2}`.

The three hypotheses are kept for documentation and for the call sites of
`SingularEndpoint/RankOneStationaryFamily/FamilyBase.lean`; the content is `Esys2_zero'`. -/
theorem Esys2_zero (hd : 2 ≤ d) (_hu0 : 0 < u) (_hu1 : u ^ 2 < 1) :
    Esys2 d g u 0
      = 4 * u / (1 - u ^ 2) + 4 / u - 4 * g * u * (((d - 1 : ℕ) : ℝ) * (u ^ 2) ^ (d - 2)) := by
  have _hd : 2 ≤ d := hd
  exact Esys2_zero' g u

/-- The value of `E₃` at `h = 0` for *every* `u`, the hypothesis-free form
`SingularEndpoint/RankOneStationaryFamily/FamilyDeriv.lean` consumes.

The three natural-number casts must be kept as written: over `ℝ` the factor `(d-2)` would
be wrong at `d = 2`, where the last sum is empty. -/
theorem Esys3_zero' (g u : ℝ) :
    Esys3 d g u 0
      = 4 / (1 - u ^ 2) ^ 2 - 4 * g * (((d - 1 : ℕ) : ℝ) * (u ^ 2) ^ (d - 2)
          + u * (((d - 1 : ℕ) : ℝ) * u ^ (d - 2)) * (((d - 2 : ℕ) : ℝ) * u ^ (d - 3))) := by
  have key1 : ∀ i ∈ Finset.range (d - 1),
      ((u + 0) ^ 2) ^ i * ((u - 0) * (u + 0)) ^ (d - 1 - 1 - i) = (u ^ 2) ^ (d - 2) := by
    intro i hi
    have hik : i < d - 1 := Finset.mem_range.mp hi
    have he : i + (d - 1 - 1 - i) = d - 2 := by omega
    have hz : u * u = u ^ 2 := by ring
    rw [add_zero, sub_zero, hz, ← pow_add, he]
  have key2 : ∀ i ∈ Finset.range (d - 1),
      (u - 0) ^ (d - 1 - 1 - i) * (u + 0) ^ i = u ^ (d - 2) := by
    intro i hi
    have hik : i < d - 1 := Finset.mem_range.mp hi
    have he : d - 1 - 1 - i + i = d - 2 := by omega
    rw [add_zero, sub_zero, ← pow_add, he]
  have key3 : ∀ j ∈ Finset.range (d - 2),
      (u + 0) ^ j * (u - 0) ^ (d - 2 - 1 - j) = u ^ (d - 3) := by
    intro j hj
    have hjk : j < d - 2 := Finset.mem_range.mp hj
    have he : j + (d - 2 - 1 - j) = d - 3 := by omega
    rw [add_zero, sub_zero, ← pow_add, he]
  have hsum1 : ∑ i ∈ Finset.range (d - 1),
        ((u + 0) ^ 2) ^ i * ((u - 0) * (u + 0)) ^ (d - 1 - 1 - i)
      = ((d - 1 : ℕ) : ℝ) * (u ^ 2) ^ (d - 2) := by
    calc ∑ i ∈ Finset.range (d - 1),
          ((u + 0) ^ 2) ^ i * ((u - 0) * (u + 0)) ^ (d - 1 - 1 - i)
        = ∑ _i ∈ Finset.range (d - 1), (u ^ 2) ^ (d - 2) := Finset.sum_congr rfl key1
      _ = ((d - 1 : ℕ) : ℝ) * (u ^ 2) ^ (d - 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum2 : ∑ i ∈ Finset.range (d - 1), (u - 0) ^ (d - 1 - 1 - i) * (u + 0) ^ i
      = ((d - 1 : ℕ) : ℝ) * u ^ (d - 2) := by
    calc ∑ i ∈ Finset.range (d - 1), (u - 0) ^ (d - 1 - 1 - i) * (u + 0) ^ i
        = ∑ _i ∈ Finset.range (d - 1), u ^ (d - 2) := Finset.sum_congr rfl key2
      _ = ((d - 1 : ℕ) : ℝ) * u ^ (d - 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum3 : ∑ j ∈ Finset.range (d - 2), (u + 0) ^ j * (u - 0) ^ (d - 2 - 1 - j)
      = ((d - 2 : ℕ) : ℝ) * u ^ (d - 3) := by
    calc ∑ j ∈ Finset.range (d - 2), (u + 0) ^ j * (u - 0) ^ (d - 2 - 1 - j)
        = ∑ _j ∈ Finset.range (d - 2), u ^ (d - 3) := Finset.sum_congr rfl key3
      _ = ((d - 2 : ℕ) : ℝ) * u ^ (d - 3) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have harg : 4 * (0 : ℝ) ^ 2 / (1 - (u - 0) * (u + 0)) ^ 2 = 0 := by norm_num
  have hz : (u - 0) * (u + 0) = u ^ 2 := by ring
  rw [Esys3, hsum1, hsum2, hsum3, harg, logSlope_zero, hz]
  simp only [sub_zero, mul_one]

/-- The value of `E₃` at `h = 0`, i.e. `4𝓛′(u²) + 4u²·𝓛″(u²)` of
`lem:rank-one-kkt-family`:

  `E₃(u, 0) = 4/(1-u²)² - 4γ·((d-1)(u²)^{d-2} + u·(d-1)u^{d-2}·(d-2)u^{d-3})`.

The three hypotheses are kept for documentation and for the call sites of
`SingularEndpoint/RankOneStationaryFamily/FamilyBase.lean`; the content is `Esys3_zero'`. -/
theorem Esys3_zero (hd : 2 ≤ d) (_hu0 : 0 < u) (_hu1 : u ^ 2 < 1) :
    Esys3 d g u 0
      = 4 / (1 - u ^ 2) ^ 2 - 4 * g * (((d - 1 : ℕ) : ℝ) * (u ^ 2) ^ (d - 2)
          + u * (((d - 1 : ℕ) : ℝ) * u ^ (d - 2)) * (((d - 2 : ℕ) : ℝ) * u ^ (d - 3))) := by
  have _hd : 2 ≤ d := hd
  exact Esys3_zero' g u

end UpperTailOptimizers
