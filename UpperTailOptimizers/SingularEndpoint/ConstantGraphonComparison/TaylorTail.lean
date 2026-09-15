import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Quotient

/-!
# The analytic Taylor tail (Section 5, `paper/sections/singular.tex`)

`SingularEndpoint/RankOneStationaryFamily/Quotient.lean` divides an analytic function by a *cubic* whose roots are the three
nodes of the coalescing family.  Section 5 also needs the confluent case at a **single**
node, to arbitrary order: the expansions `eq:rank-one-parameter-expansions` are read off from

  `𝓛_*(z) = \frac{𝓛_*'''(r_*)}{6}(z - r_*)^3 + (z - r_*)^4 · S(z)`,
  `Γ_d(z) = \frac{Γ_d^{(4)}(r_*)}{24}(z - r_*)^4 + (z - r_*)^5 · T(z)`,

with `S`, `T` analytic near `r_*` and `S(r_*) = 𝓛_*^{(4)}(r_*)/24`,
`T(r_*) = Γ_d^{(5)}(r_*)/120`.  These are Taylor's theorem with an **analytic** remainder
factor, which is stronger than the Lagrange form of `SingularEndpoint/RankOneStationaryFamily/Interp3.lean`: the remainder is
a named function of `z`, not an unlocated `ξ`, so it can be evaluated in a limit.

That is exactly what the `h⁵` order needs.  The `h⁴` order of `SingularEndpoint/RankOneStationaryFamily/Order4.lean` only
compares `𝓛_h'''` against two constants over a shrinking interval, and an unlocated `ξ` is
harmless there; at `h⁵` the coefficient depends on *where* in the interval the remainder is
evaluated, so the Lagrange form is not enough.

## The construction

The tail is the `n`-fold difference quotient based `n` times at the same point,

  `taylorTail f a n = dslope (⋯ (dslope f a) ⋯) a`   (`n` times),

which is the function `SingularEndpoint/RankOneStationaryFamily/Quotient.lean` already knows preserves analyticity
(`analyticOnNhd_dslope`) and whose value at `a` is the `n`-th Taylor coefficient
(`iterate_dslope_self`).  The expansion itself, `taylorTail_expand`, is pure `dslope`
algebra — it holds at **every** real `z` for **every** function, analytic or not, because
`(z - a)·dslope g a z = g z - g a` is an identity.  Analyticity enters only to *name* the
coefficients.

## Contents

* `taylorTail` — the `n`-fold difference quotient, with `taylorTail_zero`, `taylorTail_succ`;
* `analyticOnNhd_taylorTail` — analyticity is preserved;
* `taylorTail_apply_self` — `taylorTail f a n a = f⁽ⁿ⁾(a)/n!` (`iterate_dslope_self`);
* `taylorTail_expand` — `f z = Σ_{k<n} f⁽ᵏ⁾(a)/k! · (z-a)^k + (z-a)^n · taylorTail f a n z`;
* `taylorTail_expand_of_vanishing`, `taylorTail_expand_of_iteratedDeriv_eq_zero` — the
  two-term form used in Section 5, where the first `n` coefficients vanish.
-/

namespace UpperTailOptimizers

open Filter

/-- The **`n`-th Taylor tail** of `f` at `a`: the `n`-fold difference quotient of `f`, based
each time at `a`.

`taylorTail f a 0 = f`, and `taylorTail f a (n+1) = dslope (taylorTail f a n) a`. For `f`
analytic at `a` this is the function `z ↦ (f z - Σ_{k<n} c_k (z-a)^k)/(z-a)^n` extended
analytically across `a`, where `c_k = f⁽ᵏ⁾(a)/k!`. -/
noncomputable def taylorTail (f : ℝ → ℝ) (a : ℝ) (n : ℕ) : ℝ → ℝ :=
  (Function.swap dslope a)^[n] f

@[simp] theorem taylorTail_zero (f : ℝ → ℝ) (a : ℝ) : taylorTail f a 0 = f := rfl

theorem taylorTail_succ (f : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    taylorTail f a (n + 1) = dslope (taylorTail f a n) a :=
  Function.iterate_succ_apply' _ _ _

/-- **The tail of an analytic function is analytic.**  Iterating `analyticOnNhd_dslope`. -/
theorem analyticOnNhd_taylorTail {f : ℝ → ℝ} {s : Set ℝ} {a : ℝ} (hf : AnalyticOnNhd ℝ f s)
    (ha : a ∈ s) (n : ℕ) : AnalyticOnNhd ℝ (taylorTail f a n) s := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [taylorTail_succ]; exact analyticOnNhd_dslope ih ha

/-- **The tail reads off the Taylor coefficient.**  `taylorTail f a n a = f⁽ⁿ⁾(a)/n!`.  This
is `iterate_dslope_self` of `SingularEndpoint/RankOneStationaryFamily/Quotient.lean` under the new name. -/
theorem taylorTail_apply_self {f : ℝ → ℝ} {a : ℝ} (hf : AnalyticAt ℝ f a) (n : ℕ) :
    taylorTail f a n a = iteratedDeriv n f a / n.factorial :=
  iterate_dslope_self hf n

/-- **Taylor's theorem with an analytic remainder factor.**

  `f z = Σ_{k<n} taylorTail f a k a · (z-a)^k + (z-a)^n · taylorTail f a n z`,

at every real `z`.  No hypothesis whatsoever: this is the telescoping of the `dslope`
identity `(z-a)·dslope g a z = g z - g a`.  Analyticity is needed only to identify the
coefficients `taylorTail f a k a` with `f⁽ᵏ⁾(a)/k!` (`taylorTail_apply_self`) and the
remainder factor with an analytic function (`analyticOnNhd_taylorTail`). -/
theorem taylorTail_expand (f : ℝ → ℝ) (a : ℝ) (n : ℕ) (z : ℝ) :
    f z = (∑ k ∈ Finset.range n, taylorTail f a k a * (z - a) ^ k)
      + (z - a) ^ n * taylorTail f a n z := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hd := sub_mul_dslope (taylorTail f a n) a z
      rw [← taylorTail_succ] at hd
      have hstep : taylorTail f a n z
          = taylorTail f a n a + (z - a) * taylorTail f a (n + 1) z := by linarith
      rw [ih, Finset.sum_range_succ, hstep]
      ring

/-- The two-term form: when the first `n` Taylor coefficients vanish,

  `f z = taylorTail f a n a · (z-a)^n + (z-a)^{n+1} · taylorTail f a (n+1) z`. -/
theorem taylorTail_expand_of_vanishing {f : ℝ → ℝ} {a : ℝ} {n : ℕ}
    (hvan : ∀ k, k < n → taylorTail f a k a = 0) (z : ℝ) :
    f z = taylorTail f a n a * (z - a) ^ n
      + (z - a) ^ (n + 1) * taylorTail f a (n + 1) z := by
  have h := taylorTail_expand f a (n + 1) z
  rw [Finset.sum_range_succ] at h
  have hzero : (∑ k ∈ Finset.range n, taylorTail f a k a * (z - a) ^ k) = 0 :=
    Finset.sum_eq_zero fun k hk => by rw [hvan k (Finset.mem_range.mp hk), zero_mul]
  rw [hzero, zero_add] at h
  exact h

/-- **The form used in Section 5.**  For `f` analytic at `a` whose first `n` derivatives at
`a` vanish,

  `f z = \frac{f⁽ⁿ⁾(a)}{n!}(z-a)^n + (z-a)^{n+1}·taylorTail f a (n+1) z`,

with `taylorTail f a (n+1) a = f⁽ⁿ⁺¹⁾(a)/(n+1)!` by `taylorTail_apply_self`.

Instantiated at `f = 𝓛_*`, `a = r_*`, `n = 3` this is the cubic-plus-quartic expansion of
`eq:kkt-quartic-expansion`; at `f = Γ_d`, `n = 4` it is
`eq:endpoint-gap-expansion` with its next term. -/
theorem taylorTail_expand_of_iteratedDeriv_eq_zero {f : ℝ → ℝ} {a : ℝ} {n : ℕ}
    (hf : AnalyticAt ℝ f a) (hvan : ∀ k, k < n → iteratedDeriv k f a = 0) (z : ℝ) :
    f z = (iteratedDeriv n f a / n.factorial) * (z - a) ^ n
      + (z - a) ^ (n + 1) * taylorTail f a (n + 1) z := by
  rw [← taylorTail_apply_self hf n]
  exact taylorTail_expand_of_vanishing
    (fun k hk => by rw [taylorTail_apply_self hf k, hvan k hk, zero_div]) z

/-! ## The rate of a flat increment

The family functions `u_h, ℓ_h, γ_h` of `lem:rank-one-kkt-family` are analytic and
**even**, so their first derivative at `0` vanishes and the increment `v_h - v_0` is
`O(h²)`.  `tendsto_sub_self_div_pow` turns that into the honest limit that
`eq:rank-one-parameter-expansions` asserts, with no appeal to power series beyond
`taylorTail_expand`. -/

/-- Analyticity of the tail at the base point itself, the one-point case of
`analyticOnNhd_taylorTail`. -/
theorem analyticAt_taylorTail {f : ℝ → ℝ} {a : ℝ} (hf : AnalyticAt ℝ f a) (n : ℕ) :
    AnalyticAt ℝ (taylorTail f a n) a :=
  analyticOnNhd_taylorTail (s := {a})
    (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact hf) rfl n a rfl

/-- **The rate of a flat increment.**  If `f` is analytic at `a` and its derivatives of
orders `1, …, n-1` vanish there, then

  `(f z - f a)/(z - a)^n  →  f⁽ⁿ⁾(a)/n!`   as `z → a`, `z ≠ a`.

Instantiated at `n = 2` and `a = 0` this reads the `h²` coefficient off an even analytic
family function; instantiated at higher `n` it is the same statement one order up. -/
theorem tendsto_sub_self_div_pow {f : ℝ → ℝ} {a : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hf : AnalyticAt ℝ f a) (hvan : ∀ k, 1 ≤ k → k < n → iteratedDeriv k f a = 0) :
    Filter.Tendsto (fun z : ℝ => (f z - f a) / (z - a) ^ n) (nhdsWithin a {a}ᶜ)
      (nhds (iteratedDeriv n f a / n.factorial)) := by
  have hsum : ∀ z : ℝ, (∑ k ∈ Finset.range n, taylorTail f a k a * (z - a) ^ k) = f a := by
    intro z
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hn)]
    · simp
    · intro k hk hk0
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      rw [taylorTail_apply_self hf k, hvan k hk1 (Finset.mem_range.mp hk), zero_div, zero_mul]
  have hquot : ∀ z : ℝ, z ≠ a → (f z - f a) / (z - a) ^ n = taylorTail f a n z := by
    intro z hz
    have h := taylorTail_expand f a n z
    rw [hsum z] at h
    have hne : (z - a) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
    field_simp
    linarith [h]
  have hcont : Filter.Tendsto (taylorTail f a n) (nhds a) (nhds (taylorTail f a n a)) :=
    (analyticAt_taylorTail hf n).continuousAt.tendsto
  rw [← taylorTail_apply_self hf n]
  refine (hcont.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hquot z hz).symm

end UpperTailOptimizers
