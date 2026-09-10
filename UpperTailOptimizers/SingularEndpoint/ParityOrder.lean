import UpperTailOptimizers.SingularEndpoint.TaylorTail

/-!
# The two-order remainder gain for a reflection-symmetric analytic function

`lem:rank-one-parameter-expansions` and `lem:constant-graphon-comparison` of
`paper/bipodal_optimizer.tex` state their remainders two orders past the leading term:
`u_h = u_* + U₂h² + O_d(h⁴)`, `α_h = 1/2 + A₁h + O_d(h³)`,
`I_{p_h}(W_h) - J_{p_h}(r_h) = -d³h⁴/3 + O_d(h⁶)`.  The paper's reason is one sentence:
the quantity is an analytic function of `h` with a definite parity, so its Taylor expansion
proceeds in steps of two and the first omitted term is already two orders down
("the first remainder improves from `O_d(h⁵)` to `O_d(h⁶)` because `∫Γ_d(W_h)` is an even
analytic function of `h`").

This file is that sentence, for an arbitrary `F : ℝ → ℝ`.  Suppose `F` is analytic at `0`,
satisfies the reflection law `F(-h) = (-1)^n F(h)`, and vanishes to order `n` in the weak sense
`F h / h^n → 0`.  Then `F h = h^{n+2} T h` globally, with `T` analytic at `0` — so `F` is
`O(h^{n+2})`, a full two orders past the `o(h^n)` that went in.

The argument uses only `taylorTail` (`SingularEndpoint/TaylorTail.lean`):

* the weak vanishing `F h / h^n → 0` kills the Taylor coefficients up to order `n`, one at a
  time: with the first `k` coefficients gone, `taylorTail_expand_of_vanishing` gives
  `F z = c_k z^k + z^{k+1}(⋯)`, and multiplying `F z / z^n` by `z^{n-k}` exhibits `c_k` as a
  limit of something tending to `0`;
* that leaves `F z = c_{n+1} z^{n+1} + z^{n+2} T z`.  Reflection compares this expansion at
  `z` and `-z`: the `z^{n+1}` term has the *wrong* parity, so `2c_{n+1} = z(T(-z) - T z)`
  for `z ≠ 0`, and letting `z → 0` gives `c_{n+1} = 0`.

Both steps are elementary because `taylorTail_expand` is an identity at every real `z`, not
just near `0`.

## Contents

* `exists_factor_of_reflect` — the factorisation `F z = z^{n+2} T z` with `T` analytic at `0`;
* `exists_pow_bound_of_reflect` — the resulting bound `|F h| ≤ C|h|^{n+2}` near `0`;
* `exists_pow_bound_sub_linear`, `exists_pow_bound_sub_quadratic`,
  `exists_pow_bound_sub_quartic` — the three shapes the family expansions use: an odd
  function against its linear term, and an even function against its quadratic or quartic term.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

/-- **The Taylor coefficients below the order of weak vanishing are zero.**  If `F` is analytic
at `0` and `F h / h^n → 0`, then `F⁽ʲ⁾(0) = 0` for every `j ≤ n`, in the `taylorTail` form
`taylorTail F 0 j 0 = 0`. -/
theorem taylorTail_eq_zero_of_tendsto_zero {F : ℝ → ℝ} {n : ℕ} (hF : AnalyticAt ℝ F 0)
    (hlim : Tendsto (fun h : ℝ => F h / h ^ n) (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    ∀ j : ℕ, j ≤ n → taylorTail F 0 j 0 = 0 := by
  -- strong induction: with the coefficients below `k` gone, the `k`-th is a limit of `0`
  have key : ∀ k : ℕ, k ≤ n + 1 → ∀ j : ℕ, j < k → taylorTail F 0 j 0 = 0 := by
    intro k
    induction k with
    | zero => intro _ j hj; exact absurd hj (Nat.not_lt_zero j)
    | succ k ih =>
      intro hk j hj
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjk | hjk
      · exact ih (by omega) j hjk
      subst hjk
      -- the new coefficient: `j ≤ n`, and all earlier ones vanish
      have hkn : j ≤ n := by omega
      have hvan := ih (by omega)
      -- `F z = c_j z^j + z^{j+1} · taylorTail F 0 (j+1) z`
      have hexp : ∀ z : ℝ, F z
          = taylorTail F 0 j 0 * z ^ j + z ^ (j + 1) * taylorTail F 0 (j + 1) z := by
        intro z
        have h := taylorTail_expand_of_vanishing (f := F) (a := 0) (n := j) hvan z
        simpa using h
      -- multiplying `F z / z^n` by `z^{n-j}` returns `c_j + z · taylorTail F 0 (j+1) z`
      have hquot : ∀ᶠ z in 𝓝[≠] (0 : ℝ),
          F z / z ^ n * z ^ (n - j)
            = taylorTail F 0 j 0 + z * taylorTail F 0 (j + 1) z := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        have hz0 : z ≠ 0 := hz
        have hpow : z ^ n = z ^ j * z ^ (n - j) := by
          rw [← pow_add, Nat.add_sub_cancel' hkn]
        rw [hexp z, hpow]
        field_simp
        ring
      -- the left side tends to `0 * 0 ^ (n - j) = 0`
      have hL : Tendsto (fun z : ℝ => F z / z ^ n * z ^ (n - j)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
        have h2 : Tendsto (fun z : ℝ => z ^ (n - j)) (𝓝[≠] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ (n - j))) :=
          ((continuous_pow (n - j)).continuousAt).mono_left nhdsWithin_le_nhds
        have := hlim.mul h2
        simpa using this
      -- the right side tends to `c_j`
      have hR : Tendsto (fun z : ℝ => taylorTail F 0 j 0 + z * taylorTail F 0 (j + 1) z)
          (𝓝[≠] (0 : ℝ)) (𝓝 (taylorTail F 0 j 0)) := by
        have hT : Tendsto (taylorTail F 0 (j + 1)) (𝓝 (0 : ℝ))
            (𝓝 (taylorTail F 0 (j + 1) 0)) :=
          (analyticAt_taylorTail hF (j + 1)).continuousAt.tendsto
        have h1 : Tendsto (fun z : ℝ => z * taylorTail F 0 (j + 1) z) (𝓝 (0 : ℝ))
            (𝓝 (0 * taylorTail F 0 (j + 1) 0)) := (continuous_id.continuousAt).mul hT
        rw [zero_mul] at h1
        have h3 : Tendsto (fun z : ℝ => taylorTail F 0 j 0 + z * taylorTail F 0 (j + 1) z)
            (𝓝 (0 : ℝ)) (𝓝 (taylorTail F 0 j 0 + 0)) :=
          (tendsto_const_nhds).add h1
        rw [add_zero] at h3
        exact h3.mono_left nhdsWithin_le_nhds
      exact (tendsto_nhds_unique (hL.congr' hquot) hR).symm
  exact fun j hj => key (n + 1) le_rfl j (by omega)

/-- **The factorisation.**  An `F` analytic at `0` with the reflection law
`F(-h) = (-1)^n F(h)` and weak vanishing `F h / h^n → 0` factors globally as
`F z = z^{n+2} T z` with `T` analytic at `0`.

The reflection law is what upgrades `n + 1` to `n + 2`: the coefficient of `z^{n+1}` has the
parity opposite to `F`, so it must vanish. -/
theorem exists_factor_of_reflect {F : ℝ → ℝ} {n : ℕ} (hF : AnalyticAt ℝ F 0)
    (hrefl : ∀ h : ℝ, F (-h) = (-1 : ℝ) ^ n * F h)
    (hlim : Tendsto (fun h : ℝ => F h / h ^ n) (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    ∃ T : ℝ → ℝ, AnalyticAt ℝ T 0 ∧ ∀ z : ℝ, F z = z ^ (n + 2) * T z := by
  have hvan := taylorTail_eq_zero_of_tendsto_zero hF hlim
  set c : ℝ := taylorTail F 0 (n + 1) 0 with hc
  set T : ℝ → ℝ := taylorTail F 0 (n + 2) with hT
  have hTana : AnalyticAt ℝ T 0 := analyticAt_taylorTail hF (n + 2)
  -- `F z = c z^{n+1} + z^{n+2} T z`
  have hexp : ∀ z : ℝ, F z = c * z ^ (n + 1) + z ^ (n + 2) * T z := by
    intro z
    have h := taylorTail_expand_of_vanishing (f := F) (a := 0) (n := n + 1)
      (fun j hj => hvan j (by omega)) z
    simpa using h
  -- reflection forces `c = 0`: the `z^{n+1}` term has the parity opposite to `F`
  have hc0 : c = 0 := by
    have hkey : ∀ z : ℝ, z ≠ 0 → z * (T (-z) - T z) = 2 * c := by
      intro z hz
      have h1 := hexp z
      have h2 := hexp (-z)
      have h3 := hrefl z
      have hznz : z ^ (n + 1) ≠ 0 := pow_ne_zero _ hz
      have hzn2 : z ^ (n + 2) = z ^ (n + 1) * z := by rw [pow_succ]
      have hmain : (z * (T (-z) - T z)) * z ^ (n + 1) = (2 * c) * z ^ (n + 1) := by
        rcases Nat.even_or_odd n with he | ho
        · have e0 : (-1 : ℝ) ^ n = 1 := he.neg_one_pow
          have e1 : (-z) ^ (n + 1) = -z ^ (n + 1) := (Even.add_one he).neg_pow z
          have e2 : (-z) ^ (n + 2) = z ^ (n + 2) := (he.add (even_two)).neg_pow z
          rw [e1, e2] at h2
          rw [e0, one_mul] at h3
          rw [h3, h1] at h2
          rw [hzn2] at h2
          nlinarith [h2]
        · have e0 : (-1 : ℝ) ^ n = -1 := ho.neg_one_pow
          have e1 : (-z) ^ (n + 1) = z ^ (n + 1) := (Odd.add_one ho).neg_pow z
          have e2 : (-z) ^ (n + 2) = -z ^ (n + 2) := (Odd.add_even ho even_two).neg_pow z
          rw [e1, e2] at h2
          rw [e0] at h3
          rw [h3, h1] at h2
          rw [hzn2] at h2
          nlinarith [h2]
      exact mul_right_cancel₀ hznz hmain
    -- letting `z → 0` on the left gives `0`
    have hR : Tendsto (fun z : ℝ => z * (T (-z) - T z)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have hT0 : Tendsto T (𝓝 (0 : ℝ)) (𝓝 (T 0)) := hTana.continuousAt.tendsto
      have hTn : Tendsto (fun z : ℝ => T (-z)) (𝓝 (0 : ℝ)) (𝓝 (T 0)) := by
        have hneg : Tendsto (fun z : ℝ => -z) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
          simpa using (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto
        exact hT0.comp hneg
      have hid : Tendsto (fun z : ℝ => z) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_id
      have h1 : Tendsto (fun z : ℝ => z * (T (-z) - T z)) (𝓝 (0 : ℝ))
          (𝓝 (0 * (T 0 - T 0))) := hid.mul (hTn.sub hT0)
      rw [sub_self, mul_zero] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    have hconst : Tendsto (fun _ : ℝ => 2 * c) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      refine hR.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hkey z hz
    have := tendsto_nhds_unique hconst (tendsto_const_nhds)
    linarith
  refine ⟨T, hTana, fun z => ?_⟩
  rw [hexp z, hc0]; ring

/-- **The bound.**  `|F h| ≤ C|h|^{n+2}` near `0`, from `exists_factor_of_reflect` and
continuity of the analytic factor. -/
theorem exists_pow_bound_of_reflect {F : ℝ → ℝ} {n : ℕ} (hF : AnalyticAt ℝ F 0)
    (hrefl : ∀ h : ℝ, F (-h) = (-1 : ℝ) ^ n * F h)
    (hlim : Tendsto (fun h : ℝ => F h / h ^ n) (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| < δ → |F h| ≤ C * |h| ^ (n + 2) := by
  obtain ⟨T, hTana, hTeq⟩ := exists_factor_of_reflect hF hrefl hlim
  have hcont : Tendsto T (𝓝 (0 : ℝ)) (𝓝 (T 0)) := hTana.continuousAt.tendsto
  have hev : ∀ᶠ z in 𝓝 (0 : ℝ), |T z| ≤ |T 0| + 1 := by
    have h1 : ∀ᶠ z in 𝓝 (0 : ℝ), |T z - T 0| < 1 := by
      have := Metric.tendsto_nhds.mp hcont 1 one_pos
      simpa [Real.dist_eq] using this
    filter_upwards [h1] with z hz
    have := abs_sub_abs_le_abs_sub (T z) (T 0)
    linarith [this, hz]
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hbound⟩ := hev
  refine ⟨|T 0| + 1, δ, by positivity, hδ, fun h hh => ?_⟩
  have hb : |T h| ≤ |T 0| + 1 := hbound (by simpa [Real.dist_eq] using hh)
  calc |F h| = |h ^ (n + 2)| * |T h| := by rw [hTeq h, abs_mul]
    _ = |h| ^ (n + 2) * |T h| := by rw [abs_pow]
    _ ≤ |h| ^ (n + 2) * (|T 0| + 1) := by
        exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (|T 0| + 1) * |h| ^ (n + 2) := by ring

/-! ## The three shapes used along the family -/

/-- **An odd function against its linear term.**  If `v` is analytic at `0`, odd, and
`v h / h → c`, then `v h = c h + O(h³)`.  This is the shape of the block weight
`α_h - 1/2` in `eq:rank-one-parameter-expansions`. -/
theorem exists_pow_bound_sub_linear {v : ℝ → ℝ} {c : ℝ} (hv : AnalyticAt ℝ v 0)
    (hodd : ∀ h : ℝ, v (-h) = -v h)
    (hlim : Tendsto (fun h : ℝ => v h / h) (𝓝[≠] (0 : ℝ)) (𝓝 c)) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| < δ → |v h - c * h| ≤ C * |h| ^ 3 := by
  have hF : AnalyticAt ℝ (fun h : ℝ => v h - c * h) 0 :=
    hv.sub (analyticAt_const.mul analyticAt_id)
  have hrefl : ∀ h : ℝ, (fun h : ℝ => v h - c * h) (-h) = (-1 : ℝ) ^ 1 * (v h - c * h) := by
    intro h; simp only [hodd h]; ring
  have hlim' : Tendsto (fun h : ℝ => (v h - c * h) / h ^ 1) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have := hlim.sub (tendsto_const_nhds (x := c) (f := 𝓝[≠] (0:ℝ)))
    rw [sub_self] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := hh
    field_simp
  obtain ⟨C, δ, hC, hδ, hb⟩ := exists_pow_bound_of_reflect hF hrefl hlim'
  exact ⟨C, δ, hC, hδ, hb⟩

/-- **An even function against its quadratic term.**  If `v` is analytic at `0`, even, and
`(v h - v 0)/h² → c`, then `v h = v 0 + c h² + O(h⁴)`.  This is the shape of `u_h`, `Λ_h` and
`r_h` in `eq:rank-one-parameter-expansions`. -/
theorem exists_pow_bound_sub_quadratic {v : ℝ → ℝ} {c : ℝ} (hv : AnalyticAt ℝ v 0)
    (hev : ∀ h : ℝ, v (-h) = v h)
    (hlim : Tendsto (fun h : ℝ => (v h - v 0) / h ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 c)) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      |v h - v 0 - c * h ^ 2| ≤ C * |h| ^ 4 := by
  have hF : AnalyticAt ℝ (fun h : ℝ => v h - v 0 - c * h ^ 2) 0 :=
    (hv.sub analyticAt_const).sub (analyticAt_const.mul (analyticAt_id.pow 2))
  have hrefl : ∀ h : ℝ, (fun h : ℝ => v h - v 0 - c * h ^ 2) (-h)
      = (-1 : ℝ) ^ 2 * (v h - v 0 - c * h ^ 2) := by
    intro h; simp only [hev h]; ring
  have hlim' : Tendsto (fun h : ℝ => (v h - v 0 - c * h ^ 2) / h ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have := hlim.sub (tendsto_const_nhds (x := c) (f := 𝓝[≠] (0:ℝ)))
    rw [sub_self] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := hh
    field_simp
  obtain ⟨C, δ, hC, hδ, hb⟩ := exists_pow_bound_of_reflect hF hrefl hlim'
  exact ⟨C, δ, hC, hδ, hb⟩

/-- **An even function against its quartic term.**  If `v` is analytic at `0`, even, and
`v h / h⁴ → c`, then `v h = c h⁴ + O(h⁶)`.  This is the shape of the cost gap in
`lem:constant-graphon-comparison`. -/
theorem exists_pow_bound_sub_quartic {v : ℝ → ℝ} {c : ℝ} (hv : AnalyticAt ℝ v 0)
    (hev : ∀ h : ℝ, v (-h) = v h)
    (hlim : Tendsto (fun h : ℝ => v h / h ^ 4) (𝓝[≠] (0 : ℝ)) (𝓝 c)) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| < δ → |v h - c * h ^ 4| ≤ C * |h| ^ 6 := by
  have hF : AnalyticAt ℝ (fun h : ℝ => v h - c * h ^ 4) 0 :=
    hv.sub (analyticAt_const.mul (analyticAt_id.pow 4))
  have hrefl : ∀ h : ℝ, (fun h : ℝ => v h - c * h ^ 4) (-h)
      = (-1 : ℝ) ^ 4 * (v h - c * h ^ 4) := by
    intro h; simp only [hev h]; ring
  have hlim' : Tendsto (fun h : ℝ => (v h - c * h ^ 4) / h ^ 4) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have := hlim.sub (tendsto_const_nhds (x := c) (f := 𝓝[≠] (0:ℝ)))
    rw [sub_self] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := hh
    field_simp
  obtain ⟨C, δ, hC, hδ, hb⟩ := exists_pow_bound_of_reflect hF hrefl hlim'
  exact ⟨C, δ, hC, hδ, hb⟩

end SingularEndpoint

end UpperTailOptimizers
