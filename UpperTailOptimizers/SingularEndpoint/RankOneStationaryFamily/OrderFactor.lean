import Mathlib

/-!
# Extracting an analytic factor from a one-sided order asymptotic

A self-contained piece of one-variable real analysis.  Suppose a real-analytic function `F`
satisfies the asymptotic `F h / h ^ k → c` as `h ↓ 0` with `c ≠ 0`.  This is a statement about
the *right-hand* germ of `F` at `0` only, yet it forces the full two-sided factorisation
`F h = h ^ k * G h` with `G` analytic at `0` and `G 0 = c`.

The point of the upgrade is that a bare asymptotic `F h = c h ^ k + o(h ^ k)` says nothing
about quotients such as `F₁ h / F₂ h`, whereas the factorised form does: the common factor
`h ^ k` cancels, turning a `0/0` indeterminacy at `h = 0` into a genuine ratio `G₁ h / G₂ h`
of functions analytic at `0` whose value at `0` can simply be read off.  That is how a
quotient of two quantities vanishing to the same order `k` is evaluated at the degenerate
parameter value.

The proof is Mathlib's vanishing-order API for analytic functions.  The hypothesis `c ≠ 0`
rules out `F` being identically zero near `0`, so
`AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` supplies an `n` and an analytic `g` with
`g 0 ≠ 0` and `F h = h ^ n • g h` near `0`; comparing the two asymptotics pins `n = k`.

Nothing in this file refers to the graphon problem; it is stated for an arbitrary
`F : ℝ → ℝ`.

## Contents

* `exists_analytic_factor_of_tendsto` — the factorisation: if `F` is analytic at `0` and
  `F h / h ^ k → c ≠ 0` along `𝓝[>] 0`, then `F h = h ^ k * G h` near `0` for some `G`
  analytic at `0` with `G 0 = c`.
-/

namespace UpperTailOptimizers

open Filter Topology

/-- **Order factorisation from a one-sided asymptotic.**

If `F` is real-analytic at `0` and `F h / h ^ k` tends to a *nonzero* limit `c` as `h ↓ 0`,
then `F` factors as `F h = h ^ k * G h` on a full neighbourhood of `0`, with `G` analytic at
`0` and `G 0 = c`.

The one-sided hypothesis suffices: analyticity propagates the right-hand germ to a two-sided
one.  The hypothesis `c ≠ 0` does two jobs.  It rules out `F` vanishing identically near `0`,
so that `F` has a finite vanishing order at all; and it forces that order to be exactly `k`,
by excluding both `> k` (which would make the limit `0`) and `< k` (which would make it
infinite).  It also makes the conclusion sharp for the intended use: `G 0 = c ≠ 0`.  (That
`G` is therefore nonvanishing *near* `0`, so that a quotient of two such factorisations is
analytic there, follows from `G 0 ≠ 0` and continuity, but is not proved here.) -/
theorem exists_analytic_factor_of_tendsto {F : ℝ → ℝ} {c : ℝ} {k : ℕ}
    (hF : AnalyticAt ℝ F 0) (hc : c ≠ 0)
    (hlim : Tendsto (fun h : ℝ => F h / h ^ k) (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    ∃ G : ℝ → ℝ, AnalyticAt ℝ G 0 ∧ G 0 = c ∧ ∀ᶠ h in 𝓝 (0 : ℝ), F h = h ^ k * G h := by
  -- `F` cannot vanish identically near `0`: that would force `c = 0`.
  have hne : ¬ ∀ᶠ z in 𝓝 (0 : ℝ), F z = 0 := by
    intro h0
    refine hc (tendsto_nhds_unique hlim (Tendsto.congr' ?_ tendsto_const_nhds))
    filter_upwards [h0.filter_mono nhdsWithin_le_nhds] with z hz
    simp [hz]
  -- Hence the vanishing order of `F` at `0` is some natural number `n`.
  obtain ⟨n, g, hg, hg0, hgeq⟩ := hF.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hgeq' : ∀ᶠ z in 𝓝 (0 : ℝ), F z = z ^ n * g z := by
    filter_upwards [hgeq] with z hz
    simpa [smul_eq_mul] using hz
  have hgtend : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
    hg.continuousAt.mono_left nhdsWithin_le_nhds
  -- Comparing the two asymptotics pins `n = k`.
  have hnk : n = k := by
    rcases lt_trichotomy n k with h | h | h
    · -- `n < k`: then `h ^ (k - n) * (F h / h ^ k) = g h`, whose two limits are `0` and `g 0`.
      exfalso
      have hkey : ∀ᶠ z in 𝓝[>] (0 : ℝ), z ^ (k - n) * (F z / z ^ k) = g z := by
        filter_upwards [self_mem_nhdsWithin,
          hgeq'.filter_mono nhdsWithin_le_nhds] with z hz hFz
        have hz0 : z ≠ 0 := ne_of_gt hz
        rw [hFz, show z ^ (k - n) * (z ^ n * g z / z ^ k)
              = z ^ (k - n) * z ^ n * g z / z ^ k from by ring,
          ← pow_add, Nat.sub_add_cancel h.le, mul_comm, mul_div_assoc,
          div_self (pow_ne_zero k hz0), mul_one]
      have hzero : Tendsto (fun z : ℝ => z ^ (k - n)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h1 : Tendsto (fun z : ℝ => z ^ (k - n)) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ (k - n))) :=
          continuousAt_pow (0 : ℝ) (k - n)
        rw [zero_pow (Nat.sub_ne_zero_of_lt h)] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      have h1 : Tendsto (fun z : ℝ => z ^ (k - n) * (F z / z ^ k)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using hzero.mul hlim
      exact hg0 (tendsto_nhds_unique (h1.congr' hkey) hgtend).symm
    · exact h
    · -- `n > k`: then `F h / h ^ k = h ^ (n - k) * g h`, which tends to `0`, so `c = 0`.
      exfalso
      have hkey : ∀ᶠ z in 𝓝[>] (0 : ℝ), z ^ (n - k) * g z = F z / z ^ k := by
        filter_upwards [self_mem_nhdsWithin,
          hgeq'.filter_mono nhdsWithin_le_nhds] with z hz hFz
        have hz0 : z ≠ 0 := ne_of_gt hz
        have hpow : z ^ n = z ^ (n - k) * z ^ k := by
          rw [← pow_add, Nat.sub_add_cancel h.le]
        rw [hFz, hpow, show z ^ (n - k) * z ^ k * g z / z ^ k
              = z ^ (n - k) * g z * (z ^ k / z ^ k) from by ring,
          div_self (pow_ne_zero k hz0), mul_one]
      have h2 : Tendsto (fun z : ℝ => z ^ (n - k) * g z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h1 : Tendsto (fun z : ℝ => z ^ (n - k) * g z) (𝓝 (0 : ℝ))
            (𝓝 ((0 : ℝ) ^ (n - k) * g 0)) := (continuousAt_pow (0 : ℝ) (n - k)).mul hg.continuousAt
        rw [zero_pow (Nat.sub_ne_zero_of_lt h), zero_mul] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      exact hc (tendsto_nhds_unique hlim (h2.congr' hkey))
  -- With `n = k` the quotient *is* `g` on the right, so `g 0 = c` by uniqueness of limits.
  subst hnk
  refine ⟨g, hg, ?_, hgeq'⟩
  have hkey : ∀ᶠ z in 𝓝[>] (0 : ℝ), F z / z ^ n = g z := by
    filter_upwards [self_mem_nhdsWithin, hgeq'.filter_mono nhdsWithin_le_nhds] with z hz hFz
    rw [hFz, mul_comm, mul_div_assoc, div_self (pow_ne_zero n (ne_of_gt hz)), mul_one]
  exact tendsto_nhds_unique hgtend (hlim.congr' hkey)

end UpperTailOptimizers
