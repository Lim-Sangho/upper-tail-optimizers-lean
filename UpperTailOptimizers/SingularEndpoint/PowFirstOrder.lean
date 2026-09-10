import UpperTailOptimizers.SingularEndpoint.PowInterp
import UpperTailOptimizers.SingularEndpoint.KernelInterp

/-!
# First-order interpolation in `{1, x^d}`, and the coefficients of `P_h`
(Section 7, `paper/singular_endpoint.tex`)

The **first-order companion** of `SingularEndpoint/PowInterp.lean`, and the first instalment of the
coefficient-bound clause in the proof of `lem:central-kernel-bound` reading

> Hence there is a single `C_d ≥ 1` such that
> `max{|p_{ij,h}|, |u_{i,h}(x)|, |v_{i,h}(x)|, |Θ_h(x,y)|} ≤ C_d`.

`SingularEndpoint/PowInterp.lean` supplies the *second*-order theory of the interpolation
`eq:moment-interpolation`: `exists_powResid_bound` and `powDD_mem_of_powDeriv2_mem` bound the
remainder through `powDeriv2`.  What is missing there, and is supplied here, is the
*first*-order statement about the **secant slope itself**: in the chart `w = x^d` the
coefficient `powCoefB` is an ordinary difference quotient, so Cauchy's mean value theorem
gives a `ξ` between the nodes with

  `powCoefB d φ s t = powDeriv d φ₁ ξ`,   `powDeriv d φ₁ x = φ₁(x)/(d x^{d-1})`.

That single line is what compensates the `1/(t_h^d - s_h^d)` inside every coefficient of
the kernel decomposition — the unlabelled display in the proof of
`lem:central-kernel-bound` — since the
coefficient slices `A_h`, `B_h`
(`KKTFamily.kernelCoefA`, `.kernelCoefB`) are themselves divided differences of `K_h`,
and their own divided differences are the four coefficients of `P_h`.

## The route to the coefficient bounds

* **Target 1** — `exists_powCoefB_eq_powDeriv` and its sandwich
  `powCoefB_mem_of_powDeriv_mem`, the exact first-order siblings of
  `exists_powResid_bound` and `powDD_mem_of_powDeriv2_mem`.  Only `d ≠ 0` is needed (the
  second-order statements need `2 ≤ d` because `powDeriv2` differentiates `x^{d-1}`).
* **Target 2** — uniform-in-`h` bounds on `J_{p_h}', J_{p_h}''` and `J_{p_h}'''` on a fixed
  closed subinterval of `(0,1)`.  The displacement `eq:entropy-parameter-shift`
  (`Jp_eq_Jp_pStar_add`) makes this **exact rather than asymptotic**: `Jp''` and `Jp3` do not
  mention `p` at all, and `J_p'` picks up only the constant `Λ_p = ℓ(p) - ℓ(p_*)`
  (`Jp'_eq_Jp'_pStar_add`), which tends to `0` with `h`.  No compactness argument is used for
  the derivatives; the one compactness argument in the file bounds `J_{p_*}` itself on `[0,1]`,
  where no formula is wanted.
* **Target 3** — the coefficients.  Differentiating a coefficient slice in the frozen
  variable commutes with the (fixed, node-indexed) linear functional that extracts it:
  `hasDerivAt_kernelCoefA`, `hasDerivAt_kernelCoefB` say that the derivative of `A_h`, `B_h`
  is the corresponding coefficient of the differentiated kernel slice
  `z ↦ z·J_{p_h}'(x z)`.  Feeding that into Target 1 twice bounds `p_{00,h}`, `p_{d0,h}`,
  `p_{0d,h}`, `p_{dd,h}` uniformly in small `h`.

## What is **not** here

The one-variable functions `u_{0,h}, u_{d,h}` and the corner quotient `Θ_h` of the kernel
decomposition are **still unbounded**.  They are `mfac`
(bounded, by
`KKTFamily.exists_mfac_window`) times a `powDD` — a *second* divided difference of a
coefficient slice — so bounding them needs `powDD_mem_of_powDeriv2_mem` applied to the chain
`A_h → A_h' → A_h''`, i.e. one more differentiation of the slice than is performed here
(`z ↦ z²·J_{p_h}''(x z)`), together with the `J'''` bound `abs_Jp3_le` proved below.  Nothing
in this file is stated conditionally and nothing is weakened: every theorem is an
unconditional identity or an explicit bound.  The constant `Θ_0(u_*,u_*) = d³/4` and the
error estimate `‖Θ_h - d³/4‖_{L^∞(𝓝_ρ²)} ≤ a/8` in the proof of
`lem:central-kernel-bound` are untouched.

## Contents

* `exists_powCoefB_eq_powDeriv`, `powCoefB_mem_of_powDeriv_mem`,
  `abs_powCoefB_le_of_abs_powDeriv_le` — **Target 1**, the first-order mean value theorem in
  the chart and its two-sided form;
* `abs_powDeriv_le`, `abs_powCoefA_le` — the two elementary bookkeeping steps that turn a
  bound on `φ₁` into a bound on `powCoefB`, and a bound on `powCoefB` into one on `powCoefA`;
* `Jp'_eq_Jp'_pStar_add`, `abs_ell_le`, `abs_Jp'_le`, `abs_Jp''_le`, `abs_Jp3_le` — **Target
  2** in exact form on a closed subinterval `[m,M] ⊂ (0,1)`;
* `KKTFamily.exists_abs_Jp'_le`, `KKTFamily.exists_abs_Jp_le` — their uniform-in-`h`
  family versions;
* `KKTFamily.hasDerivAt_kernel_snd`, `.hasDerivAt_kernel_fst`, `.hasDerivAt_mul_Jp'`,
  `.hasDerivAt_kernelCoefA`, `.hasDerivAt_kernelCoefB` — the derivative chains of the kernel,
  of its `x`-derivative slice, and of the two coefficient slices;
* `KKTFamily.exists_kernelCoefA_window`, `.exists_kernelCoefB_window`,
  `.exists_kp00_window`, `.exists_kpd0_window`, `.exists_kp0d_window`, `.exists_kpdd_window` —
  **Target 3**: the four coefficients of `P_h` and the two slices they come from are bounded
  on `𝓝_ρ`, uniformly in small `h`;
* `exists_close_of_continuousAt` — the elementary window helper `|g h - L| ≤ 1` for small `h`,
  also used by `SingularEndpoint/DistributionQuant.lean`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

/-! ## The first-order mean-value theorem in the chart `w = x^d`

`powCoefB d φ s t = (φ(t) - φ(s))/(t^d - s^d)` is the secant slope of `φ` read in the
coordinate `w = x^d`, so Cauchy's mean value theorem for the pair `(φ, z ↦ z^d)` locates it
at an interior point.  This is the first-order sibling of `exists_powResid_bound`. -/

/-- **Cauchy's mean value theorem in the chart `w = x^d`.**  If `φ` has derivative `φ₁` on
`Set.Icc s t` with `0 < s < t`, there is a `ξ` strictly between the nodes with

  `powCoefB d φ s t = powDeriv d φ₁ ξ`.

This is the first-order companion of `exists_powResid_bound` (`SingularEndpoint/PowInterp.lean`); the
missing compensation for the `1/(t^d - s^d)` of `eq:moment-interpolation`.  Only `d ≠ 0` is
required — the second-order statements need `2 ≤ d` because `powDeriv2` differentiates
`x^{d-1}`. -/
theorem exists_powCoefB_eq_powDeriv {d : ℕ} (hd : d ≠ 0) {phi phi1 : ℝ → ℝ} {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (hphi : ∀ y ∈ Set.Icc s t, HasDerivAt phi (phi1 y) y) :
    ∃ ξ ∈ Set.Ioo s t, powCoefB d phi s t = powDeriv d phi1 ξ := by
  have hdR : (0 : ℝ) < (d : ℝ) := by
    have hpos : 0 < d := Nat.pos_of_ne_zero hd
    exact_mod_cast hpos
  have hfc : ContinuousOn phi (Set.Icc s t) := fun y hy =>
    (hphi y hy).continuousAt.continuousWithinAt
  have hgc : ContinuousOn (fun z : ℝ => z ^ d) (Set.Icc s t) := (continuous_pow d).continuousOn
  obtain ⟨c, hc, hval⟩ :=
    exists_ratio_hasDerivAt_eq_ratio_slope phi phi1 hst hfc
      (fun y hy => hphi y (Set.Ioo_subset_Icc_self hy)) (fun z : ℝ => z ^ d)
      (fun z : ℝ => (d : ℝ) * z ^ (d - 1)) hgc (fun y _ => hasDerivAt_pow d y)
  have hval' : (t ^ d - s ^ d) * phi1 c = (phi t - phi s) * ((d : ℝ) * c ^ (d - 1)) := hval
  refine ⟨c, hc, ?_⟩
  have hc0 : 0 < c := hs.trans hc.1
  have hden : (0 : ℝ) < (d : ℝ) * c ^ (d - 1) := mul_pos hdR (pow_pos hc0 _)
  have hD : (0 : ℝ) < t ^ d - s ^ d := sub_pos.mpr (pow_lt_pow_left₀ hst hs.le hd)
  rw [powCoefB, powDeriv, div_eq_div_iff (ne_of_gt hD) (ne_of_gt hden)]
  linear_combination -hval'

/-- **The mean-value bound for `powCoefB` — the first-order sibling of
`powDD_mem_of_powDeriv2_mem`.**  If `φ → φ₁` is a derivative pair on `Set.Icc a b` with
`0 < a` and `m ≤ powDeriv d φ₁ ≤ M` there, then for any two nodes `s < t` of the interval

  `m ≤ powCoefB d φ s t ≤ M`.

Nothing degenerates as `t - s ↓ 0`: the bound is on the secant slope in the chart, which
converges to the tangent slope `powDeriv d φ₁ u_*`. -/
theorem powCoefB_mem_of_powDeriv_mem {d : ℕ} (hd : d ≠ 0) {phi phi1 : ℝ → ℝ} {a b m M : ℝ}
    (ha : 0 < a) (hphi : ∀ y ∈ Set.Icc a b, HasDerivAt phi (phi1 y) y)
    (hm : ∀ y ∈ Set.Icc a b, m ≤ powDeriv d phi1 y)
    (hM : ∀ y ∈ Set.Icc a b, powDeriv d phi1 y ≤ M)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s < t) :
    m ≤ powCoefB d phi s t ∧ powCoefB d phi s t ≤ M := by
  have hsub : Set.Icc s t ⊆ Set.Icc a b := Set.Icc_subset_Icc hs.1 ht.2
  obtain ⟨ξ, hξ, hval⟩ :=
    exists_powCoefB_eq_powDeriv hd (lt_of_lt_of_le ha hs.1) hst fun y hy => hphi y (hsub hy)
  have hmem : ξ ∈ Set.Icc a b := hsub (Set.Ioo_subset_Icc_self hξ)
  rw [hval]
  exact ⟨hm ξ hmem, hM ξ hmem⟩

/-- The absolute-value form of `powCoefB_mem_of_powDeriv_mem`, which is the form every
coefficient bound below consumes. -/
theorem abs_powCoefB_le_of_abs_powDeriv_le {d : ℕ} (hd : d ≠ 0) {phi phi1 : ℝ → ℝ}
    {a b C : ℝ} (ha : 0 < a) (hphi : ∀ y ∈ Set.Icc a b, HasDerivAt phi (phi1 y) y)
    (hC : ∀ y ∈ Set.Icc a b, |powDeriv d phi1 y| ≤ C)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s < t) :
    |powCoefB d phi s t| ≤ C := by
  obtain ⟨hlow, hhigh⟩ :=
    powCoefB_mem_of_powDeriv_mem hd ha hphi (fun y hy => neg_le_of_abs_le (hC y hy))
      (fun y hy => le_of_abs_le (hC y hy)) hs ht hst
  exact abs_le.mpr ⟨hlow, hhigh⟩

/-- **A pointwise bound on `φ₁` becomes one on the chart derivative.**  On `Set.Icc a b` with
`0 < a` the denominator `d x^{d-1}` of `powDeriv` is bounded below by `d a^{d-1} > 0`, so

  `|φ₁(y)| ≤ C`  implies  `|powDeriv d φ₁ y| ≤ C/(d a^{d-1})`.

The degree is symbolic and no degree count is performed. -/
theorem abs_powDeriv_le {d : ℕ} (hd : d ≠ 0) {phi1 : ℝ → ℝ} {a b C y : ℝ} (ha : 0 < a)
    (hy : y ∈ Set.Icc a b) (hC : |phi1 y| ≤ C) :
    |powDeriv d phi1 y| ≤ C / ((d : ℝ) * a ^ (d - 1)) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by
    have hpos : 0 < d := Nat.pos_of_ne_zero hd
    exact_mod_cast hpos
  have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
  have hden0 : (0 : ℝ) < (d : ℝ) * a ^ (d - 1) := mul_pos hdR (pow_pos ha _)
  have hden1 : (0 : ℝ) < (d : ℝ) * y ^ (d - 1) := mul_pos hdR (pow_pos hy0 _)
  have hle : (d : ℝ) * a ^ (d - 1) ≤ (d : ℝ) * y ^ (d - 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hy.1 _) hdR.le
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) hC
  have h1 : |phi1 y| * ((d : ℝ) * a ^ (d - 1)) ≤ C * ((d : ℝ) * a ^ (d - 1)) :=
    mul_le_mul_of_nonneg_right hC hden0.le
  have h2 : C * ((d : ℝ) * a ^ (d - 1)) ≤ C * ((d : ℝ) * y ^ (d - 1)) :=
    mul_le_mul_of_nonneg_left hle hC0
  rw [powDeriv, abs_div, abs_of_pos hden1, div_le_div_iff₀ hden1 hden0]
  linarith

/-- **From `powCoefB` to `powCoefA`.**  The constant coefficient is `φ(s) - B s^d`, so a bound
on the value at the lower node and one on the `x^d` coefficient bound it.  Pure algebra: no
node separation and no differentiability. -/
theorem abs_powCoefA_le {d : ℕ} {phi : ℝ → ℝ} {s t C0 C1 : ℝ} (hs : 0 ≤ s)
    (h0 : |phi s| ≤ C0) (h1 : |powCoefB d phi s t| ≤ C1) :
    |powCoefA d phi s t| ≤ C0 + C1 * s ^ d := by
  have hpow : (0 : ℝ) ≤ s ^ d := pow_nonneg hs d
  have htri := abs_add_le (phi s) (-(powCoefB d phi s t * s ^ d))
  rw [← sub_eq_add_neg, abs_neg, abs_mul, abs_of_nonneg hpow] at htri
  have hmul : |powCoefB d phi s t| * s ^ d ≤ C1 * s ^ d :=
    mul_le_mul_of_nonneg_right h1 hpow
  rw [powCoefA]
  linarith

/-! ## The entropy derivatives near `r_*`

`J_p''(z) = 1/(z(1-z))` and `J_p'''(z) = -1/z² + 1/(1-z)²` do not mention `p` at all — they
are `Jp''` and `Jp3` of `SingularEndpoint/Defs.lean` — so their bounds on a closed subinterval of
`(0,1)` are already uniform in `p`.  Only `J_p'` moves with `p`, and by the displacement
`eq:entropy-parameter-shift` it moves by the **constant** `Λ_p = ℓ(p) - ℓ(p_*)`.  That is what
`Jp'_eq_Jp'_pStar_add` records, and it is why nothing asymptotic is needed. -/

/-- **The first derivative moves by a constant.**  `J_p'(z) = J_{p_*}'(z) + (ℓ(p) - ℓ(p_*))`
on `(0,1)`: the derivative form of `eq:entropy-parameter-shift`.  Both sides are `ℓ(p) - ℓ(z)` up to
the bookkeeping of `Jp'_eq_ell_sub`. -/
theorem Jp'_eq_Jp'_pStar_add {d : ℕ} (hd : 2 ≤ d) {p z : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hz0 : 0 < z) (hz1 : z < 1) :
    Jp' p z = Jp' (pStar d) z + (ell p - ell (pStar d)) := by
  rw [Jp'_eq_ell_sub hp0 hp1 hz0 hz1,
    Jp'_eq_ell_sub (pStar_pos hd) (pStar_lt_one hd) hz0 hz1]
  ring

/-- The log-odds is bounded on a closed subinterval of `(0,1)`, with the explicit bound
`|ℓ(z)| ≤ |log m| + |log(1-M)|`: on `[m,M]` both `log z` and `log(1-z)` are nonpositive and
bounded below by their values at the endpoints. -/
theorem abs_ell_le {m M z : ℝ} (hm : 0 < m) (hM : M < 1) (hz : z ∈ Set.Icc m M) :
    |ell z| ≤ |Real.log m| + |Real.log (1 - M)| := by
  have hz1 : m ≤ z := hz.1
  have hz2 : z ≤ M := hz.2
  have hz0 : 0 < z := lt_of_lt_of_le hm hz1
  have hzu : z < 1 := lt_of_le_of_lt hz2 hM
  have hm1 : m < 1 := lt_of_le_of_lt hz1 hzu
  have hM0 : 0 < M := lt_of_lt_of_le hz0 hz2
  have hlz : Real.log m ≤ Real.log z := Real.log_le_log hm hz1
  have hlz0 : Real.log z ≤ 0 := Real.log_nonpos hz0.le hzu.le
  have hlm : Real.log m ≤ 0 := Real.log_nonpos hm.le hm1.le
  have hw : Real.log (1 - M) ≤ Real.log (1 - z) :=
    Real.log_le_log (by linarith) (by linarith)
  have hw0 : Real.log (1 - z) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hwM : Real.log (1 - M) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have habs1 : |Real.log m| = -Real.log m := abs_of_nonpos hlm
  have habs2 : |Real.log (1 - M)| = -Real.log (1 - M) := abs_of_nonpos hwM
  have hell : ell z = Real.log (1 - z) - Real.log z := by
    rw [ell, Real.log_div (ne_of_gt (by linarith : (0 : ℝ) < 1 - z)) (ne_of_gt hz0)]
  rw [hell, habs1, habs2, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **`|J_p'|` on a closed subinterval of `(0,1)`**, with an explicit constant: by
`Jp'_eq_ell_sub` the derivative is `ℓ(p) - ℓ(z)`, and `abs_ell_le` bounds the second term. -/
theorem abs_Jp'_le {p m M z : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hm : 0 < m) (hM : M < 1)
    (hz : z ∈ Set.Icc m M) :
    |Jp' p z| ≤ |ell p| + (|Real.log m| + |Real.log (1 - M)|) := by
  have hz0 : 0 < z := lt_of_lt_of_le hm hz.1
  have hz1 : z < 1 := lt_of_le_of_lt hz.2 hM
  have htri := abs_add_le (ell p) (-(ell z))
  rw [← sub_eq_add_neg, abs_neg] at htri
  rw [Jp'_eq_ell_sub hp0 hp1 hz0 hz1]
  linarith [abs_ell_le hm hM hz]

/-- **`|J_p''|` on a closed subinterval of `(0,1)`**: `J_p'' = 1/(z(1-z))` is `p`-free and
positive, and `z(1-z) ≥ m(1-M)` on `[m,M]`. -/
theorem abs_Jp''_le {m M z : ℝ} (hm : 0 < m) (hM : M < 1) (hz : z ∈ Set.Icc m M) :
    |Jp'' z| ≤ 1 / (m * (1 - M)) := by
  have hz0 : 0 < z := lt_of_lt_of_le hm hz.1
  have hz1 : z < 1 := lt_of_le_of_lt hz.2 hM
  have hpos : 0 < Jp'' z := Jp''_pos hz0 hz1
  have hden : 0 < m * (1 - M) := mul_pos hm (by linarith)
  have h1 : m * (1 - M) ≤ m * (1 - z) :=
    mul_le_mul_of_nonneg_left (by linarith [hz.2]) hm.le
  have h2 : m * (1 - z) ≤ z * (1 - z) :=
    mul_le_mul_of_nonneg_right hz.1 (by linarith)
  rw [abs_of_pos hpos, Jp'']
  exact one_div_le_one_div_of_le hden (by linarith)

/-- **`|J_p'''|` on a closed subinterval of `(0,1)`**: `J_p''' = -1/z² + 1/(1-z)²` is `p`-free
and each summand is bounded by its value at the nearer endpoint.  This is the third of the
three uniform derivative bounds; it is what a second-order treatment of `u_{0,h}, u_{d,h}`
would consume. -/
theorem abs_Jp3_le {m M z : ℝ} (hm : 0 < m) (hM : M < 1) (hz : z ∈ Set.Icc m M) :
    |Jp3 z| ≤ 1 / m ^ 2 + 1 / (1 - M) ^ 2 := by
  have hz0 : 0 < z := lt_of_lt_of_le hm hz.1
  have hz1 : z < 1 := lt_of_le_of_lt hz.2 hM
  have hsz : (0 : ℝ) < 1 - z := by linarith
  have hsM : (0 : ℝ) < 1 - M := by linarith
  have e1 : (0 : ℝ) < 1 / z ^ 2 := div_pos one_pos (pow_pos hz0 2)
  have e2 : (0 : ℝ) < 1 / (1 - z) ^ 2 := div_pos one_pos (pow_pos hsz 2)
  have b1 : 1 / z ^ 2 ≤ 1 / m ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hm 2) (pow_le_pow_left₀ hm.le hz.1 2)
  have b2 : 1 / (1 - z) ^ 2 ≤ 1 / (1 - M) ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hsM 2) (pow_le_pow_left₀ hsM.le (by linarith [hz.2]) 2)
  rw [Jp3, abs_le]
  exact ⟨by linarith, by linarith⟩

/-! ## Two elementary window helpers -/

/-- A quantity that is continuous at the origin stays within `1` of its value there, for all
small `h`.  Used twice below, for `h ↦ ℓ(p_h)` and for `h ↦ J_{p_h}(0)` — the two coefficients
`Λ_h`, `C_h` of `eq:entropy-parameter-shift` — and again, at `L = 0`, in
`SingularEndpoint/DistributionQuant.lean`. -/
theorem exists_close_of_continuousAt {g : ℝ → ℝ} {L : ℝ} (hg : ContinuousAt g 0)
    (hL : g 0 = L) : ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → |g h - L| ≤ 1 := by
  have htend : Tendsto g (𝓝 0) (𝓝 L) := by
    rw [← hL]
    exact hg.tendsto
  have hev : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), |g h - L| < 1 := by
    have h := Metric.tendsto_nhds.mp htend 1 one_pos
    simpa [Real.dist_eq] using h
  obtain ⟨δ, hδ, hprop⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨δ, hδ, fun h hh => (hprop (by rwa [Real.dist_eq, sub_zero])).le⟩

/-- A factor from a positive window multiplies a bounded quantity to a bounded one. -/
private theorem abs_mul_le_window {A Bb C x w : ℝ} (hA : 0 < A) (hx : x ∈ Set.Icc A Bb)
    (hw : |w| ≤ C) : |x * w| ≤ Bb * C := by
  have hx0 : 0 < x := lt_of_lt_of_le hA hx.1
  have hBb0 : (0 : ℝ) ≤ Bb := le_trans hx0.le hx.2
  rw [abs_mul, abs_of_pos hx0]
  exact mul_le_mul hx.2 hw (abs_nonneg w) hBb0

/-- Two factors from a positive window multiply a bounded quantity to a bounded one. -/
private theorem abs_mul_mul_le_window {A Bb C x y w : ℝ} (hA : 0 < A) (hx : x ∈ Set.Icc A Bb)
    (hy : y ∈ Set.Icc A Bb) (hw : |w| ≤ C) : |x * y * w| ≤ Bb * Bb * C := by
  have hx0 : 0 < x := lt_of_lt_of_le hA hx.1
  have hy0 : 0 < y := lt_of_lt_of_le hA hy.1
  have hBb0 : (0 : ℝ) ≤ Bb := le_trans hx0.le hx.2
  have hxy : x * y ≤ Bb * Bb := mul_le_mul hx.2 hy.2 hy0.le hBb0
  rw [abs_mul, abs_mul, abs_of_pos hx0, abs_of_pos hy0]
  exact mul_le_mul hxy hw (abs_nonneg w) (mul_nonneg hBb0 hBb0)

namespace KKTFamily

variable {d : ℕ}

/-! ## The uniform entropy bounds along the family -/

/-- **`|J_{p_h}'|` is bounded on a fixed closed subinterval of `(0,1)`, uniformly in small
`h`.**  Explicitly one may take `C = |ℓ(p_*)| + |log m| + |log(1-M)| + 1`: by
`Jp'_eq_Jp'_pStar_add` the family derivative differs from the singular endpoint one by the constant
`Λ_h = ℓ(p_h) - ℓ(p_*)`, which is at most `1` once `h` is small.  Nothing asymptotic and no
compactness argument is involved. -/
theorem exists_abs_Jp'_le (hd : 2 ≤ d) (B : KKTFamily d) {m M : ℝ} (hm : 0 < m)
    (hM : M < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      ∀ z ∈ Set.Icc m M, |Jp' (B.p h) z| ≤ C := by
  have hp0 : 0 < pStar d := pStar_pos hd
  have hp1 : pStar d < 1 := pStar_lt_one hd
  have hcomp : ContinuousAt (fun h : ℝ => ell (B.p h)) 0 := ell_p_continuousAt hd B
  obtain ⟨δ₁, hδ₁, hclose⟩ := exists_close_of_continuousAt hcomp (by rw [B.p_zero])
  refine ⟨|ell (pStar d)| + (|Real.log m| + |Real.log (1 - M)|) + 1, ?_, min δ₁ B.h₀,
    lt_min hδ₁ B.h₀_pos, ?_⟩
  · have h1 := abs_nonneg (ell (pStar d))
    have h2 := abs_nonneg (Real.log m)
    have h3 := abs_nonneg (Real.log (1 - M))
    linarith
  · intro h hh z hz
    have hh1 : |h| < δ₁ := lt_of_lt_of_le hh (min_le_left _ _)
    have hh2 : |h| < B.h₀ := lt_of_lt_of_le hh (min_le_right _ _)
    have hp := B.p_mem h hh2
    have hz0 : 0 < z := lt_of_lt_of_le hm hz.1
    have hz1 : z < 1 := lt_of_le_of_lt hz.2 hM
    have hbase := abs_Jp'_le hp0 hp1 hm hM hz
    have htri := abs_add_le (Jp' (pStar d) z) (ell (B.p h) - ell (pStar d))
    rw [Jp'_eq_Jp'_pStar_add hd hp.1 hp.2 hz0 hz1]
    linarith [hclose h hh1]

/-- **`|J_{p_h}|` is bounded on `[0,1]`, uniformly in small `h`.**  Here the displacement
`eq:entropy-parameter-shift` is used in full: `J_{p_h} = J_{p_*} + Λ_h z + C_h` with both `Λ_h` and
`C_h` at most `1` for small `h`, and `J_{p_*}` bounded on the compact `[0,1]`.  This is the
one compactness argument of the file; it bounds the entropy itself, for which no closed
formula is wanted. -/
theorem exists_abs_Jp_le (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      ∀ z ∈ Set.Icc (0 : ℝ) 1, |Jp (B.p h) z| ≤ C := by
  have hp0 : 0 < pStar d := pStar_pos hd
  have hp1 : pStar d < 1 := pStar_lt_one hd
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (continuousOn_Jp_Icc hp0 hp1)
  have hC₀0 : (0 : ℝ) ≤ C₀ := by
    have h := hC₀ 0 ⟨le_rfl, zero_le_one⟩
    exact le_trans (norm_nonneg _) h
  have hcomp : ContinuousAt (fun h : ℝ => ell (B.p h)) 0 := ell_p_continuousAt hd B
  obtain ⟨δ₁, hδ₁, hL⟩ := exists_close_of_continuousAt hcomp (by rw [B.p_zero])
  have hzero : ContinuousAt (fun h : ℝ => Jp (B.p h) 0) 0 := Jp_p_zero_continuousAt hd B
  obtain ⟨δ₂, hδ₂, hK⟩ := exists_close_of_continuousAt hzero (by rw [B.p_zero])
  refine ⟨C₀ + 2, by linarith, min (min δ₁ δ₂) B.h₀, lt_min (lt_min hδ₁ hδ₂) B.h₀_pos, ?_⟩
  intro h hh z hz
  have hh1 : |h| < δ₁ := lt_of_lt_of_le hh (le_trans (min_le_left _ _) (min_le_left _ _))
  have hh2 : |h| < δ₂ := lt_of_lt_of_le hh (le_trans (min_le_left _ _) (min_le_right _ _))
  have hh3 : |h| < B.h₀ := lt_of_lt_of_le hh (min_le_right _ _)
  have hp := B.p_mem h hh3
  have hbase : |Jp (pStar d) z| ≤ C₀ := by
    have h := hC₀ z hz
    rwa [Real.norm_eq_abs] at h
  have hlam : |ell (B.p h) - ell (pStar d)| ≤ 1 := hL h hh1
  have hcst : |Jp (B.p h) 0 - Jp (pStar d) 0| ≤ 1 := hK h hh2
  have hdis : Jp (B.p h) z
      = Jp (pStar d) z + (ell (B.p h) - ell (pStar d)) * z + (Jp (B.p h) 0 - Jp (pStar d) 0) :=
    Jp_eq_Jp_pStar_add hd hp.1 hp.2 hz.1 hz.2
  have hprod : |(ell (B.p h) - ell (pStar d)) * z| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hz.1]
    have := mul_le_mul hlam hz.2 hz.1 (by linarith [abs_nonneg (ell (B.p h) - ell (pStar d))])
    linarith
  have ht1 := abs_add_le (Jp (pStar d) z + (ell (B.p h) - ell (pStar d)) * z)
    (Jp (B.p h) 0 - Jp (pStar d) 0)
  have ht2 := abs_add_le (Jp (pStar d) z) ((ell (B.p h) - ell (pStar d)) * z)
  rw [hdis]
  linarith

/-! ## The derivative chains of the kernel and of its coefficient slices -/

/-- **The kernel slice is differentiable in the free variable**: for `0 < xz < 1`,
`z ↦ K_h(x,z) = J_{p_h}(xz)` has derivative `x·J_{p_h}'(xz)`.  The chain rule through the
inner map `w ↦ xw`. -/
theorem hasDerivAt_kernel_snd (B : KKTFamily d) {h x z : ℝ} (hp0 : 0 < B.p h)
    (hp1 : B.p h < 1) (h0 : 0 < x * z) (h1 : x * z < 1) :
    HasDerivAt (fun w : ℝ => B.kernel h x w) (x * Jp' (B.p h) (x * z)) z := by
  have hinner : HasDerivAt (fun w : ℝ => x * w) x z := by
    simpa using (hasDerivAt_id z).const_mul x
  have hcomp := (hasDerivAt_Jp hp0 hp1 h0 h1).comp z hinner
  have hfun : (Jp (B.p h) ∘ fun w : ℝ => x * w) = fun w : ℝ => B.kernel h x w := rfl
  rw [hfun] at hcomp
  exact hcomp.congr_deriv (by ring)

/-- The `x`-derivative of the kernel slice at a frozen second argument `z`, as a function of
`z`: `∂₁K_h(x,z) = z·J_{p_h}'(xz)`.  It is this function of `z` whose interpolation
coefficients are the derivatives of `A_h` and `B_h`. -/
theorem hasDerivAt_kernel_fst (B : KKTFamily d) {h x z : ℝ} (hp0 : 0 < B.p h)
    (hp1 : B.p h < 1) (h0 : 0 < x * z) (h1 : x * z < 1) :
    HasDerivAt (fun w : ℝ => Jp (B.p h) (w * z)) (z * Jp' (B.p h) (x * z)) x := by
  have hinner : HasDerivAt (fun w : ℝ => w * z) z x := by
    simpa using (hasDerivAt_id x).mul_const z
  have hcomp := (hasDerivAt_Jp hp0 hp1 h0 h1).comp x hinner
  have hfun : (Jp (B.p h) ∘ fun w : ℝ => w * z) = fun w : ℝ => Jp (B.p h) (w * z) := rfl
  rw [hfun] at hcomp
  exact hcomp.congr_deriv (by ring)

/-- The `z`-derivative of the differentiated slice `z ↦ z·J_{p_h}'(xz)`, by the product
rule.  It is the function whose `powDeriv` bounds the interpolation coefficients of the
differentiated slice. -/
theorem hasDerivAt_mul_Jp' (B : KKTFamily d) {h x z : ℝ} (hp0 : 0 < B.p h)
    (hp1 : B.p h < 1) (h0 : 0 < x * z) (h1 : x * z < 1) :
    HasDerivAt (fun w : ℝ => w * Jp' (B.p h) (x * w))
      (Jp' (B.p h) (x * z) + z * x * Jp'' (x * z)) z := by
  have hinner : HasDerivAt (fun w : ℝ => x * w) x z := by
    simpa using (hasDerivAt_id z).const_mul x
  have hcomp := (hasDerivAt_Jp' hp0 hp1 h0 h1).comp z hinner
  have hfun : (Jp' (B.p h) ∘ fun w : ℝ => x * w) = fun w : ℝ => Jp' (B.p h) (x * w) := rfl
  rw [hfun] at hcomp
  exact ((hasDerivAt_id' (x := z)).mul hcomp).congr_deriv (by ring)

/-- **Differentiating the constant coefficient slice.**  `A_h(x)` is a *fixed* linear
combination of the two node values `K_h(x,s_h)`, `K_h(x,t_h)`, so its `x`-derivative is the
same combination of the differentiated slice:

  `A_h'(x) = powCoefA d (z ↦ z J_{p_h}'(xz)) s_h t_h`.

This is what lets the first-order mean value theorem be applied a *second* time, in the
frozen variable, and is exactly the step the coefficient bounds in the proof of
`lem:central-kernel-bound` need. -/
theorem hasDerivAt_kernelCoefA (B : KKTFamily d) {h x : ℝ} (hp0 : 0 < B.p h)
    (hp1 : B.p h < 1) (hs0 : 0 < x * B.sVal h) (hs1 : x * B.sVal h < 1)
    (ht0 : 0 < x * B.tVal h) (ht1 : x * B.tVal h < 1) :
    HasDerivAt (B.kernelCoefA h)
      (powCoefA d (fun z => z * Jp' (B.p h) (x * z)) (B.sVal h) (B.tVal h)) x := by
  have hS := hasDerivAt_kernel_fst B hp0 hp1 hs0 hs1
  have hT := hasDerivAt_kernel_fst B hp0 hp1 ht0 ht1
  exact hS.sub
    (((hT.sub hS).div_const (B.tVal h ^ d - B.sVal h ^ d)).mul_const (B.sVal h ^ d))

/-- **Differentiating the `y^d` coefficient slice**, the companion of
`hasDerivAt_kernelCoefA`:

  `B_h'(x) = powCoefB d (z ↦ z J_{p_h}'(xz)) s_h t_h`. -/
theorem hasDerivAt_kernelCoefB (B : KKTFamily d) {h x : ℝ} (hp0 : 0 < B.p h)
    (hp1 : B.p h < 1) (hs0 : 0 < x * B.sVal h) (hs1 : x * B.sVal h < 1)
    (ht0 : 0 < x * B.tVal h) (ht1 : x * B.tVal h < 1) :
    HasDerivAt (B.kernelCoefB h)
      (powCoefB d (fun z => z * Jp' (B.p h) (x * z)) (B.sVal h) (B.tVal h)) x := by
  have hS := hasDerivAt_kernel_fst B hp0 hp1 hs0 hs1
  have hT := hasDerivAt_kernel_fst B hp0 hp1 ht0 ht1
  exact (hT.sub hS).div_const (B.tVal h ^ d - B.sVal h ^ d)

/-! ## The window package

Everything the coefficient bounds need about a small `h`, collected once: the nodes are inside
the window, and the three entropy quantities are bounded on the product of the window with
itself.  The two smallness hypotheses on `ρ` say that `𝓝_ρ ⊂ (0,1)` with room to square. -/

/-- The uniform data attached to the central window: a single constant `C ≥ 1` bounding
`|J_{p_h}|`, `|J_{p_h}'|` and `|J_{p_h}''|` at every product `xz` of two window points, valid
for every `0 < h < δ`, together with the fact that both nodes lie in the window. -/
private theorem exists_window_package (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      |h| < B.h₀ ∧ B.sVal h ∈ centralWindow d ρ ∧ B.tVal h ∈ centralWindow d ρ ∧
        ∀ x ∈ centralWindow d ρ, ∀ z ∈ centralWindow d ρ,
          0 < x * z ∧ x * z < 1 ∧ |Jp (B.p h) (x * z)| ≤ C ∧
            |Jp' (B.p h) (x * z)| ≤ C ∧ |Jp'' (x * z)| ≤ C := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  have hA : 0 < uStar d - ρ := by linarith
  have hB1 : uStar d + ρ < 1 := by linarith
  have hB0 : (0 : ℝ) < uStar d + ρ := by linarith
  have hmm : 0 < (uStar d - ρ) * (uStar d - ρ) := mul_pos hA hA
  have hMM : (uStar d + ρ) * (uStar d + ρ) < 1 := by nlinarith
  obtain ⟨C₁, hC₁, δ₁, hδ₁, hJ1⟩ := exists_abs_Jp'_le hd B hmm hMM
  obtain ⟨C₀, hC₀, δ₀, hδ₀, hJ0⟩ := exists_abs_Jp_le hd B
  obtain ⟨δ₂, hδ₂, hatoms⟩ := exists_atoms_mem_centralWindow B hρ
  refine ⟨max C₀ (max C₁ (max (1 / ((uStar d - ρ) * (uStar d - ρ)
      * (1 - (uStar d + ρ) * (uStar d + ρ)))) 1)),
    le_max_of_le_right (le_max_of_le_right (le_max_right _ _)),
    min (min δ₀ δ₁) (min δ₂ B.h₀), lt_min (lt_min hδ₀ hδ₁) (lt_min hδ₂ B.h₀_pos), ?_⟩
  intro h hh0 hhδ
  have habs : |h| = h := abs_of_pos hh0
  have hd0 : |h| < δ₀ := by
    rw [habs]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hd1 : |h| < δ₁ := by
    rw [habs]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hd2 : h < δ₂ := lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdb : |h| < B.h₀ := by
    rw [habs]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hsmem, htmem⟩ := hatoms h hh0 hd2
  refine ⟨hdb, hsmem, htmem, ?_⟩
  intro x hx z hz
  have hx' : x ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hx
  have hz' : z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hz
  have hx0 : 0 < x := lt_of_lt_of_le hA hx'.1
  have hz0 : 0 < z := lt_of_lt_of_le hA hz'.1
  have hlow : (uStar d - ρ) * (uStar d - ρ) ≤ x * z :=
    mul_le_mul hx'.1 hz'.1 hA.le hx0.le
  have hhigh : x * z ≤ (uStar d + ρ) * (uStar d + ρ) :=
    mul_le_mul hx'.2 hz'.2 hz0.le hB0.le
  have hmem : x * z ∈ Set.Icc ((uStar d - ρ) * (uStar d - ρ)) ((uStar d + ρ) * (uStar d + ρ)) :=
    ⟨hlow, hhigh⟩
  have hpos : 0 < x * z := mul_pos hx0 hz0
  have hlt1 : x * z < 1 := lt_of_le_of_lt hhigh hMM
  refine ⟨hpos, hlt1, ?_, ?_, ?_⟩
  · exact le_trans (hJ0 h hd0 (x * z) ⟨hpos.le, hlt1.le⟩) (le_max_left _ _)
  · exact le_trans (hJ1 h hd1 (x * z) hmem) (le_max_of_le_right (le_max_left _ _))
  · exact le_trans (abs_Jp''_le hmm hMM hmem)
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))

/-! ## The coefficient bounds

Every bound below has the same three-step shape: a derivative chain for the function being
interpolated, `abs_powDeriv_le` to convert a bound on that derivative into one on the chart
derivative, and `abs_powCoefB_le_of_abs_powDeriv_le` (Target 1) to reach the coefficient.
`abs_powCoefA_le` then converts the `x^d` coefficient into the constant one. -/

/-- **The `y^d` coefficient slice `B_h` is bounded on the window, uniformly in small `h`.**
By the first-order mean value theorem `B_h(x)` is `x J_{p_h}'(xξ)/(d ξ^{d-1})` at some `ξ`
between the nodes, and every factor is controlled by the window package. -/
theorem exists_kernelCoefB_window (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ x ∈ centralWindow d ρ, |B.kernelCoefB h x| ≤ C := by
  have hd0 : d ≠ 0 := by omega
  have hu0 : 0 < uStar d := uStar_pos hd
  have hA : 0 < uStar d - ρ := by linarith
  have hB0 : (0 : ℝ) < uStar d + ρ := by linarith
  have hE : (0 : ℝ) < (d : ℝ) * (uStar d - ρ) ^ (d - 1) := mul_pos (dpos hd) (pow_pos hA _)
  obtain ⟨C, hC, δ, hδ, hpack⟩ := exists_window_package hd B hρ hρu hρ1
  refine ⟨(uStar d + ρ) * C / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)),
    div_pos (mul_pos hB0 (by linarith)) hE, δ, hδ, ?_⟩
  intro h hh0 hhδ x hx
  obtain ⟨hhb, hsmem, htmem, hbnd⟩ := hpack h hh0 hhδ
  have hp := B.p_mem h hhb
  have hsmem' : B.sVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hsmem
  have htmem' : B.tVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := htmem
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hh0
  refine abs_powCoefB_le_of_abs_powDeriv_le (d := d) (phi1 := fun z => x * Jp' (B.p h) (x * z))
    hd0 hA ?_ ?_ hsmem' htmem' hst
  · intro y hy
    obtain ⟨h0, h1, _, _, _⟩ := hbnd x hx y hy
    exact hasDerivAt_kernel_snd B hp.1 hp.2 h0 h1
  · intro y hy
    obtain ⟨_, _, _, hJ1, _⟩ := hbnd x hx y hy
    exact abs_powDeriv_le hd0 hA hy (abs_mul_le_window hA hx hJ1)

/-- **The constant coefficient slice `A_h` is bounded on the window, uniformly in small `h`.**
`A_h(x) = K_h(x,s_h) - B_h(x)s_h^d`, so `abs_powCoefA_le` combines the entropy bound of the
window package with `exists_kernelCoefB_window`. -/
theorem exists_kernelCoefA_window (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ x ∈ centralWindow d ρ, |B.kernelCoefA h x| ≤ C := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hA : 0 < uStar d - ρ := by linarith
  have hB0 : (0 : ℝ) < uStar d + ρ := by linarith
  obtain ⟨C, hC, δ, hδ, hpack⟩ := exists_window_package hd B hρ hρu hρ1
  obtain ⟨CB, hCB, δB, hδB, hbB⟩ := exists_kernelCoefB_window hd B hρ hρu hρ1
  have hnum : (0 : ℝ) < C + CB * (uStar d + ρ) ^ d := by
    have h1 : (0 : ℝ) ≤ CB * (uStar d + ρ) ^ d := mul_nonneg hCB.le (pow_nonneg hB0.le d)
    linarith
  refine ⟨C + CB * (uStar d + ρ) ^ d, hnum, min δ δB, lt_min hδ hδB, ?_⟩
  intro h hh0 hhδ x hx
  have hhδ1 : h < δ := lt_of_lt_of_le hhδ (min_le_left _ _)
  have hhδ2 : h < δB := lt_of_lt_of_le hhδ (min_le_right _ _)
  obtain ⟨hhb, hsmem, htmem, hbnd⟩ := hpack h hh0 hhδ1
  have hsmem' : B.sVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hsmem
  have hs0 : 0 < B.sVal h := lt_of_lt_of_le hA hsmem'.1
  obtain ⟨_, _, hJ0, _, _⟩ := hbnd x hx (B.sVal h) hsmem
  have hval : |B.kernel h x (B.sVal h)| ≤ C := hJ0
  have hBb : |powCoefB d (fun z => B.kernel h x z) (B.sVal h) (B.tVal h)| ≤ CB :=
    hbB h hh0 hhδ2 x hx
  have hkey : |B.kernelCoefA h x| ≤ C + CB * B.sVal h ^ d :=
    abs_powCoefA_le (d := d) (phi := fun z => B.kernel h x z) hs0.le hval hBb
  have hpow : B.sVal h ^ d ≤ (uStar d + ρ) ^ d := pow_le_pow_left₀ hs0.le hsmem'.2 d
  have hmul : CB * B.sVal h ^ d ≤ CB * (uStar d + ρ) ^ d :=
    mul_le_mul_of_nonneg_left hpow hCB.le
  linarith

/-- **The coefficient `p_{dd,h}` of the kernel decomposition is bounded, uniformly in
small `h`.**  `p_{dd,h}` is the `x^d` coefficient of the slice `B_h`, whose derivative is by
`hasDerivAt_kernelCoefB` the corresponding coefficient of `z ↦ z J_{p_h}'(xz)`; the first-order
mean value theorem is therefore applied twice, once in each variable. -/
theorem exists_kpdd_window (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → |B.kpdd h| ≤ C := by
  have hd0 : d ≠ 0 := by omega
  have hu0 : 0 < uStar d := uStar_pos hd
  have hA : 0 < uStar d - ρ := by linarith
  have hB0 : (0 : ℝ) < uStar d + ρ := by linarith
  have hE : (0 : ℝ) < (d : ℝ) * (uStar d - ρ) ^ (d - 1) := mul_pos (dpos hd) (pow_pos hA _)
  obtain ⟨C, hC, δ, hδ, hpack⟩ := exists_window_package hd B hρ hρu hρ1
  have hnum : (0 : ℝ) < C + (uStar d + ρ) * (uStar d + ρ) * C := by
    have h1 : (0 : ℝ) ≤ (uStar d + ρ) * (uStar d + ρ) * C :=
      mul_nonneg (mul_nonneg hB0.le hB0.le) (by linarith)
    linarith
  refine ⟨(C + (uStar d + ρ) * (uStar d + ρ) * C) / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))
      / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)),
    div_pos (div_pos hnum hE) hE, δ, hδ, ?_⟩
  intro h hh0 hhδ
  obtain ⟨hhb, hsmem, htmem, hbnd⟩ := hpack h hh0 hhδ
  have hp := B.p_mem h hhb
  have hsmem' : B.sVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hsmem
  have htmem' : B.tVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := htmem
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hh0
  -- the inner bound: the coefficients of the differentiated slice
  have hinner : ∀ y ∈ centralWindow d ρ,
      |powCoefB d (fun z => z * Jp' (B.p h) (y * z)) (B.sVal h) (B.tVal h)|
        ≤ (C + (uStar d + ρ) * (uStar d + ρ) * C)
            / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) := by
    intro y hy
    refine abs_powCoefB_le_of_abs_powDeriv_le (d := d)
      (phi1 := fun z => Jp' (B.p h) (y * z) + z * y * Jp'' (y * z)) hd0 hA ?_ ?_ hsmem'
      htmem' hst
    · intro w hw
      obtain ⟨h0, h1, _, _, _⟩ := hbnd y hy w hw
      exact hasDerivAt_mul_Jp' B hp.1 hp.2 h0 h1
    · intro w hw
      obtain ⟨_, _, _, hJ1, hJ2⟩ := hbnd y hy w hw
      refine abs_powDeriv_le hd0 hA hw ?_
      exact le_trans (abs_add_le _ _)
        (add_le_add hJ1 (abs_mul_mul_le_window hA hw hy hJ2))
  -- the outer step, in the frozen variable
  refine abs_powCoefB_le_of_abs_powDeriv_le (d := d)
    (phi1 := fun y => powCoefB d (fun z => z * Jp' (B.p h) (y * z)) (B.sVal h) (B.tVal h))
    hd0 hA ?_ ?_ hsmem' htmem' hst
  · intro y hy
    obtain ⟨hs0, hs1, _, _, _⟩ := hbnd y hy (B.sVal h) hsmem
    obtain ⟨ht0, ht1, _, _, _⟩ := hbnd y hy (B.tVal h) htmem
    exact hasDerivAt_kernelCoefB B hp.1 hp.2 hs0 hs1 ht0 ht1
  · intro y hy
    exact abs_powDeriv_le hd0 hA hy (hinner y hy)

/-- **The coefficient `p_{d0,h}` is bounded, uniformly in small `h`.**  Same two applications
of the first-order mean value theorem as for `p_{dd,h}`, with `powCoefA` in the inner step:
the derivative of `A_h` is the constant coefficient of the differentiated slice. -/
theorem exists_kpd0_window (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → |B.kpd0 h| ≤ C := by
  have hd0 : d ≠ 0 := by omega
  have hu0 : 0 < uStar d := uStar_pos hd
  have hA : 0 < uStar d - ρ := by linarith
  have hB0 : (0 : ℝ) < uStar d + ρ := by linarith
  have hE : (0 : ℝ) < (d : ℝ) * (uStar d - ρ) ^ (d - 1) := mul_pos (dpos hd) (pow_pos hA _)
  obtain ⟨C, hC, δ, hδ, hpack⟩ := exists_window_package hd B hρ hρu hρ1
  have hnum : (0 : ℝ) < C + (uStar d + ρ) * (uStar d + ρ) * C := by
    have h1 : (0 : ℝ) ≤ (uStar d + ρ) * (uStar d + ρ) * C :=
      mul_nonneg (mul_nonneg hB0.le hB0.le) (by linarith)
    linarith
  have hK : (0 : ℝ) < (C + (uStar d + ρ) * (uStar d + ρ) * C)
      / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) := div_pos hnum hE
  have hnum2 : (0 : ℝ) < (uStar d + ρ) * C + (C + (uStar d + ρ) * (uStar d + ρ) * C)
      / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) * (uStar d + ρ) ^ d := by
    have h1 : (0 : ℝ) < (uStar d + ρ) * C := mul_pos hB0 (by linarith)
    have h2 : (0 : ℝ) ≤ (C + (uStar d + ρ) * (uStar d + ρ) * C)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) * (uStar d + ρ) ^ d :=
      mul_nonneg hK.le (pow_nonneg hB0.le d)
    linarith
  refine ⟨((uStar d + ρ) * C + (C + (uStar d + ρ) * (uStar d + ρ) * C)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) * (uStar d + ρ) ^ d)
      / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)),
    div_pos hnum2 hE, δ, hδ, ?_⟩
  intro h hh0 hhδ
  obtain ⟨hhb, hsmem, htmem, hbnd⟩ := hpack h hh0 hhδ
  have hp := B.p_mem h hhb
  have hsmem' : B.sVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hsmem
  have htmem' : B.tVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := htmem
  have hs0 : 0 < B.sVal h := lt_of_lt_of_le hA hsmem'.1
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hh0
  have hinner : ∀ y ∈ centralWindow d ρ,
      |powCoefB d (fun z => z * Jp' (B.p h) (y * z)) (B.sVal h) (B.tVal h)|
        ≤ (C + (uStar d + ρ) * (uStar d + ρ) * C)
            / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) := by
    intro y hy
    refine abs_powCoefB_le_of_abs_powDeriv_le (d := d)
      (phi1 := fun z => Jp' (B.p h) (y * z) + z * y * Jp'' (y * z)) hd0 hA ?_ ?_ hsmem'
      htmem' hst
    · intro w hw
      obtain ⟨h0, h1, _, _, _⟩ := hbnd y hy w hw
      exact hasDerivAt_mul_Jp' B hp.1 hp.2 h0 h1
    · intro w hw
      obtain ⟨_, _, _, hJ1, hJ2⟩ := hbnd y hy w hw
      refine abs_powDeriv_le hd0 hA hw ?_
      exact le_trans (abs_add_le _ _)
        (add_le_add hJ1 (abs_mul_mul_le_window hA hw hy hJ2))
  have hinnerA : ∀ y ∈ centralWindow d ρ,
      |powCoefA d (fun z => z * Jp' (B.p h) (y * z)) (B.sVal h) (B.tVal h)|
        ≤ (uStar d + ρ) * C + (C + (uStar d + ρ) * (uStar d + ρ) * C)
            / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) * (uStar d + ρ) ^ d := by
    intro y hy
    obtain ⟨_, _, _, hJ1, _⟩ := hbnd y hy (B.sVal h) hsmem
    have hnode : |B.sVal h * Jp' (B.p h) (y * B.sVal h)| ≤ (uStar d + ρ) * C :=
      abs_mul_le_window hA hsmem' hJ1
    have hkey := abs_powCoefA_le (d := d) (phi := fun z => z * Jp' (B.p h) (y * z)) hs0.le
      hnode (hinner y hy)
    have hpow : B.sVal h ^ d ≤ (uStar d + ρ) ^ d := pow_le_pow_left₀ hs0.le hsmem'.2 d
    have hmul : (C + (uStar d + ρ) * (uStar d + ρ) * C)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) * B.sVal h ^ d
        ≤ (C + (uStar d + ρ) * (uStar d + ρ) * C)
          / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) * (uStar d + ρ) ^ d :=
      mul_le_mul_of_nonneg_left hpow hK.le
    linarith
  refine abs_powCoefB_le_of_abs_powDeriv_le (d := d)
    (phi1 := fun y => powCoefA d (fun z => z * Jp' (B.p h) (y * z)) (B.sVal h) (B.tVal h))
    hd0 hA ?_ ?_ hsmem' htmem' hst
  · intro y hy
    obtain ⟨hz0, hz1, _, _, _⟩ := hbnd y hy (B.sVal h) hsmem
    obtain ⟨hw0, hw1, _, _, _⟩ := hbnd y hy (B.tVal h) htmem
    exact hasDerivAt_kernelCoefA B hp.1 hp.2 hz0 hz1 hw0 hw1
  · intro y hy
    exact abs_powDeriv_le hd0 hA hy (hinnerA y hy)

/-- **The coefficient `p_{0d,h}` is bounded**, by symmetry of the kernel: `p_{0d,h} = p_{d0,h}`
(`kpd0_eq_kp0d`). -/
theorem exists_kp0d_window (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → |B.kp0d h| ≤ C := by
  obtain ⟨C, hC, δ, hδ, hb⟩ := exists_kpd0_window hd B hρ hρu hρ1
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro h hh0 hhδ
  rw [← kpd0_eq_kp0d]
  exact hb h hh0 hhδ

/-- **The coefficient `p_{00,h}` is bounded, uniformly in small `h`.**
`p_{00,h} = A_h(s_h) - p_{d0,h}s_h^d`, so the two previous bounds suffice. -/
theorem exists_kp00_window (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → |B.kp00 h| ≤ C := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hA : 0 < uStar d - ρ := by linarith
  have hB0 : (0 : ℝ) < uStar d + ρ := by linarith
  obtain ⟨CA, hCA, δA, hδA, hbA⟩ := exists_kernelCoefA_window hd B hρ hρu hρ1
  obtain ⟨CD, hCD, δD, hδD, hbD⟩ := exists_kpd0_window hd B hρ hρu hρ1
  obtain ⟨δ₂, hδ₂, hatoms⟩ := exists_atoms_mem_centralWindow B hρ
  have hnum : (0 : ℝ) < CA + CD * (uStar d + ρ) ^ d := by
    have h1 : (0 : ℝ) ≤ CD * (uStar d + ρ) ^ d := mul_nonneg hCD.le (pow_nonneg hB0.le d)
    linarith
  refine ⟨CA + CD * (uStar d + ρ) ^ d, hnum, min (min δA δD) δ₂,
    lt_min (lt_min hδA hδD) hδ₂, ?_⟩
  intro h hh0 hhδ
  have hhA : h < δA := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hhD : h < δD := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hh2 : h < δ₂ := lt_of_lt_of_le hhδ (min_le_right _ _)
  obtain ⟨hsmem, _⟩ := hatoms h hh0 hh2
  have hsmem' : B.sVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hsmem
  have hs0 : 0 < B.sVal h := lt_of_lt_of_le hA hsmem'.1
  have hkey : |B.kp00 h| ≤ CA + CD * B.sVal h ^ d :=
    abs_powCoefA_le (d := d) (phi := B.kernelCoefA h) hs0.le (hbA h hh0 hhA _ hsmem)
      (hbD h hh0 hhD)
  have hpow : B.sVal h ^ d ≤ (uStar d + ρ) ^ d := pow_le_pow_left₀ hs0.le hsmem'.2 d
  have hmul : CD * B.sVal h ^ d ≤ CD * (uStar d + ρ) ^ d :=
    mul_le_mul_of_nonneg_left hpow hCD.le
  linarith

end KKTFamily

end SingularEndpoint

end UpperTailOptimizers
