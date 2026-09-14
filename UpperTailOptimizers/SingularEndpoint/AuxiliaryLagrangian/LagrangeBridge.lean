import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.MuExpansion
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.KernelOp
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.FactorMain

/-!
# The graph-carrying Lagrangian (Section 5, `paper/sections/singular.tex`)

The `SingularEndpoint` layer is deliberately graph-free: `lem:graphon-lagrangian-bound` and everything
under it subtract `η_hΔ_h(ν)`, with `η_h = 2γ_hq_h/d = μ_hvq_h^{v-1}`, where the paper writes
`μ_h{t(H,W) - r_h^m}`.  The paper
reconciles the two in the unlabelled display following `eq:first-variation`,

`μ_h{(q_h + Δ)^v - q_h^v} = η_hΔ + O(Δ²)`,

together with the rank-one splitting `t(H,W) = q^v + 𝓡_H(f,E)`, `|𝓡_H| ≤ C‖E‖₂³`, of
`eq:rank-one-reduction-bounds`.  Both errors are absorbed: the `O(Δ²)` by the
retained `MΔ²`, and the `‖E‖₂³ = ‖E‖₂·‖E‖₂²` by the retained `M⁻¹‖E‖₂²` once `‖E‖₂ = O(h²)`.

For a `d`-regular `H` the exponent `v = 2m/d` is the *natural* number `|V|`, so the expansion
is a polynomial one and no `rpow` Taylor theorem is needed.

## Contents

* `abs_pow_sub_taylor_le` — `|aⁿ - bⁿ - n bⁿ⁻¹(a-b)| ≤ n²M^{2n}(a-b)²` on `[0,M]`;
* `KKTFamily.etaVal_eq_muVal` — `η_h = μ_h·n·q_h^{n-1}`, the relation
  `η_h = μ_h v q_h^{v-1}` of `eq:first-variation` with `v = n`;
* `FactorDecomp.qVal_mem_Icc` — `q = ∫f^d ∈ [0, 2^d]`;
* **`muVal_tDensity_le_etaVal`** — the conversion
  `μ_h{t(H,W) - r_h^m} ≤ η_hΔ + |μ_h|{n²2^{2dn}Δ² + 40^m‖E‖₂³}`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-! ## The second-order expansion of `x ↦ xⁿ` -/

/-- **`|aⁿ - bⁿ - n bⁿ⁻¹(a - b)| ≤ n²M^{2n}(a - b)²`** for `a, b ∈ [0,M]`, `M ≥ 1`.

`aⁿ - bⁿ = (a-b)∑_{i<n}aⁱbⁿ⁻¹⁻ⁱ`, so the left-hand side is
`|a-b|·|∑_{i<n}bⁿ⁻¹⁻ⁱ(aⁱ - bⁱ)|`, and each summand is at most `nM^{2n}|a-b|` by
`abs_pow_sub_pow_le_box`.  The range is `[0,M]` rather than `[0,1]` because the moment
`q = ∫f^d` of a Factor factor is only known to lie in `[0,2^d]`.  This is the polynomial form of the paper's
`μ_h{(q_h+Δ)^v - q_h^v} = η_hΔ + O(Δ²)`; for a `d`-regular `H` the exponent `v = 2m/d` is the
natural number `|V|`, so no `rpow` Taylor expansion is involved. -/
theorem abs_pow_sub_taylor_le {a b M : ℝ} (hM : 1 ≤ M) (ha0 : 0 ≤ a) (ha1 : a ≤ M)
    (hb0 : 0 ≤ b) (hb1 : b ≤ M) (n : ℕ) :
    |a ^ n - b ^ n - (n : ℝ) * b ^ (n - 1) * (a - b)|
      ≤ (n : ℝ) ^ 2 * M ^ (2 * n) * (a - b) ^ 2 := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hMn : (1 : ℝ) ≤ M ^ (2 * n) := one_le_pow₀ hM
  -- the summandwise identity
  have hterm : ∀ i ∈ Finset.range n,
      a ^ i * b ^ (n - 1 - i) - b ^ (n - 1) = b ^ (n - 1 - i) * (a ^ i - b ^ i) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have he : b ^ (n - 1 - i) * b ^ i = b ^ (n - 1) := by
      rw [← pow_add, show n - 1 - i + i = n - 1 from by omega]
    rw [mul_sub, he]
    ring
  have hconst : (n : ℝ) * b ^ (n - 1) = ∑ _i ∈ Finset.range n, b ^ (n - 1) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum : (∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)) - (n : ℝ) * b ^ (n - 1)
      = ∑ i ∈ Finset.range n, b ^ (n - 1 - i) * (a ^ i - b ^ i) := by
    rw [hconst, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hterm
  have hfac : a ^ n - b ^ n = (∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)) * (a - b) :=
    (geom_sum₂_mul a b n).symm
  have hid : a ^ n - b ^ n - (n : ℝ) * b ^ (n - 1) * (a - b)
      = (∑ i ∈ Finset.range n, b ^ (n - 1 - i) * (a ^ i - b ^ i)) * (a - b) := by
    rw [hfac, ← hsum]
    ring
  -- each summand is at most `n|a - b|`
  have hbnd : ∀ i ∈ Finset.range n, |b ^ (n - 1 - i) * (a ^ i - b ^ i)|
      ≤ (n : ℝ) * M ^ (2 * n) * |a - b| := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hb : |b ^ (n - 1 - i)| ≤ M ^ n := by
      rw [abs_of_nonneg (pow_nonneg hb0 _)]
      calc b ^ (n - 1 - i) ≤ M ^ (n - 1 - i) := pow_le_pow_left₀ hb0 hb1 _
        _ ≤ M ^ n := pow_le_pow_right₀ hM (by omega)
    have hpow : |a ^ i - b ^ i| ≤ (n : ℝ) * M ^ n * |a - b| := by
      have h := abs_pow_sub_pow_le_box ha0 ha1 hb0 hb1 i
      have hin' : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hin.le
      have hMi : M ^ (i - 1) ≤ M ^ n := pow_le_pow_right₀ hM (by omega)
      have hc : (i : ℝ) * M ^ (i - 1) ≤ (n : ℝ) * M ^ n :=
        mul_le_mul hin' hMi (by positivity) (Nat.cast_nonneg n)
      exact le_trans h (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
    rw [abs_mul]
    have hprod : M ^ n * ((n : ℝ) * M ^ n) = (n : ℝ) * M ^ (2 * n) := by
      rw [show 2 * n = n + n from by omega, pow_add]; ring
    calc |b ^ (n - 1 - i)| * |a ^ i - b ^ i|
        ≤ M ^ n * ((n : ℝ) * M ^ n * |a - b|) := by
          refine mul_le_mul hb hpow (abs_nonneg _) (by positivity)
      _ = (n : ℝ) * M ^ (2 * n) * |a - b| := by rw [← hprod]; ring
  have hsumb : |∑ i ∈ Finset.range n, b ^ (n - 1 - i) * (a ^ i - b ^ i)|
      ≤ (n : ℝ) * ((n : ℝ) * M ^ (2 * n) * |a - b|) := by
    calc |∑ i ∈ Finset.range n, b ^ (n - 1 - i) * (a ^ i - b ^ i)|
        ≤ ∑ i ∈ Finset.range n, |b ^ (n - 1 - i) * (a ^ i - b ^ i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, (n : ℝ) * M ^ (2 * n) * |a - b| := Finset.sum_le_sum hbnd
      _ = (n : ℝ) * ((n : ℝ) * M ^ (2 * n) * |a - b|) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hid, abs_mul]
  have hsq : (a - b) ^ 2 = |a - b| * |a - b| := by rw [abs_mul_abs_self]; ring
  rw [hsq]
  calc |∑ i ∈ Finset.range n, b ^ (n - 1 - i) * (a ^ i - b ^ i)| * |a - b|
      ≤ ((n : ℝ) * ((n : ℝ) * M ^ (2 * n) * |a - b|)) * |a - b| :=
        mul_le_mul_of_nonneg_right hsumb (abs_nonneg _)
    _ = (n : ℝ) ^ 2 * M ^ (2 * n) * (|a - b| * |a - b|) := by ring

namespace KKTFamily

/-! ## `η_h = μ_h·v·q_h^{v-1}` -/

/-- **`eq:first-variation`'s defining relation, with `v` read as the natural number
`n = |V|`**: `η_h = μ_h·n·q_h^{n-1}`.

`μ_h = γ_h/(m q_h^{v-2})` and `η_h = 2γ_hq_h/d`; the identity is `2m = nd` together with
`q_h^{n-2}·q_h^{n-1}` cancelling down to `q_h`.  The `rpow` in `muVal` is discharged by
`q_h > 0` and `2m/d = n`. -/
theorem etaVal_eq_muVal (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) {n : ℕ} {m : ℝ}
    (hm : 0 < m) (hn : 2 * m = (n : ℝ) * (d : ℝ)) (hd0 : (0 : ℝ) < (d : ℝ)) (hn2 : 2 ≤ n) :
    B.etaVal h = B.muVal m h * (n : ℝ) * B.qVal h ^ (n - 1) := by
  have hq : 0 < B.qVal h := qVal_pos hh
  have hexp : 2 * m / (d : ℝ) - 2 = ((n : ℝ) - 2) := by field_simp; linarith
  have hrp : B.qVal h ^ (2 * m / (d : ℝ) - 2) = B.qVal h ^ n / B.qVal h ^ 2 := by
    rw [hexp, Real.rpow_sub hq, show ((n : ℕ) : ℝ) = ((n : ℕ) : ℝ) from rfl,
      Real.rpow_natCast, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hqn : B.qVal h ^ n = B.qVal h ^ (n - 1) * B.qVal h := by
    rw [← pow_succ, show n - 1 + 1 = n from by omega]
  have hqne : B.qVal h ^ (n - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hq)
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have key : B.muVal m h * (n : ℝ) * B.qVal h ^ (n - 1)
      = B.gam h * B.qVal h * (n : ℝ) / m := by
    rw [muVal, hrp, hqn]
    field_simp
  rw [key, etaVal, div_eq_div_iff (ne_of_gt hd0) (ne_of_gt hm)]
  linear_combination (B.gam h * B.qVal h) * hn

end KKTFamily

/-! ## The Lagrangian conversion -/

/-- `0 ≤ q = ∫f^d ≤ 2^d`, from `0 ≤ f ≤ 2` on the probability space. -/
theorem FactorDecomp.qVal_mem_Icc {W : Graphon} (P : FactorDecomp d W) :
    P.qVal ∈ Set.Icc (0 : ℝ) (2 ^ d) := by
  constructor
  · exact integral_nonneg fun x => pow_nonneg (P.f_nonneg x) d
  · have hb : ∀ x : ℝ, P.f x ^ d ≤ 2 ^ d := fun x =>
      pow_le_pow_left₀ (P.f_nonneg x) (P.f_bdd x) d
    have hci : Integrable (fun _ : ℝ => (2 : ℝ) ^ d) unitμ := integrable_const _
    have h := integral_mono (P.integrable_f_pow d) hci hb
    rwa [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul,
      one_mul] at h

/-- **The graph-carrying Lagrangian** (`paper/sections/singular.tex` together with
`eq:rank-one-reduction-bounds`).

`μ_h{t(H,W) - r_h^m} ≤ η_hΔ + |μ_h|{n²2^{2dn}Δ² + 40^m‖E‖₂³}`.

The `SingularEndpoint` layer subtracts the graph-free `η_hΔ_h(ν)`; the comparison route to
`thm:singular-endpoint` wants `μ_h{t(H,W) - r_h^m}`.  (`μ_h` itself belongs to
`lem:rank-one-kkt-family`; the theorem's own statement does not mention it.)
Three steps convert one to the other, and both errors are the ones
the paper says are absorbed:

* `r_h^m = q_h^n` (`KKTFamily.rVal_pow_card_edges`), so the constraint slack is a
  difference of `n`-th powers of moments;
* `t(H,W) = q^n + 𝓡_H` with `|𝓡_H| ≤ 40^m‖E‖₂³`
  (`FactorDecomp.abs_tDensity_sub_qVal_pow_le`) — the rank-one splitting;
* `q^n - q_h^n = n q_h^{n-1}Δ + O(Δ²)` (`abs_pow_sub_taylor_le`) and
  `η_h = μ_h n q_h^{n-1}` (`KKTFamily.etaVal_eq_muVal`).

The `O(Δ²)` is absorbed by the master estimate's retained `MΔ²`, and
`‖E‖₂³ = ‖E‖₂·‖E‖₂²` by its retained `M⁻¹‖E‖₂²` once `‖E‖₂ = O(h²)`. -/
theorem muVal_tDensity_le_etaVal (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hv : 2 ≤ Fintype.card V) (hm : 1 ≤ H.edgeFinset.card) (B : KKTFamily d) {h : ℝ}
    (hh : |h| < B.h₀) {W : Graphon} (P : FactorDecomp d W) :
    B.muVal (H.edgeFinset.card : ℝ) h * (W.tDensity H - B.rVal h ^ H.edgeFinset.card)
      ≤ B.etaVal h * (P.qVal - B.qVal h)
        + |B.muVal (H.edgeFinset.card : ℝ) h|
            * ((Fintype.card V : ℝ) ^ 2 * (2 ^ d : ℝ) ^ (2 * Fintype.card V)
                * (P.qVal - B.qVal h) ^ 2
              + (40 : ℝ) ^ H.edgeFinset.card * P.residL2 ^ 3) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := dpos hd
  have hmpos : (0 : ℝ) < (H.edgeFinset.card : ℝ) := by exact_mod_cast hm
  have hnR : 2 * (H.edgeFinset.card : ℝ) = (Fintype.card V : ℝ) * (d : ℝ) := by
    have := factorMain_two_mul_card_edgeFinset H hreg
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
  have heta := KKTFamily.etaVal_eq_muVal B hh hmpos hnR hd0 hv
  have hr := KKTFamily.rVal_pow_card_edges H hd hreg hh
  have hT := P.abs_tDensity_sub_qVal_pow_le H hreg
  -- the two moments lie in `[0, 2^d]`
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  obtain ⟨hq0, hqM⟩ := P.qVal_mem_Icc
  have hb0 : (0 : ℝ) ≤ B.qVal h := (KKTFamily.qVal_pos hh).le
  have hbM : B.qVal h ≤ (2 : ℝ) ^ d := le_trans (KKTFamily.qVal_lt_one hd hh).le hM1
  have hTay := abs_pow_sub_taylor_le hM1 hq0 hqM hb0 hbM (Fintype.card V)
  -- the two error terms
  obtain ⟨mu, hmu⟩ : ∃ t : ℝ, t = B.muVal (H.edgeFinset.card : ℝ) h := ⟨_, rfl⟩
  have habs1 : |mu * (W.tDensity H - P.qVal ^ Fintype.card V)|
      ≤ |mu| * ((40 : ℝ) ^ H.edgeFinset.card * P.residL2 ^ 3) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hT (abs_nonneg _)
  have habs2 : |mu * (P.qVal ^ Fintype.card V - B.qVal h ^ Fintype.card V
        - (Fintype.card V : ℝ) * B.qVal h ^ (Fintype.card V - 1) * (P.qVal - B.qVal h))|
      ≤ |mu| * ((Fintype.card V : ℝ) ^ 2 * (2 ^ d : ℝ) ^ (2 * Fintype.card V)
          * (P.qVal - B.qVal h) ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hTay (abs_nonneg _)
  -- assemble
  have hid : mu * (W.tDensity H - B.rVal h ^ H.edgeFinset.card)
      = mu * (W.tDensity H - P.qVal ^ Fintype.card V)
        + mu * (P.qVal ^ Fintype.card V - B.qVal h ^ Fintype.card V
            - (Fintype.card V : ℝ) * B.qVal h ^ (Fintype.card V - 1) * (P.qVal - B.qVal h))
        + mu * ((Fintype.card V : ℝ) * B.qVal h ^ (Fintype.card V - 1))
            * (P.qVal - B.qVal h) := by
    rw [hr]; ring
  have hlast : mu * ((Fintype.card V : ℝ) * B.qVal h ^ (Fintype.card V - 1))
      = B.etaVal h := by
    rw [heta, hmu]; ring
  rw [← hmu, hid, hlast]
  linarith [(abs_le.mp habs1).2, (abs_le.mp habs2).2]

end SingularEndpoint

end UpperTailOptimizers
