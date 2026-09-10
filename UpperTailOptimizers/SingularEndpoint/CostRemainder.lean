import UpperTailOptimizers.SingularEndpoint.StrictImprovement
import UpperTailOptimizers.SingularEndpoint.ParameterRemainders
import UpperTailOptimizers.SingularEndpoint.MfunAnalytic

/-!
# `lem:constant-graphon-comparison` with the paper's `O_d(h⁶)` remainder

`tendsto_cost_gap` (`SingularEndpoint/StrictImprovement.lean`) proves the rate

  `(I_{p_h}(W_h) - J_{p_h}(r_h))/h⁴ → -d³/3`,

i.e. `I_{p_h}(W_h) - J_{p_h}(r_h) = -d³h⁴/3 + o(h⁴)`.  `lem:constant-graphon-comparison` states
the remainder as `O_d(h⁶)`, and the paper's reason is parity: "the first remainder improves from
`O_d(h⁵)` to `O_d(h⁶)` because `∫Γ_d(W_h)` is an even analytic function of `h`".

Here the cost gap itself is exhibited as an even analytic function of `h`, which is what
`SingularEndpoint/ParityOrder.lean` needs.  Both halves are already available:

* the gap is the scalar `I_{p_h}(W_h) = α_h²J_{p_h}(s_h²) + 2α_h(1-α_h)J_{p_h}(s_ht_h) +
  (1-α_h)²J_{p_h}(t_h²)` (`graphon_Ip_eq_IpScalar`) minus `J_{p_h}(r_h)`, so it is a function of
  `h` alone — no dependence on the window proof — and it is analytic at `0` because `α_h, p_h,
  u_h, r_h` are and `J` is jointly analytic on `(0,1)²` (`analyticAt_Jp_comp`);
* it is **even** because reflection exchanges the two blocks: `alph_reflect` turns `α_h` into
  `1-α_h` while `sVal_neg`/`tVal_neg` exchange `s_h` and `t_h`, which permutes the three terms of
  `IpScalar` among themselves, and `p_h, r_h` are even outright.

## Contents

* `KKTFamily.costScalar` — the cost gap as a function of `h`, with `costScalar_eq`;
* `KKTFamily.IpScalar_even`, `KKTFamily.costScalar_even`, `analyticAt_IpScalar`,
  `analyticAt_costScalar` — the parity and analyticity inputs;
* `constant_graphon_comparison` — `lem:constant-graphon-comparison`:
  `I_{p_h}(W_h) - J_{p_h}(r_h) = -d³h⁴/3 + O_d(h⁶)`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology MeasureTheory

variable {d : ℕ}

namespace KKTFamily

variable {B : KKTFamily d}

/-- **The cost gap as a function of `h`.**  `I_{p_h}(W_h) - J_{p_h}(r_h)`, written through the
scalar form `IpScalar` so that it does not mention the window proof. -/
noncomputable def costScalar (B : KKTFamily d) (h : ℝ) : ℝ :=
  B.IpScalar h - Jp (B.p h) (B.rVal h)

theorem costScalar_eq {h : ℝ} (hh : |h| < B.h₀) :
    B.costScalar h = (B.graphon hh).Ip (B.p h) - Jp (B.p h) (B.rVal h) := by
  rw [costScalar, graphon_Ip_eq_IpScalar hh]

/-- **`I_{p_h}(W_h)` is even in `h`.**  Reflection exchanges the two blocks: `α_h ↦ 1-α_h` and
`s_h ↔ t_h`, which permutes the three terms of `IpScalar` among themselves. -/
theorem IpScalar_even (B : KKTFamily d) (h : ℝ) : B.IpScalar (-h) = B.IpScalar h := by
  simp only [IpScalar, B.p_even, B.alph_reflect, sVal_neg, tVal_neg]
  rw [show B.tVal h * B.sVal h = B.sVal h * B.tVal h from mul_comm _ _]
  ring

/-- **The cost gap is even in `h`**: `IpScalar_even` for the first term, `p_even` and `rVal_even`
for the second. -/
theorem costScalar_even (B : KKTFamily d) (h : ℝ) : B.costScalar (-h) = B.costScalar h := by
  simp only [costScalar, IpScalar_even, B.p_even, rVal_even]

end KKTFamily

/-! ## Analyticity at the endpoint -/

/-- `I_{p_h}(W_h)` is analytic at `h = 0`.  The three entropies are `J` composed with the
analytic parameters `p_h` and the three edge values, all of which lie in `(0,1)` at `h = 0`
(where they are `p_*` and `r_* = u_*²`). -/
theorem analyticAt_IpScalar (hd : 2 ≤ d) (B : KKTFamily d) :
    AnalyticAt ℝ B.IpScalar 0 := by
  have hw := KKTFamily.zero_mem_window B
  have hp := B.analyticAt_p 0 hw
  have ha := B.analyticAt_alph 0 hw
  have hu := B.analyticAt_u 0 hw
  have hs : AnalyticAt ℝ B.sVal 0 := hu.sub analyticAt_id
  have ht : AnalyticAt ℝ B.tVal 0 := hu.add analyticAt_id
  have hp0 : 0 < B.p 0 := by rw [B.p_zero]; exact pStar_pos hd
  have hp1 : B.p 0 < 1 := by rw [B.p_zero]; exact pStar_lt_one hd
  have hs0 : 0 < B.sVal 0 := KKTFamily.sVal_pos hw
  have hs1 : B.sVal 0 < 1 := KKTFamily.sVal_lt_one hw
  have ht0 : 0 < B.tVal 0 := KKTFamily.tVal_pos hw
  have ht1 : B.tVal 0 < 1 := KKTFamily.tVal_lt_one hw
  have hss1 : B.sVal 0 ^ 2 < 1 := pow_lt_one₀ hs0.le hs1 (n := 2) (by norm_num)
  have htt1 : B.tVal 0 ^ 2 < 1 := pow_lt_one₀ ht0.le ht1 (n := 2) (by norm_num)
  have hJss : AnalyticAt ℝ (fun h : ℝ => Jp (B.p h) (B.sVal h ^ 2)) 0 :=
    analyticAt_Jp_comp hp (hs.pow 2) hp0 hp1 (by positivity) (by simpa using hss1)
  have hJst : AnalyticAt ℝ (fun h : ℝ => Jp (B.p h) (B.sVal h * B.tVal h)) 0 :=
    analyticAt_Jp_comp hp (hs.mul ht) hp0 hp1 (by positivity)
      (by simpa using mul_lt_one_of_nonneg_of_lt_one_left hs0.le hs1 ht1.le)
  have hJtt : AnalyticAt ℝ (fun h : ℝ => Jp (B.p h) (B.tVal h ^ 2)) 0 :=
    analyticAt_Jp_comp hp (ht.pow 2) hp0 hp1 (by positivity) (by simpa using htt1)
  exact (((ha.pow 2).mul hJss).add
    (((analyticAt_const.mul ha).mul (analyticAt_const.sub ha)).mul hJst)).add
    (((analyticAt_const.sub ha).pow 2).mul hJtt)

/-- The cost gap is analytic at `h = 0`. -/
theorem analyticAt_costScalar (hd : 2 ≤ d) (B : KKTFamily d) :
    AnalyticAt ℝ B.costScalar 0 := by
  have hw := KKTFamily.zero_mem_window B
  have hr0 : 0 < B.rVal 0 := KKTFamily.rVal_pos hd hw
  have hr1 : B.rVal 0 < 1 := KKTFamily.rVal_lt_one hd hw
  have hp0 : 0 < B.p 0 := by rw [B.p_zero]; exact pStar_pos hd
  have hp1 : B.p 0 < 1 := by rw [B.p_zero]; exact pStar_lt_one hd
  exact (analyticAt_IpScalar hd B).sub
    (analyticAt_Jp_comp (B.analyticAt_p 0 hw) (KKTFamily.analyticAt_rVal hw) hp0 hp1 hr0 hr1)

/-! ## `lem:constant-graphon-comparison` -/

/-- **`lem:constant-graphon-comparison`.**  For all small `h`,

  `I_{p_h}(W_h) - J_{p_h}(r_h) = -\frac{d³}{3}h⁴ + O_d(h⁶)`.

The `h⁴` coefficient is `tendsto_cost_gap`; the `O_d(h⁶)` remainder — two orders past it, rather
than the one order an `o(h⁴)` statement would give — is the parity of the gap
(`costScalar_even`) together with its analyticity, through
`exists_pow_bound_sub_quartic`. -/
theorem constant_graphon_comparison (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ (h : ℝ) (hh : |h| < B.h₀), |h| < δ →
      |((B.graphon hh).Ip (B.p h) - Jp (B.p h) (B.rVal h)) + (d : ℝ) ^ 3 / 3 * h ^ 4|
        ≤ C * |h| ^ 6 := by
  have hlim := tendsto_cost_gap hd B (K := B.costScalar)
    (fun h hh => KKTFamily.costScalar_eq hh)
  obtain ⟨C, δ, hC, hδ, hb⟩ := exists_pow_bound_sub_quartic (analyticAt_costScalar hd B)
    (KKTFamily.costScalar_even B) hlim
  refine ⟨C, δ, hC, hδ, fun h hh hhδ => ?_⟩
  have h1 := hb h hhδ
  rw [← KKTFamily.costScalar_eq hh]
  rw [show B.costScalar h + (d : ℝ) ^ 3 / 3 * h ^ 4
      = B.costScalar h - -((d : ℝ) ^ 3 / 3) * h ^ 4 from by ring]
  exact h1

end SingularEndpoint

end UpperTailOptimizers
