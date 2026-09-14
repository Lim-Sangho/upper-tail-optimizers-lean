import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.BipodalUpper

/-!
# The matching quadratic upper bound (`lem:bipodal-quadratic-bound` of `paper/paper.tex`)

The headline theorem `quadratic_upper`: uniformly for `r` in a compact subarc `K` of a
Lubetzky–Zhao boundary arc, for every `0 < δ < δ₀` there is a **bipodal** graphon `V_δ` with

* `e(V_δ) = r - δ`,
* `t(H, V_δ) = r^m`, and
* `I_{pc(r)}(V_δ) ≤ J_{pc(r)}(r) + C' δ²`.

See the module documentation of `NonexceptionalEndpoint/QuadraticGrowth/BipodalUpper.lean` for the proof
strategy (a quantitative one-variable intermediate-value solve replacing the paper's
analytic implicit function theorem at `(r₀,0,0,r₀)`).
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set

-- Atom comparisons in `linarith`/`gcongr` must not unfold the scalar entropy or the
-- constraint solve into their `Real.log`/rational bodies (this blows the heartbeat
-- budget in the large main proof); every access below goes through equation lemmas.
attribute [local irreducible] Jp Jp' slope qSolve Real.log

/-! ### Graph-theoretic preliminaries

`nonempty_of_edge`, `regular_handshake` and `degree_le_card_edges` now live in
`UpperTailOptimizers/Preliminaries/Graphons/RegularGraph.lean`. -/

/-- The linear coefficient of the constraint solve equals `n r^{m-d} G(r,s)`, where
`G` is the strict-convexity gap of `u ↦ u^d`. -/
theorem alpha_eq {n m d : ℕ} (hd1 : 1 ≤ d) (hdm : d ≤ m) (hnd : n * d = 2 * m) (r s : ℝ) :
    2 * (m : ℝ) * r ^ (m - 1) * (r - s) + (n : ℝ) * (s ^ d * r ^ (m - d) - r ^ m)
      = (n : ℝ) * (r ^ (m - d) * (s ^ d - r ^ d - d * r ^ (d - 1) * (s - r))) := by
  have hpow1 : r ^ (m - d) * r ^ d = r ^ m := by
    rw [← pow_add]; congr 1; omega
  have hpow2 : r ^ (m - d) * r ^ (d - 1) = r ^ (m - 1) := by
    rw [← pow_add]; congr 1; omega
  have hndR : (n : ℝ) * (d : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hnd
  linear_combination (n : ℝ) * hpow1 + (n : ℝ) * (d : ℝ) * (s - r) * hpow2
    + r ^ (m - 1) * (s - r) * hndR

/-! ### The quadratic upper bound -/

-- The heartbeat budget is raised because this single proof carries a ~90-hypothesis
-- context through its final assembly; each individual step is small.
set_option maxHeartbeats 1600000 in
/-- **`lem:bipodal-quadratic-bound` (quadratic upper bound).**  There are `C' > 0` and `δ₀ > 0`, uniform over
the compact subarc `K`, such that for every `r ∈ K` and `0 < δ < δ₀` there is a bipodal
graphon `W` with edge density `r - δ`, `H`-density exactly `r^m`, and
`I_{pc(r)}(W) ≤ J_{pc(r)}(r) + C' δ²`. -/
theorem quadratic_upper {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {K : Set ℝ} (hK : K ⊆ M.U) (hKc : IsCompact K) (hKne : K.Nonempty)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    ∃ C' δ₀ : ℝ, 0 < C' ∧ 0 < δ₀ ∧ ∀ r ∈ K, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ W : Graphon, W.edgeDensity = r - δ ∧
        W.tDensity H = r ^ H.edgeFinset.card ∧ IsBipodal W ∧
        W.Ip (M.pc r) ≤ Jp (M.pc r) r + C' * δ ^ 2 := by
  classical
  obtain ⟨η, hη0, hη12, hηbd⟩ := arc_uniform_bounds M hK hKc hKne
  -- ### Numerical preliminaries
  set n : ℕ := Fintype.card V with hn_def
  set m : ℕ := H.edgeFinset.card with hm_def
  have hd1 : 1 ≤ d := le_trans one_le_two hd
  have hVne : Nonempty V := nonempty_of_edge H hm
  have hn1 : 1 ≤ n := Fintype.card_pos
  have hnd : n * d = 2 * m := regular_handshake H hreg
  have hdm : d ≤ m := degree_le_card_edges H hreg hm
  have hm1 : 1 ≤ m := hm
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hn0R : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hnR
  have hm0R : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le one_pos hmR
  have hd0R : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le one_pos hdR
  have h2n0 : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
  have hη1 : η < 1 := lt_of_le_of_lt hη12 (by norm_num)
  have hlogη : 0 ≤ -Real.log η := by
    have := Real.log_nonpos hη0.le hη1.le
    linarith
  have hβ0 : (0 : ℝ) < η / 2 := by linarith
  have hβ14 : η / 2 ≤ 1 / 4 := by linarith
  have hlogβ : 0 ≤ -Real.log (η / 2) := by
    have := Real.log_nonpos hβ0.le (by linarith : η / 2 ≤ 1)
    linarith
  -- ### The uniform constants (introduced opaquely, with defining equations)
  obtain ⟨MJ, hMJ_def⟩ : ∃ x : ℝ, x = 1 / (η / 2 * (1 - η / 2)) := ⟨_, rfl⟩
  have hMJ0 : 0 < MJ := by
    rw [hMJ_def]
    exact one_div_pos.mpr (by nlinarith)
  obtain ⟨LJb, hLJb_def⟩ : ∃ x : ℝ, x = 4 * (-Real.log (η / 2)) := ⟨_, rfl⟩
  have hLJb0 : 0 ≤ LJb := by rw [hLJb_def]; linarith
  obtain ⟨JM, hJM_def⟩ : ∃ x : ℝ, x = 2 * (-Real.log (η / 2)) := ⟨_, rfl⟩
  have hJM0 : 0 ≤ JM := by rw [hJM_def]; linarith
  obtain ⟨Lslope, hLslope_def⟩ :
      ∃ x : ℝ, x = 4 * (-Real.log η) / ((d : ℝ) * η ^ (d - 1)) := ⟨_, rfl⟩
  have hLslope0 : 0 ≤ Lslope := by
    rw [hLslope_def]
    exact div_nonneg (by linarith) (mul_pos hd0R (pow_pos hη0 _)).le
  obtain ⟨CE, hCE_def⟩ : ∃ x : ℝ, x = 2 * (n : ℝ) ^ 2 + 2 ^ n := ⟨_, rfl⟩
  have hCE0 : 0 < CE := by
    rw [hCE_def]
    have h1 : (0:ℝ) ≤ 2 * (n : ℝ) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
    linarith
  obtain ⟨CΨ, hCΨ_def⟩ :
      ∃ x : ℝ, x = 512 * (m : ℝ) ^ 2 + 36 * (n : ℝ) * (m : ℝ) + CE + 28 * (m : ℝ) :=
    ⟨_, rfl⟩
  have hCΨ0 : 0 < CΨ := by
    rw [hCΨ_def]
    have h1 : (0:ℝ) ≤ 512 * (m : ℝ) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
    have h2 : (0:ℝ) ≤ 36 * (n : ℝ) * (m : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) hn0R.le) hm0R.le
    have h3 : (0:ℝ) ≤ 28 * (m : ℝ) := mul_nonneg (by norm_num) hm0R.le
    linarith
  obtain ⟨αmin, hαmin_def⟩ : ∃ x : ℝ, x = (n : ℝ) * η ^ m := ⟨_, rfl⟩
  have hαmin0 : 0 < αmin := by
    rw [hαmin_def]
    exact mul_pos hn0R (pow_pos hη0 m)
  obtain ⟨c₀, hc₀_def⟩ :
      ∃ x : ℝ, x = min (1/2) (min (η / 64) (αmin / (4 * CΨ))) := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by
    rw [hc₀_def]
    exact lt_min (by norm_num)
      (lt_min (by linarith) (div_pos hαmin0 (mul_pos (by norm_num) hCΨ0)))
  have hc₀12 : c₀ ≤ 1/2 := by rw [hc₀_def]; exact min_le_left _ _
  have hc₀η : c₀ ≤ η / 64 := by
    rw [hc₀_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hc₀α : c₀ ≤ αmin / (4 * CΨ) := by
    rw [hc₀_def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hmCΨ0 : (0 : ℝ) < (m : ℝ) + CΨ := add_pos hm0R hCΨ0
  obtain ⟨δ₀, hδ₀_def⟩ :
      ∃ x : ℝ, x = min (min (η / 32) 1) (αmin * c₀ / (4 * ((m : ℝ) + CΨ))) := ⟨_, rfl⟩
  have hδ₀0 : 0 < δ₀ := by
    rw [hδ₀_def]
    exact lt_min (lt_min (by linarith) (by norm_num))
      (div_pos (mul_pos hαmin0 hc₀0) (mul_pos (by norm_num) hmCΨ0))
  have hδ₀η : δ₀ ≤ η / 32 := by
    rw [hδ₀_def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₀1 : δ₀ ≤ 1 := by
    rw [hδ₀_def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₀α : δ₀ ≤ αmin * c₀ / (4 * ((m : ℝ) + CΨ)) := by
    rw [hδ₀_def]; exact min_le_right _ _
  obtain ⟨C₁, hC₁_def⟩ : ∃ x : ℝ, x = 2 * ((m : ℝ) + CΨ) / αmin := ⟨_, rfl⟩
  have hC₁0 : 0 < C₁ := by
    rw [hC₁_def]
    exact div_pos (mul_pos two_pos hmCΨ0) hαmin0
  obtain ⟨CX, hCX_def⟩ : ∃ x : ℝ, x = 28 * (d : ℝ) + 2 * CΨ / η ^ (m - d) := ⟨_, rfl⟩
  have hCX0 : 0 < CX := by
    rw [hCX_def]
    have h1 : (0:ℝ) < 28 * (d : ℝ) := mul_pos (by norm_num) hd0R
    have h2 : (0:ℝ) < 2 * CΨ / η ^ (m - d) :=
      div_pos (mul_pos two_pos hCΨ0) (pow_pos hη0 _)
    linarith
  obtain ⟨CI, hCI_def⟩ :
      ∃ x : ℝ, x = 512 * MJ + Lslope * CX + 36 * (LJb + MJ) + 4 * JM := ⟨_, rfl⟩
  have hCI0 : 0 < CI := by
    rw [hCI_def]
    have h1 : 0 ≤ Lslope * CX := mul_nonneg hLslope0 hCX0.le
    linarith
  refine ⟨CI * (C₁ ^ 2 + 1), δ₀,
    mul_pos hCI0 (add_pos_of_nonneg_of_pos (sq_nonneg C₁) one_pos), hδ₀0, ?_⟩
  intro r hr δ hδ0 hδlt
  -- ### Per-`r` data
  obtain ⟨hpc0, hpcr, hr1, hsmne, hsm0, hsm1⟩ := M.ordering r (hK hr)
  have hr0 : 0 < r := lt_trans hpc0 hpcr
  obtain ⟨hηr, hr1', hηs, hs1', hηpc, hηdist⟩ := hηbd r hr
  have hpc1 : M.pc r < 1 := lt_trans hpcr hr1
  have hδ1 : δ ≤ 1 := le_trans hδlt.le hδ₀1
  have hδη : δ < η / 32 := lt_of_lt_of_le hδlt hδ₀η
  have haIcc : (1/2 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
  have hrIcc : r ∈ Set.Icc (0:ℝ) 1 := ⟨hr0.le, hr1.le⟩
  have hsIcc : M.sm r ∈ Set.Icc (0:ℝ) 1 := ⟨hsm0.le, hsm1.le⟩
  -- the strict-convexity gap and the linear coefficient
  obtain ⟨G, hG_def⟩ :
      ∃ x : ℝ, x = (M.sm r) ^ d - r ^ d - (d : ℝ) * r ^ (d - 1) * (M.sm r - r) := ⟨_, rfl⟩
  have hGge : η ^ d ≤ G := by
    have h1 : r ^ (d - 2) * (M.sm r - r) ^ 2 ≤ G := by
      rw [hG_def]
      exact pow_convex_gap_ge hr0.le hsm0.le hd
    have h2 : η ^ (d - 2) * η ^ 2 ≤ r ^ (d - 2) * (M.sm r - r) ^ 2 := by
      refine mul_le_mul (pow_le_pow_left₀ hη0.le hηr _) ?_ (sq_nonneg η)
        (pow_nonneg hr0.le _)
      calc η ^ 2 ≤ |M.sm r - r| ^ 2 := pow_le_pow_left₀ hη0.le hηdist 2
        _ = (M.sm r - r) ^ 2 := sq_abs _
    have h3 : η ^ (d - 2) * η ^ 2 = η ^ d := by
      rw [← pow_add]; congr 1; omega
    linarith [h3 ▸ h2]
  have hG0 : 0 < G := lt_of_lt_of_le (pow_pos hη0 d) hGge
  obtain ⟨αL, hαL_def⟩ :
      ∃ x : ℝ, x = 2 * (m : ℝ) * r ^ (m - 1) * (r - M.sm r)
        + (n : ℝ) * ((M.sm r) ^ d * r ^ (m - d) - r ^ m) := ⟨_, rfl⟩
  have hαLG : αL = (n : ℝ) * (r ^ (m - d) * G) := by
    rw [hαL_def, hG_def]
    exact alpha_eq hd1 hdm hnd r (M.sm r)
  have hαLmin : αmin ≤ αL := by
    rw [hαLG, hαmin_def]
    have h1 : η ^ (m - d) * η ^ d ≤ r ^ (m - d) * G :=
      mul_le_mul (pow_le_pow_left₀ hη0.le hηr _) hGge (pow_nonneg hη0.le _)
        (pow_nonneg hr0.le _)
    have h2 : η ^ (m - d) * η ^ d = η ^ m := by
      rw [← pow_add]; congr 1; omega
    have h3 : η ^ m ≤ r ^ (m - d) * G := by linarith [h2 ▸ h1]
    exact mul_le_mul_of_nonneg_left h3 hn0R.le
  -- ### The box for the large-block density
  have hqbox : ∀ c ∈ Set.Icc (0:ℝ) c₀,
      qSolve (1/2) (M.sm r) r δ c ∈ Set.Icc (η / 2) (1 - η / 2) := by
    intro c hc
    have hc2 : c ≤ 1/2 := le_trans hc.2 hc₀12
    have hdev := qSolve_dev_bound haIcc hsIcc hrIcc hc.1 hc2 hδ0.le
    have hcη : c ≤ η / 64 := le_trans hc.2 hc₀η
    obtain ⟨hdl, hdr⟩ := abs_le.mp hdev
    constructor
    · linarith
    · linarith
  have hqbox01 : ∀ c ∈ Set.Icc (0:ℝ) c₀,
      qSolve (1/2) (M.sm r) r δ c ∈ Set.Icc (0:ℝ) 1 := by
    intro c hc
    obtain ⟨h1, h2⟩ := hqbox c hc
    exact ⟨by linarith, by linarith⟩
  -- ### The linearisation of the constraint function
  have hlin : ∀ c ∈ Set.Icc (0:ℝ) c₀,
      |tBip H (1/2) (M.sm r) (qSolve (1/2) (M.sm r) r δ c) c - r ^ m
          - (αL * c - (m : ℝ) * r ^ (m - 1) * δ)|
        ≤ CΨ * (c ^ 2 + δ ^ 2) := by
    intro c hc
    have hc2 : c ≤ 1/2 := le_trans hc.2 hc₀12
    have hc1 : c ≤ 1 := le_trans hc2 (by norm_num)
    obtain ⟨q, hq_def⟩ : ∃ x : ℝ, x = qSolve (1/2) (M.sm r) r δ c := ⟨_, rfl⟩
    rw [← hq_def]
    have hq01 : q ∈ Set.Icc (0:ℝ) 1 := by rw [hq_def]; exact hqbox01 c hc
    have hw : |q - r| ≤ 16 * c + 4 * δ := by
      rw [hq_def]
      exact qSolve_dev_bound haIcc hsIcc hrIcc hc.1 hc2 hδ0.le
    have hw2 : (q - r) ^ 2 ≤ 512 * (c ^ 2 + δ ^ 2) := abs_le_sq_bound hc.1 hδ0.le hw
    have hcw : c * |q - r| ≤ 18 * (c ^ 2 + δ ^ 2) := abs_le_mul_bound hc.1 hδ0.le hw
    have hT := tBip_linearization H hreg haIcc hsIcc hq01 hrIcc hc.1 hc1
    rw [← hn_def, ← hm_def] at hT
    have hlb : |q - r - (2 * c * (r - M.sm r) - δ)| ≤ 28 * (c ^ 2 + δ ^ 2) := by
      rw [hq_def]
      exact qSolve_linear_bound haIcc hsIcc hrIcc hc.1 hc2 hδ0.le
    -- the middle linear form in `(q - r)`
    have hmid : αL * c - (m : ℝ) * r ^ (m - 1) * δ
        = (m : ℝ) * r ^ (m - 1) * (2 * c * (r - M.sm r) - δ)
          + (n : ℝ) * c * ((M.sm r) ^ d * r ^ (m - d) - r ^ m) := by
      rw [hαL_def]; ring
    have hrpow1 : |r ^ (m - 1)| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hr0.le _)]
      exact pow_le_one₀ hr0.le hr1.le
    have hbridge : |(m : ℝ) * r ^ (m - 1) * (q - r)
        - (m : ℝ) * r ^ (m - 1) * (2 * c * (r - M.sm r) - δ)|
        ≤ (m : ℝ) * (28 * (c ^ 2 + δ ^ 2)) := by
      have h1 : (m : ℝ) * r ^ (m - 1) * (q - r)
          - (m : ℝ) * r ^ (m - 1) * (2 * c * (r - M.sm r) - δ)
          = (m : ℝ) * r ^ (m - 1) * (q - r - (2 * c * (r - M.sm r) - δ)) := by ring
      rw [h1, abs_mul, abs_mul]
      have hmabs : |(m : ℝ)| = (m : ℝ) := abs_of_pos hm0R
      rw [hmabs]
      calc (m : ℝ) * |r ^ (m - 1)| * |q - r - (2 * c * (r - M.sm r) - δ)|
          ≤ (m : ℝ) * 1 * (28 * (c ^ 2 + δ ^ 2)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hrpow1 hm0R.le) hlb
              (abs_nonneg _) (mul_nonneg hm0R.le zero_le_one)
        _ = (m : ℝ) * (28 * (c ^ 2 + δ ^ 2)) := by ring
    -- assemble via the triangle inequality
    have htri := abs_sub_le
      (tBip H (1/2) (M.sm r) q c - r ^ m)
      ((m : ℝ) * r ^ (m - 1) * (q - r) + (n : ℝ) * c * ((M.sm r) ^ d * r ^ (m - d) - r ^ m))
      (αL * c - (m : ℝ) * r ^ (m - 1) * δ)
    have hT2 : |(m : ℝ) * r ^ (m - 1) * (q - r)
        + (n : ℝ) * c * ((M.sm r) ^ d * r ^ (m - d) - r ^ m)
        - (αL * c - (m : ℝ) * r ^ (m - 1) * δ)| ≤ (m : ℝ) * (28 * (c ^ 2 + δ ^ 2)) := by
      rw [hmid]
      have heq : (m : ℝ) * r ^ (m - 1) * (q - r)
          + (n : ℝ) * c * ((M.sm r) ^ d * r ^ (m - d) - r ^ m)
          - ((m : ℝ) * r ^ (m - 1) * (2 * c * (r - M.sm r) - δ)
            + (n : ℝ) * c * ((M.sm r) ^ d * r ^ (m - d) - r ^ m))
          = (m : ℝ) * r ^ (m - 1) * (q - r)
            - (m : ℝ) * r ^ (m - 1) * (2 * c * (r - M.sm r) - δ) := by ring
      rw [heq]
      exact hbridge
    have hTfinal : |tBip H (1/2) (M.sm r) q c - r ^ m
        - ((m : ℝ) * r ^ (m - 1) * (q - r)
          + (n : ℝ) * c * ((M.sm r) ^ d * r ^ (m - d) - r ^ m))|
        ≤ (m : ℝ) ^ 2 * (512 * (c ^ 2 + δ ^ 2))
          + 2 * (n : ℝ) * (m : ℝ) * (18 * (c ^ 2 + δ ^ 2)) + CE * c ^ 2 := by
      refine le_trans hT ?_
      have h1 : (m : ℝ) ^ 2 * (q - r) ^ 2 ≤ (m : ℝ) ^ 2 * (512 * (c ^ 2 + δ ^ 2)) :=
        mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
      have h2 : 2 * (n : ℝ) * (m : ℝ) * c * |q - r|
          ≤ 2 * (n : ℝ) * (m : ℝ) * (18 * (c ^ 2 + δ ^ 2)) := by
        have hnm : (0:ℝ) ≤ 2 * (n : ℝ) * (m : ℝ) :=
          mul_nonneg (mul_nonneg (by norm_num) hn0R.le) hm0R.le
        have h3 := mul_le_mul_of_nonneg_left hcw hnm
        calc 2 * (n : ℝ) * (m : ℝ) * c * |q - r|
            = 2 * (n : ℝ) * (m : ℝ) * (c * |q - r|) := by ring
          _ ≤ 2 * (n : ℝ) * (m : ℝ) * (18 * (c ^ 2 + δ ^ 2)) := h3
      have h4 : (2 * (n : ℝ) ^ 2 + 2 ^ n) * c ^ 2 = CE * c ^ 2 := by rw [hCE_def]
      linarith only [hT, h1, h2, h4]
    calc |tBip H (1/2) (M.sm r) q c - r ^ m - (αL * c - (m : ℝ) * r ^ (m - 1) * δ)|
        ≤ _ + _ := htri
      _ ≤ ((m : ℝ) ^ 2 * (512 * (c ^ 2 + δ ^ 2))
            + 2 * (n : ℝ) * (m : ℝ) * (18 * (c ^ 2 + δ ^ 2)) + CE * c ^ 2)
          + (m : ℝ) * (28 * (c ^ 2 + δ ^ 2)) := add_le_add hTfinal hT2
      _ ≤ CΨ * (c ^ 2 + δ ^ 2) := by
          rw [hCΨ_def]
          linarith only [mul_nonneg hCE0.le (sq_nonneg δ)]
  -- ### Continuity and the endpoint signs
  have hqcont : ContinuousOn (fun c => qSolve (1/2) (M.sm r) r δ c) (Set.Icc 0 c₀) :=
    continuousOn_qSolve (1/2) (M.sm r) r δ (fun x hx => le_trans hx.2 hc₀12)
  have hΨcont : ContinuousOn
      (fun c => tBip H (1/2) (M.sm r) (qSolve (1/2) (M.sm r) r δ c) c - r ^ m)
      (Set.Icc 0 c₀) :=
    continuousOn_tBip_comp_sub H (1/2) (M.sm r) (r ^ m) hqcont
  have hΨ0 : tBip H (1/2) (M.sm r) (qSolve (1/2) (M.sm r) r δ 0) 0 - r ^ m < 0 := by
    rw [qSolve_zero]
    have hrδIcc : (r - δ) ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · have hδη' : δ < η := by linarith
        linarith
      · linarith
    have hRem0 : tBipRem H (1/2) (M.sm r) (r - δ) 0 = 0 := by
      refine le_antisymm ?_ (tBipRem_nonneg H haIcc hsIcc hrδIcc le_rfl zero_le_one)
      have h1 := tBipRem_le H haIcc hsIcc hrδIcc le_rfl zero_le_one
      simpa using h1
    have hval : tBip H (1/2) (M.sm r) (r - δ) 0 = (r - δ) ^ m := by
      rw [tBip_expansion H hreg, hRem0, ← hn_def, ← hm_def]
      simp
    rw [hval]
    have hlt : (r - δ) ^ m < r ^ m :=
      pow_lt_pow_left₀ (by linarith) hrδIcc.1 (by omega)
    linarith
  have hΨc₀ : 0 < tBip H (1/2) (M.sm r) (qSolve (1/2) (M.sm r) r δ c₀) c₀ - r ^ m := by
    have hc₀mem : c₀ ∈ Set.Icc (0:ℝ) c₀ := ⟨hc₀0.le, le_rfl⟩
    obtain ⟨hl, _⟩ := abs_le.mp (hlin c₀ hc₀mem)
    have hα1 : αmin * c₀ ≤ αL * c₀ := mul_le_mul_of_nonneg_right hαLmin hc₀0.le
    have hmr : (m : ℝ) * r ^ (m - 1) * δ ≤ (m : ℝ) * δ := by
      have h1 : r ^ (m - 1) ≤ 1 := pow_le_one₀ hr0.le hr1.le
      have h2 : (m : ℝ) * r ^ (m - 1) ≤ (m : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left h1 hm0R.le
      calc (m : ℝ) * r ^ (m - 1) * δ ≤ ((m : ℝ) * 1) * δ :=
            mul_le_mul_of_nonneg_right h2 hδ0.le
        _ = (m : ℝ) * δ := by ring
    have h4C : 4 * CΨ * c₀ ≤ αmin := by
      rw [le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 4) hCΨ0)] at hc₀α
      linarith only [hc₀α]
    have hCc : CΨ * c₀ ^ 2 ≤ αmin / 4 * c₀ := by
      have h2 := mul_le_mul_of_nonneg_right h4C hc₀0.le
      linarith only [h2]
    have hδsq : δ ^ 2 ≤ δ :=
      by linarith only [mul_nonneg hδ0.le (sub_nonneg.mpr hδ1)]
    have hCδ : CΨ * δ ^ 2 ≤ CΨ * δ := mul_le_mul_of_nonneg_left hδsq hCΨ0.le
    have hmδ : ((m : ℝ) + CΨ) * δ ≤ αmin * c₀ / 4 := by
      have h1 : ((m : ℝ) + CΨ) * δ ≤ ((m : ℝ) + CΨ) * δ₀ :=
        mul_le_mul_of_nonneg_left hδlt.le hmCΨ0.le
      have h2 : ((m : ℝ) + CΨ) * δ₀ ≤ αmin * c₀ / 4 := by
        rw [le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 4) hmCΨ0)] at hδ₀α
        linarith only [hδ₀α]
      linarith only [h1, h2]
    have hαc₀ : 0 < αmin * c₀ := mul_pos hαmin0 hc₀0
    linarith only [hl, hα1, hmr, hCc, hCδ, hmδ, hαc₀]
  -- ### The intermediate-value solve
  have hivt := intermediate_value_Icc hc₀0.le hΨcont
  have h0mem : (0:ℝ) ∈ Set.Icc
      (tBip H (1/2) (M.sm r) (qSolve (1/2) (M.sm r) r δ 0) 0 - r ^ m)
      (tBip H (1/2) (M.sm r) (qSolve (1/2) (M.sm r) r δ c₀) c₀ - r ^ m) :=
    ⟨hΨ0.le, hΨc₀.le⟩
  obtain ⟨c, hcmem, hroot⟩ := hivt h0mem
  have hrootΨ : tBip H (1/2) (M.sm r) (qSolve (1/2) (M.sm r) r δ c) c - r ^ m = 0 := hroot
  have hc0 : 0 ≤ c := hcmem.1
  have hcc₀ : c ≤ c₀ := hcmem.2
  have hc2 : c ≤ 1/2 := le_trans hcc₀ hc₀12
  have hc1 : c ≤ 1 := le_trans hc2 (by norm_num)
  have hcne1 : c ≠ 1 := by intro h; rw [h] at hc2; norm_num at hc2
  -- ### Root bounds
  have hclin := hlin c ⟨hc0, hcc₀⟩
  rw [hrootΨ] at hclin
  rw [abs_sub_comm, sub_zero] at hclin
  -- `hclin : |αL c - m r^{m-1} δ| ≤ CΨ (c² + δ²)`
  have hcC₁ : c ≤ C₁ * δ := by
    obtain ⟨_, hup⟩ := abs_le.mp hclin
    have hα1 : αmin * c ≤ αL * c := mul_le_mul_of_nonneg_right hαLmin hc0
    have hmr : (m : ℝ) * r ^ (m - 1) * δ ≤ (m : ℝ) * δ := by
      have h1 : r ^ (m - 1) ≤ 1 := pow_le_one₀ hr0.le hr1.le
      have h2 : (m : ℝ) * r ^ (m - 1) ≤ (m : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left h1 hm0R.le
      calc (m : ℝ) * r ^ (m - 1) * δ ≤ ((m : ℝ) * 1) * δ :=
            mul_le_mul_of_nonneg_right h2 hδ0.le
        _ = (m : ℝ) * δ := by ring
    have h4C : 4 * CΨ * c₀ ≤ αmin := by
      rw [le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 4) hCΨ0)] at hc₀α
      linarith only [hc₀α]
    have hCc : CΨ * c ^ 2 ≤ αmin / 4 * c := by
      have h2 : CΨ * c ≤ CΨ * c₀ := mul_le_mul_of_nonneg_left hcc₀ hCΨ0.le
      have h3 := mul_le_mul_of_nonneg_right h2 hc0
      have h4 := mul_le_mul_of_nonneg_right h4C hc0
      linarith only [h3, h4]
    have hδsq : δ ^ 2 ≤ δ :=
      by linarith only [mul_nonneg hδ0.le (sub_nonneg.mpr hδ1)]
    have hCδ : CΨ * δ ^ 2 ≤ CΨ * δ := mul_le_mul_of_nonneg_left hδsq hCΨ0.le
    have hkey : 3 / 4 * (αmin * c) ≤ ((m : ℝ) + CΨ) * δ := by
      linarith only [hup, hα1, hmr, hCc, hCδ]
    rw [hC₁_def, div_mul_eq_mul_div, le_div_iff₀ hαmin0]
    linarith only [hkey, mul_nonneg hmCΨ0.le hδ0.le]
  -- ### The slope-times-`X` bound for the entropy expansion
  obtain ⟨q, hq_def⟩ : ∃ x : ℝ, x = qSolve (1/2) (M.sm r) r δ c := ⟨_, rfl⟩
  rw [← hq_def] at hrootΨ
  have hq01 : q ∈ Set.Icc (0:ℝ) 1 := by rw [hq_def]; exact hqbox01 c ⟨hc0, hcc₀⟩
  have hqβ : q ∈ Set.Icc (η / 2) (1 - η / 2) := by
    rw [hq_def]; exact hqbox c ⟨hc0, hcc₀⟩
  have hlb : |q - r - (2 * c * (r - M.sm r) - δ)| ≤ 28 * (c ^ 2 + δ ^ 2) := by
    rw [hq_def]
    exact qSolve_linear_bound haIcc hsIcc hrIcc hc0 hc2 hδ0.le
  have hXbound : |(d : ℝ) * r ^ (d - 1) * (q - r) + 2 * c * ((M.sm r) ^ d - r ^ d)|
      ≤ CX * (c ^ 2 + δ ^ 2) := by
    have hXsplit : (d : ℝ) * r ^ (d - 1) * (q - r) + 2 * c * ((M.sm r) ^ d - r ^ d)
        = (2 * c * G - (d : ℝ) * r ^ (d - 1) * δ)
          + (d : ℝ) * r ^ (d - 1) * (q - r - (2 * c * (r - M.sm r) - δ)) := by
      rw [hG_def]; ring
    have hE3 : |(d : ℝ) * r ^ (d - 1) * (q - r - (2 * c * (r - M.sm r) - δ))|
        ≤ (d : ℝ) * (28 * (c ^ 2 + δ ^ 2)) := by
      rw [abs_mul, abs_mul]
      have hdabs : |(d : ℝ)| = (d : ℝ) := abs_of_pos hd0R
      have hrabs : |r ^ (d - 1)| ≤ 1 := by
        rw [abs_of_nonneg (pow_nonneg hr0.le _)]
        exact pow_le_one₀ hr0.le hr1.le
      rw [hdabs]
      calc (d : ℝ) * |r ^ (d - 1)| * |q - r - (2 * c * (r - M.sm r) - δ)|
          ≤ (d : ℝ) * 1 * (28 * (c ^ 2 + δ ^ 2)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hrabs hd0R.le) hlb
              (abs_nonneg _) (mul_nonneg hd0R.le zero_le_one)
        _ = (d : ℝ) * (28 * (c ^ 2 + δ ^ 2)) := by ring
    have hpow2 : r ^ (m - d) * r ^ (d - 1) = r ^ (m - 1) := by
      rw [← pow_add]; congr 1; omega
    have hndR : (n : ℝ) * (d : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hnd
    have hXid : (n : ℝ) * r ^ (m - d) * (2 * c * G - (d : ℝ) * r ^ (d - 1) * δ)
        = 2 * (αL * c - (m : ℝ) * r ^ (m - 1) * δ) := by
      rw [hαLG]
      linear_combination (-δ * (n : ℝ) * (d : ℝ)) * hpow2 + (-δ * r ^ (m - 1)) * hndR
    have hnr0 : (0:ℝ) < (n : ℝ) * r ^ (m - d) := mul_pos hn0R (pow_pos hr0 _)
    have hX'bound : |2 * c * G - (d : ℝ) * r ^ (d - 1) * δ|
        ≤ 2 * CΨ / η ^ (m - d) * (c ^ 2 + δ ^ 2) := by
      have habs : (n : ℝ) * r ^ (m - d) * |2 * c * G - (d : ℝ) * r ^ (d - 1) * δ|
          = 2 * |αL * c - (m : ℝ) * r ^ (m - 1) * δ| := by
        rw [show (n : ℝ) * r ^ (m - d) * |2 * c * G - (d : ℝ) * r ^ (d - 1) * δ|
            = |(n : ℝ) * r ^ (m - d)| * |2 * c * G - (d : ℝ) * r ^ (d - 1) * δ|
          from by rw [abs_of_pos hnr0], ← abs_mul, hXid, abs_mul]
        norm_num
      have hηr' : η ^ (m - d) ≤ (n : ℝ) * r ^ (m - d) := by
        calc η ^ (m - d) ≤ r ^ (m - d) := pow_le_pow_left₀ hη0.le hηr _
          _ = 1 * r ^ (m - d) := (one_mul _).symm
          _ ≤ (n : ℝ) * r ^ (m - d) :=
              mul_le_mul_of_nonneg_right hnR (pow_nonneg hr0.le _)
      have h1 : η ^ (m - d) * |2 * c * G - (d : ℝ) * r ^ (d - 1) * δ|
          ≤ 2 * CΨ * (c ^ 2 + δ ^ 2) := by
        calc η ^ (m - d) * |2 * c * G - (d : ℝ) * r ^ (d - 1) * δ|
            ≤ (n : ℝ) * r ^ (m - d) * |2 * c * G - (d : ℝ) * r ^ (d - 1) * δ| :=
              mul_le_mul_of_nonneg_right hηr' (abs_nonneg _)
          _ = 2 * |αL * c - (m : ℝ) * r ^ (m - 1) * δ| := habs
          _ ≤ 2 * (CΨ * (c ^ 2 + δ ^ 2)) :=
              mul_le_mul_of_nonneg_left hclin (by norm_num)
          _ = 2 * CΨ * (c ^ 2 + δ ^ 2) := by ring
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hη0 (m - d))]
      linarith only [h1]
    calc |(d : ℝ) * r ^ (d - 1) * (q - r) + 2 * c * ((M.sm r) ^ d - r ^ d)|
        ≤ |2 * c * G - (d : ℝ) * r ^ (d - 1) * δ|
          + |(d : ℝ) * r ^ (d - 1) * (q - r - (2 * c * (r - M.sm r) - δ))| := by
          rw [hXsplit]; exact abs_add_le _ _
      _ ≤ 2 * CΨ / η ^ (m - d) * (c ^ 2 + δ ^ 2) + (d : ℝ) * (28 * (c ^ 2 + δ ^ 2)) :=
          add_le_add hX'bound hE3
      _ = CX * (c ^ 2 + δ ^ 2) := by rw [hCX_def]; ring
  -- ### Assemble the graphon
  refine ⟨bipodalGraphon (Set.Icc 0 c) measurableSet_Icc (1/2) (M.sm r) q haIcc hsIcc hq01,
    ?_, ?_, ?_, ?_⟩
  · -- edge density
    rw [bipodalGraphon_edgeDensity, unitμ_Icc_toReal hc0 hc1, hq_def]
    exact qSolve_edge (1/2) (M.sm r) r δ hcne1
  · -- `H`-density
    rw [tBip_eq_tDensity H haIcc hsIcc hq01 hc0 hc1]
    linarith only [hrootΨ]
  · -- bipodality
    exact ⟨Set.Icc 0 c, 1/2, M.sm r, q, measurableSet_Icc, haIcc, hsIcc, hq01,
      Filter.Eventually.of_forall fun _ => rfl⟩
  · -- the entropy bound
    rw [Ip_bipodalGraphon_Icc hpc0 hpc1 haIcc hsIcc hq01 hc0 hc1]
    -- box memberships for the `Jp` estimates
    have hpβ : M.pc r ∈ Set.Icc (η / 2) (1 - η / 2) :=
      ⟨by linarith only [hηpc, hη0], by linarith only [hpcr, hr1', hη0]⟩
    have hrβ : r ∈ Set.Icc (η / 2) (1 - η / 2) :=
      ⟨by linarith only [hηr, hη0], by linarith only [hr1', hη0]⟩
    have hsβ : M.sm r ∈ Set.Icc (η / 2) (1 - η / 2) :=
      ⟨by linarith only [hηs, hη0], by linarith only [hs1', hη0]⟩
    have haβ : (1/2 : ℝ) ∈ Set.Icc (η / 2) (1 - η / 2) :=
      ⟨by linarith only [hη12], by linarith only [hη12, hη0]⟩
    -- Taylor expansion of `Jp` at `r`
    have hJT : |Jp (M.pc r) q - Jp (M.pc r) r - Jp' (M.pc r) r * (q - r)|
        ≤ MJ * (q - r) ^ 2 := by
      rw [hMJ_def]
      exact Jp_taylor_box hβ0 hpc0 hpc1 hqβ hrβ
    have hw : |q - r| ≤ 16 * c + 4 * δ := by
      rw [hq_def]
      exact qSolve_dev_bound haIcc hsIcc hrIcc hc0 hc2 hδ0.le
    have hw2 : (q - r) ^ 2 ≤ 512 * (c ^ 2 + δ ^ 2) := abs_le_sq_bound hc0 hδ0.le hw
    have hcw : c * |q - r| ≤ 18 * (c ^ 2 + δ ^ 2) := abs_le_mul_bound hc0 hδ0.le hw
    -- the second-contact identity
    have hsecond : Jp (M.pc r) (M.sm r)
        = Jp (M.pc r) r + slope d M.pc r * ((M.sm r) ^ d - r ^ d) :=
      M.secondContact r (hK hr)
    -- the slope identity and bound
    have hdr0 : ((d : ℝ) * r ^ (d - 1)) ≠ 0 :=
      (mul_pos hd0R (pow_pos hr0 _)).ne'
    have hslope_id : Jp' (M.pc r) r = slope d M.pc r * ((d : ℝ) * r ^ (d - 1)) := by
      unfold slope
      exact (div_mul_cancel₀ _ hdr0).symm
    have hslope_abs : |slope d M.pc r| ≤ Lslope := by
      unfold slope
      rw [abs_div, hLslope_def]
      have hnum : |Jp' (M.pc r) r| ≤ 4 * (-Real.log η) :=
        Jp'_abs_le_box hη0 ⟨hηpc, by linarith only [hpcr, hr1']⟩ ⟨hηr, hr1'⟩
      have hden : (d : ℝ) * η ^ (d - 1) ≤ |(d : ℝ) * r ^ (d - 1)| := by
        rw [abs_of_pos (mul_pos hd0R (pow_pos hr0 _))]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη0.le hηr _) hd0R.le
      exact div_le_div₀ (by linarith only [hlogη]) hnum
        (mul_pos hd0R (pow_pos hη0 _)) hden
    -- the `Jp`-difference bound
    have hqr1 : |q - r| ≤ 1 := by
      have h1 := hqβ.1
      have h2 := hqβ.2
      exact abs_le.mpr ⟨by linarith only [h1, hη0, hr1], by linarith only [h2, hη0, hr0]⟩
    have hJp'r : |Jp' (M.pc r) r| ≤ LJb := by
      rw [hLJb_def]
      exact Jp'_abs_le_box hβ0 hpβ hrβ
    have hJdiff : |Jp (M.pc r) r - Jp (M.pc r) q| ≤ (LJb + MJ) * |q - r| := by
      have h1 : |Jp (M.pc r) q - Jp (M.pc r) r|
          ≤ MJ * (q - r) ^ 2 + |Jp' (M.pc r) r * (q - r)| := by
        have habs := abs_add_le
          (Jp (M.pc r) q - Jp (M.pc r) r - Jp' (M.pc r) r * (q - r))
          (Jp' (M.pc r) r * (q - r))
        have heq : Jp (M.pc r) q - Jp (M.pc r) r - Jp' (M.pc r) r * (q - r)
            + Jp' (M.pc r) r * (q - r) = Jp (M.pc r) q - Jp (M.pc r) r := by ring
        -- fold the sum back
        rw [heq] at habs
        linarith only [habs, hJT]
      have h2 : |Jp' (M.pc r) r * (q - r)| ≤ LJb * |q - r| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hJp'r (abs_nonneg _)
      have h3 : MJ * (q - r) ^ 2 ≤ MJ * |q - r| := by
        have h4 : (q - r) ^ 2 ≤ |q - r| := by
          calc (q - r) ^ 2 = |q - r| * |q - r| := by
                rw [← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]
            _ ≤ 1 * |q - r| := mul_le_mul_of_nonneg_right hqr1 (abs_nonneg _)
            _ = |q - r| := one_mul _
        exact mul_le_mul_of_nonneg_left h4 hMJ0.le
      rw [abs_sub_comm]
      calc |Jp (M.pc r) q - Jp (M.pc r) r|
          ≤ MJ * (q - r) ^ 2 + |Jp' (M.pc r) r * (q - r)| := h1
        _ ≤ MJ * |q - r| + LJb * |q - r| := add_le_add h3 h2
        _ = (LJb + MJ) * |q - r| := by ring
    -- the `Jp`-magnitude bounds
    have hJa : |Jp (M.pc r) (1/2)| ≤ JM := by
      rw [hJM_def]; exact Jp_abs_le_box hβ0 hpβ haβ
    have hJs : |Jp (M.pc r) (M.sm r)| ≤ JM := by
      rw [hJM_def]; exact Jp_abs_le_box hβ0 hpβ hsβ
    have hJq : |Jp (M.pc r) q| ≤ JM := by
      rw [hJM_def]; exact Jp_abs_le_box hβ0 hpβ hqβ
    -- the decomposition of the entropy excess
    have hdecomp : c ^ 2 * Jp (M.pc r) (1/2) + 2 * c * (1 - c) * Jp (M.pc r) (M.sm r)
        + (1 - c) ^ 2 * Jp (M.pc r) q - Jp (M.pc r) r
        = (Jp (M.pc r) q - Jp (M.pc r) r - Jp' (M.pc r) r * (q - r))
          + (Jp' (M.pc r) r * (q - r)
            + 2 * c * (slope d M.pc r * ((M.sm r) ^ d - r ^ d)))
          + 2 * c * (Jp (M.pc r) r - Jp (M.pc r) q)
          + c ^ 2 * (Jp (M.pc r) (1/2) - 2 * Jp (M.pc r) (M.sm r) + Jp (M.pc r) q)
          + 2 * c * (Jp (M.pc r) (M.sm r) - Jp (M.pc r) r
            - slope d M.pc r * ((M.sm r) ^ d - r ^ d)) := by
      ring
    have hzero : Jp (M.pc r) (M.sm r) - Jp (M.pc r) r
        - slope d M.pc r * ((M.sm r) ^ d - r ^ d) = 0 := by
      rw [hsecond]; ring
    -- bound the four surviving terms
    have hslopeX : |Jp' (M.pc r) r * (q - r)
        + 2 * c * (slope d M.pc r * ((M.sm r) ^ d - r ^ d))|
        ≤ Lslope * (CX * (c ^ 2 + δ ^ 2)) := by
      have hexp : Jp' (M.pc r) r * (q - r)
          + 2 * c * (slope d M.pc r * ((M.sm r) ^ d - r ^ d))
          = slope d M.pc r
            * ((d : ℝ) * r ^ (d - 1) * (q - r) + 2 * c * ((M.sm r) ^ d - r ^ d)) := by
        rw [hslope_id]; ring
      rw [hexp, abs_mul]
      exact mul_le_mul hslope_abs hXbound (abs_nonneg _) hLslope0
    have hterm3 : |2 * c * (Jp (M.pc r) r - Jp (M.pc r) q)|
        ≤ 36 * (LJb + MJ) * (c ^ 2 + δ ^ 2) := by
      rw [abs_mul]
      have h2c : |2 * c| = 2 * c := abs_of_nonneg (by linarith only [hc0])
      rw [h2c]
      calc 2 * c * |Jp (M.pc r) r - Jp (M.pc r) q|
          ≤ 2 * c * ((LJb + MJ) * |q - r|) :=
            mul_le_mul_of_nonneg_left hJdiff (by linarith only [hc0])
        _ = 2 * (LJb + MJ) * (c * |q - r|) := by ring
        _ ≤ 2 * (LJb + MJ) * (18 * (c ^ 2 + δ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left hcw ?_
            linarith only [hLJb0, hMJ0]
        _ = 36 * (LJb + MJ) * (c ^ 2 + δ ^ 2) := by ring
    have hterm4 : |c ^ 2 * (Jp (M.pc r) (1/2) - 2 * Jp (M.pc r) (M.sm r) + Jp (M.pc r) q)|
        ≤ 4 * JM * c ^ 2 := by
      have h2s : |2 * Jp (M.pc r) (M.sm r)| ≤ 2 * JM := by
        rw [abs_mul, abs_two]
        linarith only [hJs]
      have h1 : |Jp (M.pc r) (1/2) - 2 * Jp (M.pc r) (M.sm r) + Jp (M.pc r) q|
          ≤ 4 * JM := by
        have t1 := abs_add_le
          (Jp (M.pc r) (1/2) - 2 * Jp (M.pc r) (M.sm r)) (Jp (M.pc r) q)
        have t2 := abs_sub (Jp (M.pc r) (1/2)) (2 * Jp (M.pc r) (M.sm r))
        linarith only [t1, t2, hJa, hJq, h2s]
      calc |c ^ 2 * (Jp (M.pc r) (1/2) - 2 * Jp (M.pc r) (M.sm r) + Jp (M.pc r) q)|
          = c ^ 2 * |Jp (M.pc r) (1/2) - 2 * Jp (M.pc r) (M.sm r) + Jp (M.pc r) q| := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg c)]
        _ ≤ c ^ 2 * (4 * JM) := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
        _ = 4 * JM * c ^ 2 := by ring
    have hMJw : MJ * (q - r) ^ 2 ≤ MJ * (512 * (c ^ 2 + δ ^ 2)) :=
      mul_le_mul_of_nonneg_left hw2 hMJ0.le
    -- assemble
    have hsum : c ^ 2 * Jp (M.pc r) (1/2) + 2 * c * (1 - c) * Jp (M.pc r) (M.sm r)
        + (1 - c) ^ 2 * Jp (M.pc r) q - Jp (M.pc r) r
        ≤ CI * (c ^ 2 + δ ^ 2) := by
      rw [hdecomp, hzero, mul_zero, add_zero]
      have h1 := le_trans (le_abs_self _) hJT
      have h2 := le_trans (le_abs_self _) hslopeX
      have h3 := le_trans (le_abs_self _) hterm3
      have h4 := le_trans (le_abs_self _) hterm4
      rw [hCI_def]
      linarith only [h1, h2, h3, h4, hMJw, mul_nonneg hJM0 (sq_nonneg δ)]
    have hfinal : CI * (c ^ 2 + δ ^ 2) ≤ CI * (C₁ ^ 2 + 1) * δ ^ 2 := by
      have hcsq : c ^ 2 ≤ C₁ ^ 2 * δ ^ 2 := by
        calc c ^ 2 ≤ (C₁ * δ) ^ 2 := pow_le_pow_left₀ hc0 hcC₁ 2
          _ = C₁ ^ 2 * δ ^ 2 := by ring
      calc CI * (c ^ 2 + δ ^ 2) ≤ CI * (C₁ ^ 2 * δ ^ 2 + δ ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hCI0.le
            linarith only [hcsq]
        _ = CI * (C₁ ^ 2 + 1) * δ ^ 2 := by ring
    linarith only [hsum, hfinal]

end UpperTailOptimizers
