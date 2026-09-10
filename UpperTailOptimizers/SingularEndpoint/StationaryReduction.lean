import UpperTailOptimizers.SingularEndpoint.StationaryVariation

/-!
# From `eq:graphon-stationarity` to the scalar equation `eq:rank-one-kkt`

The reduction that opens the proof of `lem:stationary-rank-one-bipodality`.  Combining the two
first variations,

  `0 = ∬ J_p'(f(x)f(y)) U - μ m q^{v-2} ∬ f(x)^{d-1}f(y)^{d-1} U
     = ∬ [J_p'(f(x)f(y)) - γ (f(x)f(y))^{d-1}] U = ∬ F_{p,γ}(f(x)f(y)) U`

for every bounded symmetric `U`, with `γ := μ m q^{v-2}`.  Testing against
`U = F_{p,γ}(f⊗f)` — itself bounded and symmetric — makes the left side `∬ F_{p,γ}(f⊗f)²`, so
`F_{p,γ}(f(x)f(y)) = 0` almost everywhere.  That is `eq:rank-one-kkt`, the hypothesis from which
the rest of Section 7 works.

`lem:rank-one-kkt-family` states the relation as an *equivalence* — the constructed family
satisfies the KKT conditions and `eq:block-stationarity`, and conversely those conditions pin the
family — so both directions are proved here.

## Contents

* `rankOneGraphon` — the graphon `f ⊗ f`;
* `kkt_scalar_of_stationary`, `isStationary_of_kkt_scalar` — `eq:graphon-stationarity` and
  `eq:rank-one-kkt` imply each other;
* `blockGraphon`, `IsBlockStationary`, `blockStationary_iff_rowBalance`,
  `rowBalance_of_blockStationary` — `eq:block-stationarity` and the block-balance equation
  of `KKTFamily.rowBalance` are equivalent;
* `stationary_rank_one_two_values` — `lem:stationary-rank-one-bipodality` from its variational
  hypothesis: a rank-one graphon satisfying the KKT conditions has an at most two-valued factor.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory Filter Topology

/-- The rank-one graphon `f ⊗ f`. -/
noncomputable def rankOneGraphon {f : ℝ → ℝ} (hf : Measurable f) (h0 : ∀ y, 0 ≤ f y)
    (h1 : ∀ y, f y ≤ 1) : Graphon where
  toFun x y := f x * f y
  symm' _ _ := mul_comm _ _
  meas' := (hf.comp measurable_fst).mul (hf.comp measurable_snd)
  nonneg' x y := mul_nonneg (h0 x) (h0 y)
  le_one' x y := mul_le_one₀ (h1 x) (h0 y) (h1 y)

@[simp] theorem rankOneGraphon_toFun {f : ℝ → ℝ} (hf : Measurable f) (h0 : ∀ y, 0 ≤ f y)
    (h1 : ∀ y, f y ≤ 1) (x y : ℝ) : (rankOneGraphon hf h0 h1).toFun x y = f x * f y := rfl

theorem graphonKernel_rankOneGraphon {f : ℝ → ℝ} (hf : Measurable f) (h0 : ∀ y, 0 ≤ f y)
    (h1 : ∀ y, f y ≤ 1) : graphonKernel (rankOneGraphon hf h0 h1) = rankOneKernel hf := rfl

/-- **`eq:graphon-stationarity` implies `eq:rank-one-kkt`.**  If the interior rank-one graphon
`f ⊗ f` is stationary for `I_p - μ t(H,·)`, then with

  `γ := μ · e(H) · q(f)^{v-2}`,   `q(f) = ∫ f^d`,

the scalar equation `F_{p,γ}(f(x)f(y)) = 0` holds for `gμ`-almost every `(x,y)`. -/
theorem kkt_scalar_of_stationary {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) {p μ η : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hη : 0 < η) {f : ℝ → ℝ} (hfm : Measurable f)
    (hf0 : ∀ y, η ≤ f y) (hf1 : ∀ y, f y ≤ 1 - η)
    (hstat : IsStationary H p μ
      (rankOneGraphon hfm (fun y => le_trans hη.le (hf0 y))
        (fun y => le_trans (hf1 y) (by linarith)))) :
    ∀ᵐ z ∂gμ, Fkkt d p
      (μ * (H.edgeFinset.card : ℝ) * (∫ y, f y ^ d ∂unitμ) ^ (Fintype.card V - 2))
      (f z.1 * f z.2) = 0 := by
  classical
  have hηle : η ≤ 1 - η := le_trans (hf0 0) (hf1 0)
  have hη1 : η < 1 := by linarith
  set h0 : ∀ y, (0:ℝ) ≤ f y := fun y => le_trans hη.le (hf0 y) with hh0
  set h1 : ∀ y, f y ≤ 1 := fun y => le_trans (hf1 y) (by linarith) with hh1
  set W : Graphon := rankOneGraphon hfm h0 h1 with hW
  set q : ℝ := ∫ y, f y ^ d ∂unitμ with hq
  set γ : ℝ := μ * (H.edgeFinset.card : ℝ) * q ^ (Fintype.card V - 2) with hγ
  -- the interiority window for `W = f ⊗ f`
  have hW0 : ∀ x y, η ^ 2 ≤ W.toFun x y := by
    intro x y
    have := mul_le_mul (hf0 x) (hf0 y) hη.le (le_trans hη.le (hf0 x))
    simpa [hW, sq] using this
  have hW1 : ∀ x y, W.toFun x y ≤ 1 - η ^ 2 := by
    intro x y
    have hle : f x * f y ≤ (1 - η) * (1 - η) :=
      mul_le_mul (hf1 x) (hf1 y) (h0 y) (by linarith)
    have : (1 - η) * (1 - η) ≤ 1 - η ^ 2 := by nlinarith
    simpa [hW] using le_trans hle this
  have hη2 : (0:ℝ) < η ^ 2 := by positivity
  -- the test direction `U = F_{p,γ}(f ⊗ f)`
  set Φ : ℝ → ℝ → ℝ := fun x y => Fkkt d p γ (f x * f y) with hΦ
  have hΦsymm : ∀ x y, Φ x y = Φ y x := by intro x y; rw [hΦ]; simp [mul_comm]
  have hΦmeas : Measurable fun z : ℝ × ℝ => Φ z.1 z.2 := by
    have hmul : Measurable fun z : ℝ × ℝ => f z.1 * f z.2 :=
      (hfm.comp measurable_fst).mul (hfm.comp measurable_snd)
    exact ((measurable_Jp' p).comp hmul).sub (measurable_const.mul (hmul.pow_const _))
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x y, |Φ x y| ≤ B := by
    refine ⟨(|ell p| + (|Real.log (η ^ 2)| + |Real.log (1 - (1 - η ^ 2))|)) + |γ|, fun x y => ?_⟩
    have hmem : f x * f y ∈ Set.Icc (η ^ 2) (1 - η ^ 2) := ⟨hW0 x y, hW1 x y⟩
    have hJ := abs_Jp'_le hp0 hp1 hη2 (by linarith : (1:ℝ) - η ^ 2 < 1) hmem
    have hz0 : (0:ℝ) ≤ f x * f y := mul_nonneg (h0 x) (h0 y)
    have hz1 : f x * f y ≤ 1 := mul_le_one₀ (h1 x) (h0 y) (h1 y)
    have hpow : |(f x * f y) ^ (d - 1)| ≤ 1 := by
      rw [abs_pow, abs_of_nonneg hz0]
      exact pow_le_one₀ hz0 hz1
    calc |Φ x y| = |Jp' p (f x * f y) - γ * (f x * f y) ^ (d - 1)| := rfl
      _ ≤ |Jp' p (f x * f y)| + |γ * (f x * f y) ^ (d - 1)| := abs_sub _ _
      _ ≤ (|ell p| + (|Real.log (η ^ 2)| + |Real.log (1 - (1 - η ^ 2))|)) + |γ| := by
          rw [abs_mul]
          have : |γ| * |(f x * f y) ^ (d - 1)| ≤ |γ| * 1 :=
            mul_le_mul_of_nonneg_left hpow (abs_nonneg γ)
          linarith
  set U : Direction := ⟨⟨Φ, hΦsymm, hΦmeas⟩, B, hB⟩ with hU
  -- the two first variations
  have hIp := hasDerivAt_Ip_pert W U hp0 hp1 hη2 hW0 hW1
  have htD := hasDerivAt_tDensity_pert H W U hη2 hW0 hW1
  have hsub := hIp.sub (htD.const_mul μ)
  have huniq := (hstat U).unique hsub
  -- evaluate the `t`-variation
  have hteval : ∫ x : V → ℝ, ∑ e ∈ H.edgeFinset,
      (∏ e' ∈ H.edgeFinset.erase e, edgeVal (graphonKernel W) x e')
        * edgeVal U.toSymKernel x e ∂(Measure.pi fun _ : V => unitμ)
      = (H.edgeFinset.card : ℝ) * q ^ (Fintype.card V - 2)
        * ∫ z, f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * Φ z.1 z.2 ∂gμ := by
    rw [hW, graphonKernel_rankOneGraphon]
    exact tDensity_variation_rankOne H hreg hfm
      (fun y => lt_of_lt_of_le hη (hf0 y)) h1 U
  rw [hteval] at huniq
  -- integrability of the three integrands
  have hmulm : Measurable fun z : ℝ × ℝ => f z.1 * f z.2 :=
    (hfm.comp measurable_fst).mul (hfm.comp measurable_snd)
  have hAm : Measurable fun z : ℝ × ℝ => Jp' p (f z.1 * f z.2) * Φ z.1 z.2 :=
    ((measurable_Jp' p).comp hmulm).mul hΦmeas
  have hBm : Measurable fun z : ℝ × ℝ =>
      f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * Φ z.1 z.2 :=
    (((hfm.comp measurable_fst).pow_const _).mul
      ((hfm.comp measurable_snd).pow_const _)).mul hΦmeas
  have hAint : Integrable (fun z : ℝ × ℝ => Jp' p (f z.1 * f z.2) * Φ z.1 z.2) gμ := by
    refine integrable_of_abs_le hAm
      ((|ell p| + (|Real.log (η ^ 2)| + |Real.log (1 - (1 - η ^ 2))|)) * |B|) (fun z => ?_)
    have hmem : f z.1 * f z.2 ∈ Set.Icc (η ^ 2) (1 - η ^ 2) := ⟨hW0 z.1 z.2, hW1 z.1 z.2⟩
    have hJ := abs_Jp'_le hp0 hp1 hη2 (by linarith : (1:ℝ) - η ^ 2 < 1) hmem
    rw [abs_mul]
    exact mul_le_mul hJ (le_trans (hB z.1 z.2) (le_abs_self B)) (abs_nonneg _) (by positivity)
  have hBint : Integrable
      (fun z : ℝ × ℝ => f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * Φ z.1 z.2) gμ := by
    refine integrable_of_abs_le hBm |B| (fun z => ?_)
    have hp1' : |f z.1 ^ (d - 1)| ≤ 1 := by
      rw [abs_pow, abs_of_nonneg (h0 _)]; exact pow_le_one₀ (h0 _) (h1 _)
    have hp2' : |f z.2 ^ (d - 1)| ≤ 1 := by
      rw [abs_pow, abs_of_nonneg (h0 _)]; exact pow_le_one₀ (h0 _) (h1 _)
    rw [abs_mul, abs_mul]
    calc |f z.1 ^ (d - 1)| * |f z.2 ^ (d - 1)| * |Φ z.1 z.2|
        ≤ 1 * 1 * |B| := by
          refine mul_le_mul (mul_le_mul hp1' hp2' (abs_nonneg _) zero_le_one)
            (le_trans (hB z.1 z.2) (le_abs_self B)) (abs_nonneg _) (by norm_num)
      _ = |B| := by ring
  -- assemble into `∬ Φ² = 0`
  have huniq' : (0:ℝ) = (∫ z, Jp' p (f z.1 * f z.2) * Φ z.1 z.2 ∂gμ)
      - μ * ((H.edgeFinset.card : ℝ) * q ^ (Fintype.card V - 2)
        * ∫ z, f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * Φ z.1 z.2 ∂gμ) := huniq
  have hsq : ∫ z, Φ z.1 z.2 * Φ z.1 z.2 ∂gμ = 0 := by
    have hcomb : (∫ z, Jp' p (f z.1 * f z.2) * Φ z.1 z.2 ∂gμ)
        - γ * ∫ z, f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * Φ z.1 z.2 ∂gμ
        = ∫ z, Φ z.1 z.2 * Φ z.1 z.2 ∂gμ := by
      rw [← integral_const_mul, ← integral_sub hAint (hBint.const_mul γ)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      show Jp' p (f z.1 * f z.2) * Φ z.1 z.2
          - γ * (f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * Φ z.1 z.2)
          = Φ z.1 z.2 * Φ z.1 z.2
      rw [show f z.1 ^ (d - 1) * f z.2 ^ (d - 1) = (f z.1 * f z.2) ^ (d - 1) from
        (mul_pow _ _ _).symm, hΦ]
      simp only [Fkkt]
      ring
    rw [← hcomb, hγ]
    linear_combination -huniq'
  -- a nonnegative integrand with zero integral vanishes a.e.
  have hnn : 0 ≤ᵐ[gμ] fun z : ℝ × ℝ => Φ z.1 z.2 * Φ z.1 z.2 :=
    Eventually.of_forall fun z => mul_self_nonneg _
  have hint : Integrable (fun z : ℝ × ℝ => Φ z.1 z.2 * Φ z.1 z.2) gμ := by
    refine integrable_of_abs_le (hΦmeas.mul hΦmeas) (|B| * |B|) (fun z => ?_)
    rw [abs_mul]
    exact mul_le_mul (le_trans (hB z.1 z.2) (le_abs_self B))
      (le_trans (hB z.1 z.2) (le_abs_self B)) (abs_nonneg _) (abs_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hsq
  filter_upwards [hae] with z hz
  have : Φ z.1 z.2 * Φ z.1 z.2 = 0 := hz
  have hΦ0 : Φ z.1 z.2 = 0 := by nlinarith [this]
  exact hΦ0


/-! ## `eq:block-stationarity` and the block-balance equation -/

/-- `W_{β,s,t}`, the two-block rank-one graphon with block `[0,β]` and factor values `s`, `t`.
Only the block moves with `β`; the three values are fixed. -/
noncomputable def blockGraphon {s t : ℝ} (h11 : s ^ 2 ∈ Set.Icc (0:ℝ) 1)
    (h12 : s * t ∈ Set.Icc (0:ℝ) 1) (h22 : t ^ 2 ∈ Set.Icc (0:ℝ) 1) (β : ℝ) : Graphon :=
  bipodalGraphon (Set.Icc 0 β) measurableSet_Icc (s ^ 2) (s * t) (t ^ 2) h11 h12 h22

/-- **`eq:block-stationarity`.**  The separate first-order condition for the block proportion:

  `d/dβ|_{β=α} [I_p(W_{β,s,t}) - μ t(H, W_{β,s,t})] = 0`.

The paper imposes it separately because moving the block boundary is not a small perturbation
in `L^∞`, so it is not covered by `eq:graphon-stationarity`. -/
def IsBlockStationary {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (p μ : ℝ) {s t : ℝ} (h11 : s ^ 2 ∈ Set.Icc (0:ℝ) 1)
    (h12 : s * t ∈ Set.Icc (0:ℝ) 1) (h22 : t ^ 2 ∈ Set.Icc (0:ℝ) 1) (α : ℝ) : Prop :=
  HasDerivAt (fun β : ℝ => (blockGraphon h11 h12 h22 β).Ip p
    - μ * (blockGraphon h11 h12 h22 β).tDensity H) 0 α

/-- **`eq:block-stationarity` is the block-balance equation.**  With
`γ := μ · e(H) · q^{v-2}` and `q := α s^d + (1-α) t^d`, block stationarity at an interior `α` is
exactly the `rowBalance` field of `KKTFamily`:

  `α (𝓜(s²) - 𝓜(st)) = (1-α) (𝓜(t²) - 𝓜(st))`,   `𝓜 = 𝓜_{d,p,γ}`.

Both sides are read off one identity.  Differentiating the two explicit formulas —
`I_p(W_β) = β²J(s²) + 2β(1-β)J(st) + (1-β)²J(t²)` and `t(H,W_β) = (βs^d + (1-β)t^d)^v` — gives a
derivative `D`, and `hbridge` below says the block-balance defect is exactly `D/2`.  Matching the
two multipliers uses the handshake identity `d·v = 2·e(H)`, which is what turns
`μ v q^{v-1}/2` into `γ q / d`. -/
theorem blockStationary_iff_rowBalance {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) (hcard : 1 ≤ H.edgeFinset.card)
    {p μ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {s t α : ℝ} (h11 : s ^ 2 ∈ Set.Icc (0:ℝ) 1)
    (h12 : s * t ∈ Set.Icc (0:ℝ) 1) (h22 : t ^ 2 ∈ Set.Icc (0:ℝ) 1)
    (hα0 : 0 < α) (hα1 : α < 1) :
    IsBlockStationary H p μ h11 h12 h22 α ↔
      α * (Mfun d p (μ * (H.edgeFinset.card : ℝ)
            * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (s ^ 2)
          - Mfun d p (μ * (H.edgeFinset.card : ℝ)
            * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (s * t))
        = (1 - α) * (Mfun d p (μ * (H.edgeFinset.card : ℝ)
            * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (t ^ 2)
          - Mfun d p (μ * (H.edgeFinset.card : ℝ)
            * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (s * t)) := by
  classical
  set v : ℕ := Fintype.card V with hv
  set S : ℝ := s ^ d with hS
  set T : ℝ := t ^ d with hT
  set q : ℝ := α * S + (1 - α) * T with hqdef
  set γ : ℝ := μ * (H.edgeFinset.card : ℝ) * q ^ (v - 2) with hγ
  -- two vertices and degree at least one, since `H` has an edge
  have hvd : 2 ≤ v ∧ 1 ≤ d := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hcard
    induction e using Sym2.ind with
    | _ a b =>
      have hadj : H.Adj a b := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hdeg : 1 ≤ H.degree a := Finset.card_pos.mpr ⟨b, by simpa using hadj⟩
      refine ⟨?_, by rwa [hreg a] at hdeg⟩
      rw [hv]
      exact Fintype.one_lt_card_iff_nontrivial.mpr ⟨a, b, hadj.ne⟩
  have hv2 : 2 ≤ v := hvd.1
  have hd1 : 1 ≤ d := hvd.2
  -- the objective agrees with an explicit polynomial near `α`
  set G : ℝ → ℝ := fun β : ℝ =>
    (β ^ 2 * Jp p (s ^ 2) + 2 * β * (1 - β) * Jp p (s * t) + (1 - β) ^ 2 * Jp p (t ^ 2))
      - μ * (β * S + (1 - β) * T) ^ v with hG
  have hevent : (fun β : ℝ => (blockGraphon h11 h12 h22 β).Ip p
      - μ * (blockGraphon h11 h12 h22 β).tDensity H) =ᶠ[nhds α] G := by
    filter_upwards [Ioo_mem_nhds hα0 hα1] with β hβ
    rw [hG, blockGraphon,
      Ip_bipodalGraphon_Icc hp0 hp1 h11 h12 h22 hβ.1.le hβ.2.le,
      tDensity_rankOne_two_block H hreg h11 h12 h22 hβ.1.le hβ.2.le, hS, hT, hv]
  -- differentiate the polynomial
  have hbase : HasDerivAt (fun β : ℝ => β * S + (1 - β) * T) (S - T) α := by
    have h1 : HasDerivAt (fun β : ℝ => β * S) S α := by
      simpa using (hasDerivAt_id α).mul_const S
    have h2 : HasDerivAt (fun β : ℝ => (1 - β) * T) (-T) α := by
      simpa using ((hasDerivAt_id α).const_sub 1).mul_const T
    have h3 : HasDerivAt (fun β : ℝ => β * S + (1 - β) * T) (S + -T) α := h1.add h2
    have hst : S + -T = S - T := by ring
    rwa [hst] at h3
  have hpow : HasDerivAt (fun β : ℝ => (β * S + (1 - β) * T) ^ v)
      ((v : ℝ) * q ^ (v - 1) * (S - T)) α := by
    have h := hbase.pow v
    rw [hqdef]
    exact h
  have hent : HasDerivAt (fun β : ℝ =>
      β ^ 2 * Jp p (s ^ 2) + 2 * β * (1 - β) * Jp p (s * t) + (1 - β) ^ 2 * Jp p (t ^ 2))
      (2 * α * Jp p (s ^ 2) + (2 - 4 * α) * Jp p (s * t) - 2 * (1 - α) * Jp p (t ^ 2)) α := by
    have h1 : HasDerivAt (fun β : ℝ => β ^ 2 * Jp p (s ^ 2)) (2 * α * Jp p (s ^ 2)) α := by
      have h := (hasDerivAt_pow 2 α).mul_const (Jp p (s ^ 2))
      have heq : ((2:ℕ) : ℝ) * α ^ (2 - 1) * Jp p (s ^ 2) = 2 * α * Jp p (s ^ 2) := by norm_num
      rwa [heq] at h
    have hq : HasDerivAt (fun β : ℝ => 2 * β * (1 - β)) (2 - 4 * α) α := by
      have ha : HasDerivAt (fun β : ℝ => 2 * β) 2 α := by
        simpa using (hasDerivAt_id α).const_mul (2:ℝ)
      have hb : HasDerivAt (fun β : ℝ => 1 - β) (-1) α := by
        simpa using (hasDerivAt_id α).const_sub 1
      have h := ha.mul hb
      have heq : (2:ℝ) * (1 - α) + 2 * α * (-1) = 2 - 4 * α := by ring
      rwa [heq] at h
    have h2 : HasDerivAt (fun β : ℝ => 2 * β * (1 - β) * Jp p (s * t))
        ((2 - 4 * α) * Jp p (s * t)) α := hq.mul_const _
    have hbl : HasDerivAt (fun β : ℝ => 1 - β) (-1) α := by
      simpa using (hasDerivAt_id α).const_sub 1
    have hb2 : HasDerivAt (fun β : ℝ => (1 - β) ^ 2) (-(2 * (1 - α))) α := by
      have h := hbl.pow 2
      have heq : ((2:ℕ) : ℝ) * (1 - α) ^ (2 - 1) * (-1) = -(2 * (1 - α)) := by norm_num
      rwa [heq] at h
    have h3 : HasDerivAt (fun β : ℝ => (1 - β) ^ 2 * Jp p (t ^ 2))
        (-(2 * (1 - α)) * Jp p (t ^ 2)) α := hb2.mul_const _
    have hsum := (h1.add h2).add h3
    have heq : 2 * α * Jp p (s ^ 2) + (2 - 4 * α) * Jp p (s * t)
          + -(2 * (1 - α)) * Jp p (t ^ 2)
        = 2 * α * Jp p (s ^ 2) + (2 - 4 * α) * Jp p (s * t)
          - 2 * (1 - α) * Jp p (t ^ 2) := by ring
    rwa [heq] at hsum
  have hGderiv : HasDerivAt G
      ((2 * α * Jp p (s ^ 2) + (2 - 4 * α) * Jp p (s * t) - 2 * (1 - α) * Jp p (t ^ 2))
        - μ * ((v : ℝ) * q ^ (v - 1) * (S - T))) α := by
    rw [hG]
    exact hent.sub (hpow.const_mul μ)
  have hobj : HasDerivAt (fun β : ℝ => (blockGraphon h11 h12 h22 β).Ip p
      - μ * (blockGraphon h11 h12 h22 β).tDensity H)
      ((2 * α * Jp p (s ^ 2) + (2 - 4 * α) * Jp p (s * t) - 2 * (1 - α) * Jp p (t ^ 2))
        - μ * ((v : ℝ) * q ^ (v - 1) * (S - T))) α :=
    hGderiv.congr_of_eventuallyEq hevent
  -- the handshake identity converts the multiplier
  have hhand : (v : ℝ) * (d : ℝ) = 2 * (H.edgeFinset.card : ℝ) := by
    have := regular_handshake H hreg
    rw [hv]
    exact_mod_cast this
  have hqpow : q ^ (v - 2) * q = q ^ (v - 1) := by
    rw [← pow_succ]
    congr 1
    omega
  have hdne : (d : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    linarith
  have hkey : 2 * (γ / (d : ℝ) * q) = μ * (v : ℝ) * q ^ (v - 1) := by
    have hstep : 2 * (γ / (d : ℝ) * q) * (d : ℝ)
        = (μ * (v : ℝ) * q ^ (v - 1)) * (d : ℝ) := by
      rw [hγ]
      have h1 : 2 * (μ * (H.edgeFinset.card : ℝ) * q ^ (v - 2) / (d : ℝ) * q) * (d : ℝ)
          = 2 * (μ * (H.edgeFinset.card : ℝ) * (q ^ (v - 2) * q)) := by
        field_simp
      rw [h1, hqpow]
      linear_combination (-(μ * q ^ (v - 1))) * hhand
    exact mul_right_cancel₀ hdne hstep
  -- expand `𝓜` and finish
  have hzs : (s ^ 2) ^ d = S * S := by
    simp only [hS, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hzt : (t ^ 2) ^ d = T * T := by
    simp only [hT, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hzst : (s * t) ^ d = S * T := by rw [hS, hT, mul_pow]
  -- the block-balance defect is half the derivative
  have hbridge : α * (Mfun d p γ (s ^ 2) - Mfun d p γ (s * t))
      - (1 - α) * (Mfun d p γ (t ^ 2) - Mfun d p γ (s * t))
      = ((2 * α * Jp p (s ^ 2) + (2 - 4 * α) * Jp p (s * t) - 2 * (1 - α) * Jp p (t ^ 2))
        - μ * ((v : ℝ) * q ^ (v - 1) * (S - T))) / 2 := by
    simp only [Mfun, hzs, hzt, hzst]
    have hexp : α * (Jp p (s ^ 2) - γ / (d : ℝ) * (S * S)
        - (Jp p (s * t) - γ / (d : ℝ) * (S * T)))
      - (1 - α) * (Jp p (t ^ 2) - γ / (d : ℝ) * (T * T)
        - (Jp p (s * t) - γ / (d : ℝ) * (S * T)))
        = (1 / 2) * (2 * α * Jp p (s ^ 2) + (2 - 4 * α) * Jp p (s * t)
          - 2 * (1 - α) * Jp p (t ^ 2))
          - (γ / (d : ℝ) * q) * (S - T) := by
      rw [hqdef]; ring
    rw [hexp]
    linear_combination (-(S - T) / 2) * hkey
  constructor
  · intro hstat
    have hD := (hstat.unique hobj).symm
    rw [hD] at hbridge
    linarith [hbridge]
  · intro hrb
    have hD : (2 * α * Jp p (s ^ 2) + (2 - 4 * α) * Jp p (s * t) - 2 * (1 - α) * Jp p (t ^ 2))
        - μ * ((v : ℝ) * q ^ (v - 1) * (S - T)) = 0 := by
      have h : α * (Mfun d p γ (s ^ 2) - Mfun d p γ (s * t))
          - (1 - α) * (Mfun d p γ (t ^ 2) - Mfun d p γ (s * t)) = 0 := by linarith [hrb]
      rw [h] at hbridge
      linarith [hbridge]
    rw [hD] at hobj
    exact hobj

/-- **`eq:block-stationarity` implies the block-balance equation**, the direction used in the
reduction. -/
theorem rowBalance_of_blockStationary {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) (hcard : 1 ≤ H.edgeFinset.card)
    {p μ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {s t α : ℝ} (h11 : s ^ 2 ∈ Set.Icc (0:ℝ) 1)
    (h12 : s * t ∈ Set.Icc (0:ℝ) 1) (h22 : t ^ 2 ∈ Set.Icc (0:ℝ) 1)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hstat : IsBlockStationary H p μ h11 h12 h22 α) :
    α * (Mfun d p (μ * (H.edgeFinset.card : ℝ)
          * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (s ^ 2)
        - Mfun d p (μ * (H.edgeFinset.card : ℝ)
          * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (s * t))
      = (1 - α) * (Mfun d p (μ * (H.edgeFinset.card : ℝ)
          * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (t ^ 2)
        - Mfun d p (μ * (H.edgeFinset.card : ℝ)
          * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (s * t)) :=
  (blockStationary_iff_rowBalance H hreg hcard hp0 hp1 h11 h12 h22 hα0 hα1).mp hstat

/-! ## `lem:stationary-rank-one-bipodality` -/

/-- **`lem:stationary-rank-one-bipodality`.**  Let `p ∈ (0,1)`, let `μ ≥ 0`, and let `f` be
measurable with `η ≤ f ≤ 1-η` for some `η > 0`.  If the rank-one graphon `f ⊗ f` satisfies the
KKT conditions at `(p,r)` with multiplier `μ`, then `f` takes at most two values up to null sets.

This is the paper's lemma with its variational hypothesis: `kkt_scalar_of_stationary` turns
`eq:graphon-stationarity` into the scalar equation `eq:rank-one-kkt`, and `exists_two_values`
runs the root count of `F_{p,γ}` on it.  If `f` is moreover not a.e. constant the two values are
distinct and `f ⊗ f` is a two-block graphon; `exists_relabel_eq_bipodalGraphon` then puts it in
the paper's normal form `W_{α,s,t}` after a measure-preserving relabelling. -/
theorem stationary_rank_one_two_values {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    {p r μ η : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hη : 0 < η) {f : ℝ → ℝ} (hfm : Measurable f)
    (hf0 : ∀ y, η ≤ f y) (hf1 : ∀ y, f y ≤ 1 - η)
    (hkkt : SatisfiesKKT H p r μ
      (rankOneGraphon hfm (fun y => le_trans hη.le (hf0 y))
        (fun y => le_trans (hf1 y) (by linarith)))) :
    ∃ a b : ℝ, ∀ᵐ x ∂unitμ, f x = a ∨ f x = b := by
  have hηle : η ≤ 1 - η := le_trans (hf0 0) (hf1 0)
  have hscalar := kkt_scalar_of_stationary H hreg hp0 hp1 hη hfm hf0 hf1 hkkt.2.2
  exact exists_two_values hd hp0 hp1 hfm (fun x => lt_of_lt_of_le hη (hf0 x))
    (fun x => lt_of_le_of_lt (hf1 x) (by linarith)) hscalar


/-! ## The converse: the scalar equations imply stationarity

`lem:rank-one-kkt-family` asserts an *equivalence*: the constructed family satisfies the KKT
conditions and `eq:block-stationarity`, and conversely those conditions pin the family.  The two
lemmas above are the forward reduction; these two run it backwards, so `eq:graphon-stationarity`
and `eq:block-stationarity` are equivalent to the scalar conditions the rest of Section 7
uses. -/

/-- **`eq:rank-one-kkt` implies `eq:graphon-stationarity`.**  If the scalar equation holds almost
everywhere with `γ = μ e(H) q^{v-2}`, then `f ⊗ f` is stationary for `I_p - μ t(H,·)`: the first
variation in every bounded symmetric direction `U` is `∬ F_{p,γ}(f⊗f) U`, which vanishes. -/
theorem isStationary_of_kkt_scalar {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) {p μ η : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hη : 0 < η) {f : ℝ → ℝ} (hfm : Measurable f)
    (hf0 : ∀ y, η ≤ f y) (hf1 : ∀ y, f y ≤ 1 - η)
    (hscalar : ∀ᵐ z ∂gμ, Fkkt d p
      (μ * (H.edgeFinset.card : ℝ) * (∫ y, f y ^ d ∂unitμ) ^ (Fintype.card V - 2))
      (f z.1 * f z.2) = 0) :
    IsStationary H p μ
      (rankOneGraphon hfm (fun y => le_trans hη.le (hf0 y))
        (fun y => le_trans (hf1 y) (by linarith))) := by
  classical
  have hηle : η ≤ 1 - η := le_trans (hf0 0) (hf1 0)
  set h0 : ∀ y, (0:ℝ) ≤ f y := fun y => le_trans hη.le (hf0 y) with hh0
  set h1 : ∀ y, f y ≤ 1 := fun y => le_trans (hf1 y) (by linarith) with hh1
  set W : Graphon := rankOneGraphon hfm h0 h1 with hW
  set q : ℝ := ∫ y, f y ^ d ∂unitμ with hq
  set γ : ℝ := μ * (H.edgeFinset.card : ℝ) * q ^ (Fintype.card V - 2) with hγ
  have hW0 : ∀ x y, η ^ 2 ≤ W.toFun x y := by
    intro x y
    have := mul_le_mul (hf0 x) (hf0 y) hη.le (le_trans hη.le (hf0 x))
    simpa [hW, sq] using this
  have hW1 : ∀ x y, W.toFun x y ≤ 1 - η ^ 2 := by
    intro x y
    have hle : f x * f y ≤ (1 - η) * (1 - η) := mul_le_mul (hf1 x) (hf1 y) (h0 y) (by linarith)
    have : (1 - η) * (1 - η) ≤ 1 - η ^ 2 := by nlinarith
    simpa [hW] using le_trans hle this
  have hη2 : (0:ℝ) < η ^ 2 := by positivity
  intro U
  have hIp := hasDerivAt_Ip_pert W U hp0 hp1 hη2 hW0 hW1
  have htD := hasDerivAt_tDensity_pert H W U hη2 hW0 hW1
  have hsub := hIp.fun_sub (htD.const_mul μ)
  have hteval : ∫ x : V → ℝ, ∑ e ∈ H.edgeFinset,
      (∏ e' ∈ H.edgeFinset.erase e, edgeVal (graphonKernel W) x e')
        * edgeVal U.toSymKernel x e ∂(Measure.pi fun _ : V => unitμ)
      = (H.edgeFinset.card : ℝ) * q ^ (Fintype.card V - 2)
        * ∫ z, f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * U.toFun z.1 z.2 ∂gμ := by
    rw [hW, graphonKernel_rankOneGraphon]
    exact tDensity_variation_rankOne H hreg hfm (fun y => lt_of_lt_of_le hη (hf0 y)) h1 U
  rw [hteval] at hsub
  have hWval : ∀ x y : ℝ, W.toFun x y = f x * f y := fun _ _ => rfl
  -- the two integrals combine into `∬ F_{p,γ}(f⊗f) U`, which is `0`
  have hmulm : Measurable fun z : ℝ × ℝ => f z.1 * f z.2 :=
    (hfm.comp measurable_fst).mul (hfm.comp measurable_snd)
  have hAm : Measurable fun z : ℝ × ℝ =>
      Jp' p (f z.1 * f z.2) * U.toFun z.1 z.2 := ((measurable_Jp' p).comp hmulm).mul U.meas'
  have hBm : Measurable fun z : ℝ × ℝ =>
      f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * U.toFun z.1 z.2 :=
    (((hfm.comp measurable_fst).pow_const _).mul
      ((hfm.comp measurable_snd).pow_const _)).mul U.meas'
  have hUb : ∀ z : ℝ × ℝ, |U.toFun z.1 z.2| ≤ |U.bound| + 1 := fun z =>
    le_trans (le_trans (U.bound_ge z.1 z.2) (le_abs_self _)) (by linarith)
  have hAint : Integrable (fun z : ℝ × ℝ => Jp' p (f z.1 * f z.2) * U.toFun z.1 z.2) gμ := by
    refine integrable_of_abs_le hAm
      ((|ell p| + (|Real.log (η ^ 2)| + |Real.log (1 - (1 - η ^ 2))|)) * (|U.bound| + 1))
      (fun z => ?_)
    have hmem : f z.1 * f z.2 ∈ Set.Icc (η ^ 2) (1 - η ^ 2) := ⟨hW0 z.1 z.2, hW1 z.1 z.2⟩
    have hJ := abs_Jp'_le hp0 hp1 hη2 (by linarith : (1:ℝ) - η ^ 2 < 1) hmem
    rw [abs_mul]
    exact mul_le_mul hJ (hUb z) (abs_nonneg _) (by positivity)
  have hBint : Integrable
      (fun z : ℝ × ℝ => f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * U.toFun z.1 z.2) gμ := by
    refine integrable_of_abs_le hBm (|U.bound| + 1) (fun z => ?_)
    have hp1' : |f z.1 ^ (d - 1)| ≤ 1 := by
      rw [abs_pow, abs_of_nonneg (h0 _)]; exact pow_le_one₀ (h0 _) (h1 _)
    have hp2' : |f z.2 ^ (d - 1)| ≤ 1 := by
      rw [abs_pow, abs_of_nonneg (h0 _)]; exact pow_le_one₀ (h0 _) (h1 _)
    rw [abs_mul, abs_mul]
    calc |f z.1 ^ (d - 1)| * |f z.2 ^ (d - 1)| * |U.toFun z.1 z.2|
        ≤ 1 * 1 * (|U.bound| + 1) :=
          mul_le_mul (mul_le_mul hp1' hp2' (abs_nonneg _) zero_le_one) (hUb z)
            (abs_nonneg _) (by norm_num)
      _ = |U.bound| + 1 := by ring
  have hzero : (∫ z, Jp' p (W.toFun z.1 z.2) * U.toFun z.1 z.2 ∂gμ)
      - μ * ((H.edgeFinset.card : ℝ) * q ^ (Fintype.card V - 2)
        * ∫ z, f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * U.toFun z.1 z.2 ∂gμ) = 0 := by
    simp only [hWval]
    have hcomb : (∫ z, Jp' p (f z.1 * f z.2) * U.toFun z.1 z.2 ∂gμ)
        - γ * ∫ z, f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * U.toFun z.1 z.2 ∂gμ
        = ∫ z, Fkkt d p γ (f z.1 * f z.2) * U.toFun z.1 z.2 ∂gμ := by
      rw [← integral_const_mul, ← integral_sub hAint (hBint.const_mul γ)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      show Jp' p (f z.1 * f z.2) * U.toFun z.1 z.2
          - γ * (f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * U.toFun z.1 z.2)
          = Fkkt d p γ (f z.1 * f z.2) * U.toFun z.1 z.2
      rw [show f z.1 ^ (d - 1) * f z.2 ^ (d - 1) = (f z.1 * f z.2) ^ (d - 1) from
        (mul_pow _ _ _).symm]
      simp only [Fkkt]
      ring
    have hvanish : ∫ z, Fkkt d p γ (f z.1 * f z.2) * U.toFun z.1 z.2 ∂gμ = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hscalar] with z hz
      simp [hz]
    have hassoc : μ * ((H.edgeFinset.card : ℝ) * q ^ (Fintype.card V - 2)
        * ∫ z, f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * U.toFun z.1 z.2 ∂gμ)
        = γ * ∫ z, f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * U.toFun z.1 z.2 ∂gμ := by
      rw [hγ]; ring
    rw [hassoc, hcomb, hvanish]
  rw [hzero] at hsub
  exact hsub

end SingularEndpoint

end UpperTailOptimizers
