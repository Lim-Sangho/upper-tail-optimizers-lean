import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.MfunSandwich
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilySymm

/-!
# The `h⁴` order along the coalescing family (Section 5, `paper/sections/singular.tex`)

This is the leading term of the paper's expansion of the left increment (in
`app:rank-one-kkt-family`, with remainder `O_d(h⁵)`):

    𝓜_h(s_h²) - 𝓜_h(s_h t_h) = -2d³h⁴/3 + o(h⁴).

The proof is the Lagrange-remainder route rather than the paper's analytic Weierstrass
division.  Two ingredients are already in place:

* `Mfun_sandwich_left` (`SingularEndpoint/RankOneStationaryFamily/MfunSandwich.lean`) — for any two-sided bound
  `m ≤ F_{p,γ}''' ≤ M` on `[z₁, z₃]`, the increment `𝓜(z₂) - 𝓜(z₁)` is pinched between
  `m/6` and `M/6` times the cubic factor, which `cubic_factor_left` evaluates as
  `h⁴ · C_h` with `C_h = 4 s_h³(s_h + 2t_h)/3`;
* `exists_scalar_family_density` (`SingularEndpoint/RankOneStationaryFamily/FamilySymm.lean`) — the family itself.

What this file adds is the bridge: `eventually_Fkkt3_near` makes the bound *uniform* over
the shrinking node interval, so `m` and `M` can be taken to be `K ∓ ε` with
`K = d⁵/(d-1)²`.  The pinched quotient `6·(𝓜(z₂) - 𝓜(z₁))/(h⁴ C_h)` then converges to `K`
straight from the ε-definition — no double limit to juggle — and multiplying by
`C_h/6 → 4r_*²/6` gives the coefficient `2d³/3` of `cubic_constant_left`.

**Why `h > 0`.**  The three nodes are ordered `s² < st < t²` exactly when `s < t`, i.e.
`h > 0`; for `h < 0` the roles of the two blocks are exchanged.  The statement is therefore
made on `𝓝[>] 0`, which loses nothing: the family is even in `h`
(`exists_scalar_family_density`) and the reflection `α_{-h} = 1 - α_h` already handles the
other side.

## Contents

* `eventually_Fkkt3_near` — the uniform two-sided bound on `F'''` over a shrinking interval;
* `family_left_increment_asymptotics` — the `h⁴` limit, with constant `2d³/3`, for a family
  supplied as hypotheses; this hypothesis-taking form exists so that the left increment and
  the right increment of `SingularEndpoint/RankOneStationaryFamily/Order4Right.lean` can be taken against one and the same
  family, which is what the block weight `α_h = B_h/(A_h + B_h)` needs;
* `exists_family_left_increment_asymptotics` — the same limit packaged existentially.
-/

namespace UpperTailOptimizers

open Filter Topology

variable {d : ℕ}

/-- If both endpoints of a closed interval are within `δ` of `c`, so is every point of it.
No case split is needed: the upper bound comes from the right endpoint and the lower bound
from the left. -/
private theorem abs_sub_lt_of_mem_Icc {a b c x δ : ℝ} (hx : x ∈ Set.Icc a b)
    (ha : |a - c| < δ) (hb : |b - c| < δ) : |x - c| < δ := by
  rw [abs_sub_lt_iff] at ha hb ⊢
  exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- **The uniform bound.**

If the parameter `g h` tends to `γ_*` and the two endpoints of the node interval both tend
to `r_*`, then `F_{p,g h}'''` is eventually uniformly within `ε` of its singular endpoint value
`d⁵/(d-1)²` over the whole interval.  This is `continuousAt_Fkkt3` plus the observation
above that a closed interval with both endpoints near `r_*` lies near `r_*`. -/
theorem eventually_Fkkt3_near (hd : 2 ≤ d) {g z₁ z₃ : ℝ → ℝ}
    (hg : Tendsto g (𝓝 (0 : ℝ)) (𝓝 (gammaStar d)))
    (h₁ : Tendsto z₁ (𝓝 (0 : ℝ)) (𝓝 (rStar d)))
    (h₃ : Tendsto z₃ (𝓝 (0 : ℝ)) (𝓝 (rStar d)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in 𝓝 (0 : ℝ), ∀ x ∈ Set.Icc (z₁ h) (z₃ h),
      |Fkkt3 d (g h) x - (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2| < ε := by
  set K : ℝ := (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 with hK
  -- joint continuity at the base point, with its value identified
  have hcont : Tendsto (fun q : ℝ × ℝ => Fkkt3 d q.1 q.2)
      (𝓝 ((gammaStar d, rStar d) : ℝ × ℝ)) (𝓝 K) := by
    have h := continuousAt_Fkkt3 d (γ := gammaStar d) (rStar_pos hd) (rStar_lt_one hd)
    rwa [ContinuousAt, Fkkt3_gammaStar_rStar hd] at h
  have hball : ∀ᶠ q in 𝓝 ((gammaStar d, rStar d) : ℝ × ℝ), |Fkkt3 d q.1 q.2 - K| < ε := by
    have h := hcont (Metric.ball_mem_nhds K hε)
    rw [Filter.mem_map] at h
    filter_upwards [h] with q hq
    simpa only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] using hq
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.mp hball
  -- both coordinates are eventually within `δ`
  have hgδ : ∀ᶠ h in 𝓝 (0 : ℝ), |g h - gammaStar d| < δ := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp hg δ hδ
  have h₁δ : ∀ᶠ h in 𝓝 (0 : ℝ), |z₁ h - rStar d| < δ := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp h₁ δ hδ
  have h₃δ : ∀ᶠ h in 𝓝 (0 : ℝ), |z₃ h - rStar d| < δ := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp h₃ δ hδ
  filter_upwards [hgδ, h₁δ, h₃δ] with h hgh h1h h3h x hx
  refine hδP (y := (g h, x)) ?_
  rw [Prod.dist_eq]
  exact max_lt (by simpa only [Real.dist_eq] using hgh)
    (by simpa only [Real.dist_eq] using abs_sub_lt_of_mem_Icc hx h1h h3h)

/-- **The left-increment expansion, along a prescribed family.**

The hypotheses are exactly the data that `exists_scalar_family_density` produces, taken as
arguments instead of opened from an existential.  That is the whole point of this form: the
right increment of `SingularEndpoint/RankOneStationaryFamily/Order4Right.lean` can then be evaluated along *the same*
`(u, lv, g, p)`, which is what computing the block weight `α_h = B_h/(A_h + B_h)` requires.
The functions `lv` and `p` are carried in the binder even though `lv` occurs only in the
KKT hypotheses, so that a caller can pass a family through unchanged.

The conclusion is

    (𝓜_h(s_h t_h) - 𝓜_h(s_h²)) / h⁴  →  2d³/3   as `h ↓ 0`. -/
theorem family_left_increment_asymptotics (hd : 2 ≤ d) {h0 : ℝ} {u lv g p : ℝ → ℝ}
    (hh0 : 0 < h0) (hu0 : u 0 = uStar d) (hg0 : g 0 = gammaStar d)
    (hua : ∀ h : ℝ, |h| < h0 → AnalyticAt ℝ u h)
    (hga : ∀ h : ℝ, |h| < h0 → AnalyticAt ℝ g h)
    (hadm : ∀ h : ℝ, |h| < h0 → 0 < u h - |h| ∧ u h + |h| < 1)
    (hp01 : ∀ h : ℝ, |h| < h0 → 0 < p h ∧ p h < 1)
    (hellp : ∀ h : ℝ, |h| < h0 → ell (p h) = lv h)
    (hkkt : ∀ h : ℝ, |h| < h0 → h ≠ 0 →
        Lell d (lv h) (g h) ((u h - h) ^ 2) = 0 ∧
          Lell d (lv h) (g h) ((u h - h) * (u h + h)) = 0 ∧
          Lell d (lv h) (g h) ((u h + h) ^ 2) = 0) :
    Tendsto (fun h : ℝ => (Mfun d (p h) (g h) ((u h - h) * (u h + h))
          - Mfun d (p h) (g h) ((u h - h) ^ 2)) / h ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * (d : ℝ) ^ 3 / 3)) := by
  set K : ℝ := (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 with hKdef
  set s : ℝ → ℝ := fun h => u h - h with hs
  set t : ℝ → ℝ := fun h => u h + h with ht
  set C : ℝ → ℝ := fun h => 4 * s h ^ 3 * (s h + 2 * t h) / 3 with hC
  set D : ℝ → ℝ := fun h => Mfun d (p h) (g h) (s h * t h) - Mfun d (p h) (g h) (s h ^ 2)
    with hD
  -- continuity of the family at `0`
  have h0mem : |(0 : ℝ)| < h0 := by simpa using hh0
  have huT : Tendsto u (𝓝 (0 : ℝ)) (𝓝 (uStar d)) := by
    have := (hua 0 h0mem).continuousAt.tendsto
    rwa [hu0] at this
  have hgT : Tendsto g (𝓝 (0 : ℝ)) (𝓝 (gammaStar d)) := by
    have := (hga 0 h0mem).continuousAt.tendsto
    rwa [hg0] at this
  have hsT : Tendsto s (𝓝 (0 : ℝ)) (𝓝 (uStar d)) := by
    simpa [hs] using huT.sub (continuous_id.continuousAt (x := (0 : ℝ))).tendsto
  have htT : Tendsto t (𝓝 (0 : ℝ)) (𝓝 (uStar d)) := by
    simpa [ht] using huT.add (continuous_id.continuousAt (x := (0 : ℝ))).tendsto
  have hsqT : Tendsto (fun h => s h ^ 2) (𝓝 (0 : ℝ)) (𝓝 (rStar d)) := by
    simpa [uStar_sq hd] using hsT.pow 2
  have htqT : Tendsto (fun h => t h ^ 2) (𝓝 (0 : ℝ)) (𝓝 (rStar d)) := by
    simpa [uStar_sq hd] using htT.pow 2
  -- the limit of the shape factor `C`
  have hu4 : uStar d ^ 4 = rStar d ^ 2 := by
    have : uStar d ^ 4 = (uStar d ^ 2) ^ 2 := by ring
    rw [this, uStar_sq hd]
  have hCT : Tendsto C (𝓝 (0 : ℝ)) (𝓝 (4 * rStar d ^ 2)) := by
    have := ((hsT.pow 3).mul (hsT.add (htT.const_mul 2)))
    have h2 : Tendsto (fun h => 4 * (s h ^ 3 * (s h + 2 * t h)) / 3) (𝓝 (0 : ℝ))
        (𝓝 (4 * (uStar d ^ 3 * (uStar d + 2 * uStar d)) / 3)) :=
      (this.const_mul 4).div_const 3
    have hval : 4 * (uStar d ^ 3 * (uStar d + 2 * uStar d)) / 3 = 4 * rStar d ^ 2 := by
      rw [← hu4]; ring
    rw [hval] at h2
    simpa [hC, mul_assoc] using h2
  -- admissibility and the KKT equations, on the positive side
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ |h| < h0 := by
    refine (eventually_nhdsWithin_iff.mpr ?_).and ?_
    · filter_upwards with x hx using hx
    · exact (Metric.eventually_nhds_iff.mpr ⟨h0, hh0, fun {y} hy => by
        simpa [Real.dist_eq] using hy⟩).filter_mono nhdsWithin_le_nhds
  -- the pinched quotient converges to `K`
  have hR : Tendsto (fun h => 6 * D h / (h ^ 4 * C h)) (𝓝[>] (0 : ℝ)) (𝓝 K) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hnear := eventually_Fkkt3_near hd (g := g) (z₁ := fun h => s h ^ 2)
      (z₃ := fun h => t h ^ 2) hgT hsqT htqT (half_pos hε)
    filter_upwards [hpos, hnear.filter_mono nhdsWithin_le_nhds] with h ⟨hh, hhlt⟩ hbnd
    -- the three nodes, in order, inside `(0,1)`
    obtain ⟨hs0, ht1⟩ := hadm h hhlt
    have habs : |h| = h := abs_of_pos hh
    rw [habs] at hs0 ht1
    have hspos : 0 < s h := hs0
    have hst : s h < t h := by simp only [hs, ht]; linarith
    have ht1' : t h < 1 := by simpa [ht] using ht1
    have htpos : 0 < t h := hspos.trans hst
    have hz₁ : (0 : ℝ) < s h ^ 2 := by positivity
    have hz₁₂ : s h ^ 2 < s h * t h := by nlinarith
    have hz₂₃ : s h * t h < t h ^ 2 := by nlinarith
    have hz₃ : t h ^ 2 < 1 := by nlinarith
    -- the KKT equations, transported from `Lell` to `Fkkt`
    obtain ⟨hp0, hp1⟩ := hp01 h hhlt
    obtain ⟨e₁, e₂, e₃⟩ := hkkt h hhlt (ne_of_gt hh)
    rw [← hellp h hhlt] at e₁ e₂ e₃
    rw [Lell_eq_Fkkt hp0 hp1 hz₁ (hz₁₂.trans (hz₂₃.trans hz₃))] at e₁
    rw [Lell_eq_Fkkt hp0 hp1 (hz₁.trans hz₁₂) (hz₂₃.trans hz₃)] at e₂
    rw [Lell_eq_Fkkt hp0 hp1 ((hz₁.trans hz₁₂).trans hz₂₃) hz₃] at e₃
    -- the sandwich, with `m = K - ε/2` and `M = K + ε/2`
    have hm : ∀ x ∈ Set.Icc (s h ^ 2) (t h ^ 2), K - ε / 2 ≤ Fkkt3 d (g h) x := by
      intro x hx
      have := hbnd x hx
      rw [abs_sub_lt_iff] at this
      linarith [this.2]
    have hM : ∀ x ∈ Set.Icc (s h ^ 2) (t h ^ 2), Fkkt3 d (g h) x ≤ K + ε / 2 := by
      intro x hx
      have := hbnd x hx
      rw [abs_sub_lt_iff] at this
      linarith [this.1]
    obtain ⟨hlow, hhigh⟩ :=
      Mfun_sandwich_left hd hp0 hp1 hz₁ hz₁₂ hz₂₃ hz₃ e₁ e₂ e₃ hm hM
    -- rewrite the cubic factor as `h⁴ · C h`
    have hcf : (s h * t h - s h ^ 2) ^ 3 *
        ((s h * t h - s h ^ 2) + 2 * (t h ^ 2 - s h * t h)) / 12 = h ^ 4 * C h := by
      simp only [hs, ht, hC]
      rw [cubic_factor_left]
      ring
    rw [hcf] at hlow hhigh
    -- divide by the positive quantity `h⁴ · C h`
    have hCpos : 0 < C h := by
      simp only [hC]
      have : 0 < s h + 2 * t h := by linarith
      positivity
    have hXpos : 0 < h ^ 4 * C h := by positivity
    set R : ℝ := 6 * D h / (h ^ 4 * C h) with hRdef
    have hDR : D h = R * (h ^ 4 * C h) / 6 := by
      rw [hRdef]; field_simp
    rw [show Mfun d (p h) (g h) (s h * t h) - Mfun d (p h) (g h) (s h ^ 2) = D h from rfl,
      hDR] at hlow hhigh
    have hlow' : (K - ε / 2) * (h ^ 4 * C h) ≤ R * (h ^ 4 * C h) := by linarith
    have hhigh' : R * (h ^ 4 * C h) ≤ (K + ε / 2) * (h ^ 4 * C h) := by linarith
    have hb1 : K - ε / 2 ≤ R := le_of_mul_le_mul_right hlow' hXpos
    have hb2 : R ≤ K + ε / 2 := le_of_mul_le_mul_right hhigh' hXpos
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  -- assemble
  have hfin : Tendsto (fun h => 6 * D h / (h ^ 4 * C h) * (C h / 6)) (𝓝[>] (0 : ℝ))
      (𝓝 (K * (4 * rStar d ^ 2 / 6))) :=
    hR.mul ((hCT.mono_left nhdsWithin_le_nhds).div_const 6)
  have hconst : K * (4 * rStar d ^ 2 / 6) = 2 * (d : ℝ) ^ 3 / 3 := by
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hd1ne : (d : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
    rw [hKdef, rStar_eq, div_pow]
    field_simp
    ring
  rw [hconst] at hfin
  refine hfin.congr' ?_
  filter_upwards [hpos] with h ⟨hh, hhlt⟩
  obtain ⟨hs0, ht1⟩ := hadm h hhlt
  have habs : |h| = h := abs_of_pos hh
  rw [habs] at hs0 ht1
  have hspos : 0 < s h := hs0
  have hst : s h < t h := by simp only [hs, ht]; linarith
  have hCpos : 0 < C h := by
    simp only [hC]
    have : 0 < s h + 2 * t h := by linarith [hspos.trans hst]
    positivity
  have h4 : (0 : ℝ) < h ^ 4 := by positivity
  field_simp
  rfl

/-- **The left-increment expansion.**

Along the coalescing family of `lem:rank-one-kkt-family`,

    (𝓜_h(s_h t_h) - 𝓜_h(s_h²)) / h⁴  →  2d³/3   as `h ↓ 0`,

so `A_h = 𝓜_h(s_h²) - 𝓜_h(s_h t_h) = -2d³h⁴/3 + o(h⁴)`, the leading term of the paper's
expansion.
`SingularEndpoint/RankOneStationaryFamily/RowSign.lean` already gives `A_h < 0`; this gives its size. -/
theorem exists_family_left_increment_asymptotics (hd : 2 ≤ d) :
    ∃ (h0 : ℝ) (u g p : ℝ → ℝ),
      0 < h0 ∧ u 0 = uStar d ∧ g 0 = gammaStar d ∧ p 0 = pStar d ∧
      Tendsto (fun h : ℝ => (Mfun d (p h) (g h) ((u h - h) * (u h + h))
            - Mfun d (p h) (g h) ((u h - h) ^ 2)) / h ^ 4)
        (𝓝[>] (0 : ℝ)) (𝓝 (2 * (d : ℝ) ^ 3 / 3)) := by
  obtain ⟨h0, u, lv, g, p, hh0, hu0, _hlv0, hg0, hp00, hua, _hlva, hga, _hpa,
    hadm, hp01, hellp, _hsym, hkkt⟩ := exists_scalar_family_density hd
  exact ⟨h0, u, g, p, hh0, hu0, hg0, hp00,
    family_left_increment_asymptotics hd hh0 hu0 hg0 hua hga hadm hp01 hellp hkkt⟩

end UpperTailOptimizers
