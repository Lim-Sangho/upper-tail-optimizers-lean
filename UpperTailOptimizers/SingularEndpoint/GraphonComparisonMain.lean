import UpperTailOptimizers.SingularEndpoint.GraphonComparison
import UpperTailOptimizers.SingularEndpoint.FactorHDensity
import UpperTailOptimizers.SingularEndpoint.JpConvexGap
import UpperTailOptimizers.SingularEndpoint.Interp3
import UpperTailOptimizers.SingularEndpoint.FkktDeriv

/-!
# The residual half of `lem:graphon-lagrangian-bound` (Section 7, `paper/singular_endpoint.tex`)

`SingularEndpoint/GraphonComparison.lean` carries `lem:graphon-lagrangian-bound` as far as the *law* half:
`comparison_splitting` writes the cost gap as a law term plus the residual entropy
integral `∫∫{J_{p_h}(W) - J̃_{p_h}(f ⊗ f)}`, and `exists_comparison_gap` estimates the
law term.  This file estimates the residual entropy integral — Step 3 of the paper's
proof, together with a crude form of the tail contribution of Step 4.

## Paper results realised

* **`lem:graphon-lagrangian-bound`** — `comparisonMain_cubic_ideal`, with *explicit* quotients
  `U_h, V_h` (the paper obtains them by an analytic Weierstrass division; they are in fact
  polynomials, computed here in closed form) and `comparisonMainU_diag`, `comparisonMainV_diag` for
  `U_0(u_*,u_*) = V_0(u_*,u_*) = 0`;
* the multiplier bound behind **`lem:graphon-lagrangian-bound`** —
  `comparisonMain_exists_multiplier_bound`: on a small enough window and for small `h`,
  `|F_{p_h,γ_h}(xy)| ≤ θ(|Q_h(x)| + |Q_h(y)|)` with `θ` as small as one likes.  This is the
  paper's `θ_{ρ,h} → 0`, in the pointwise form the Cauchy–Schwarz step consumes;
* **`lem:graphon-lagrangian-bound`** — `comparisonMain_central_convexGap` (pointwise) and
  its integrated consequence inside `comparisonMain_exists_residual_bound`;
* **`lem:graphon-lagrangian-bound`** — `comparisonMain_weighted_ortho_fst`,
  `comparisonMain_weighted_ortho_snd` and `comparisonMain_abs_tailSq_le`;
* the residual estimate itself — `comparisonMain_exists_residual_bound`.

## What is **not** done here

`comparisonMain_exists_residual_bound` treats the tail part `(T)` of the splitting *crudely*,
bounding it below by `-Cν(T_ρ)` using that both entropies are bounded on their compact
ranges.  It therefore produces

  `∫∫{J_{p_h}(W) - J̃_{p_h}(f ⊗ f)} ≥ ‖E‖₂² - θ·A_ρ - C·ν(T_ρ)`,

which is the paper's `M_ρ^{-1}‖E‖₂²` together with the `A_ρ` loss it is allowed, but with
`ν(T_ρ)` appearing as a **loss** rather than as the gain `c_ρν(T_ρ)/2`.

In the proof that gain is not manufactured here at all: it is the rank-one tail
`∫_{T_ρ}Ψ_h dν ≥ b_ρ ε_ρ(ν)` of `lem:auxiliary-lagrangian-bound`, and Steps 2 and 3 only have
to stay below it.  So this file also exposes the **central-only** bound

  `∬_{G_ρ²}{J_{p_h}(W) - J̃_{p_h}(f ⊗ f)}
     ≥ 2‖E‖²_{2,G_ρ²} - θ{A_ρ + ‖E‖²_{2,G_ρ²}} - C·ν(T_ρ)·‖E‖₂`,

as `comparisonMain_exists_central_bound`, with the corner in its sharp form
`comparisonMain_abs_tailSq_le_L2`.  `comparisonMain_exists_residual_bound` is the same three ingredients
proved separately with the tail added back crudely, at the cost of the weaker constants
displayed above.  Step 5 puts the three estimates
together in `SingularEndpoint/GraphonComparisonMaster.lean` (`exists_comparison_master`), where the
replacement of the layer's graph-free Lagrangian `η_hΔ_h(ν)` by `μ_h{t(H,W) - r_h^m}` is
`exists_singular_endpoint_comparison_graph`.

Everything below is stated for an arbitrary `FactorDecomp d W`; the only field used is the
orthogonality `ortho`, and it is used only for the corner estimate.

## Contents

* `comparisonMainU`, `comparisonMainV`, `comparisonMain_cubic_ideal`, `comparisonMainU_diag`, `comparisonMainV_diag`,
  `comparisonMain_exists_UV_small` — the ideal division and the smallness of its quotients;
* `comparisonMainA`, `comparisonMainB`, `comparisonMainA_pos`, `comparisonMainB_lt_one`, `comparisonMainA_lt_comparisonMainB`,
  `comparisonMain_mem_Ioo`, `comparisonMain_mul_mem` — the compact working interval
  `[r_*/2, (1+r_*)/2] ⊂ (0,1)` and the window arithmetic that lands `f(x)f(y)` in it;
* `comparisonMain_exists_multiplier_bound` — the `θ_{ρ,h} → 0` multiplier bound;
* `comparisonMain_central_convexGap` — the pointwise strong-convexity step;
* `comparisonMainChi`, `comparisonMainChic` and their calculus (`comparisonMainChi_of_mem`,
  `comparisonMainChi_of_not_mem`, `comparisonMainChic_of_mem`, `comparisonMainChic_of_not_mem`,
  `comparisonMainChi_add_chic`, `comparisonMainChi_nonneg`, `comparisonMainChic_nonneg`, `comparisonMainChi_le_one`,
  `comparisonMainChic_le_one`, `measurable_comparisonMainChi`, `measurable_comparisonMainChic`,
  `comparisonMain_integral_chic`) — the central set carried as a pair of weights, so that no
  restricted measure occurs below;
* `comparisonMain_weighted_ortho_fst`, `comparisonMain_weighted_ortho_snd`, `comparisonMain_abs_tailSq_le` and its
  sharp form `comparisonMain_abs_tailSq_le_L2` — the Factor corner;
* `comparisonMain_abs_kkt_error_le` — `lem:graphon-lagrangian-bound`;
* `comparisonMain_exists_central_bound` — the central-only residual bound, the form Step 5 consumes;
* `comparisonMain_exists_residual_bound` — the residual estimate;
* `comparisonMain_exists_splitting_gap` — that estimate fed into `comparison_splitting`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-! ## `lem:graphon-lagrangian-bound`: the cubic lies in the ideal `(Q_h(x), Q_h(y))`

The paper divides `D_h(xy) = (xy - s_h²)(xy - s_ht_h)(xy - t_h²)` by the monic quadratic
`Q_h(x) = (x - s_h)(x - t_h)` in `x` and then the remainder by `Q_h(y)` in `y`, and argues
by unisolvence on the grid `{s_h,t_h}²` that the final remainder vanishes.  Both divisions
are *polynomial*, so the quotients can be written down; `comparisonMain_cubic_ideal` is then a
`ring` identity, valid for every `(s,t,x,y)` with no side condition at all — in particular
through the coalescing point `s = t`, where the paper has to invoke analyticity in `h`. -/

/-- The first quotient `U_h(x,y)` of `lem:graphon-lagrangian-bound`, in closed form.

With `σ = s + t` and `π = st` the `x`-division of `D_h(xy)` by `Q_h(x)` leaves the quotient
`y³(x + σ) - (σ² - π)y²`, which is the expression below. -/
def comparisonMainU (s t x y : ℝ) : ℝ := y ^ 2 * (x * y + (s + t) * y - (s + t) ^ 2 + s * t)

/-- The second quotient `V_h(x,y)` of `lem:graphon-lagrangian-bound`, in closed form: the
`y`-division of the remaining remainder by `Q_h(y)`. -/
def comparisonMainV (s t x y : ℝ) : ℝ :=
  ((s + t) ^ 2 - s * t) * (x * y) - (s + t) * (s * t) * y - (s * t) ^ 2

/-- **`lem:graphon-lagrangian-bound`.**

`D_h(xy) = Q_h(x)U_h(x,y) + Q_h(y)V_h(x,y)` with `D_h(u) = (u - s²)(u - st)(u - t²)` and
`Q_h(x) = (x - s)(x - t)`.  An identity of polynomials: no smallness, no distinctness of
`s` and `t`, and no analyticity in `h`. -/
theorem comparisonMain_cubic_ideal (s t x y : ℝ) :
    (x * y - s ^ 2) * (x * y - s * t) * (x * y - t ^ 2)
      = (x - s) * (x - t) * comparisonMainU s t x y + (y - s) * (y - t) * comparisonMainV s t x y := by
  simp only [comparisonMainU, comparisonMainV]; ring

/-- `U_0(u_*,u_*) = 0`: the first quotient vanishes at the coalescing point.  In the paper
this is read off from `D_0(xy) = (u_*X + u_*Y + XY)³`, every monomial of which has degree at
least two in `X` or in `Y`. -/
theorem comparisonMainU_diag (u : ℝ) : comparisonMainU u u u u = 0 := by simp only [comparisonMainU]; ring

/-- `V_0(u_*,u_*) = 0`, the companion of `comparisonMainU_diag`. -/
theorem comparisonMainV_diag (u : ℝ) : comparisonMainV u u u u = 0 := by simp only [comparisonMainV]; ring

/-- **The quotients are uniformly small near the coalescing point.**  Joint continuity of
the two polynomials, together with `comparisonMainU_diag` and `comparisonMainV_diag`, is the paper's
"`U_h, V_h` tend to zero uniformly on `𝓝_ρ²` as first `ρ ↓ 0` and then `h ↓ 0`". -/
theorem comparisonMain_exists_UV_small (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s t x y : ℝ, |s - u| < δ → |t - u| < δ → |x - u| < δ → |y - u| < δ →
      |comparisonMainU s t x y| + |comparisonMainV s t x y| ≤ ε := by
  have hU : Continuous fun z : ℝ × ℝ × ℝ × ℝ => comparisonMainU z.1 z.2.1 z.2.2.1 z.2.2.2 := by
    unfold comparisonMainU; fun_prop
  have hV : Continuous fun z : ℝ × ℝ × ℝ × ℝ => comparisonMainV z.1 z.2.1 z.2.2.1 z.2.2.2 := by
    unfold comparisonMainV; fun_prop
  have hF : Continuous fun z : ℝ × ℝ × ℝ × ℝ =>
      |comparisonMainU z.1 z.2.1 z.2.2.1 z.2.2.2| + |comparisonMainV z.1 z.2.1 z.2.2.1 z.2.2.2| :=
    hU.abs.add hV.abs
  have hval : |comparisonMainU u u u u| + |comparisonMainV u u u u| = 0 := by
    rw [comparisonMainU_diag, comparisonMainV_diag]; simp
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuous_iff.mp hF (u, u, u, u) ε hε
  refine ⟨δ, hδ0, ?_⟩
  intro s t x y hs ht hx hy
  have hdist : dist ((s, t, x, y) : ℝ × ℝ × ℝ × ℝ) (u, u, u, u) < δ := by
    simp only [Prod.dist_eq, Real.dist_eq, max_lt_iff]
    exact ⟨hs, ht, hx, hy⟩
  have hlt := hδ _ hdist
  rw [Real.dist_eq, hval, sub_zero,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ |comparisonMainU s t x y| + |comparisonMainV s t x y|)] at hlt
  exact hlt.le

/-! ## The compact working interval -/

/-- The left endpoint `r_*/2` of the working interval. -/
noncomputable def comparisonMainA (d : ℕ) : ℝ := rStar d / 2

/-- The right endpoint `(1 + r_*)/2` of the working interval. -/
noncomputable def comparisonMainB (d : ℕ) : ℝ := (1 + rStar d) / 2

theorem comparisonMainA_pos (hd : 2 ≤ d) : 0 < comparisonMainA d := by
  have := rStar_pos hd; unfold comparisonMainA; linarith

theorem comparisonMainB_lt_one (hd : 2 ≤ d) : comparisonMainB d < 1 := by
  have := rStar_lt_one hd; unfold comparisonMainB; linarith

theorem comparisonMainA_lt_comparisonMainB (hd : 2 ≤ d) : comparisonMainA d < comparisonMainB d := by
  have h1 := rStar_pos hd
  have h2 := rStar_lt_one hd
  unfold comparisonMainA comparisonMainB; linarith

/-- Every point of the working interval is an interior point of `[0,1]`. -/
theorem comparisonMain_mem_Ioo (hd : 2 ≤ d) {z : ℝ} (hz : z ∈ Set.Icc (comparisonMainA d) (comparisonMainB d)) :
    0 < z ∧ z < 1 :=
  ⟨lt_of_lt_of_le (comparisonMainA_pos hd) hz.1, lt_of_le_of_lt hz.2 (comparisonMainB_lt_one hd)⟩

/-- **The window arithmetic**: if `|x - u_*| ≤ ρ` and `|y - u_*| ≤ ρ` with
`ρ ≤ min(r_*/4, (1-r_*)/6)` and `ρ ≤ 1`, then `xy` lies in the working interval.  Uses only
`u_*² = r_*` and `0 < u_* < 1`. -/
theorem comparisonMain_mul_mem (hd : 2 ≤ d) {ρ x y : ℝ} (hρ0 : 0 < ρ)
    (hρa : ρ ≤ rStar d / 4) (hρb : ρ ≤ (1 - rStar d) / 6)
    (hx : |x - uStar d| ≤ ρ) (hy : |y - uStar d| ≤ ρ) :
    x * y ∈ Set.Icc (comparisonMainA d) (comparisonMainB d) := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  have husq : uStar d ^ 2 = rStar d := uStar_sq hd
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  have hxlow : uStar d - ρ ≤ x := by linarith
  have hylow : uStar d - ρ ≤ y := by linarith
  have hxup : x ≤ uStar d + ρ := by linarith
  have hyup : y ≤ uStar d + ρ := by linarith
  have hrs : rStar d < 1 := rStar_lt_one hd
  have hrp : 0 < rStar d := rStar_pos hd
  have hpos : 0 < uStar d - ρ := by nlinarith
  constructor
  · have h1 : (uStar d - ρ) ^ 2 ≤ x * y := by nlinarith
    have h2 : comparisonMainA d ≤ (uStar d - ρ) ^ 2 := by
      unfold comparisonMainA; nlinarith
    linarith
  · have h1 : x * y ≤ (uStar d + ρ) ^ 2 := by nlinarith
    have h2 : (uStar d + ρ) ^ 2 ≤ comparisonMainB d := by
      unfold comparisonMainB; nlinarith
    linarith

/-! ## The KKT multiplier is small on the central window

`F_{p_h,γ_h}` vanishes at the three edge values `s_h², s_ht_h, t_h²` — that is
`eq:three-value-kkt`, carried by the family as `kkt_ss`, `kkt_st`, `kkt_tt` — so the
three-node Lagrange remainder `exists_deriv3_eq_of_three_roots` factors it through the monic
cubic `D_h`, with the *fourth* derivative `F'''` as coefficient.  This is the elementary
substitute for the paper's analytic Weierstrass division `J_{p_h}' - γ_hu^{d-1} = D_h𝒜_h`;
the bound on `𝒜_h` becomes a bound on `F'''_{p_h,γ_h}` on a compact interval, uniform in
`h` by joint continuity (`continuousAt_Fkkt3`). -/

/-- A uniform bound for `F'''_{p_h,γ_h}` on the working interval, for all small `h`. -/
private theorem comparisonMain_exists_Fkkt3_bound (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      ∀ z ∈ Set.Icc (comparisonMainA d) (comparisonMainB d), |Fkkt3 d (B.gam h) z| ≤ C := by
  have hK : IsCompact (Set.Icc (gammaStar d - 1) (gammaStar d + 1)
      ×ˢ Set.Icc (comparisonMainA d) (comparisonMainB d)) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Fkkt3 d q.1 q.2)
      (Set.Icc (gammaStar d - 1) (gammaStar d + 1) ×ˢ Set.Icc (comparisonMainA d) (comparisonMainB d)) := by
    intro q hq
    obtain ⟨hz0, hz1⟩ := comparisonMain_mem_Ioo hd hq.2
    exact (continuousAt_Fkkt3 d hz0 hz1).continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hcont
  have hgc : ContinuousAt B.gam 0 := B.gam_continuousAt
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hgc (1 : ℝ) one_pos)
  refine ⟨C₀ + 1, ?_, δ, hδ0, ?_⟩
  · have h0 : (0 : ℝ) ≤ C₀ := by
      have hmem : ((gammaStar d, comparisonMainA d) : ℝ × ℝ) ∈
          Set.Icc (gammaStar d - 1) (gammaStar d + 1) ×ˢ Set.Icc (comparisonMainA d) (comparisonMainB d) :=
        ⟨⟨by linarith, by linarith⟩, ⟨le_rfl, (comparisonMainA_lt_comparisonMainB hd).le⟩⟩
      exact le_trans (norm_nonneg _) (hC₀ _ hmem)
    linarith
  intro h hh z hz
  have hdist : dist h (0 : ℝ) < δ := by rwa [Real.dist_eq, sub_zero]
  have hg := hδ hdist
  rw [Real.dist_eq, B.gam_zero] at hg
  have hmem : ((B.gam h, z) : ℝ × ℝ) ∈
      Set.Icc (gammaStar d - 1) (gammaStar d + 1) ×ˢ Set.Icc (comparisonMainA d) (comparisonMainB d) := by
    refine ⟨?_, hz⟩
    have := abs_lt.mp hg
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have := hC₀ _ hmem
  rw [Real.norm_eq_abs] at this
  linarith

/-- **The cubic factorisation of the KKT function.**  If `F_{p,γ}` vanishes at `s²`, `st`,
`t²` and `|F'''_{p,γ}| ≤ C` on the working interval, then `|F_{p,γ}(z)| ≤ (C/6)|D(z)|`
there.  This is the paper's `J_{p_h}'(u) - γ_hu^{d-1} = D_h(u)𝒜_h(u)` with `|𝒜_h| ≤ C/6`. -/
private theorem comparisonMain_abs_Fkkt_le (hd : 2 ≤ d) {p γ s t : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hs0 : 0 < s) (hst : s < t)
    (hkss : Fkkt d p γ (s ^ 2) = 0) (hkst : Fkkt d p γ (s * t) = 0)
    (hktt : Fkkt d p γ (t ^ 2) = 0)
    {C : ℝ} (hC : ∀ z ∈ Set.Icc (comparisonMainA d) (comparisonMainB d), |Fkkt3 d γ z| ≤ C)
    (hsm : s ^ 2 ∈ Set.Icc (comparisonMainA d) (comparisonMainB d))
    (htm : t ^ 2 ∈ Set.Icc (comparisonMainA d) (comparisonMainB d))
    {z : ℝ} (hz : z ∈ Set.Icc (comparisonMainA d) (comparisonMainB d)) :
    |Fkkt d p γ z| ≤ C / 6 * |(z - s ^ 2) * (z - s * t) * (z - t ^ 2)| := by
  have ht0 : 0 < t := lt_trans hs0 hst
  have h12 : s ^ 2 < s * t := by nlinarith
  have h23 : s * t < t ^ 2 := by nlinarith
  have hstm : s * t ∈ Set.Icc (comparisonMainA d) (comparisonMainB d) :=
    ⟨le_trans hsm.1 h12.le, le_trans h23.le htm.2⟩
  have hchain0 : ∀ x ∈ Set.Icc (comparisonMainA d) (comparisonMainB d),
      HasDerivAt (Fkkt d p γ) (Fkkt1 d γ x) x := by
    intro x hx
    obtain ⟨h0, h1⟩ := comparisonMain_mem_Ioo hd hx
    exact hasDerivAt_Fkkt' hd hp0 hp1 h0 h1
  have hchain1 : ∀ x ∈ Set.Icc (comparisonMainA d) (comparisonMainB d),
      HasDerivAt (Fkkt1 d γ) (Fkkt2 d γ x) x := by
    intro x hx
    obtain ⟨h0, h1⟩ := comparisonMain_mem_Ioo hd hx
    exact hasDerivAt_Fkkt1 hd h0 h1
  have hchain2 : ∀ x ∈ Set.Icc (comparisonMainA d) (comparisonMainB d),
      HasDerivAt (Fkkt2 d γ) (Fkkt3 d γ x) x := by
    intro x hx
    obtain ⟨h0, h1⟩ := comparisonMain_mem_Ioo hd hx
    exact hasDerivAt_Fkkt2 hd h0 h1
  obtain ⟨ξ, hξ, hval⟩ := exists_deriv3_eq_of_three_roots hchain0 hchain1 hchain2
    hsm hstm htm h12 h23 hkss hkst hktt hz
  have hb := hC ξ hξ
  have hD : (0 : ℝ) ≤ |(z - s ^ 2) * (z - s * t) * (z - t ^ 2)| := abs_nonneg _
  rw [hval, abs_mul, abs_div]
  have h6 : |(6 : ℝ)| = 6 := by norm_num
  rw [h6]
  exact mul_le_mul_of_nonneg_right (by linarith) hD

/-- **The multiplier bound behind `lem:graphon-lagrangian-bound`.**

For every `θ > 0` there is a window radius `ρ > 0` and a threshold `δ > 0` such that, for
`0 < h < δ` inside the family window and all `x, y ∈ 𝓝_ρ`,

`|F_{p_h,γ_h}(xy)| ≤ θ(|Q_h(x)| + |Q_h(y)|)`.

This is the paper's `θ_{ρ,h} → 0` as first `ρ ↓ 0` and then `h ↓ 0`, in the pointwise form
that the Cauchy–Schwarz/Young step of `lem:graphon-lagrangian-bound` consumes.  Its two
ingredients are `lem:graphon-lagrangian-bound` (`comparisonMain_cubic_ideal`, with the smallness of
the quotients `comparisonMain_exists_UV_small`) and the cubic factorisation
`comparisonMain_abs_Fkkt_le`.  The two extra clauses `ρ ≤ r_*/4` and `ρ ≤ (1-r_*)/6` are the window
arithmetic of `comparisonMain_mul_mem`, carried along because every later step needs it. -/
theorem comparisonMain_exists_multiplier_bound (hd : 2 ≤ d) (B : KKTFamily d) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ rStar d / 4 ∧ ρ ≤ (1 - rStar d) / 6 ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, 0 < h → h < δ → |h| < B.h₀ →
        ∀ x ∈ centralWindow d ρ, ∀ y ∈ centralWindow d ρ,
          |Fkkt d (B.p h) (B.gam h) (x * y)| ≤ θ * (|B.Qh h x| + |B.Qh h y|) := by
  have hrp : 0 < rStar d := rStar_pos hd
  have hrs : rStar d < 1 := rStar_lt_one hd
  obtain ⟨C, hC0, δ₁, hδ₁, hFk⟩ := comparisonMain_exists_Fkkt3_bound hd B
  have hε : 0 < 6 * θ / C := by positivity
  obtain ⟨δ₂, hδ₂0, hUV⟩ := comparisonMain_exists_UV_small (uStar d) hε
  obtain ⟨ρ, hρ0, hρa, hρb, hρδ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ rStar d / 4 ∧
      ρ ≤ (1 - rStar d) / 6 ∧ ρ < δ₂ :=
    ⟨min (min (rStar d / 4) ((1 - rStar d) / 6)) (δ₂ / 2),
      lt_min (lt_min (by linarith) (by linarith)) (by linarith),
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _),
      lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
  have huc : ContinuousAt B.u 0 := B.u_continuousAt
  obtain ⟨δ₃, hδ₃0, hδ₃⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp huc (ρ / 2) (by linarith))
  refine ⟨ρ, hρ0, hρa, hρb, min δ₁ (min δ₃ (ρ / 2)), lt_min hδ₁ (lt_min hδ₃0 (by linarith)), ?_⟩
  intro h hh0 hhδ hhb x hx y hy
  have hh1 : h < δ₁ := lt_of_lt_of_le hhδ (min_le_left _ _)
  have hh3 : h < δ₃ := lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hhρ : h < ρ / 2 := lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_right _ _))
  have habs : |h| = h := abs_of_pos hh0
  -- the two atoms sit within `ρ` of `u_*`
  have hu : |B.u h - uStar d| < ρ / 2 := by
    have hdist : dist h (0 : ℝ) < δ₃ := by rw [Real.dist_eq, sub_zero, habs]; exact hh3
    have := hδ₃ hdist
    rwa [Real.dist_eq, B.u_zero] at this
  have hsρ : |B.sVal h - uStar d| ≤ ρ := by
    have : B.sVal h - uStar d = (B.u h - uStar d) - h := by rw [KKTFamily.sVal]; ring
    rw [this]
    have h1 := abs_lt.mp hu
    rw [abs_le]
    constructor <;> linarith
  have htρ : |B.tVal h - uStar d| ≤ ρ := by
    have : B.tVal h - uStar d = (B.u h - uStar d) + h := by rw [KKTFamily.tVal]; ring
    rw [this]
    have h1 := abs_lt.mp hu
    rw [abs_le]
    constructor <;> linarith
  have hxρ : |x - uStar d| ≤ ρ := (factorTail_mem_centralWindow_iff d ρ x).mp hx
  have hyρ : |y - uStar d| ≤ ρ := (factorTail_mem_centralWindow_iff d ρ y).mp hy
  -- the products lie in the working interval
  have hxy : x * y ∈ Set.Icc (comparisonMainA d) (comparisonMainB d) :=
    comparisonMain_mul_mem hd hρ0 hρa hρb hxρ hyρ
  have hsm : B.sVal h ^ 2 ∈ Set.Icc (comparisonMainA d) (comparisonMainB d) := by
    have := comparisonMain_mul_mem hd hρ0 hρa hρb hsρ hsρ
    rwa [← sq] at this
  have htm : B.tVal h ^ 2 ∈ Set.Icc (comparisonMainA d) (comparisonMainB d) := by
    have := comparisonMain_mul_mem hd hρ0 hρa hρb htρ htρ
    rwa [← sq] at this
  -- the cubic factorisation
  have hp := B.p_mem h hhb
  have hs0 : 0 < B.sVal h := KKTFamily.sVal_pos hhb
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hh0
  have hcub := comparisonMain_abs_Fkkt_le hd hp.1 hp.2 hs0 hst (B.kkt_ss h hhb) (B.kkt_st h hhb)
    (B.kkt_tt h hhb) (fun z hz => hFk h (by rw [habs]; exact hh1) z hz) hsm htm hxy
  -- the ideal division
  have hid := comparisonMain_cubic_ideal (B.sVal h) (B.tVal h) x y
  have hUVs := hUV (B.sVal h) (B.tVal h) x y (lt_of_le_of_lt hsρ hρδ)
    (lt_of_le_of_lt htρ hρδ) (lt_of_le_of_lt hxρ hρδ) (lt_of_le_of_lt hyρ hρδ)
  set U := comparisonMainU (B.sVal h) (B.tVal h) x y with hUdef
  set V := comparisonMainV (B.sVal h) (B.tVal h) x y with hVdef
  have hQx : B.Qh h x = (x - B.sVal h) * (x - B.tVal h) := rfl
  have hQy : B.Qh h y = (y - B.sVal h) * (y - B.tVal h) := rfl
  have hDle : |(x * y - B.sVal h ^ 2) * (x * y - B.sVal h * B.tVal h)
      * (x * y - B.tVal h ^ 2)| ≤ (6 * θ / C) * (|B.Qh h x| + |B.Qh h y|) := by
    rw [hid]
    calc |(x - B.sVal h) * (x - B.tVal h) * U + (y - B.sVal h) * (y - B.tVal h) * V|
        ≤ |(x - B.sVal h) * (x - B.tVal h) * U| + |(y - B.sVal h) * (y - B.tVal h) * V| :=
          abs_add_le _ _
      _ = |B.Qh h x| * |U| + |B.Qh h y| * |V| := by
          rw [hQx, hQy, abs_mul ((x - B.sVal h) * (x - B.tVal h)) U,
            abs_mul ((y - B.sVal h) * (y - B.tVal h)) V]
      _ ≤ (6 * θ / C) * (|B.Qh h x| + |B.Qh h y|) := by
          have h1 : |U| ≤ 6 * θ / C := by linarith [abs_nonneg V]
          have h2 : |V| ≤ 6 * θ / C := by linarith [abs_nonneg U]
          have e1 : |B.Qh h x| * |U| ≤ |B.Qh h x| * (6 * θ / C) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          have e2 : |B.Qh h y| * |V| ≤ |B.Qh h y| * (6 * θ / C) :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
          linarith
  have hCne : C ≠ 0 := ne_of_gt hC0
  calc |Fkkt d (B.p h) (B.gam h) (x * y)|
      ≤ C / 6 * |(x * y - B.sVal h ^ 2) * (x * y - B.sVal h * B.tVal h)
          * (x * y - B.tVal h ^ 2)| := hcub
    _ ≤ C / 6 * ((6 * θ / C) * (|B.Qh h x| + |B.Qh h y|)) :=
        mul_le_mul_of_nonneg_left hDle (by positivity)
    _ = θ * (|B.Qh h x| + |B.Qh h y|) := by field_simp

/-! ## `lem:graphon-lagrangian-bound`, pointwise

On the central set the rank-one value `f(x)f(y)` stays in the working interval, a compact
subinterval of `(0,1)`, so the continuation `J̃_{p_h}` *is* the true entropy there
(`JpTildeH_eq_Jp`) and `J_{p_h}'' ≥ 4` gives the convexity gap `2E²`.  The modulus `2` is the
paper's. -/

/-- **`lem:graphon-lagrangian-bound`, pointwise.**  Wherever the rank-one value
`f(x)f(y)` lies in the working interval,

`J_{p_h}(W(x,y)) - J̃_{p_h}(f(x)f(y)) - J_{p_h}'(f(x)f(y))E(x,y) ≥ 2E(x,y)²`.

The only analytic input is `two_sq_le_Jp_convexGap`, i.e. `J_p'' ≥ 4`. -/
theorem comparisonMain_central_convexGap (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ}
    (hh : |h| < B.h₀) {W : Graphon} (P : FactorDecomp d W) {x y : ℝ}
    (hv : P.f x * P.f y ∈ Set.Icc (comparisonMainA d) (comparisonMainB d)) :
    2 * P.resid x y ^ 2 + Jp' (B.p h) (P.f x * P.f y) * P.resid x y
      ≤ Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y) := by
  obtain ⟨hv0, hv1⟩ := comparisonMain_mem_Ioo hd hv
  have hp := B.p_mem h hh
  have hbr := two_sq_le_Jp_convexGap hp.1 hp.2 (W.mem_Icc x y) hv0 hv1
  have hres : P.resid x y = W.toFun x y - P.f x * P.f y := rfl
  rw [KKTFamily.JpTildeH_eq_Jp hd hh hv0.le hv1.le, hres]
  linarith

/-- **The multiplier bound at every small enough radius.**  `comparisonMain_exists_multiplier_bound`
produces *one* admissible `ρ`; the join of Step 5 needs the law half and the residual
half at a **common** radius, and each manufactures its own.  Capping one by the other yields
a *smaller* radius, not an equal one, so what is needed is the `∀ 0 < ρ ≤ ρ₀` form.

Here it is free: the conclusion quantifies over `x, y ∈ 𝓝_ρ`, so shrinking the window only
weakens it (`centralWindow_subset_of_le`).  The law side is not free — there the atoms
have to *lie in* the window — and is restated separately in `SingularEndpoint/DistributionWindow.lean`. -/
theorem comparisonMain_exists_multiplier_bound_forall (hd : 2 ≤ d) (B : KKTFamily d) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ rStar d / 4 ∧ ρ₀ ≤ (1 - rStar d) / 6 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℝ, 0 < h → h < δ → |h| < B.h₀ →
          ∀ x ∈ centralWindow d ρ, ∀ y ∈ centralWindow d ρ,
            |Fkkt d (B.p h) (B.gam h) (x * y)| ≤ θ * (|B.Qh h x| + |B.Qh h y|) := by
  obtain ⟨ρ₀, hρ₀0, hρ₀a, hρ₀b, δ, hδ0, hmul⟩ := comparisonMain_exists_multiplier_bound hd B hθ
  exact ⟨ρ₀, hρ₀0, hρ₀a, hρ₀b, fun ρ _ hρle => ⟨δ, hδ0, fun h hh0 hhδ hhb x hx y hy =>
    hmul h hh0 hhδ hhb x (centralWindow_subset_of_le d hρle hx) y
      (centralWindow_subset_of_le d hρle hy)⟩⟩


/-! ## `lem:graphon-lagrangian-bound`: the Factor corner

The nonlinear Factor orthogonality `eq:rank-one-orthogonality` holds in every row and, by
the symmetry of `E`, in every column.  Both statements below are that orthogonality
integrated against an arbitrary bounded weight in one variable; the corner estimate is the
inclusion–exclusion `∫∫_{G²} = ∫∫ - ∫∫_{Gᶜ×[0,1]} - ∫∫_{[0,1]×Gᶜ} + ∫∫_{(Gᶜ)²}` with the
first three terms vanishing. -/

/-- The uniform bound on the integrand of the two orthogonality lemmas. -/
private theorem comparisonMain_abs_ortho_integrand_le {W : Graphon} (P : FactorDecomp d W)
    {w : ℝ → ℝ} {Cw : ℝ} (hwb : ∀ x, |w x| ≤ Cw) (a x y : ℝ) :
    |w a * (P.f x ^ (d - 1) * P.f y ^ (d - 1) * P.resid x y)|
      ≤ Cw * (2 ^ (d - 1) * 2 ^ (d - 1) * 5) := by
  have h1 : |w a| ≤ Cw := hwb a
  have h2 : |P.f x ^ (d - 1)| ≤ 2 ^ (d - 1) := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (P.abs_f_le x) _
  have h3 : |P.f y ^ (d - 1)| ≤ 2 ^ (d - 1) := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (P.abs_f_le y) _
  have h4 : |P.resid x y| ≤ 5 := P.abs_resid_le x y
  have h23 : |P.f x ^ (d - 1)| * |P.f y ^ (d - 1)| ≤ 2 ^ (d - 1) * 2 ^ (d - 1) :=
    mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
  have h234 : |P.f x ^ (d - 1)| * |P.f y ^ (d - 1)| * |P.resid x y|
      ≤ 2 ^ (d - 1) * 2 ^ (d - 1) * 5 :=
    mul_le_mul h23 h4 (abs_nonneg _) (by positivity)
  rw [abs_mul, abs_mul, abs_mul]
  exact mul_le_mul h1 h234 (by positivity) (le_trans (abs_nonneg _) h1)

/-- **The row orthogonality, integrated against a weight in the first variable.**  For any
bounded measurable `w`, `∫∫ w(x)f(x)^{d-1}f(y)^{d-1}E(x,y) = 0`. -/
theorem comparisonMain_weighted_ortho_fst {W : Graphon} (P : FactorDecomp d W) {w : ℝ → ℝ}
    (hw : Measurable w) {Cw : ℝ} (hwb : ∀ x, |w x| ≤ Cw) :
    ∫ z, w z.1 * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ = 0 := by
  have hmeas : Measurable fun z : ℝ × ℝ =>
      w z.1 * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) :=
    (hw.comp measurable_fst).mul
      ((((P.measurable_f_pow (d - 1)).comp measurable_fst).mul
        ((P.measurable_f_pow (d - 1)).comp measurable_snd)).mul P.measurable_resid)
  have hint : Integrable (fun z : ℝ × ℝ =>
      w z.1 * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) gμ :=
    integrable_of_abs_le hmeas _
      (fun z => comparisonMain_abs_ortho_integrand_le P hwb z.1 z.1 z.2)
  rw [show gμ = unitμ.prod unitμ from rfl, integral_prod _ hint]
  have hae : ∀ᵐ x ∂unitμ,
      (∫ y, w x * (P.f x ^ (d - 1) * P.f y ^ (d - 1) * P.resid x y) ∂unitμ) = 0 := by
    filter_upwards [P.ortho] with x hx
    have e : ∀ y : ℝ, w x * (P.f x ^ (d - 1) * P.f y ^ (d - 1) * P.resid x y)
        = (w x * P.f x ^ (d - 1))
          * ((W.toFun x y - P.f x * P.f y) * P.f y ^ (d - 1)) := by
      intro y; simp only [FactorDecomp.resid]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, hx, mul_zero]
  rw [integral_congr_ae hae, integral_zero]

/-- **The column orthogonality**, the same with the weight in the second variable.  It uses
`FactorDecomp.resid_symm`, i.e. the symmetry of `E`. -/
theorem comparisonMain_weighted_ortho_snd {W : Graphon} (P : FactorDecomp d W) {w : ℝ → ℝ}
    (hw : Measurable w) {Cw : ℝ} (hwb : ∀ x, |w x| ≤ Cw) :
    ∫ z, w z.2 * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ = 0 := by
  have hmeas : Measurable fun z : ℝ × ℝ =>
      w z.2 * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) :=
    (hw.comp measurable_snd).mul
      ((((P.measurable_f_pow (d - 1)).comp measurable_fst).mul
        ((P.measurable_f_pow (d - 1)).comp measurable_snd)).mul P.measurable_resid)
  have hint : Integrable (fun z : ℝ × ℝ =>
      w z.2 * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) gμ :=
    integrable_of_abs_le hmeas _
      (fun z => comparisonMain_abs_ortho_integrand_le P hwb z.2 z.1 z.2)
  rw [show gμ = unitμ.prod unitμ from rfl, integral_prod_symm _ hint]
  have hae : ∀ᵐ y ∂unitμ,
      (∫ x, w y * (P.f x ^ (d - 1) * P.f y ^ (d - 1) * P.resid x y) ∂unitμ) = 0 := by
    filter_upwards [P.ortho] with y hy
    have e : ∀ x : ℝ, w y * (P.f x ^ (d - 1) * P.f y ^ (d - 1) * P.resid x y)
        = (w y * P.f y ^ (d - 1))
          * ((W.toFun y x - P.f y * P.f x) * P.f x ^ (d - 1)) := by
      intro x
      rw [P.resid_symm x y]
      simp only [FactorDecomp.resid]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, hy, mul_zero]
  rw [integral_congr_ae hae, integral_zero]

/-! ## The central set as a pair of weights

The paper splits the residual entropy integral over `G_ρ²` and its complement.  Here the
split is carried by the two `{0,1}`-valued weights `χ = 1_{G_ρ}` and `χᶜ = 1_{G_ρᶜ}`
composed with the factor, so that every integral below is an *ordinary* integral over `gμ`
of a bounded measurable function and no restricted measure appears. -/

/-- `χ`, the indicator of the central set `G_ρ = {x : f(x) ∈ 𝓝_ρ}`. -/
noncomputable def comparisonMainChi (d : ℕ) (ρ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Set.indicator {x | f x ∈ centralWindow d ρ} (fun _ => (1 : ℝ)) x

/-- `χᶜ`, the indicator of the rare rows `G_ρᶜ = {x : f(x) ∉ 𝓝_ρ}`. -/
noncomputable def comparisonMainChic (d : ℕ) (ρ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Set.indicator {x | f x ∉ centralWindow d ρ} (fun _ => (1 : ℝ)) x

theorem comparisonMainChi_of_mem {ρ : ℝ} {f : ℝ → ℝ} {x : ℝ} (hx : f x ∈ centralWindow d ρ) :
    comparisonMainChi d ρ f x = 1 := by
  have hx' : x ∈ {x : ℝ | f x ∈ centralWindow d ρ} := hx
  simp only [comparisonMainChi]
  exact Set.indicator_of_mem hx' _

theorem comparisonMainChi_of_not_mem {ρ : ℝ} {f : ℝ → ℝ} {x : ℝ} (hx : f x ∉ centralWindow d ρ) :
    comparisonMainChi d ρ f x = 0 := by
  have hx' : x ∉ {x : ℝ | f x ∈ centralWindow d ρ} := hx
  simp only [comparisonMainChi]
  exact Set.indicator_of_notMem hx' _

theorem comparisonMainChic_of_mem {ρ : ℝ} {f : ℝ → ℝ} {x : ℝ} (hx : f x ∈ centralWindow d ρ) :
    comparisonMainChic d ρ f x = 0 := by
  have hx' : x ∉ {x : ℝ | f x ∉ centralWindow d ρ} := by simpa using hx
  simp only [comparisonMainChic]
  exact Set.indicator_of_notMem hx' _

theorem comparisonMainChic_of_not_mem {ρ : ℝ} {f : ℝ → ℝ} {x : ℝ} (hx : f x ∉ centralWindow d ρ) :
    comparisonMainChic d ρ f x = 1 := by
  have hx' : x ∈ {x : ℝ | f x ∉ centralWindow d ρ} := hx
  simp only [comparisonMainChic]
  exact Set.indicator_of_mem hx' _

/-- The two weights partition unity. -/
theorem comparisonMainChi_add_chic (d : ℕ) (ρ : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    comparisonMainChi d ρ f x + comparisonMainChic d ρ f x = 1 := by
  by_cases hx : f x ∈ centralWindow d ρ
  · rw [comparisonMainChi_of_mem hx, comparisonMainChic_of_mem hx]; ring
  · rw [comparisonMainChi_of_not_mem hx, comparisonMainChic_of_not_mem hx]; ring

theorem comparisonMainChi_nonneg (d : ℕ) (ρ : ℝ) (f : ℝ → ℝ) (x : ℝ) : 0 ≤ comparisonMainChi d ρ f x := by
  by_cases hx : f x ∈ centralWindow d ρ
  · rw [comparisonMainChi_of_mem hx]; norm_num
  · rw [comparisonMainChi_of_not_mem hx]

theorem comparisonMainChic_nonneg (d : ℕ) (ρ : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    0 ≤ comparisonMainChic d ρ f x := by
  by_cases hx : f x ∈ centralWindow d ρ
  · rw [comparisonMainChic_of_mem hx]
  · rw [comparisonMainChic_of_not_mem hx]; norm_num

theorem comparisonMainChi_le_one (d : ℕ) (ρ : ℝ) (f : ℝ → ℝ) (x : ℝ) : comparisonMainChi d ρ f x ≤ 1 := by
  have := comparisonMainChic_nonneg d ρ f x
  have := comparisonMainChi_add_chic d ρ f x
  linarith

theorem comparisonMainChic_le_one (d : ℕ) (ρ : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    comparisonMainChic d ρ f x ≤ 1 := by
  have := comparisonMainChi_nonneg d ρ f x
  have := comparisonMainChi_add_chic d ρ f x
  linarith

theorem measurable_comparisonMainChi (d : ℕ) (ρ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (comparisonMainChi d ρ f) :=
  measurable_const.indicator (hf (measurableSet_centralWindow d ρ))

theorem measurable_comparisonMainChic (d : ℕ) (ρ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (comparisonMainChic d ρ f) :=
  measurable_const.indicator (hf (measurableSet_centralWindow d ρ)).compl

/-- The mass of the rare rows: `∫χᶜ = |G_ρᶜ|`, the law layer's `ν(T_ρ)`. -/
theorem comparisonMain_integral_chic (d : ℕ) (ρ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, comparisonMainChic d ρ f x ∂unitμ = (unitμ {x | f x ∉ centralWindow d ρ}).toReal := by
  have hmeas : MeasurableSet {x : ℝ | f x ∉ centralWindow d ρ} :=
    (hf (measurableSet_centralWindow d ρ)).compl
  simp only [comparisonMainChic]
  rw [integral_indicator_const (1 : ℝ) hmeas]
  simp [measureReal_def]

/-! ## Two Fubini reductions -/

/-- `∫∫F(x) = ∫F` for a bounded measurable `F`: the second variable integrates out. -/
private theorem comparisonMain_integral_fst {F : ℝ → ℝ} (hm : Measurable F) {C : ℝ}
    (hb : ∀ x, |F x| ≤ C) : ∫ z : ℝ × ℝ, F z.1 ∂gμ = ∫ x, F x ∂unitμ := by
  have hint : Integrable (fun z : ℝ × ℝ => F z.1) gμ :=
    integrable_of_abs_le (hm.comp measurable_fst) C fun z => hb z.1
  rw [show gμ = unitμ.prod unitμ from rfl, integral_prod _ hint]
  simp

/-- `∫∫F(y) = ∫F`, the companion of `comparisonMain_integral_fst`. -/
private theorem comparisonMain_integral_snd {F : ℝ → ℝ} (hm : Measurable F) {C : ℝ}
    (hb : ∀ x, |F x| ≤ C) : ∫ z : ℝ × ℝ, F z.2 ∂gμ = ∫ x, F x ∂unitμ := by
  have hint : Integrable (fun z : ℝ × ℝ => F z.2) gμ :=
    integrable_of_abs_le (hm.comp measurable_snd) C fun z => hb z.2
  rw [show gμ = unitμ.prod unitμ from rfl, integral_prod_symm _ hint]
  simp

/-- The weighted first-variation integral `∫(χ|Q_h(f)|)² = A_ρ`: squaring turns the weight into the
indicator of `G_ρ` and the absolute value away. -/
private theorem comparisonMain_integral_qa (d : ℕ) (ρ : ℝ) {f g : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, (comparisonMainChi d ρ f x * |g x|) ^ 2 ∂unitμ
      = ∫ x in {x | f x ∈ centralWindow d ρ}, g x ^ 2 ∂unitμ := by
  have hmeas : MeasurableSet {x : ℝ | f x ∈ centralWindow d ρ} :=
    hf (measurableSet_centralWindow d ρ)
  have hpt : ∀ x : ℝ, (comparisonMainChi d ρ f x * |g x|) ^ 2
      = Set.indicator {x : ℝ | f x ∈ centralWindow d ρ} (fun x => g x ^ 2) x := by
    intro x
    by_cases hx : f x ∈ centralWindow d ρ
    · have hx' : x ∈ {x : ℝ | f x ∈ centralWindow d ρ} := hx
      rw [comparisonMainChi_of_mem hx, Set.indicator_of_mem hx', one_mul, sq_abs]
    · have hx' : x ∉ {x : ℝ | f x ∈ centralWindow d ρ} := hx
      rw [comparisonMainChi_of_not_mem hx, Set.indicator_of_notMem hx']
      ring
  rw [← integral_indicator hmeas, integral_congr_ae (Filter.Eventually.of_forall hpt)]

/-! ## The three integral estimates of Step 3 -/

/-- The uniform bound on the orthogonality integrand, without a weight. -/
private theorem comparisonMain_abs_gfun_le {W : Graphon} (P : FactorDecomp d W) (x y : ℝ) :
    |P.f x ^ (d - 1) * P.f y ^ (d - 1) * P.resid x y| ≤ 2 ^ (d - 1) * 2 ^ (d - 1) * 5 := by
  have h := comparisonMain_abs_ortho_integrand_le P (w := fun _ : ℝ => (1 : ℝ)) (Cw := 1)
    (fun _ => by norm_num) 0 x y
  simpa using h

private theorem comparisonMain_measurable_Jp' (p : ℝ) : Measurable (Jp' p) := by
  unfold Jp'
  exact Real.measurable_log.comp
    ((measurable_id.mul_const (1 - p)).div ((measurable_const.sub measurable_id).mul_const p))

private theorem comparisonMain_measurable_gfun {W : Graphon} (P : FactorDecomp d W) :
    Measurable fun z : ℝ × ℝ =>
      P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2 :=
  (((P.measurable_f_pow (d - 1)).comp measurable_fst).mul
    ((P.measurable_f_pow (d - 1)).comp measurable_snd)).mul P.measurable_resid

/-- The corner integrand is integrable: `|χᶜ(x)χᶜ(y)(ff)^{d-1}E| ≤ 2^{d-1}2^{d-1}·5`. -/
private theorem comparisonMain_integrable_tailSq {W : Graphon} (P : FactorDecomp d W) (ρ : ℝ) :
    Integrable (fun z : ℝ × ℝ => comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
      * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) gμ := by
  have hgm := comparisonMain_measurable_gfun P
  have hchic := measurable_comparisonMainChic d ρ P.meas_f
  have hK0 : (0:ℝ) ≤ 2 ^ (d - 1) * 2 ^ (d - 1) * 5 := by positivity
  have hcornerbd : ∀ z : ℝ × ℝ, |comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
      * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)|
      ≤ (2 ^ (d - 1) * 2 ^ (d - 1) * 5) * comparisonMainChic d ρ P.f z.1 := by
    intro z
    have hc1 := comparisonMainChic_nonneg d ρ P.f z.1
    have hc2 := comparisonMainChic_nonneg d ρ P.f z.2
    have hc2' := comparisonMainChic_le_one d ρ P.f z.2
    have hg := comparisonMain_abs_gfun_le P z.1 z.2
    rw [abs_mul, abs_mul, abs_of_nonneg hc1, abs_of_nonneg hc2]
    have hstep : comparisonMainChic d ρ P.f z.2
        * |P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2|
        ≤ 1 * (2 ^ (d - 1) * 2 ^ (d - 1) * 5) :=
      mul_le_mul hc2' hg (abs_nonneg _) (by norm_num)
    calc comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
          * |P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2|
        = comparisonMainChic d ρ P.f z.1 * (comparisonMainChic d ρ P.f z.2
            * |P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2|) := by ring
      _ ≤ comparisonMainChic d ρ P.f z.1 * (1 * (2 ^ (d - 1) * 2 ^ (d - 1) * 5)) :=
          mul_le_mul_of_nonneg_left hstep hc1
      _ = (2 ^ (d - 1) * 2 ^ (d - 1) * 5) * comparisonMainChic d ρ P.f z.1 := by ring
  have hi4 : Integrable (fun z : ℝ × ℝ => comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
      * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) gμ := by
    refine integrable_of_abs_le
      (((hchic.comp measurable_fst).mul (hchic.comp measurable_snd)).mul hgm)
      (2 ^ (d - 1) * 2 ^ (d - 1) * 5) fun z => ?_
    refine le_trans (hcornerbd z) ?_
    have := comparisonMainChic_le_one d ρ P.f z.1
    nlinarith [comparisonMainChic_nonneg d ρ P.f z.1]
  exact hi4

/-- **`lem:graphon-lagrangian-bound`, the identity.**  Inclusion–exclusion turns the
*central* part of `∫∫(ff)^{d-1}E` into the *rare–rare corner*:

`∬_{G_ρ²}(ff)^{d-1}E = ∬_{(G_ρ^c)²}(ff)^{d-1}E`.

The three vanishing terms are `comparisonMain_weighted_ortho_fst` (twice, once with the weight `1`)
and `comparisonMain_weighted_ortho_snd`.  Separating this identity from the estimate is what lets
the corner be bounded either crudely (`comparisonMain_abs_tailSq_le`, by `|E| ≤ 5`) or sharply
(`comparisonMain_abs_tailSq_le_L2`, by Cauchy–Schwarz), as the caller needs. -/
theorem comparisonMain_tailSq_eq {W : Graphon} (P : FactorDecomp d W) (ρ : ℝ) :
    (∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ)
      = ∫ z, comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ := by
  have hK0 : (0:ℝ) ≤ 2 ^ (d - 1) * 2 ^ (d - 1) * 5 := by positivity
  have hgm := comparisonMain_measurable_gfun P
  have hchic := measurable_comparisonMainChic d ρ P.meas_f
  -- the four integrands
  have hi1 : Integrable (fun z : ℝ × ℝ =>
      (1 : ℝ) * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) gμ :=
    integrable_of_abs_le (measurable_const.mul hgm) _
      fun z => comparisonMain_abs_ortho_integrand_le P (w := fun _ : ℝ => (1 : ℝ)) (Cw := 1)
        (fun _ => by norm_num) z.1 z.1 z.2
  have hi2 : Integrable (fun z : ℝ × ℝ => comparisonMainChic d ρ P.f z.1
      * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) gμ :=
    integrable_of_abs_le ((hchic.comp measurable_fst).mul hgm) _
      fun z => comparisonMain_abs_ortho_integrand_le P (Cw := 1)
        (fun x => by rw [abs_of_nonneg (comparisonMainChic_nonneg d ρ P.f x)]
                     exact comparisonMainChic_le_one d ρ P.f x) z.1 z.1 z.2
  have hi3 : Integrable (fun z : ℝ × ℝ => comparisonMainChic d ρ P.f z.2
      * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) gμ :=
    integrable_of_abs_le ((hchic.comp measurable_snd).mul hgm) _
      fun z => comparisonMain_abs_ortho_integrand_le P (Cw := 1)
        (fun x => by rw [abs_of_nonneg (comparisonMainChic_nonneg d ρ P.f x)]
                     exact comparisonMainChic_le_one d ρ P.f x) z.2 z.1 z.2
  have hi4 := comparisonMain_integrable_tailSq P ρ
  -- the inclusion-exclusion identity
  have hpt : ∀ z : ℝ × ℝ, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
      * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
      = ((1 : ℝ) * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
          - comparisonMainChic d ρ P.f z.1
            * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
          - comparisonMainChic d ρ P.f z.2
            * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2))
        + comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
            * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) := by
    intro z
    have e1 := comparisonMainChi_add_chic d ρ P.f z.1
    have e2 := comparisonMainChi_add_chic d ρ P.f z.2
    have h1 : comparisonMainChi d ρ P.f z.1 = 1 - comparisonMainChic d ρ P.f z.1 := by linarith
    have h2 : comparisonMainChi d ρ P.f z.2 = 1 - comparisonMainChic d ρ P.f z.2 := by linarith
    rw [h1, h2]; ring
  have hchicb : ∀ x : ℝ, |comparisonMainChic d ρ P.f x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (comparisonMainChic_nonneg d ρ P.f x)]
    exact comparisonMainChic_le_one d ρ P.f x
  have hi12 : Integrable (fun z : ℝ × ℝ =>
      (1 : ℝ) * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
        - comparisonMainChic d ρ P.f z.1
          * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) gμ := hi1.sub hi2
  have hi123 : Integrable (fun z : ℝ × ℝ =>
      (1 : ℝ) * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
        - comparisonMainChic d ρ P.f z.1
          * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
        - comparisonMainChic d ρ P.f z.2
          * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) gμ := hi12.sub hi3
  have e1 : ∫ z, ((1 : ℝ) * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
        - comparisonMainChic d ρ P.f z.1
          * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
        - comparisonMainChic d ρ P.f z.2
          * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
        + comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
          * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) ∂gμ
      = (∫ z, ((1 : ℝ) * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
            - comparisonMainChic d ρ P.f z.1
              * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
            - comparisonMainChic d ρ P.f z.2
              * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) ∂gμ)
        + ∫ z, comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
            * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ :=
    integral_add hi123 hi4
  have e2 : ∫ z, ((1 : ℝ) * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
        - comparisonMainChic d ρ P.f z.1
          * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
        - comparisonMainChic d ρ P.f z.2
          * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) ∂gμ
      = (∫ z, ((1 : ℝ) * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
            - comparisonMainChic d ρ P.f z.1
              * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) ∂gμ)
        - ∫ z, comparisonMainChic d ρ P.f z.2
            * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ :=
    integral_sub hi12 hi3
  have e3 : ∫ z, ((1 : ℝ) * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)
        - comparisonMainChic d ρ P.f z.1
          * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) ∂gμ
      = (∫ z, (1 : ℝ) * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ)
        - ∫ z, comparisonMainChic d ρ P.f z.1
            * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ :=
    integral_sub hi1 hi2
  have z1 : ∫ z, (1 : ℝ) * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ = 0 :=
    comparisonMain_weighted_ortho_fst P (w := fun _ : ℝ => (1 : ℝ)) measurable_const (Cw := 1)
      (fun _ => by norm_num)
  have z2 : ∫ z, comparisonMainChic d ρ P.f z.1
      * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ = 0 :=
    comparisonMain_weighted_ortho_fst P hchic (Cw := 1) hchicb
  have z3 : ∫ z, comparisonMainChic d ρ P.f z.2
      * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ = 0 :=
    comparisonMain_weighted_ortho_snd P hchic (Cw := 1) hchicb
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), e1, e2, e3, z1, z2, z3]
  simp

/-- **`lem:graphon-lagrangian-bound`, crude form.**  The corner is bounded by a constant
times `|G_ρᶜ|`, using `|E| ≤ 5` pointwise. -/
theorem comparisonMain_abs_tailSq_le {W : Graphon} (P : FactorDecomp d W) (ρ : ℝ) :
    |∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ|
      ≤ (2 ^ (d - 1) * 2 ^ (d - 1) * 5)
          * (unitμ {x | P.f x ∉ centralWindow d ρ}).toReal := by
  have hK0 : (0:ℝ) ≤ 2 ^ (d - 1) * 2 ^ (d - 1) * 5 := by positivity
  have hgm := comparisonMain_measurable_gfun P
  have hchic := measurable_comparisonMainChic d ρ P.meas_f
  have hi4 := comparisonMain_integrable_tailSq P ρ
  have hcornerbd : ∀ z : ℝ × ℝ, |comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
      * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)|
      ≤ (2 ^ (d - 1) * 2 ^ (d - 1) * 5) * comparisonMainChic d ρ P.f z.1 := by
    intro z
    have hc1 := comparisonMainChic_nonneg d ρ P.f z.1
    have hc2 := comparisonMainChic_nonneg d ρ P.f z.2
    have hc2' := comparisonMainChic_le_one d ρ P.f z.2
    have hg := comparisonMain_abs_gfun_le P z.1 z.2
    rw [abs_mul, abs_mul, abs_of_nonneg hc1, abs_of_nonneg hc2]
    have hstep : comparisonMainChic d ρ P.f z.2
        * |P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2|
        ≤ 1 * (2 ^ (d - 1) * 2 ^ (d - 1) * 5) :=
      mul_le_mul hc2' hg (abs_nonneg _) (by norm_num)
    calc comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
          * |P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2|
        = comparisonMainChic d ρ P.f z.1 * (comparisonMainChic d ρ P.f z.2
            * |P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2|) := by ring
      _ ≤ comparisonMainChic d ρ P.f z.1 * (1 * (2 ^ (d - 1) * 2 ^ (d - 1) * 5)) :=
          mul_le_mul_of_nonneg_left hstep hc1
      _ = (2 ^ (d - 1) * 2 ^ (d - 1) * 5) * comparisonMainChic d ρ P.f z.1 := by ring
  rw [comparisonMain_tailSq_eq P ρ]
  have hle : |∫ z, comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
      * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ|
      ≤ ∫ z, (2 ^ (d - 1) * 2 ^ (d - 1) * 5) * comparisonMainChic d ρ P.f z.1 ∂gμ := by
    refine le_trans (abs_integral_le_integral_abs) (integral_mono hi4.abs ?_ hcornerbd)
    exact (integrable_of_abs_le ((hchic.comp measurable_fst).const_mul _)
      (2 ^ (d - 1) * 2 ^ (d - 1) * 5) fun z => by
        rw [abs_mul, abs_of_nonneg hK0, abs_of_nonneg (comparisonMainChic_nonneg d ρ P.f z.1)]
        nlinarith [comparisonMainChic_le_one d ρ P.f z.1, comparisonMainChic_nonneg d ρ P.f z.1])
  rw [integral_const_mul,
    comparisonMain_integral_fst hchic (C := 1)
      (fun x => by rw [abs_of_nonneg (comparisonMainChic_nonneg d ρ P.f x)]
                   exact comparisonMainChic_le_one d ρ P.f x),
    comparisonMain_integral_chic d ρ P.meas_f] at hle
  exact hle

/-- `χᶜ` is idempotent, being `{0,1}`-valued. -/
private theorem comparisonMain_chic_sq (d : ℕ) (ρ : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    comparisonMainChic d ρ f x * comparisonMainChic d ρ f x = comparisonMainChic d ρ f x := by
  by_cases hx : f x ∈ centralWindow d ρ
  · rw [comparisonMainChic_of_mem hx]; ring
  · rw [comparisonMainChic_of_not_mem hx]; ring

/-- `∫∫χᶜ(x)χᶜ(y) = ε²`: the rare–rare corner has product measure `ε²`.  This is the factor
that turns the crude `Cε` of `comparisonMain_abs_tailSq_le` into the paper's `Cε‖E‖₂`. -/
private theorem comparisonMain_integral_chic_prod (d : ℕ) (ρ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ z : ℝ × ℝ, comparisonMainChic d ρ f z.1 * comparisonMainChic d ρ f z.2 ∂gμ
      = (unitμ {x | f x ∉ centralWindow d ρ}).toReal ^ 2 := by
  have hchic := measurable_comparisonMainChic d ρ hf
  have hb : ∀ x : ℝ, |comparisonMainChic d ρ f x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (comparisonMainChic_nonneg d ρ f x)]; exact comparisonMainChic_le_one d ρ f x
  have hint : Integrable (fun z : ℝ × ℝ =>
      comparisonMainChic d ρ f z.1 * comparisonMainChic d ρ f z.2) gμ := by
    refine integrable_of_abs_le
      ((hchic.comp measurable_fst).mul (hchic.comp measurable_snd)) 1 fun z => ?_
    rw [abs_mul]
    exact mul_le_one₀ (hb z.1) (abs_nonneg _) (hb z.2)
  rw [show gμ = unitμ.prod unitμ from rfl, integral_prod _ hint]
  have hpt : ∀ x : ℝ, (∫ y, comparisonMainChic d ρ f x * comparisonMainChic d ρ f y ∂unitμ)
      = comparisonMainChic d ρ f x * (unitμ {x | f x ∉ centralWindow d ρ}).toReal := by
    intro x
    rw [integral_const_mul, comparisonMain_integral_chic d ρ hf]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_mul_const,
    comparisonMain_integral_chic d ρ hf]
  ring

/-- **`lem:graphon-lagrangian-bound`, sharp form**.

`|∬_{G_ρ²}(ff)^{d-1}E| ≤ 2^{d-1}2^{d-1}·ε·‖E‖₂`.

`comparisonMain_abs_tailSq_le` bounds the same quantity by `2^{d-1}2^{d-1}·5·ε`, using `|E| ≤ 5`
pointwise.  That is enough for the crude tail treatment of `comparisonMain_exists_residual_bound`,
but **not** for `eq:graphon-lagrangian-bound`: there the loss must be beaten by the rare-row
gain `c_ρε` of the assembled rare-row step, and `c_ρ` is a fixed insertion-gap constant with
no reason to exceed `Γ2^{2(d-1)}·5`.  The paper's route is Cauchy–Schwarz on the corner,
whose product measure is `ε²`, giving `Cε‖E‖_{2,(G_ρ^c)²} ≤ Cε‖E‖₂ ≤ CMεh²` along the
family — a loss that vanishes relative to `ε`.

The identity `∬_{G_ρ²} = ∬_{(G_ρ^c)²}` is `comparisonMain_tailSq_eq`; only the estimate differs. -/
theorem comparisonMain_abs_tailSq_le_L2 {W : Graphon} (P : FactorDecomp d W) (ρ : ℝ) :
    |∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ|
      ≤ 2 ^ (d - 1) * 2 ^ (d - 1)
          * ((unitμ {x | P.f x ∉ centralWindow d ρ}).toReal * P.residL2) := by
  rw [comparisonMain_tailSq_eq P ρ]
  have hK0 : (0:ℝ) ≤ (2 : ℝ) ^ (d - 1) * 2 ^ (d - 1) := by positivity
  have hchic := measurable_comparisonMainChic d ρ P.meas_f
  have hi4 := comparisonMain_integrable_tailSq P ρ
  have hcm : Measurable fun z : ℝ × ℝ =>
      comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 :=
    (hchic.comp measurable_fst).mul (hchic.comp measurable_snd)
  have hcb : ∀ z : ℝ × ℝ, |comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2| ≤ 1 := by
    intro z
    rw [abs_mul, abs_of_nonneg (comparisonMainChic_nonneg d ρ P.f z.1),
      abs_of_nonneg (comparisonMainChic_nonneg d ρ P.f z.2)]
    exact mul_le_one₀ (comparisonMainChic_le_one d ρ P.f z.1) (comparisonMainChic_nonneg d ρ P.f z.2)
      (comparisonMainChic_le_one d ρ P.f z.2)
  -- the three integrands of the Cauchy–Schwarz step
  have hAi : Integrable (fun z : ℝ × ℝ =>
      (comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2) ^ 2) gμ :=
    integrable_of_abs_le (hcm.pow_const 2) 1 fun z => by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hcb z)
  have hBi : Integrable (fun z : ℝ × ℝ => |P.resid z.1 z.2| ^ 2) gμ := by
    have h := P.integrable_resid_sq
    exact h.congr (Filter.Eventually.of_forall fun z => by simp [sq_abs])
  have hABi : Integrable (fun z : ℝ × ℝ =>
      comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 * |P.resid z.1 z.2|) gμ := by
    refine integrable_of_abs_le (hcm.mul P.measurable_resid.abs) 5 fun z => ?_
    rw [abs_mul, abs_abs]
    calc |comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2| * |P.resid z.1 z.2|
        ≤ 1 * 5 := mul_le_mul (hcb z) (P.abs_resid_le z.1 z.2) (abs_nonneg _) zero_le_one
      _ = 5 := one_mul 5
  -- pointwise: `|χᶜχᶜ(ff)^{d-1}E| ≤ 2^{d-1}2^{d-1}·(χᶜχᶜ|E|)`
  have hptb : ∀ z : ℝ × ℝ, |comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
        * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)|
      ≤ 2 ^ (d - 1) * 2 ^ (d - 1)
        * (comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 * |P.resid z.1 z.2|) := by
    intro z
    have hf1 : |P.f z.1 ^ (d - 1)| ≤ 2 ^ (d - 1) := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (P.abs_f_le z.1) _
    have hf2 : |P.f z.2 ^ (d - 1)| ≤ 2 ^ (d - 1) := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (P.abs_f_le z.2) _
    have hgle : |P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2|
        ≤ 2 ^ (d - 1) * 2 ^ (d - 1) * |P.resid z.1 z.2| := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hf1 hf2 (abs_nonneg _) (by positivity)) le_rfl
        (abs_nonneg _) (by positivity)
    rw [abs_mul, abs_mul, abs_of_nonneg (comparisonMainChic_nonneg d ρ P.f z.1),
      abs_of_nonneg (comparisonMainChic_nonneg d ρ P.f z.2)]
    have hc0 : (0:ℝ) ≤ comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 :=
      mul_nonneg (comparisonMainChic_nonneg d ρ P.f z.1) (comparisonMainChic_nonneg d ρ P.f z.2)
    calc comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
          * |P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2|
        ≤ comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
            * (2 ^ (d - 1) * 2 ^ (d - 1) * |P.resid z.1 z.2|) :=
          mul_le_mul_of_nonneg_left hgle hc0
      _ = 2 ^ (d - 1) * 2 ^ (d - 1)
            * (comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 * |P.resid z.1 z.2|) := by
          ring
  have h1 : |∫ z, comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
        * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ|
      ≤ ∫ z, 2 ^ (d - 1) * 2 ^ (d - 1)
          * (comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 * |P.resid z.1 z.2|) ∂gμ :=
    le_trans abs_integral_le_integral_abs
      (integral_mono hi4.abs (hABi.const_mul _) hptb)
  -- Cauchy–Schwarz
  have h2 := integral_mul_le_sqrt_mul_sqrt (μ := gμ)
    (f := fun z : ℝ × ℝ => comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2)
    (g := fun z : ℝ × ℝ => |P.resid z.1 z.2|) hAi hBi hABi
  have hsq : ∫ z : ℝ × ℝ, (comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2) ^ 2 ∂gμ
      = (unitμ {x | P.f x ∉ centralWindow d ρ}).toReal ^ 2 := by
    rw [← comparisonMain_integral_chic_prod d ρ P.meas_f]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    calc (comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2) ^ 2
        = (comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.1)
          * (comparisonMainChic d ρ P.f z.2 * comparisonMainChic d ρ P.f z.2) := by ring
      _ = comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 := by
          rw [comparisonMain_chic_sq, comparisonMain_chic_sq]
  have hE : ∫ z : ℝ × ℝ, |P.resid z.1 z.2| ^ 2 ∂gμ = P.residSq :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by simp [sq_abs])
  have hep : (0:ℝ) ≤ (unitμ {x | P.f x ∉ centralWindow d ρ}).toReal := ENNReal.toReal_nonneg
  rw [hsq, hE, Real.sqrt_sq hep] at h2
  rw [integral_const_mul] at h1
  have h3 : ∫ z : ℝ × ℝ, comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
        * |P.resid z.1 z.2| ∂gμ
      ≤ (unitμ {x | P.f x ∉ centralWindow d ρ}).toReal * P.residL2 := h2
  calc |∫ z, comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
          * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ|
      ≤ 2 ^ (d - 1) * 2 ^ (d - 1)
          * ∫ z : ℝ × ℝ, comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
              * |P.resid z.1 z.2| ∂gμ := h1
    _ ≤ 2 ^ (d - 1) * 2 ^ (d - 1)
          * ((unitμ {x | P.f x ∉ centralWindow d ρ}).toReal * P.residL2) :=
        mul_le_mul_of_nonneg_left h3 hK0

/-- A crude uniform bound on the first-variation quadratic along a factor valued in `[0,2]`. -/
private theorem comparisonMain_abs_Qh_le {B : KKTFamily d} {h : ℝ} (hh : |h| < B.h₀)
    {u : ℝ} (hu0 : 0 ≤ u) (hu2 : u ≤ 2) : |B.Qh h u| ≤ 9 := by
  have hs0 := KKTFamily.sVal_pos hh
  have hs1 := KKTFamily.sVal_lt_one hh
  have ht0 := KKTFamily.tVal_pos hh
  have ht1 := KKTFamily.tVal_lt_one hh
  have h1 : |u - B.sVal h| ≤ 3 := by rw [abs_le]; constructor <;> linarith
  have h2 : |u - B.tVal h| ≤ 3 := by rw [abs_le]; constructor <;> linarith
  have he : |B.Qh h u| = |u - B.sVal h| * |u - B.tVal h| := by
    simp only [KKTFamily.Qh, abs_mul]
  rw [he]
  nlinarith [abs_nonneg (u - B.sVal h), abs_nonneg (u - B.tVal h)]

/-- The weighted first-variation factor is bounded: `(χ|Q_h(f)|)² ≤ 81`. -/
private theorem comparisonMain_qa_sq_le {B : KKTFamily d} {h : ℝ} (hh : |h| < B.h₀) (ρ : ℝ)
    {f : ℝ → ℝ} (hnn : ∀ x, 0 ≤ f x) (hbd : ∀ x, f x ≤ 2) (x : ℝ) :
    (comparisonMainChi d ρ f x * |B.Qh h (f x)|) ^ 2 ≤ 81 := by
  have h1 := comparisonMainChi_nonneg d ρ f x
  have h2 := comparisonMainChi_le_one d ρ f x
  have h3 := comparisonMain_abs_Qh_le hh (hnn x) (hbd x)
  have h4 : (0:ℝ) ≤ |B.Qh h (f x)| := abs_nonneg _
  have hprod : comparisonMainChi d ρ f x * |B.Qh h (f x)| ≤ 9 := by
    have := mul_le_mul h2 h3 h4 (by norm_num : (0:ℝ) ≤ 1)
    linarith
  have hprod0 : (0:ℝ) ≤ comparisonMainChi d ρ f x * |B.Qh h (f x)| := mul_nonneg h1 h4
  calc (comparisonMainChi d ρ f x * |B.Qh h (f x)|) ^ 2 ≤ 9 ^ 2 :=
        pow_le_pow_left₀ hprod0 hprod 2
    _ = 81 := by norm_num

private theorem comparisonMain_measurable_Fkkt (d : ℕ) (p γ : ℝ) : Measurable (Fkkt d p γ) := by
  unfold Fkkt
  exact (comparisonMain_measurable_Jp' p).sub ((measurable_id.pow_const (d - 1)).const_mul γ)

/-- The weighted first-variation integral is `A_ρ`, in the `gμ`-form used below. -/
private theorem comparisonMain_integral_qa_fst (d : ℕ) (ρ : ℝ) (B : KKTFamily d) {h : ℝ}
    (hh : |h| < B.h₀) {W : Graphon} (P : FactorDecomp d W) :
    ∫ z : ℝ × ℝ, (comparisonMainChi d ρ P.f z.1 * |B.Qh h (P.f z.1)|) ^ 2 ∂gμ
      = ∫ x in {x | P.f x ∈ centralWindow d ρ}, B.Qh h (P.f x) ^ 2 ∂unitμ := by
  have hmQ : Measurable fun x : ℝ => (comparisonMainChi d ρ P.f x * |B.Qh h (P.f x)|) ^ 2 :=
    (((measurable_comparisonMainChi d ρ P.meas_f).mul
      (((measurable_id.sub measurable_const).mul
        (measurable_id.sub measurable_const)).comp P.meas_f).abs)).pow_const 2
  have hbQ : ∀ x : ℝ, |(comparisonMainChi d ρ P.f x * |B.Qh h (P.f x)|) ^ 2| ≤ 81 := by
    intro x
    rw [abs_of_nonneg (by positivity)]
    exact comparisonMain_qa_sq_le hh ρ P.f_nonneg P.f_bdd x
  rw [comparisonMain_integral_fst hmQ hbQ, comparisonMain_integral_qa d ρ P.meas_f]

/-- The same integral read off the second variable. -/
private theorem comparisonMain_integral_qa_snd (d : ℕ) (ρ : ℝ) (B : KKTFamily d) {h : ℝ}
    (hh : |h| < B.h₀) {W : Graphon} (P : FactorDecomp d W) :
    ∫ z : ℝ × ℝ, (comparisonMainChi d ρ P.f z.2 * |B.Qh h (P.f z.2)|) ^ 2 ∂gμ
      = ∫ x in {x | P.f x ∈ centralWindow d ρ}, B.Qh h (P.f x) ^ 2 ∂unitμ := by
  have hmQ : Measurable fun x : ℝ => (comparisonMainChi d ρ P.f x * |B.Qh h (P.f x)|) ^ 2 :=
    (((measurable_comparisonMainChi d ρ P.meas_f).mul
      (((measurable_id.sub measurable_const).mul
        (measurable_id.sub measurable_const)).comp P.meas_f).abs)).pow_const 2
  have hbQ : ∀ x : ℝ, |(comparisonMainChi d ρ P.f x * |B.Qh h (P.f x)|) ^ 2| ≤ 81 := by
    intro x
    rw [abs_of_nonneg (by positivity)]
    exact comparisonMain_qa_sq_le hh ρ P.f_nonneg P.f_bdd x
  rw [comparisonMain_integral_snd hmQ hbQ, comparisonMain_integral_qa d ρ P.meas_f]

/-- **`lem:graphon-lagrangian-bound`.**  The KKT-linear term over the central set is bounded
by `θ(A_ρ + ‖E‖²_{2,G_ρ²})` — the **central** residual norm, which is what Step 5 needs: a
bound against the full `‖E‖₂²` would cost a fixed multiple of `ε` on the mixed rectangles,
and the rare-row gain `c_ρε` has no reason to beat it.  The multiplier bound `comparisonMain_exists_multiplier_bound` supplies the
factor `θ(|Q_h(f(x))| + |Q_h(f(y))|)`, and Young's inequality in the form
`ab ≤ (a² + b²)/2` replaces the paper's Cauchy–Schwarz. -/
theorem comparisonMain_abs_kkt_error_le (hd : 2 ≤ d) (B : KKTFamily d) {h ρ θ : ℝ}
    (hθ0 : 0 < θ) (hh : |h| < B.h₀) (hρ0 : 0 < ρ) (hρa : ρ ≤ rStar d / 4)
    (hρb : ρ ≤ (1 - rStar d) / 6)
    (hmul : ∀ x ∈ centralWindow d ρ, ∀ y ∈ centralWindow d ρ,
      |Fkkt d (B.p h) (B.gam h) (x * y)| ≤ θ * (|B.Qh h x| + |B.Qh h y|))
    {W : Graphon} (P : FactorDecomp d W) {CF : ℝ} (hCF0 : 0 ≤ CF)
    (hCF : ∀ z ∈ Set.Icc (comparisonMainA d) (comparisonMainB d), |Fkkt d (B.p h) (B.gam h) z| ≤ CF) :
    |∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * (Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2) ∂gμ|
      ≤ θ * ((∫ x in {x | P.f x ∈ centralWindow d ρ}, B.Qh h (P.f x) ^ 2 ∂unitμ)
              + ∫ z : ℝ × ℝ, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2 ∂gμ) := by
  have hmv : Measurable fun z : ℝ × ℝ => P.f z.1 * P.f z.2 :=
    (P.meas_f.comp measurable_fst).mul (P.meas_f.comp measurable_snd)
  have hmchi1 : Measurable fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1 :=
    (measurable_comparisonMainChi d ρ P.meas_f).comp measurable_fst
  have hmchi2 : Measurable fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.2 :=
    (measurable_comparisonMainChi d ρ P.meas_f).comp measurable_snd
  have hmQ1 : Measurable fun z : ℝ × ℝ =>
      (comparisonMainChi d ρ P.f z.1 * |B.Qh h (P.f z.1)|) ^ 2 :=
    ((hmchi1.mul ((((measurable_id.sub measurable_const).mul
      (measurable_id.sub measurable_const)).comp P.meas_f).comp measurable_fst).abs)).pow_const 2
  have hmQ2 : Measurable fun z : ℝ × ℝ =>
      (comparisonMainChi d ρ P.f z.2 * |B.Qh h (P.f z.2)|) ^ 2 :=
    ((hmchi2.mul ((((measurable_id.sub measurable_const).mul
      (measurable_id.sub measurable_const)).comp P.meas_f).comp measurable_snd).abs)).pow_const 2
  -- the pointwise Young bound
  have hpt : ∀ z : ℝ × ℝ, |comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * (Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)|
      ≤ θ / 2 * (comparisonMainChi d ρ P.f z.1 * |B.Qh h (P.f z.1)|) ^ 2
        + θ / 2 * (comparisonMainChi d ρ P.f z.2 * |B.Qh h (P.f z.2)|) ^ 2
        + θ * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2) := by
    intro z
    by_cases h1 : P.f z.1 ∈ centralWindow d ρ
    · by_cases h2 : P.f z.2 ∈ centralWindow d ρ
      · simp only [comparisonMainChi_of_mem h1, comparisonMainChi_of_mem h2, one_mul]
        have hb := hmul _ h1 _ h2
        have hE : (0:ℝ) ≤ |P.resid z.1 z.2| := abs_nonneg _
        rw [abs_mul]
        have hstep : |Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2)| * |P.resid z.1 z.2|
            ≤ θ * (|B.Qh h (P.f z.1)| + |B.Qh h (P.f z.2)|) * |P.resid z.1 z.2| :=
          mul_le_mul_of_nonneg_right hb hE
        have hy1 : (0:ℝ) ≤ θ * (|B.Qh h (P.f z.1)| - |P.resid z.1 z.2|) ^ 2 := by positivity
        have hy2 : (0:ℝ) ≤ θ * (|B.Qh h (P.f z.2)| - |P.resid z.1 z.2|) ^ 2 := by positivity
        have hsq : |P.resid z.1 z.2| ^ 2 = P.resid z.1 z.2 ^ 2 := sq_abs _
        nlinarith [hstep, hy1, hy2, hsq]
      · simp only [comparisonMainChi_of_not_mem h2, mul_zero, zero_mul, abs_zero]
        positivity
    · simp only [comparisonMainChi_of_not_mem h1, zero_mul, abs_zero]
      positivity
  -- integrability of both sides
  have hbdL : ∀ z : ℝ × ℝ, |comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
      * (Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)| ≤ CF * 5 := by
    intro z
    by_cases h1 : P.f z.1 ∈ centralWindow d ρ
    · by_cases h2 : P.f z.2 ∈ centralWindow d ρ
      · have hv : P.f z.1 * P.f z.2 ∈ Set.Icc (comparisonMainA d) (comparisonMainB d) :=
          comparisonMain_mul_mem hd hρ0 hρa hρb
            ((factorTail_mem_centralWindow_iff d ρ _).mp h1)
            ((factorTail_mem_centralWindow_iff d ρ _).mp h2)
        simp only [comparisonMainChi_of_mem h1, comparisonMainChi_of_mem h2, one_mul]
        rw [abs_mul]
        exact mul_le_mul (hCF _ hv) (P.abs_resid_le _ _) (abs_nonneg _) hCF0
      · simp only [comparisonMainChi_of_not_mem h2, mul_zero, zero_mul, abs_zero]
        positivity
    · simp only [comparisonMainChi_of_not_mem h1, zero_mul, abs_zero]
      positivity
  have hintL : Integrable (fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
      * (Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)) gμ :=
    integrable_of_abs_le
      ((hmchi1.mul hmchi2).mul
        (((comparisonMain_measurable_Fkkt d (B.p h) (B.gam h)).comp hmv).mul P.measurable_resid))
      (CF * 5) hbdL
  have hintQ1 : Integrable (fun z : ℝ × ℝ =>
      θ / 2 * (comparisonMainChi d ρ P.f z.1 * |B.Qh h (P.f z.1)|) ^ 2) gμ := by
    refine integrable_of_abs_le (hmQ1.const_mul _) (θ / 2 * 81) fun z => ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ θ / 2),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (comparisonMainChi d ρ P.f z.1
        * |B.Qh h (P.f z.1)|) ^ 2)]
    have hq := comparisonMain_qa_sq_le hh ρ P.f_nonneg P.f_bdd z.1
    nlinarith [hθ0.le]
  have hintQ2 : Integrable (fun z : ℝ × ℝ =>
      θ / 2 * (comparisonMainChi d ρ P.f z.2 * |B.Qh h (P.f z.2)|) ^ 2) gμ := by
    refine integrable_of_abs_le (hmQ2.const_mul _) (θ / 2 * 81) fun z => ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ θ / 2),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (comparisonMainChi d ρ P.f z.2
        * |B.Qh h (P.f z.2)|) ^ 2)]
    have hq := comparisonMain_qa_sq_le hh ρ P.f_nonneg P.f_bdd z.2
    nlinarith [hθ0.le]
  have hccint : Integrable (fun z : ℝ × ℝ =>
      comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2) gμ := by
    refine integrable_of_abs_le
      ((hmchi1.mul hmchi2).mul (P.measurable_resid.pow_const 2)) 25 fun z => ?_
    have h1 := comparisonMainChi_nonneg d ρ P.f z.1
    have h3 := comparisonMainChi_nonneg d ρ P.f z.2
    have h5 : P.resid z.1 z.2 ^ 2 ≤ 25 := by
      have := P.abs_resid_le z.1 z.2
      nlinarith [abs_nonneg (P.resid z.1 z.2), sq_abs (P.resid z.1 z.2)]
    have h7 : comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 ≤ 1 :=
      mul_le_one₀ (comparisonMainChi_le_one d ρ P.f z.1) h3 (comparisonMainChi_le_one d ρ P.f z.2)
    rw [abs_of_nonneg (by positivity)]
    calc comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2
        ≤ 1 * 25 := mul_le_mul h7 h5 (sq_nonneg _) zero_le_one
      _ = 25 := by norm_num
  have hintE : Integrable (fun z : ℝ × ℝ => θ * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2)) gμ :=
    hccint.const_mul θ
  have hint12 : Integrable (fun z : ℝ × ℝ =>
      θ / 2 * (comparisonMainChi d ρ P.f z.1 * |B.Qh h (P.f z.1)|) ^ 2
      + θ / 2 * (comparisonMainChi d ρ P.f z.2 * |B.Qh h (P.f z.2)|) ^ 2) gμ := hintQ1.add hintQ2
  have hintR : Integrable (fun z : ℝ × ℝ =>
      θ / 2 * (comparisonMainChi d ρ P.f z.1 * |B.Qh h (P.f z.1)|) ^ 2
      + θ / 2 * (comparisonMainChi d ρ P.f z.2 * |B.Qh h (P.f z.2)|) ^ 2
      + θ * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2)) gμ := hint12.add hintE
  -- integrate
  have hmono := integral_mono hintL.abs hintR hpt
  have hRhs : ∫ z, (θ / 2 * (comparisonMainChi d ρ P.f z.1 * |B.Qh h (P.f z.1)|) ^ 2
      + θ / 2 * (comparisonMainChi d ρ P.f z.2 * |B.Qh h (P.f z.2)|) ^ 2
      + θ * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2)) ∂gμ
      = θ * ((∫ x in {x | P.f x ∈ centralWindow d ρ}, B.Qh h (P.f x) ^ 2 ∂unitμ)
              + ∫ z : ℝ × ℝ, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2 ∂gμ) := by
    have e1 : ∫ z, (θ / 2 * (comparisonMainChi d ρ P.f z.1 * |B.Qh h (P.f z.1)|) ^ 2
        + θ / 2 * (comparisonMainChi d ρ P.f z.2 * |B.Qh h (P.f z.2)|) ^ 2
        + θ * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2)) ∂gμ
        = (∫ z, (θ / 2 * (comparisonMainChi d ρ P.f z.1 * |B.Qh h (P.f z.1)|) ^ 2
            + θ / 2 * (comparisonMainChi d ρ P.f z.2 * |B.Qh h (P.f z.2)|) ^ 2) ∂gμ)
          + ∫ z, θ * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2) ∂gμ := integral_add hint12 hintE
    have e2 : ∫ z, (θ / 2 * (comparisonMainChi d ρ P.f z.1 * |B.Qh h (P.f z.1)|) ^ 2
        + θ / 2 * (comparisonMainChi d ρ P.f z.2 * |B.Qh h (P.f z.2)|) ^ 2) ∂gμ
        = (∫ z, θ / 2 * (comparisonMainChi d ρ P.f z.1 * |B.Qh h (P.f z.1)|) ^ 2 ∂gμ)
          + ∫ z, θ / 2 * (comparisonMainChi d ρ P.f z.2 * |B.Qh h (P.f z.2)|) ^ 2 ∂gμ :=
      integral_add hintQ1 hintQ2
    rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul,
      comparisonMain_integral_qa_fst d ρ B hh P, comparisonMain_integral_qa_snd d ρ B hh P]
    ring
  calc |∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
          * (Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2) ∂gμ|
      ≤ ∫ z, |comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
          * (Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)| ∂gμ :=
        abs_integral_le_integral_abs
    _ ≤ _ := hmono
    _ = _ := hRhs

/-- `∫(χᶜ(x) + χᶜ(y)) = 2ν(T_ρ)`. -/
private theorem comparisonMain_integral_chic_sum (d : ℕ) (ρ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ z : ℝ × ℝ, (comparisonMainChic d ρ f z.1 + comparisonMainChic d ρ f z.2) ∂gμ
      = 2 * (unitμ {x | f x ∉ centralWindow d ρ}).toReal := by
  have hchic := measurable_comparisonMainChic d ρ hf
  have hb : ∀ x : ℝ, |comparisonMainChic d ρ f x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (comparisonMainChic_nonneg d ρ f x)]
    exact comparisonMainChic_le_one d ρ f x
  have h1 : Integrable (fun z : ℝ × ℝ => comparisonMainChic d ρ f z.1) gμ :=
    integrable_of_abs_le (hchic.comp measurable_fst) 1 fun z => hb z.1
  have h2 : Integrable (fun z : ℝ × ℝ => comparisonMainChic d ρ f z.2) gμ :=
    integrable_of_abs_le (hchic.comp measurable_snd) 1 fun z => hb z.2
  have e : ∫ z : ℝ × ℝ, (comparisonMainChic d ρ f z.1 + comparisonMainChic d ρ f z.2) ∂gμ
      = (∫ z : ℝ × ℝ, comparisonMainChic d ρ f z.1 ∂gμ)
        + ∫ z : ℝ × ℝ, comparisonMainChic d ρ f z.2 ∂gμ := integral_add h1 h2
  rw [e, comparisonMain_integral_fst hchic hb, comparisonMain_integral_snd hchic hb,
    comparisonMain_integral_chic d ρ hf]
  ring

/-- The central part of `‖E‖₂²` differs from the whole by at most `25` times the mass of the
rare rows: the paper's `‖E‖_{2,(G_ρ^c)²}² ≤ Cε` together with the two mixed rectangles. -/
private theorem comparisonMain_central_resid_ge (d : ℕ) (ρ : ℝ) {W : Graphon} (P : FactorDecomp d W) :
    P.residSq
        - 25 * (∫ z : ℝ × ℝ, (comparisonMainChic d ρ P.f z.1 + comparisonMainChic d ρ P.f z.2) ∂gμ)
      ≤ ∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
          * P.resid z.1 z.2 ^ 2 ∂gμ := by
  have hmchi1 : Measurable fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1 :=
    (measurable_comparisonMainChi d ρ P.meas_f).comp measurable_fst
  have hmchi2 : Measurable fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.2 :=
    (measurable_comparisonMainChi d ρ P.meas_f).comp measurable_snd
  have hmchic1 : Measurable fun z : ℝ × ℝ => comparisonMainChic d ρ P.f z.1 :=
    (measurable_comparisonMainChic d ρ P.meas_f).comp measurable_fst
  have hmchic2 : Measurable fun z : ℝ × ℝ => comparisonMainChic d ρ P.f z.2 :=
    (measurable_comparisonMainChic d ρ P.meas_f).comp measurable_snd
  have hE2 : ∀ z : ℝ × ℝ, P.resid z.1 z.2 ^ 2 ≤ 25 := by
    intro z
    have := P.abs_resid_le z.1 z.2
    nlinarith [abs_nonneg (P.resid z.1 z.2), sq_abs (P.resid z.1 z.2)]
  have hF1int : Integrable (fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1
      * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2) gμ := by
    refine integrable_of_abs_le
      ((hmchi1.mul hmchi2).mul (P.measurable_resid.pow_const 2)) 25 fun z => ?_
    have h1 := comparisonMainChi_nonneg d ρ P.f z.1
    have h2 := comparisonMainChi_le_one d ρ P.f z.1
    have h3 := comparisonMainChi_nonneg d ρ P.f z.2
    have h4 := comparisonMainChi_le_one d ρ P.f z.2
    have h5 := hE2 z
    have h6 : (0:ℝ) ≤ P.resid z.1 z.2 ^ 2 := sq_nonneg _
    have h7 : comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 ≤ 1 :=
      mul_le_one₀ h2 h3 h4
    have h8 : (0:ℝ) ≤ comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 := mul_nonneg h1 h3
    rw [abs_of_nonneg (by positivity)]
    calc comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2
        ≤ 1 * 25 := mul_le_mul h7 h5 h6 zero_le_one
      _ = 25 := by norm_num
  have hccint : Integrable (fun z : ℝ × ℝ =>
      25 * (comparisonMainChic d ρ P.f z.1 + comparisonMainChic d ρ P.f z.2)) gμ := by
    refine integrable_of_abs_le ((hmchic1.add hmchic2).const_mul 25) 50 fun z => ?_
    have h1 := comparisonMainChic_nonneg d ρ P.f z.1
    have h2 := comparisonMainChic_le_one d ρ P.f z.1
    have h3 := comparisonMainChic_nonneg d ρ P.f z.2
    have h4 := comparisonMainChic_le_one d ρ P.f z.2
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hpt : ∀ z : ℝ × ℝ, P.resid z.1 z.2 ^ 2 - comparisonMainChi d ρ P.f z.1
      * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2
      ≤ 25 * (comparisonMainChic d ρ P.f z.1 + comparisonMainChic d ρ P.f z.2) := by
    intro z
    have h1 := comparisonMainChi_nonneg d ρ P.f z.1
    have h2 := comparisonMainChi_le_one d ρ P.f z.1
    have h3 := comparisonMainChi_nonneg d ρ P.f z.2
    have h4 := comparisonMainChi_le_one d ρ P.f z.2
    have e1 := comparisonMainChi_add_chic d ρ P.f z.1
    have e2 := comparisonMainChi_add_chic d ρ P.f z.2
    have h5 := hE2 z
    have h6 : (0:ℝ) ≤ P.resid z.1 z.2 ^ 2 := sq_nonneg _
    have hprod : (0:ℝ) ≤ 1 - comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 := by nlinarith
    have hkey : (0:ℝ) ≤ (25 - P.resid z.1 z.2 ^ 2)
        * (1 - comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2) :=
      mul_nonneg (by linarith) hprod
    have hcor : (0:ℝ) ≤ (1 - comparisonMainChi d ρ P.f z.1) * (1 - comparisonMainChi d ρ P.f z.2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hsubint : Integrable (fun z : ℝ × ℝ => P.resid z.1 z.2 ^ 2
      - comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2) gμ :=
    P.integrable_resid_sq.sub hF1int
  have hmono := integral_mono hsubint hccint hpt
  have esub : ∫ z, (P.resid z.1 z.2 ^ 2 - comparisonMainChi d ρ P.f z.1
      * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2) ∂gμ
      = (∫ z, P.resid z.1 z.2 ^ 2 ∂gμ)
        - ∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * P.resid z.1 z.2 ^ 2 ∂gμ := integral_sub P.integrable_resid_sq hF1int
  have hrs : P.residSq = ∫ z, P.resid z.1 z.2 ^ 2 ∂gμ := rfl
  rw [esub, integral_const_mul] at hmono
  rw [hrs]
  linarith

/-- A uniform bound on `γ_h` for small `h`, from continuity of the family multiplier. -/
private theorem comparisonMain_exists_gam_bound (B : KKTFamily d) :
    ∃ Γ : ℝ, 0 ≤ Γ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → |B.gam h| ≤ Γ := by
  have hgc : ContinuousAt B.gam 0 := B.gam_continuousAt
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hgc (1 : ℝ) one_pos)
  refine ⟨|gammaStar d| + 1, by positivity, δ, hδ0, fun h hh => ?_⟩
  have hdist : dist h (0 : ℝ) < δ := by rwa [Real.dist_eq, sub_zero]
  have hlt := hδ hdist
  rw [Real.dist_eq, B.gam_zero] at hlt
  have h1 : |B.gam h| - |gammaStar d| ≤ |B.gam h - gammaStar d| := abs_sub_abs_le_abs_sub _ _
  linarith

/-- **The central part of the residual estimate**, the paper's Step 3 `(C)`.

For every `θ > 0` there are a window radius `ρ > 0` admissible for the window arithmetic, a
constant `C > 0` and a threshold `δ > 0` such that, for every `0 < h < δ` inside the family
window, every graphon `W` and every nonlinear Factor decomposition `W = f ⊗ f + E`,

`∬_{G_ρ²}{J_{p_h}(W) - J̃_{p_h}(f ⊗ f)} ≥ 2‖E‖²_{2,G_ρ²} - θ{A_ρ + ‖E‖²_{2,G_ρ²}} - Cε‖E‖₂`.

`comparisonMain_exists_residual_bound` is the corresponding whole-square bound, proved separately
with the tail bounded crudely; that is enough for `comparisonMain_exists_splitting_gap`, but
`eq:graphon-lagrangian-bound`
needs the two apart, because Step 4 supplies a *gain* on the tail where the crude treatment
only pays a loss.  The three ingredients are the same as there —
`lem:graphon-lagrangian-bound` (`comparisonMain_central_convexGap`, now applied under the
`χχ` weight so that the tail simply drops out), `lem:graphon-lagrangian-bound`
(`comparisonMain_abs_kkt_error_le`) and `lem:graphon-lagrangian-bound` — except that the corner
is taken in its **sharp** form `comparisonMain_abs_tailSq_le_L2`, `Cε‖E‖₂` rather than `Cε`; see
that lemma for why the crude form cannot reach the master estimate. -/
theorem comparisonMain_exists_central_bound (hd : 2 ≤ d) (B : KKTFamily d) {θ : ℝ}
    (hθ0 : 0 < θ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ rStar d / 4 ∧ ρ₀ ≤ (1 - rStar d) / 6 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, 0 < h → h < δ → |h| < B.h₀ →
      ∀ (W : Graphon) (P : FactorDecomp d W),
        2 * (∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
              * P.resid z.1 z.2 ^ 2 ∂gμ)
            - θ * ((∫ x in {x | P.f x ∈ centralWindow d ρ}, B.Qh h (P.f x) ^ 2 ∂unitμ)
                + ∫ z : ℝ × ℝ, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2 ∂gμ)
            - C * ((unitμ {x | P.f x ∉ centralWindow d ρ}).toReal * P.residL2)
          ≤ ∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
              * (Jp (B.p h) (W.toFun z.1 z.2) - B.JpTildeH h (P.f z.1 * P.f z.2)) ∂gμ := by
  obtain ⟨ρ₀, hρ₀0, hρ₀a, hρ₀b, hmulall⟩ :=
    comparisonMain_exists_multiplier_bound_forall hd B (θ := min θ 1) (lt_min hθ0 one_pos)
  obtain ⟨CJ, hCJ0, δJ, hδJ0, hJ⟩ := KKTFamily.exists_abs_Jp_le hd B
  obtain ⟨CT, hCT0, δT, hδT0, hT⟩ := KKTFamily.exists_abs_JpTildeH_le hd B
  obtain ⟨CD, hCD0, δD, hδD0, hD⟩ :=
    KKTFamily.exists_abs_Jp'_le hd B (comparisonMainA_pos hd) (comparisonMainB_lt_one hd)
  obtain ⟨Γ, hΓ0, δg, hδg0, hgam⟩ := comparisonMain_exists_gam_bound B
  refine ⟨ρ₀, hρ₀0, hρ₀a, hρ₀b, ?_⟩
  intro ρ hρ0 hρle
  have hρa : ρ ≤ rStar d / 4 := le_trans hρle hρ₀a
  have hρb : ρ ≤ (1 - rStar d) / 6 := le_trans hρle hρ₀b
  obtain ⟨δm, hδm0, hmul⟩ := hmulall ρ hρ0 hρle
  refine ⟨Γ * (2 ^ (d - 1) * 2 ^ (d - 1)) + 1, by positivity,
    min δm (min δJ (min δT (min δD δg))),
    lt_min hδm0 (lt_min hδJ0 (lt_min hδT0 (lt_min hδD0 hδg0))), ?_⟩
  intro h hh0 hhδ hhb W P
  have habs : |h| = h := abs_of_pos hh0
  have hhm : h < δm := lt_of_lt_of_le hhδ (min_le_left _ _)
  have hhJ : |h| < δJ := by
    rw [habs]; exact lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hhT : |h| < δT := by
    rw [habs]
    exact lt_of_lt_of_le hhδ
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hhD : |h| < δD := by
    rw [habs]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hhg : |h| < δg := by
    rw [habs]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hΓh := hgam h hhg
  -- measurability
  have hmchi1 : Measurable fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1 :=
    (measurable_comparisonMainChi d ρ P.meas_f).comp measurable_fst
  have hmchi2 : Measurable fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.2 :=
    (measurable_comparisonMainChi d ρ P.meas_f).comp measurable_snd
  have hmv : Measurable fun z : ℝ × ℝ => P.f z.1 * P.f z.2 :=
    (P.meas_f.comp measurable_fst).mul (P.meas_f.comp measurable_snd)
  have hWjoint : Measurable fun z : ℝ × ℝ => W.toFun z.1 z.2 := by
    have := P.measurable_resid.fun_add P.measurable_rankOne
    simpa only [FactorDecomp.resid, FactorDecomp.rankOne, sub_add_cancel] using this
  have hvmem : ∀ z : ℝ × ℝ, P.f z.1 ∈ centralWindow d ρ → P.f z.2 ∈ centralWindow d ρ →
      P.f z.1 * P.f z.2 ∈ Set.Icc (comparisonMainA d) (comparisonMainB d) := by
    intro z h1 h2
    exact comparisonMain_mul_mem hd hρ0 hρa hρb ((factorTail_mem_centralWindow_iff d ρ _).mp h1)
      ((factorTail_mem_centralWindow_iff d ρ _).mp h2)
  have hv04 : ∀ z : ℝ × ℝ, P.f z.1 * P.f z.2 ∈ Set.Icc (0 : ℝ) 4 := by
    intro z
    exact ⟨mul_nonneg (P.f_nonneg _) (P.f_nonneg _), by
      nlinarith [P.f_nonneg z.1, P.f_nonneg z.2, P.f_bdd z.1, P.f_bdd z.2]⟩
  have hΦbd : ∀ z : ℝ × ℝ, |Jp (B.p h) (W.toFun z.1 z.2)
      - B.JpTildeH h (P.f z.1 * P.f z.2)| ≤ CJ + CT := by
    intro z
    have h1 := hJ h hhJ _ (W.mem_Icc z.1 z.2)
    have h2 := hT h hhT _ (hv04 z)
    calc |Jp (B.p h) (W.toFun z.1 z.2) - B.JpTildeH h (P.f z.1 * P.f z.2)|
        ≤ |Jp (B.p h) (W.toFun z.1 z.2)| + |B.JpTildeH h (P.f z.1 * P.f z.2)| := abs_sub _ _
      _ ≤ CJ + CT := by linarith
  -- the three integrands
  have hF1int : Integrable (fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1
      * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2) gμ := by
    refine integrable_of_abs_le
      ((hmchi1.mul hmchi2).mul (P.measurable_resid.pow_const 2)) 25 fun z => ?_
    have h1 := comparisonMainChi_nonneg d ρ P.f z.1
    have h3 := comparisonMainChi_nonneg d ρ P.f z.2
    have h5 : P.resid z.1 z.2 ^ 2 ≤ 25 := by
      have := P.abs_resid_le z.1 z.2
      nlinarith [abs_nonneg (P.resid z.1 z.2), sq_abs (P.resid z.1 z.2)]
    have h7 : comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 ≤ 1 :=
      mul_le_one₀ (comparisonMainChi_le_one d ρ P.f z.1) h3 (comparisonMainChi_le_one d ρ P.f z.2)
    rw [abs_of_nonneg (by positivity)]
    calc comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2
        ≤ 1 * 25 := mul_le_mul h7 h5 (sq_nonneg _) zero_le_one
      _ = 25 := by norm_num
  have hF2bd : ∀ z : ℝ × ℝ, |comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
      * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)| ≤ CD * 5 := by
    intro z
    by_cases h1 : P.f z.1 ∈ centralWindow d ρ
    · by_cases h2 : P.f z.2 ∈ centralWindow d ρ
      · simp only [comparisonMainChi_of_mem h1, comparisonMainChi_of_mem h2, one_mul]
        rw [abs_mul]
        exact mul_le_mul (hD h hhD _ (hvmem z h1 h2)) (P.abs_resid_le _ _) (abs_nonneg _)
          hCD0.le
      · simp only [comparisonMainChi_of_not_mem h2, mul_zero, zero_mul, abs_zero]
        positivity
    · simp only [comparisonMainChi_of_not_mem h1, zero_mul, abs_zero]
      positivity
  have hF2int : Integrable (fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1
      * comparisonMainChi d ρ P.f z.2
      * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)) gμ :=
    integrable_of_abs_le
      ((hmchi1.mul hmchi2).mul (((comparisonMain_measurable_Jp' (B.p h)).comp hmv).mul
        P.measurable_resid)) (CD * 5) hF2bd
  have hp := B.p_mem h hhb
  have hΦint : Integrable (fun z : ℝ × ℝ => Jp (B.p h) (W.toFun z.1 z.2)
      - B.JpTildeH h (P.f z.1 * P.f z.2)) gμ :=
    (W.integrable_comp (measurable_Jp _) (continuousOn_Jp_Icc hp.1 hp.2)).sub
      (comparison_integrable_rankOne hd B h P.meas_f P.f_nonneg P.f_bdd)
  have hΦχint : Integrable (fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1
      * comparisonMainChi d ρ P.f z.2
      * (Jp (B.p h) (W.toFun z.1 z.2) - B.JpTildeH h (P.f z.1 * P.f z.2))) gμ := by
    refine hΦint.bdd_mul (c := 1) (hmchi1.mul hmchi2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have h1 := comparisonMainChi_nonneg d ρ P.f z.1
    have h3 := comparisonMainChi_nonneg d ρ P.f z.2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h3)]
    exact mul_le_one₀ (comparisonMainChi_le_one d ρ P.f z.1) h3 (comparisonMainChi_le_one d ρ P.f z.2)
  -- the pointwise convexity bound under the `χχ` weight: off the central square both sides
  -- vanish, so no crude tail estimate is needed
  have hψΦ : ∀ z : ℝ × ℝ,
      2 * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2)
        + comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
          * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)
      ≤ comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
          * (Jp (B.p h) (W.toFun z.1 z.2) - B.JpTildeH h (P.f z.1 * P.f z.2)) := by
    intro z
    by_cases h1 : P.f z.1 ∈ centralWindow d ρ
    · by_cases h2 : P.f z.2 ∈ centralWindow d ρ
      · simp only [comparisonMainChi_of_mem h1, comparisonMainChi_of_mem h2, one_mul]
        have := comparisonMain_central_convexGap hd B hhb P (hvmem z h1 h2)
        linarith
      · simp only [comparisonMainChi_of_not_mem h2, mul_zero, zero_mul]
        norm_num
    · simp only [comparisonMainChi_of_not_mem h1, zero_mul]
      norm_num
  have hψint : Integrable (fun z : ℝ × ℝ =>
      2 * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2)
        + comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
          * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)) gμ :=
    (hF1int.const_mul 2).add hF2int
  have hmono := integral_mono hψint hΦχint hψΦ
  have e2 : ∫ z, (2 * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * P.resid z.1 z.2 ^ 2)
      + comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)) ∂gμ
      = (∫ z, 2 * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
          * P.resid z.1 z.2 ^ 2) ∂gμ)
        + ∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2) ∂gμ :=
    integral_add (hF1int.const_mul 2) hF2int
  rw [e2, integral_const_mul] at hmono
  -- the KKT splitting of the second integral
  have hcorint : Integrable (fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1
      * comparisonMainChi d ρ P.f z.2
      * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) gμ := by
    refine integrable_of_abs_le
      ((hmchi1.mul hmchi2).mul (comparisonMain_measurable_gfun P))
      (2 ^ (d - 1) * 2 ^ (d - 1) * 5) fun z => ?_
    have h1 := comparisonMainChi_nonneg d ρ P.f z.1
    have h3 := comparisonMainChi_nonneg d ρ P.f z.2
    have h5 := comparisonMain_abs_gfun_le P z.1 z.2
    have h7 : comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 ≤ 1 :=
      mul_le_one₀ (comparisonMainChi_le_one d ρ P.f z.1) h3 (comparisonMainChi_le_one d ρ P.f z.2)
    rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h3]
    calc comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
          * |P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2|
        ≤ 1 * (2 ^ (d - 1) * 2 ^ (d - 1) * 5) := mul_le_mul h7 h5 (abs_nonneg _) zero_le_one
      _ = 2 ^ (d - 1) * 2 ^ (d - 1) * 5 := by ring
  have hCF0 : (0:ℝ) ≤ CD + Γ := by linarith
  have hCF : ∀ z ∈ Set.Icc (comparisonMainA d) (comparisonMainB d),
      |Fkkt d (B.p h) (B.gam h) z| ≤ CD + Γ := by
    intro z hz
    obtain ⟨hz0, hz1⟩ := comparisonMain_mem_Ioo hd hz
    have hJz := hD h hhD z hz
    have hpw : |z ^ (d - 1)| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hz0.le _)]
      exact pow_le_one₀ hz0.le hz1.le
    have hgz : |B.gam h * z ^ (d - 1)| ≤ Γ := by
      rw [abs_mul]
      calc |B.gam h| * |z ^ (d - 1)| ≤ Γ * 1 := mul_le_mul hΓh hpw (abs_nonneg _) hΓ0
        _ = Γ := by ring
    have he : Fkkt d (B.p h) (B.gam h) z = Jp' (B.p h) z - B.gam h * z ^ (d - 1) := rfl
    rw [he]
    calc |Jp' (B.p h) z - B.gam h * z ^ (d - 1)|
        ≤ |Jp' (B.p h) z| + |B.gam h * z ^ (d - 1)| := abs_sub _ _
      _ ≤ CD + Γ := by linarith
  have hkkt := comparisonMain_abs_kkt_error_le hd B (lt_min hθ0 one_pos) hhb hρ0 hρa hρb
    (hmul h hh0 hhm hhb) P hCF0 hCF
  have hcorner := comparisonMain_abs_tailSq_le_L2 P ρ
  have hsplit : ∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2) ∂gμ
      = (∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * (Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2) ∂gμ)
        + B.gam h * ∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ := by
    have hFint : Integrable (fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1
        * comparisonMainChi d ρ P.f z.2
        * (Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)) gμ := by
      refine integrable_of_abs_le
        ((hmchi1.mul hmchi2).mul
          (((comparisonMain_measurable_Fkkt d (B.p h) (B.gam h)).comp hmv).mul P.measurable_resid))
        ((CD + Γ) * 5) fun z => ?_
      by_cases h1 : P.f z.1 ∈ centralWindow d ρ
      · by_cases h2 : P.f z.2 ∈ centralWindow d ρ
        · simp only [comparisonMainChi_of_mem h1, comparisonMainChi_of_mem h2, one_mul]
          rw [abs_mul]
          exact mul_le_mul (hCF _ (hvmem z h1 h2)) (P.abs_resid_le _ _) (abs_nonneg _) hCF0
        · simp only [comparisonMainChi_of_not_mem h2, mul_zero, zero_mul, abs_zero]
          positivity
      · simp only [comparisonMainChi_of_not_mem h1, zero_mul, abs_zero]
        positivity
    have hpt : ∀ z : ℝ × ℝ, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)
        = comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * (Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)
          + B.gam h * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) := by
      intro z
      have he : Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2)
          = Jp' (B.p h) (P.f z.1 * P.f z.2)
            - B.gam h * (P.f z.1 * P.f z.2) ^ (d - 1) := rfl
      have hm : (P.f z.1 * P.f z.2) ^ (d - 1) = P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) :=
        mul_pow _ _ _
      rw [he, hm]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add hFint (hcorint.const_mul _), integral_const_mul]
  -- assemble
  have hA0 : (0:ℝ) ≤ ∫ x in {x | P.f x ∈ centralWindow d ρ},
      B.Qh h (P.f x) ^ 2 ∂unitμ :=
    setIntegral_nonneg (P.meas_f (measurableSet_centralWindow d ρ)) fun x _ => sq_nonneg _
  have hres0 : (0:ℝ) ≤ P.residSq := P.residSq_nonneg
  have hep0 : (0:ℝ) ≤ (unitμ {x | P.f x ∉ centralWindow d ρ}).toReal := ENNReal.toReal_nonneg
  have hL20 : (0:ℝ) ≤ P.residL2 := P.residL2_nonneg
  have hgamcor : |B.gam h * ∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
      * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ|
      ≤ Γ * (2 ^ (d - 1) * 2 ^ (d - 1)
          * ((unitμ {x | P.f x ∉ centralWindow d ρ}).toReal * P.residL2)) := by
    rw [abs_mul]
    exact mul_le_mul hΓh hcorner (abs_nonneg _) hΓ0
  have hlow1 := (abs_le.mp hkkt).1
  have hlow2 := (abs_le.mp hgamcor).1
  have hEcc0 : (0:ℝ) ≤ ∫ z : ℝ × ℝ, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2 ∂gμ :=
    integral_nonneg fun z => by
      have h1 := comparisonMainChi_nonneg d ρ P.f z.1
      have h2 := comparisonMainChi_nonneg d ρ P.f z.2
      positivity
  have h10 : (0:ℝ) ≤ (θ - min θ 1)
      * ((∫ x in {x | P.f x ∈ centralWindow d ρ}, B.Qh h (P.f x) ^ 2 ∂unitμ)
        + ∫ z : ℝ × ℝ, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2 ∂gμ) :=
    mul_nonneg (by linarith [min_le_left θ (1:ℝ)]) (by linarith)
  have h11 : (0:ℝ) ≤ (unitμ {x | P.f x ∉ centralWindow d ρ}).toReal * P.residL2 :=
    mul_nonneg hep0 hL20
  rw [hsplit] at hmono
  nlinarith [hmono, hlow1, hlow2, h10, h11]

/-! ## The three-way split of a symmetric double integral

`eq:graphon-lagrangian-bound` adds the central estimate of `comparisonMain_exists_central_bound` to
the Step-3 estimates of `SingularEndpoint/RowJensen.lean`.  The first is stated with the `χ`
weights of this file, the second with iterated set-restricted integrals matching the paper's
display, so the two have to be put in one language.  These lemmas do that, and record the
splitting `∬ = ∬_{G_ρ²} + 2∬_{G_ρ^c×G_ρ} + ∬_{(G_ρ^c)²}` that the assembly runs on. -/

/-- `∫χ(y)g(y) = ∫_{G_ρ}g`: the weight is the indicator of the central set. -/
theorem comparisonMain_integral_chi_mul (d : ℕ) (ρ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) (g : ℝ → ℝ) :
    ∫ y, comparisonMainChi d ρ f y * g y ∂unitμ
      = ∫ y in {y | f y ∈ centralWindow d ρ}, g y ∂unitμ := by
  have hmeas : MeasurableSet {y : ℝ | f y ∈ centralWindow d ρ} :=
    hf (measurableSet_centralWindow d ρ)
  rw [← integral_indicator hmeas]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show comparisonMainChi d ρ f y * g y = Set.indicator {y | f y ∈ centralWindow d ρ} g y
  by_cases hy : f y ∈ centralWindow d ρ
  · rw [comparisonMainChi_of_mem hy, one_mul,
      Set.indicator_of_mem (show y ∈ {y : ℝ | f y ∈ centralWindow d ρ} from hy)]
  · rw [comparisonMainChi_of_not_mem hy, zero_mul,
      Set.indicator_of_notMem (show y ∉ {y : ℝ | f y ∈ centralWindow d ρ} from hy)]

/-- `∫χᶜ(y)g(y) = ∫_{G_ρ^c}g`. -/
theorem comparisonMain_integral_chic_mul (d : ℕ) (ρ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) (g : ℝ → ℝ) :
    ∫ y, comparisonMainChic d ρ f y * g y ∂unitμ
      = ∫ y in {y | f y ∉ centralWindow d ρ}, g y ∂unitμ := by
  have hmeas : MeasurableSet {y : ℝ | f y ∉ centralWindow d ρ} :=
    (hf (measurableSet_centralWindow d ρ)).compl
  rw [← integral_indicator hmeas]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show comparisonMainChic d ρ f y * g y = Set.indicator {y | f y ∉ centralWindow d ρ} g y
  by_cases hy : f y ∈ centralWindow d ρ
  · rw [comparisonMainChic_of_mem hy, zero_mul,
      Set.indicator_of_notMem (show y ∉ {y : ℝ | f y ∉ centralWindow d ρ} from not_not.mpr hy)]
  · rw [comparisonMainChic_of_not_mem hy, one_mul,
      Set.indicator_of_mem (show y ∈ {y : ℝ | f y ∉ centralWindow d ρ} from hy)]

/-- **The mixed rectangle in the two languages**:
`∬χᶜ(x)χ(y)F = ∫_{G_ρ^c}∫_{G_ρ}F`. -/
theorem comparisonMain_integral_mixed_eq {F : ℝ → ℝ → ℝ}
    (hF : Measurable fun z : ℝ × ℝ => F z.1 z.2) {C : ℝ} (hb : ∀ x y, |F x y| ≤ C)
    (d : ℕ) (ρ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ z : ℝ × ℝ, comparisonMainChic d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2 ∂gμ)
      = ∫ x in {x | f x ∉ centralWindow d ρ},
          (∫ y in {y | f y ∈ centralWindow d ρ}, F x y ∂unitμ) ∂unitμ := by
  have hint : Integrable (fun z : ℝ × ℝ =>
      comparisonMainChic d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2) gμ := by
    refine integrable_of_abs_le
      ((((measurable_comparisonMainChic d ρ hf).comp measurable_fst).mul
        ((measurable_comparisonMainChi d ρ hf).comp measurable_snd)).mul hF) |C| fun z => ?_
    have h1 := comparisonMainChic_nonneg d ρ f z.1
    have h3 := comparisonMainChi_nonneg d ρ f z.2
    rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h3]
    calc comparisonMainChic d ρ f z.1 * comparisonMainChi d ρ f z.2 * |F z.1 z.2|
        ≤ 1 * 1 * |C| := by
          refine mul_le_mul (mul_le_mul (comparisonMainChic_le_one d ρ f z.1)
            (comparisonMainChi_le_one d ρ f z.2) h3 zero_le_one) ?_ (abs_nonneg _) (by norm_num)
          exact le_trans (hb z.1 z.2) (le_abs_self C)
      _ = |C| := by ring
  rw [show gμ = unitμ.prod unitμ from rfl, integral_prod _ hint]
  have hpt : ∀ x : ℝ, (∫ y, comparisonMainChic d ρ f x * comparisonMainChi d ρ f y * F x y ∂unitμ)
      = comparisonMainChic d ρ f x * ∫ y in {y | f y ∈ centralWindow d ρ}, F x y ∂unitμ := by
    intro x
    have he : ∀ y : ℝ, comparisonMainChic d ρ f x * comparisonMainChi d ρ f y * F x y
        = comparisonMainChic d ρ f x * (comparisonMainChi d ρ f y * F x y) := fun y => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_const_mul,
      comparisonMain_integral_chi_mul d ρ hf]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    comparisonMain_integral_chic_mul d ρ hf]

/-- **The rare–rare corner in the two languages**:
`∬χᶜ(x)χᶜ(y)F = ∫_{G_ρ^c}∫_{G_ρ^c}F`. -/
theorem comparisonMain_integral_tailSqRect_eq {F : ℝ → ℝ → ℝ}
    (hF : Measurable fun z : ℝ × ℝ => F z.1 z.2) {C : ℝ} (hb : ∀ x y, |F x y| ≤ C)
    (d : ℕ) (ρ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ z : ℝ × ℝ, comparisonMainChic d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2 ∂gμ)
      = ∫ x in {x | f x ∉ centralWindow d ρ},
          (∫ y in {y | f y ∉ centralWindow d ρ}, F x y ∂unitμ) ∂unitμ := by
  have hint : Integrable (fun z : ℝ × ℝ =>
      comparisonMainChic d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2) gμ := by
    refine integrable_of_abs_le
      ((((measurable_comparisonMainChic d ρ hf).comp measurable_fst).mul
        ((measurable_comparisonMainChic d ρ hf).comp measurable_snd)).mul hF) |C| fun z => ?_
    have h1 := comparisonMainChic_nonneg d ρ f z.1
    have h3 := comparisonMainChic_nonneg d ρ f z.2
    rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h3]
    calc comparisonMainChic d ρ f z.1 * comparisonMainChic d ρ f z.2 * |F z.1 z.2|
        ≤ 1 * 1 * |C| := by
          refine mul_le_mul (mul_le_mul (comparisonMainChic_le_one d ρ f z.1)
            (comparisonMainChic_le_one d ρ f z.2) h3 zero_le_one) ?_ (abs_nonneg _) (by norm_num)
          exact le_trans (hb z.1 z.2) (le_abs_self C)
      _ = |C| := by ring
  rw [show gμ = unitμ.prod unitμ from rfl, integral_prod _ hint]
  have hpt : ∀ x : ℝ, (∫ y, comparisonMainChic d ρ f x * comparisonMainChic d ρ f y * F x y ∂unitμ)
      = comparisonMainChic d ρ f x * ∫ y in {y | f y ∉ centralWindow d ρ}, F x y ∂unitμ := by
    intro x
    have he : ∀ y : ℝ, comparisonMainChic d ρ f x * comparisonMainChic d ρ f y * F x y
        = comparisonMainChic d ρ f x * (comparisonMainChic d ρ f y * F x y) := fun y => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_const_mul,
      comparisonMain_integral_chic_mul d ρ hf]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    comparisonMain_integral_chic_mul d ρ hf]

/-- The two mixed rectangles carry the same mass when `F` is symmetric. -/
private theorem comparisonMain_integral_mixed_swap {F : ℝ → ℝ → ℝ}
    (_hF : Measurable fun z : ℝ × ℝ => F z.1 z.2) (hsymm : ∀ x y, F x y = F y x)
    (d : ℕ) (ρ : ℝ) {f : ℝ → ℝ} (_hf : Measurable f) :
    (∫ z : ℝ × ℝ, comparisonMainChi d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2 ∂gμ)
      = ∫ z : ℝ × ℝ, comparisonMainChic d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2 ∂gμ := by
  have key : (fun z : ℝ × ℝ => comparisonMainChi d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2)
      = fun z : ℝ × ℝ =>
        (fun w : ℝ × ℝ => comparisonMainChic d ρ f w.1 * comparisonMainChi d ρ f w.2 * F w.1 w.2) z.swap := by
    funext z
    show comparisonMainChi d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2
      = comparisonMainChic d ρ f z.2 * comparisonMainChi d ρ f z.1 * F z.2 z.1
    rw [hsymm z.2 z.1]; ring
  rw [show gμ = unitμ.prod unitμ from rfl, key]
  exact integral_prod_swap (μ := unitμ) (ν := unitμ)
    (fun w : ℝ × ℝ => comparisonMainChic d ρ f w.1 * comparisonMainChi d ρ f w.2 * F w.1 w.2)

/-- **The three-way split** of a bounded symmetric double integral:

`∬F = ∬_{G_ρ²}F + 2∬_{G_ρ^c×G_ρ}F + ∬_{(G_ρ^c)²}F`.

`1 = (χ + χᶜ)(x)(χ + χᶜ)(y)` expands into four terms, and the two mixed ones agree by the
measure-preserving swap of `gμ` together with the symmetry of `F`. -/
theorem comparisonMain_split_three {F : ℝ → ℝ → ℝ}
    (hF : Measurable fun z : ℝ × ℝ => F z.1 z.2) {C : ℝ} (hb : ∀ x y, |F x y| ≤ C)
    (hsymm : ∀ x y, F x y = F y x) (d : ℕ) (ρ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ z : ℝ × ℝ, F z.1 z.2 ∂gμ)
      = (∫ z : ℝ × ℝ, comparisonMainChi d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2 ∂gμ)
        + 2 * (∫ z : ℝ × ℝ, comparisonMainChic d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2 ∂gμ)
        + ∫ z : ℝ × ℝ, comparisonMainChic d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2 ∂gμ := by
  have hchi := measurable_comparisonMainChi d ρ hf
  have hchic := measurable_comparisonMainChic d ρ hf
  have hbnd : ∀ (u v : ℝ → ℝ), (∀ x, 0 ≤ u x) → (∀ x, u x ≤ 1) → (∀ x, 0 ≤ v x) →
      (∀ x, v x ≤ 1) → ∀ z : ℝ × ℝ, |u z.1 * v z.2 * F z.1 z.2| ≤ |C| := by
    intro u v hu0 hu1 hv0 hv1 z
    rw [abs_mul, abs_mul, abs_of_nonneg (hu0 z.1), abs_of_nonneg (hv0 z.2)]
    calc u z.1 * v z.2 * |F z.1 z.2|
        ≤ 1 * 1 * |C| := by
          refine mul_le_mul (mul_le_mul (hu1 z.1) (hv1 z.2) (hv0 z.2) zero_le_one) ?_
            (abs_nonneg _) (by norm_num)
          exact le_trans (hb z.1 z.2) (le_abs_self C)
      _ = |C| := by ring
  have i11 : Integrable (fun z : ℝ × ℝ =>
      comparisonMainChi d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2) gμ :=
    integrable_of_abs_le
      ((((hchi.comp measurable_fst)).mul (hchi.comp measurable_snd)).mul hF) |C|
      (hbnd _ _ (comparisonMainChi_nonneg d ρ f) (comparisonMainChi_le_one d ρ f)
        (comparisonMainChi_nonneg d ρ f) (comparisonMainChi_le_one d ρ f))
  have ic1 : Integrable (fun z : ℝ × ℝ =>
      comparisonMainChic d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2) gμ :=
    integrable_of_abs_le
      ((((hchic.comp measurable_fst)).mul (hchi.comp measurable_snd)).mul hF) |C|
      (hbnd _ _ (comparisonMainChic_nonneg d ρ f) (comparisonMainChic_le_one d ρ f)
        (comparisonMainChi_nonneg d ρ f) (comparisonMainChi_le_one d ρ f))
  have i1c : Integrable (fun z : ℝ × ℝ =>
      comparisonMainChi d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2) gμ :=
    integrable_of_abs_le
      ((((hchi.comp measurable_fst)).mul (hchic.comp measurable_snd)).mul hF) |C|
      (hbnd _ _ (comparisonMainChi_nonneg d ρ f) (comparisonMainChi_le_one d ρ f)
        (comparisonMainChic_nonneg d ρ f) (comparisonMainChic_le_one d ρ f))
  have icc : Integrable (fun z : ℝ × ℝ =>
      comparisonMainChic d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2) gμ :=
    integrable_of_abs_le
      ((((hchic.comp measurable_fst)).mul (hchic.comp measurable_snd)).mul hF) |C|
      (hbnd _ _ (comparisonMainChic_nonneg d ρ f) (comparisonMainChic_le_one d ρ f)
        (comparisonMainChic_nonneg d ρ f) (comparisonMainChic_le_one d ρ f))
  have hpt : ∀ z : ℝ × ℝ, F z.1 z.2
      = comparisonMainChi d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2
        + comparisonMainChic d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2
        + comparisonMainChi d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2
        + comparisonMainChic d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2 := by
    intro z
    have e1 := comparisonMainChi_add_chic d ρ f z.1
    have e2 := comparisonMainChi_add_chic d ρ f z.2
    have h1 : comparisonMainChic d ρ f z.1 = 1 - comparisonMainChi d ρ f z.1 := by linarith
    have h2 : comparisonMainChic d ρ f z.2 = 1 - comparisonMainChi d ρ f z.2 := by linarith
    rw [h1, h2]; ring
  have e0 : ∫ z : ℝ × ℝ, F z.1 z.2 ∂gμ
      = ∫ z : ℝ × ℝ, (comparisonMainChi d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2
          + comparisonMainChic d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2
          + comparisonMainChi d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2
          + comparisonMainChic d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2) ∂gμ :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have e1 : ∫ z : ℝ × ℝ, (comparisonMainChi d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2
        + comparisonMainChic d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2
        + comparisonMainChi d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2
        + comparisonMainChic d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2) ∂gμ
      = (∫ z : ℝ × ℝ, (comparisonMainChi d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2
            + comparisonMainChic d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2
            + comparisonMainChi d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2) ∂gμ)
        + ∫ z : ℝ × ℝ, comparisonMainChic d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2 ∂gμ :=
    integral_add ((i11.add ic1).add i1c) icc
  have e2 : ∫ z : ℝ × ℝ, (comparisonMainChi d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2
        + comparisonMainChic d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2
        + comparisonMainChi d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2) ∂gμ
      = (∫ z : ℝ × ℝ, (comparisonMainChi d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2
            + comparisonMainChic d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2) ∂gμ)
        + ∫ z : ℝ × ℝ, comparisonMainChi d ρ f z.1 * comparisonMainChic d ρ f z.2 * F z.1 z.2 ∂gμ :=
    integral_add (i11.add ic1) i1c
  have e3 : ∫ z : ℝ × ℝ, (comparisonMainChi d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2
        + comparisonMainChic d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2) ∂gμ
      = (∫ z : ℝ × ℝ, comparisonMainChi d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2 ∂gμ)
        + ∫ z : ℝ × ℝ, comparisonMainChic d ρ f z.1 * comparisonMainChi d ρ f z.2 * F z.1 z.2 ∂gμ :=
    integral_add i11 ic1
  rw [e0, e1, e2, e3, comparisonMain_integral_mixed_swap hF hsymm d ρ hf]
  ring

/-! ## The three-way split of the two double integrals -/

/-- The residual entropy integrand is symmetric, `W` and `f ⊗ f` both being so. -/
private theorem comparisonMain_symm_entropy (B : KKTFamily d) (h : ℝ) {W : Graphon}
    (P : FactorDecomp d W) (x y : ℝ) :
    Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)
      = Jp (B.p h) (W.toFun y x) - B.JpTildeH h (P.f y * P.f x) := by
  rw [W.symm' x y, mul_comm (P.f x) (P.f y)]

/-- The squared residual is symmetric. -/
private theorem comparisonMain_symm_resid {W : Graphon} (P : FactorDecomp d W) (x y : ℝ) :
    P.resid x y ^ 2 = P.resid y x ^ 2 := by
  simp only [FactorDecomp.resid]
  rw [W.symm' x y, mul_comm (P.f x) (P.f y)]

/-- **The rare–rare corner of `‖E‖₂²` is `O(ε²)`**: `‖E‖²_{2,(G_ρ^c)²} ≤ 25ε²`, the paper's
`‖E‖_∞²ε²` with `‖E‖_∞ ≤ 5`. -/
theorem comparisonMain_tailSq_resid_le {W : Graphon} (P : FactorDecomp d W) (ρ : ℝ) :
    (∫ x in {x | P.f x ∉ centralWindow d ρ},
        (∫ y in {y | P.f y ∉ centralWindow d ρ}, P.resid x y ^ 2 ∂unitμ) ∂unitμ)
      ≤ 25 * (unitμ {x | P.f x ∉ centralWindow d ρ}).toReal ^ 2 := by
  have hEsq : Measurable fun z : ℝ × ℝ => P.resid z.1 z.2 ^ 2 :=
    P.measurable_resid.pow_const 2
  have hEsqb : ∀ x y, |P.resid x y ^ 2| ≤ 25 := by
    intro x y
    rw [abs_of_nonneg (sq_nonneg _)]
    have hb := abs_le.mp (P.abs_resid_le x y)
    nlinarith [hb.1, hb.2]
  rw [← comparisonMain_integral_tailSqRect_eq hEsq hEsqb d ρ P.meas_f]
  have hchic := measurable_comparisonMainChic d ρ P.meas_f
  have hcm : Measurable fun z : ℝ × ℝ =>
      comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 :=
    (hchic.comp measurable_fst).mul (hchic.comp measurable_snd)
  have hcnn : ∀ z : ℝ × ℝ, 0 ≤ comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 := fun z =>
    mul_nonneg (comparisonMainChic_nonneg d ρ P.f z.1) (comparisonMainChic_nonneg d ρ P.f z.2)
  have hcle : ∀ z : ℝ × ℝ, comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 ≤ 1 := fun z =>
    mul_le_one₀ (comparisonMainChic_le_one d ρ P.f z.1) (comparisonMainChic_nonneg d ρ P.f z.2)
      (comparisonMainChic_le_one d ρ P.f z.2)
  have hli : Integrable (fun z : ℝ × ℝ =>
      comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 * P.resid z.1 z.2 ^ 2) gμ := by
    refine integrable_of_abs_le (hcm.mul hEsq) 25 fun z => ?_
    rw [abs_mul, abs_of_nonneg (hcnn z)]
    calc comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 * |P.resid z.1 z.2 ^ 2|
        ≤ 1 * 25 := mul_le_mul (hcle z) (hEsqb z.1 z.2) (abs_nonneg _) zero_le_one
      _ = 25 := by norm_num
  have hri : Integrable (fun z : ℝ × ℝ =>
      25 * (comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2)) gμ :=
    integrable_of_abs_le (hcm.const_mul _) 25 fun z => by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 25), abs_of_nonneg (hcnn z)]
      nlinarith [hcle z, hcnn z]
  have hmono : (∫ z : ℝ × ℝ, comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2
        * P.resid z.1 z.2 ^ 2 ∂gμ)
      ≤ ∫ z : ℝ × ℝ, 25 * (comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2) ∂gμ := by
    refine integral_mono hli hri fun z => ?_
    have h1 : P.resid z.1 z.2 ^ 2 ≤ 25 := by
      have := hEsqb z.1 z.2
      rwa [abs_of_nonneg (sq_nonneg _)] at this
    calc comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 * P.resid z.1 z.2 ^ 2
        ≤ comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2 * 25 :=
          mul_le_mul_of_nonneg_left h1 (hcnn z)
      _ = 25 * (comparisonMainChic d ρ P.f z.1 * comparisonMainChic d ρ P.f z.2) := by ring
  rwa [integral_const_mul, comparisonMain_integral_chic_prod d ρ P.meas_f] at hmono

/-- **The residual norm split three ways**:
`‖E‖₂² = ‖E‖²_{2,G_ρ²} + 2‖E‖²_{2,G_ρ^c×G_ρ} + ‖E‖²_{2,(G_ρ^c)²}`. -/
theorem comparisonMain_residSq_split {W : Graphon} (P : FactorDecomp d W) (ρ : ℝ) :
    P.residSq
      = (∫ z : ℝ × ℝ, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * P.resid z.1 z.2 ^ 2 ∂gμ)
        + 2 * (∫ x in {x | P.f x ∉ centralWindow d ρ},
            (∫ y in {y | P.f y ∈ centralWindow d ρ}, P.resid x y ^ 2 ∂unitμ) ∂unitμ)
        + ∫ x in {x | P.f x ∉ centralWindow d ρ},
            (∫ y in {y | P.f y ∉ centralWindow d ρ}, P.resid x y ^ 2 ∂unitμ) ∂unitμ := by
  have hEsq : Measurable fun z : ℝ × ℝ => P.resid z.1 z.2 ^ 2 :=
    P.measurable_resid.pow_const 2
  have hEsqb : ∀ x y, |P.resid x y ^ 2| ≤ 25 := by
    intro x y
    rw [abs_of_nonneg (sq_nonneg _)]
    have hb := abs_le.mp (P.abs_resid_le x y)
    nlinarith [hb.1, hb.2]
  have hsplit := comparisonMain_split_three hEsq hEsqb (comparisonMain_symm_resid P) d ρ P.meas_f
  rw [comparisonMain_integral_mixed_eq hEsq hEsqb d ρ P.meas_f,
    comparisonMain_integral_tailSqRect_eq hEsq hEsqb d ρ P.meas_f] at hsplit
  exact hsplit

/-- **The residual entropy integral split three ways**, the paper's `(C) + (T)` with `(T)`
resolved into its two mixed rectangles and the rare–rare corner. -/
theorem comparisonMain_entropy_split (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ}
    (hhb : |h| < B.h₀) {W : Graphon} (P : FactorDecomp d W) (ρ : ℝ) :
    (∫ z, (Jp (B.p h) (W.toFun z.1 z.2) - B.JpTildeH h (P.f z.1 * P.f z.2)) ∂gμ)
      = (∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * (Jp (B.p h) (W.toFun z.1 z.2) - B.JpTildeH h (P.f z.1 * P.f z.2)) ∂gμ)
        + 2 * (∫ x in {x | P.f x ∉ centralWindow d ρ},
            (∫ y in {y | P.f y ∈ centralWindow d ρ},
              (Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)) ∂unitμ) ∂unitμ)
        + ∫ x in {x | P.f x ∉ centralWindow d ρ},
            (∫ y in {y | P.f y ∉ centralWindow d ρ},
              (Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)) ∂unitμ) ∂unitμ := by
  -- the split needs only *some* uniform bound on the integrand, at this one `h`; the
  -- neighbourhood-of-zero bounds `exists_abs_Jp_le` / `exists_abs_JpTildeH_le` would impose a
  -- spurious threshold, so take the compact-range sup instead
  have hWjoint : Measurable fun z : ℝ × ℝ => W.toFun z.1 z.2 := by
    have := P.measurable_resid.fun_add P.measurable_rankOne
    simpa only [FactorDecomp.resid, FactorDecomp.rankOne, sub_add_cancel] using this
  have hp := B.p_mem h hhb
  obtain ⟨CJ', hCJ'⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_Jp_Icc hp.1 hp.2)
  have hcontT : ContinuousOn (B.JpTildeH h) (Set.Icc (0 : ℝ) 4) :=
    ((continuousOn_JpTilde hd).add
        (continuousOn_const.mul continuous_id.continuousOn)).add continuousOn_const
  obtain ⟨CT', hCT'⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontT
  have hKj : Measurable fun z : ℝ × ℝ =>
      Jp (B.p h) (W.toFun z.1 z.2) - B.JpTildeH h (P.f z.1 * P.f z.2) :=
    ((measurable_Jp (B.p h)).comp hWjoint).sub
      ((comparison_measurable_JpTildeH B h).comp
        ((P.meas_f.comp measurable_fst).mul (P.meas_f.comp measurable_snd)))
  have hv04 : ∀ x y : ℝ, P.f x * P.f y ∈ Set.Icc (0 : ℝ) 4 := by
    intro x y
    exact ⟨mul_nonneg (P.f_nonneg _) (P.f_nonneg _), by
      nlinarith [P.f_nonneg x, P.f_nonneg y, P.f_bdd x, P.f_bdd y]⟩
  have hKjb : ∀ x y, |Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)|
      ≤ CJ' + CT' := by
    intro x y
    have h1 : |Jp (B.p h) (W.toFun x y)| ≤ CJ' := by
      simpa [Real.norm_eq_abs] using hCJ' _ (W.mem_Icc x y)
    have h2 : |B.JpTildeH h (P.f x * P.f y)| ≤ CT' := by
      simpa [Real.norm_eq_abs] using hCT' _ (hv04 x y)
    calc |Jp (B.p h) (W.toFun x y) - B.JpTildeH h (P.f x * P.f y)|
        ≤ |Jp (B.p h) (W.toFun x y)| + |B.JpTildeH h (P.f x * P.f y)| := abs_sub _ _
      _ ≤ CJ' + CT' := by linarith
  have hsplit := comparisonMain_split_three hKj hKjb (comparisonMain_symm_entropy B h P) d ρ P.meas_f
  rw [comparisonMain_integral_mixed_eq hKj hKjb d ρ P.meas_f,
    comparisonMain_integral_tailSqRect_eq hKj hKjb d ρ P.meas_f] at hsplit
  exact hsplit

/-- The central part of `‖E‖₂²` is at most the whole, the weight `χχ` being `≤ 1`. -/
theorem comparisonMain_central_resid_le (d : ℕ) (ρ : ℝ) {W : Graphon} (P : FactorDecomp d W) :
    (∫ z : ℝ × ℝ, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * P.resid z.1 z.2 ^ 2 ∂gμ) ≤ P.residSq := by
  have hmchi1 : Measurable fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1 :=
    (measurable_comparisonMainChi d ρ P.meas_f).comp measurable_fst
  have hmchi2 : Measurable fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.2 :=
    (measurable_comparisonMainChi d ρ P.meas_f).comp measurable_snd
  have hF1int : Integrable (fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1
      * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2) gμ := by
    refine integrable_of_abs_le
      ((hmchi1.mul hmchi2).mul (P.measurable_resid.pow_const 2)) 25 fun z => ?_
    have h1 := comparisonMainChi_nonneg d ρ P.f z.1
    have h3 := comparisonMainChi_nonneg d ρ P.f z.2
    have h5 : P.resid z.1 z.2 ^ 2 ≤ 25 := by
      have := P.abs_resid_le z.1 z.2
      nlinarith [abs_nonneg (P.resid z.1 z.2), sq_abs (P.resid z.1 z.2)]
    have h7 : comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 ≤ 1 :=
      mul_le_one₀ (comparisonMainChi_le_one d ρ P.f z.1) h3 (comparisonMainChi_le_one d ρ P.f z.2)
    rw [abs_of_nonneg (by positivity)]
    calc comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2
        ≤ 1 * 25 := mul_le_mul h7 h5 (sq_nonneg _) zero_le_one
      _ = 25 := by norm_num
  refine integral_mono hF1int P.integrable_resid_sq fun z => ?_
  have h1 := comparisonMainChi_nonneg d ρ P.f z.1
  have h3 := comparisonMainChi_nonneg d ρ P.f z.2
  have h7 : comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 ≤ 1 :=
    mul_le_one₀ (comparisonMainChi_le_one d ρ P.f z.1) h3 (comparisonMainChi_le_one d ρ P.f z.2)
  calc comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2
      ≤ 1 * P.resid z.1 z.2 ^ 2 :=
        mul_le_mul_of_nonneg_right h7 (sq_nonneg _)
    _ = P.resid z.1 z.2 ^ 2 := one_mul _

/-! ## The residual estimate -/

/-- **The residual half of `lem:graphon-lagrangian-bound`.**

For every `θ > 0` there are a window radius `ρ > 0`, a constant `C > 0` and a threshold
`δ > 0` such that, for every `0 < h < δ` inside the family window, every graphon `W` and
every nonlinear Factor decomposition `W = f ⊗ f + E`,

`∫∫{J_{p_h}(W) - J̃_{p_h}(f ⊗ f)} ≥ ‖E‖₂² - θA_ρ - Cν(T_ρ)`,

with `A_ρ = ∫_{G_ρ}Q_h(f)²` and `ν(T_ρ) = |G_ρᶜ|`.

This is Step 3 of the proof of `lem:graphon-lagrangian-bound` — the central convexity
bound, the KKT error and the Factor corner — together with a *crude* treatment of the
tail part `(T)`: the rows outside the window are only bounded below by `-Cν(T_ρ)`, using that
the true and continued entropies are bounded on their compact ranges.  That loss is paid out of
the rank-one tail gain `b_ρν(T_ρ)`, which is why `eq:graphon-lagrangian-bound` does not follow
from this statement alone; the sharp form of the loss is Step 3
(`SingularEndpoint/RowJensen.lean`) and the join is Step 4, `exists_comparison_master`
(`SingularEndpoint/GraphonComparisonMaster.lean`).

The coefficient of `‖E‖₂²` is `1` rather than the paper's `M_ρ^{-1}` because the pointwise
modulus `2` of `lem:graphon-lagrangian-bound` is more than enough to absorb the
`θ`-small KKT error; `θ` is at the caller's disposal, so the `A_ρ` loss can be made smaller
than the `a_ρ/2 = d³/48` gain of the refined form of `eq:auxiliary-lagrangian-bound`. -/
theorem comparisonMain_exists_residual_bound (hd : 2 ≤ d) (B : KKTFamily d) {θ : ℝ}
    (hθ0 : 0 < θ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, 0 < h → h < δ → |h| < B.h₀ →
      ∀ (W : Graphon) (P : FactorDecomp d W),
        P.residSq
            - θ * (∫ x in {x | P.f x ∈ centralWindow d ρ}, B.Qh h (P.f x) ^ 2 ∂unitμ)
            - C * (unitμ {x | P.f x ∉ centralWindow d ρ}).toReal
          ≤ ∫ z, (Jp (B.p h) (W.toFun z.1 z.2) - B.JpTildeH h (P.f z.1 * P.f z.2)) ∂gμ := by
  obtain ⟨ρ, hρ0, hρa, hρb, δm, hδm0, hmul⟩ :=
    comparisonMain_exists_multiplier_bound hd B (θ := min θ 1) (lt_min hθ0 one_pos)
  obtain ⟨CJ, hCJ0, δJ, hδJ0, hJ⟩ := KKTFamily.exists_abs_Jp_le hd B
  obtain ⟨CT, hCT0, δT, hδT0, hT⟩ := KKTFamily.exists_abs_JpTildeH_le hd B
  obtain ⟨CD, hCD0, δD, hδD0, hD⟩ :=
    KKTFamily.exists_abs_Jp'_le hd B (comparisonMainA_pos hd) (comparisonMainB_lt_one hd)
  obtain ⟨Γ, hΓ0, δg, hδg0, hgam⟩ := comparisonMain_exists_gam_bound B
  refine ⟨ρ, hρ0, 100 + Γ * (2 ^ (d - 1) * 2 ^ (d - 1) * 5) + 2 * (CJ + CT), by positivity,
    min δm (min δJ (min δT (min δD δg))),
    lt_min hδm0 (lt_min hδJ0 (lt_min hδT0 (lt_min hδD0 hδg0))), ?_⟩
  intro h hh0 hhδ hhb W P
  have habs : |h| = h := abs_of_pos hh0
  have hhm : h < δm := lt_of_lt_of_le hhδ (min_le_left _ _)
  have hhJ : |h| < δJ := by
    rw [habs]; exact lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hhT : |h| < δT := by
    rw [habs]
    exact lt_of_lt_of_le hhδ
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hhD : |h| < δD := by
    rw [habs]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hhg : |h| < δg := by
    rw [habs]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hΓh := hgam h hhg
  -- measurability
  have hmchi1 : Measurable fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1 :=
    (measurable_comparisonMainChi d ρ P.meas_f).comp measurable_fst
  have hmchi2 : Measurable fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.2 :=
    (measurable_comparisonMainChi d ρ P.meas_f).comp measurable_snd
  have hmchic1 : Measurable fun z : ℝ × ℝ => comparisonMainChic d ρ P.f z.1 :=
    (measurable_comparisonMainChic d ρ P.meas_f).comp measurable_fst
  have hmchic2 : Measurable fun z : ℝ × ℝ => comparisonMainChic d ρ P.f z.2 :=
    (measurable_comparisonMainChic d ρ P.meas_f).comp measurable_snd
  have hmv : Measurable fun z : ℝ × ℝ => P.f z.1 * P.f z.2 :=
    (P.meas_f.comp measurable_fst).mul (P.meas_f.comp measurable_snd)
  -- the window membership of the rank-one value on the central set
  have hvmem : ∀ z : ℝ × ℝ, P.f z.1 ∈ centralWindow d ρ → P.f z.2 ∈ centralWindow d ρ →
      P.f z.1 * P.f z.2 ∈ Set.Icc (comparisonMainA d) (comparisonMainB d) := by
    intro z h1 h2
    exact comparisonMain_mul_mem hd hρ0 hρa hρb ((factorTail_mem_centralWindow_iff d ρ _).mp h1)
      ((factorTail_mem_centralWindow_iff d ρ _).mp h2)
  have hv04 : ∀ z : ℝ × ℝ, P.f z.1 * P.f z.2 ∈ Set.Icc (0 : ℝ) 4 := by
    intro z
    exact ⟨mul_nonneg (P.f_nonneg _) (P.f_nonneg _), by
      nlinarith [P.f_nonneg z.1, P.f_nonneg z.2, P.f_bdd z.1, P.f_bdd z.2]⟩
  -- the two entropies are bounded
  have hΦbd : ∀ z : ℝ × ℝ, |Jp (B.p h) (W.toFun z.1 z.2)
      - B.JpTildeH h (P.f z.1 * P.f z.2)| ≤ CJ + CT := by
    intro z
    have h1 := hJ h hhJ _ (W.mem_Icc z.1 z.2)
    have h2 := hT h hhT _ (hv04 z)
    calc |Jp (B.p h) (W.toFun z.1 z.2) - B.JpTildeH h (P.f z.1 * P.f z.2)|
        ≤ |Jp (B.p h) (W.toFun z.1 z.2)| + |B.JpTildeH h (P.f z.1 * P.f z.2)| := abs_sub _ _
      _ ≤ CJ + CT := by linarith
  have hp := B.p_mem h hhb
  have hΦint : Integrable (fun z : ℝ × ℝ => Jp (B.p h) (W.toFun z.1 z.2)
      - B.JpTildeH h (P.f z.1 * P.f z.2)) gμ :=
    (W.integrable_comp (measurable_Jp _) (continuousOn_Jp_Icc hp.1 hp.2)).sub
      (comparison_integrable_rankOne hd B h P.meas_f P.f_nonneg P.f_bdd)
  -- the three integrands of the lower bound
  have hF1int : Integrable (fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1
      * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2) gμ := by
    refine integrable_of_abs_le
      ((hmchi1.mul hmchi2).mul (P.measurable_resid.pow_const 2)) 25 fun z => ?_
    have h1 := comparisonMainChi_nonneg d ρ P.f z.1
    have h2 := comparisonMainChi_le_one d ρ P.f z.1
    have h3 := comparisonMainChi_nonneg d ρ P.f z.2
    have h4 := comparisonMainChi_le_one d ρ P.f z.2
    have h5 : P.resid z.1 z.2 ^ 2 ≤ 25 := by
      have := P.abs_resid_le z.1 z.2
      nlinarith [abs_nonneg (P.resid z.1 z.2), sq_abs (P.resid z.1 z.2)]
    have h6 : (0:ℝ) ≤ P.resid z.1 z.2 ^ 2 := sq_nonneg _
    have h7 : comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 ≤ 1 :=
      mul_le_one₀ h2 h3 h4
    have h8 : (0:ℝ) ≤ comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 := mul_nonneg h1 h3
    rw [abs_of_nonneg (by positivity)]
    calc comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2
        ≤ 1 * 25 := mul_le_mul h7 h5 h6 zero_le_one
      _ = 25 := by norm_num
  have hF2bd : ∀ z : ℝ × ℝ, |comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
      * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)| ≤ CD * 5 := by
    intro z
    by_cases h1 : P.f z.1 ∈ centralWindow d ρ
    · by_cases h2 : P.f z.2 ∈ centralWindow d ρ
      · simp only [comparisonMainChi_of_mem h1, comparisonMainChi_of_mem h2, one_mul]
        rw [abs_mul]
        exact mul_le_mul (hD h hhD _ (hvmem z h1 h2)) (P.abs_resid_le _ _) (abs_nonneg _)
          hCD0.le
      · simp only [comparisonMainChi_of_not_mem h2, mul_zero, zero_mul, abs_zero]
        positivity
    · simp only [comparisonMainChi_of_not_mem h1, zero_mul, abs_zero]
      positivity
  have hF2int : Integrable (fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1
      * comparisonMainChi d ρ P.f z.2
      * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)) gμ :=
    integrable_of_abs_le
      ((hmchi1.mul hmchi2).mul (((comparisonMain_measurable_Jp' (B.p h)).comp hmv).mul
        P.measurable_resid)) (CD * 5) hF2bd
  have hF3int : Integrable (fun z : ℝ × ℝ =>
      (CJ + CT) * (comparisonMainChic d ρ P.f z.1 + comparisonMainChic d ρ P.f z.2)) gμ := by
    refine integrable_of_abs_le ((hmchic1.add hmchic2).const_mul _)
      ((CJ + CT) * 2) fun z => ?_
    have h1 := comparisonMainChic_nonneg d ρ P.f z.1
    have h2 := comparisonMainChic_le_one d ρ P.f z.1
    have h3 := comparisonMainChic_nonneg d ρ P.f z.2
    have h4 := comparisonMainChic_le_one d ρ P.f z.2
    have h5 : (0:ℝ) ≤ CJ + CT := by linarith
    have h6 : comparisonMainChic d ρ P.f z.1 + comparisonMainChic d ρ P.f z.2 ≤ 2 := by linarith
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left h6 h5
  -- the pointwise lower bound `ψ ≤ Φ`
  have hψΦ : ∀ z : ℝ × ℝ,
      2 * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2)
        + comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
          * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)
        - (CJ + CT) * (comparisonMainChic d ρ P.f z.1 + comparisonMainChic d ρ P.f z.2)
      ≤ Jp (B.p h) (W.toFun z.1 z.2) - B.JpTildeH h (P.f z.1 * P.f z.2) := by
    intro z
    by_cases h1 : P.f z.1 ∈ centralWindow d ρ
    · by_cases h2 : P.f z.2 ∈ centralWindow d ρ
      · simp only [comparisonMainChi_of_mem h1, comparisonMainChi_of_mem h2, comparisonMainChic_of_mem h1,
          comparisonMainChic_of_mem h2, one_mul, add_zero, mul_zero, sub_zero]
        have := comparisonMain_central_convexGap hd B hhb P (hvmem z h1 h2)
        linarith
      · have hc : comparisonMainChi d ρ P.f z.2 = 0 := comparisonMainChi_of_not_mem h2
        have hcc : comparisonMainChic d ρ P.f z.2 = 1 := comparisonMainChic_of_not_mem h2
        have hcc1 := comparisonMainChic_nonneg d ρ P.f z.1
        have hlow := (abs_le.mp (hΦbd z)).1
        rw [hc, hcc]
        have hCsum : (0:ℝ) ≤ CJ + CT := by linarith
        have hz : (0:ℝ) ≤ (CJ + CT) * comparisonMainChic d ρ P.f z.1 := mul_nonneg hCsum hcc1
        linarith
    · have hc : comparisonMainChi d ρ P.f z.1 = 0 := comparisonMainChi_of_not_mem h1
      have hcc : comparisonMainChic d ρ P.f z.1 = 1 := comparisonMainChic_of_not_mem h1
      have hcc2 := comparisonMainChic_nonneg d ρ P.f z.2
      have hlow := (abs_le.mp (hΦbd z)).1
      rw [hc, hcc]
      have hCsum : (0:ℝ) ≤ CJ + CT := by linarith
      have hz : (0:ℝ) ≤ (CJ + CT) * comparisonMainChic d ρ P.f z.2 := mul_nonneg hCsum hcc2
      linarith
  have hψint : Integrable (fun z : ℝ × ℝ =>
      2 * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2)
        + comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
          * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)
        - (CJ + CT) * (comparisonMainChic d ρ P.f z.1 + comparisonMainChic d ρ P.f z.2)) gμ :=
    ((hF1int.const_mul 2).add hF2int).sub hF3int
  have hmono := integral_mono hψint hΦint hψΦ
  -- linearity of `∫ψ`
  have e1 : ∫ z, (2 * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * P.resid z.1 z.2 ^ 2)
      + comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)
      - (CJ + CT) * (comparisonMainChic d ρ P.f z.1 + comparisonMainChic d ρ P.f z.2)) ∂gμ
      = (∫ z, (2 * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * P.resid z.1 z.2 ^ 2)
          + comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)) ∂gμ)
        - ∫ z, (CJ + CT) * (comparisonMainChic d ρ P.f z.1
            + comparisonMainChic d ρ P.f z.2) ∂gμ :=
    integral_sub ((hF1int.const_mul 2).add hF2int) hF3int
  have e2 : ∫ z, (2 * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * P.resid z.1 z.2 ^ 2)
      + comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)) ∂gμ
      = (∫ z, 2 * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
          * P.resid z.1 z.2 ^ 2) ∂gμ)
        + ∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2) ∂gμ :=
    integral_add (hF1int.const_mul 2) hF2int
  rw [e1, e2, integral_const_mul, integral_const_mul,
    comparisonMain_integral_chic_sum d ρ P.meas_f] at hmono
  -- the KKT splitting of the second integral
  have hcorint : Integrable (fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1
      * comparisonMainChi d ρ P.f z.2
      * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) gμ := by
    refine integrable_of_abs_le
      ((hmchi1.mul hmchi2).mul (comparisonMain_measurable_gfun P))
      (2 ^ (d - 1) * 2 ^ (d - 1) * 5) fun z => ?_
    have h1 := comparisonMainChi_nonneg d ρ P.f z.1
    have h2 := comparisonMainChi_le_one d ρ P.f z.1
    have h3 := comparisonMainChi_nonneg d ρ P.f z.2
    have h4 := comparisonMainChi_le_one d ρ P.f z.2
    have h5 := comparisonMain_abs_gfun_le P z.1 z.2
    have h6 : (0:ℝ) ≤ |P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2| :=
      abs_nonneg _
    have h7 : comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 ≤ 1 :=
      mul_le_one₀ h2 h3 h4
    rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h3]
    calc comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
          * |P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2|
        ≤ 1 * (2 ^ (d - 1) * 2 ^ (d - 1) * 5) := mul_le_mul h7 h5 h6 zero_le_one
      _ = 2 ^ (d - 1) * 2 ^ (d - 1) * 5 := by ring
  have hCF0 : (0:ℝ) ≤ CD + Γ := by linarith
  have hCF : ∀ z ∈ Set.Icc (comparisonMainA d) (comparisonMainB d),
      |Fkkt d (B.p h) (B.gam h) z| ≤ CD + Γ := by
    intro z hz
    obtain ⟨hz0, hz1⟩ := comparisonMain_mem_Ioo hd hz
    have hJz := hD h hhD z hz
    have hpw : |z ^ (d - 1)| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hz0.le _)]
      exact pow_le_one₀ hz0.le hz1.le
    have hgz : |B.gam h * z ^ (d - 1)| ≤ Γ := by
      rw [abs_mul]
      calc |B.gam h| * |z ^ (d - 1)| ≤ Γ * 1 :=
            mul_le_mul hΓh hpw (abs_nonneg _) hΓ0
        _ = Γ := by ring
    have he : Fkkt d (B.p h) (B.gam h) z = Jp' (B.p h) z - B.gam h * z ^ (d - 1) := rfl
    rw [he]
    calc |Jp' (B.p h) z - B.gam h * z ^ (d - 1)|
        ≤ |Jp' (B.p h) z| + |B.gam h * z ^ (d - 1)| := abs_sub _ _
      _ ≤ CD + Γ := by linarith
  have hkkt := comparisonMain_abs_kkt_error_le hd B (lt_min hθ0 one_pos) hhb hρ0 hρa hρb
    (hmul h hh0 hhm hhb) P hCF0 hCF
  have hcorner := comparisonMain_abs_tailSq_le P ρ
  have hsplit : ∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2) ∂gμ
      = (∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * (Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2) ∂gμ)
        + B.gam h * ∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ := by
    have hFint : Integrable (fun z : ℝ × ℝ => comparisonMainChi d ρ P.f z.1
        * comparisonMainChi d ρ P.f z.2
        * (Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)) gμ := by
      refine integrable_of_abs_le
        ((hmchi1.mul hmchi2).mul
          (((comparisonMain_measurable_Fkkt d (B.p h) (B.gam h)).comp hmv).mul P.measurable_resid))
        ((CD + Γ) * 5) fun z => ?_
      by_cases h1 : P.f z.1 ∈ centralWindow d ρ
      · by_cases h2 : P.f z.2 ∈ centralWindow d ρ
        · simp only [comparisonMainChi_of_mem h1, comparisonMainChi_of_mem h2, one_mul]
          rw [abs_mul]
          exact mul_le_mul (hCF _ (hvmem z h1 h2)) (P.abs_resid_le _ _) (abs_nonneg _) hCF0
        · simp only [comparisonMainChi_of_not_mem h2, mul_zero, zero_mul, abs_zero]
          positivity
      · simp only [comparisonMainChi_of_not_mem h1, zero_mul, abs_zero]
        positivity
    have hpt : ∀ z : ℝ × ℝ, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
        * (Jp' (B.p h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)
        = comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * (Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2) * P.resid z.1 z.2)
          + B.gam h * (comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
            * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2)) := by
      intro z
      have he : Fkkt d (B.p h) (B.gam h) (P.f z.1 * P.f z.2)
          = Jp' (B.p h) (P.f z.1 * P.f z.2)
            - B.gam h * (P.f z.1 * P.f z.2) ^ (d - 1) := rfl
      have hm : (P.f z.1 * P.f z.2) ^ (d - 1) = P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) :=
        mul_pow _ _ _
      rw [he, hm]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add hFint (hcorint.const_mul _), integral_const_mul]
  -- assemble
  have hcentral := comparisonMain_central_resid_ge d ρ P
  rw [comparisonMain_integral_chic_sum d ρ P.meas_f] at hcentral
  have hres0 : (0:ℝ) ≤ P.residSq := P.residSq_nonneg
  have hA0 : (0:ℝ) ≤ ∫ x in {x | P.f x ∈ centralWindow d ρ},
      B.Qh h (P.f x) ^ 2 ∂unitμ :=
    setIntegral_nonneg (P.meas_f (measurableSet_centralWindow d ρ)) fun x _ => sq_nonneg _
  have hε0 : (0:ℝ) ≤ (unitμ {x | P.f x ∉ centralWindow d ρ}).toReal := ENNReal.toReal_nonneg
  have hK0 : (0:ℝ) ≤ 2 ^ (d - 1) * 2 ^ (d - 1) * 5 := by positivity
  have hgamcor : |B.gam h * ∫ z, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2
      * (P.f z.1 ^ (d - 1) * P.f z.2 ^ (d - 1) * P.resid z.1 z.2) ∂gμ|
      ≤ Γ * ((2 ^ (d - 1) * 2 ^ (d - 1) * 5)
          * (unitμ {x | P.f x ∉ centralWindow d ρ}).toReal) := by
    rw [abs_mul]
    exact mul_le_mul hΓh hcorner (abs_nonneg _) hΓ0
  have hccle := comparisonMain_central_resid_le d ρ P
  have hlow1 := (abs_le.mp hkkt).1
  have hlow2 := (abs_le.mp hgamcor).1
  have hminθ0 : (0:ℝ) ≤ min θ 1 := le_min hθ0.le zero_le_one
  have hkktrelax : (0:ℝ) ≤ min θ 1 * (P.residSq
      - ∫ z : ℝ × ℝ, comparisonMainChi d ρ P.f z.1 * comparisonMainChi d ρ P.f z.2 * P.resid z.1 z.2 ^ 2 ∂gμ) := mul_nonneg hminθ0 (by linarith)
  have h9 : (0:ℝ) ≤ (1 - min θ 1) * P.residSq :=
    mul_nonneg (by linarith [min_le_right θ (1:ℝ)]) hres0
  have h10 : (0:ℝ) ≤ (θ - min θ 1)
      * (∫ x in {x | P.f x ∈ centralWindow d ρ}, B.Qh h (P.f x) ^ 2 ∂unitμ) :=
    mul_nonneg (by linarith [min_le_left θ (1:ℝ)]) hA0
  rw [hsplit] at hmono
  linarith [hmono, hcentral, hlow1, hlow2, h9, h10, hkktrelax]

/-- **The exact splitting of `lem:graphon-lagrangian-bound` with its residual half estimated.**

`comparison_splitting` (`SingularEndpoint/GraphonComparison.lean`) is the identity

`I_{p_h}(W) - I_{p_h}(W_h) = {𝒥_h(ν) - 𝒥_h(ν_h)} + ∫∫{J_{p_h}(W) - J̃_{p_h}(f ⊗ f)}`

for `ν` the law of `f`.  Feeding `comparisonMain_exists_residual_bound` into its second summand
gives the display below: the cost gap dominates the *law* gap plus `‖E‖₂²`, up to the
two losses `θA_ρ` and `Cν(T_ρ)`.

This is the point at which the law layer and the Factor layer meet.  It is **not**
`eq:graphon-lagrangian-bound`: to reach that one must estimate the law gap by
the refined gap bound and then absorb `Cν(T_ρ)` into the rank-one tail gain `b_ρν(T_ρ)`, the
sharp form of the loss being Step 3 (`SingularEndpoint/RowJensen.lean`).  A second, purely bookkeeping
obstacle is that `KKTFamily.exists_distributionGap_refined_window` manufactures its own window
radius while `comparisonMain_exists_residual_bound` manufactures another; the common-radius form
`KKTFamily.exists_distributionGap_refined_window_forall` (`SingularEndpoint/DistributionFinal.lean`, from
`exists_distribution_window_forall`) is what removes it.  Both are carried out in Step 5,
`exists_comparison_master` (`SingularEndpoint/GraphonComparisonMaster.lean`). -/
theorem comparisonMain_exists_splitting_gap (hd : 2 ≤ d) (B : KKTFamily d) {θ : ℝ}
    (hθ0 : 0 < θ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ℝ) (hb : |h| < B.h₀), 0 < h → h < δ →
      ∀ (W : Graphon) (P : FactorDecomp d W),
        (B.distributionJ h (comparisonDistribution P.f) - B.distributionJ h (B.distributionMeasure h))
            + P.residSq
            - θ * (∫ x in {x | P.f x ∈ centralWindow d ρ}, B.Qh h (P.f x) ^ 2 ∂unitμ)
            - C * (unitμ {x | P.f x ∉ centralWindow d ρ}).toReal
          ≤ W.Ip (B.p h) - (B.graphon hb).Ip (B.p h) := by
  obtain ⟨ρ, hρ0, C, hC0, δ, hδ0, hres⟩ := comparisonMain_exists_residual_bound hd B hθ0
  refine ⟨ρ, hρ0, C, hC0, δ, hδ0, ?_⟩
  intro h hb hh0 hhδ W P
  have hsplit := comparison_splitting hd B hb W P.meas_f P.f_nonneg P.f_bdd
  have hr := hres h hh0 hhδ hb W P
  linarith

end SingularEndpoint

end UpperTailOptimizers
