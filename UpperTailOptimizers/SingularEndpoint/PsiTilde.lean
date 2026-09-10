import UpperTailOptimizers.SingularEndpoint.JpTilde
import UpperTailOptimizers.SingularEndpoint.FirstVariationBound
import UpperTailOptimizers.SingularEndpoint.FamilyContinuity

/-!
# The dual potential through the continued entropy (Section 7, `paper/singular_endpoint.tex`)

`lem:first-variation-bound` states its two lower
bounds on the whole law interval `[0,2]`.  Its `Ψ_h` is built from the **continued**
entropy of `eq:entropy-continuation` — "We suppress the tilde below" — whereas `KKTFamily.Psi` (`SingularEndpoint/FirstVariation.lean`)
is built from the plain `J_{p_h}`, which has a meaning only while `x s_h` and `x t_h` stay in
`[0,1]`.  Since `u_* = √((d-1)/d)`, that caps `x` at `1/u_* ≈ 1.41` when `d = 2`, well short
of `2`.  This file introduces the tilde version and proves on all of `[0,2]` the two clauses
that `SingularEndpoint/FirstVariationBound.lean` had to leave out: the companion bound `Ψ_h ≥ b_ρ` off the
coalescence neighbourhood `𝓝_ρ`, and the uniform bound on `sup_{[0,2]}|Ψ_h|`.  The quartic
bound `Ψ_h ≥ (d³/24) Q_h²` on `𝓝_ρ` is `KKTFamily.exists_firstVariation_lower`
(`SingularEndpoint/FirstVariationBound.lean`), and `PsiT_eq_Psi` identifies the two potentials wherever both are
defined, so the two halves are bounds on one and the same function.

## The route

`J̃_{p_h}` is the displaced continuation of the paper's display after
`eq:entropy-continuation`, `J̃_{p_h}(u) = J̃_{p_*}(u) + Λ_h u + C_h`; the displacement is
the *exact* identity `eq:entropy-parameter-shift`, so `J̃_{p_h}` agrees with `J_{p_h}` on `[0,1]`
(`JpTildeH_eq_Jp`) and `PsiT` agrees with `Psi` wherever the latter is meaningful
(`PsiT_eq_Psi`).  At `h = 0` the wells coalesce and `PsiT_zero` is the tilde form of
`eq:endpoint-first-variation`, `Ψ_0(x) = 2Γ̃_d(u_* x)`, which is positive off `x = u_*` by
`GamTilde_pos_of_ne`.  A compactness argument on `T_ρ = {x ∈ [0,2] : |x - u_*| ≥ ρ}` turns
that into a positive lower bound at `h = 0`, and the transfer to small `h > 0` is the
uniform convergence `Ψ_h → Ψ_0` on `[0,2]` that the paper's proof also invokes.

That uniform convergence is the only estimate here that has to be uniform in `x`.  It is
**not** obtained from a modulus of continuity: `J̃_{p_*}` is continuous on the compact
`[0,4]`, hence uniformly continuous there (Heine–Cantor,
`IsCompact.uniformContinuousOn_of_continuous`), and `|x s_h - x u_*| ≤ 2|s_h - u_*| → 0`
uniformly over `x ∈ [0,2]`.  Everything else in `Ψ_h - Ψ_0` is a family scalar times a
bounded power of `x`, collected in `psiDrift`.

## Contents

* `KKTFamily.JpTildeH` — the displaced continued entropy `J̃_{p_h}`, with
  `JpTildeH_eq_Jp` and `JpTildeH_zero`;
* `KKTFamily.PsiT` — the dual potential `eq:first-variation` built from `J̃`,
  with `PsiT_eq_Psi` and `PsiT_zero` `eq:endpoint-first-variation`;
* `KKTFamily.exists_firstVariation_upperGap` — the companion bound `Ψ_h ≥ b_ρ` on
  `[0,2] \ 𝓝_ρ` of `lem:first-variation-bound`;
* `KKTFamily.exists_PsiT_sup_bound` — the uniform bound on `sup_{[0,2]}|Ψ_h|` of the
  same lemma.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

variable {d : ℕ}

namespace KKTFamily

/-! ## The displaced continued entropy -/

/-- **The displaced continued entropy** `J̃_{p_h}` of the display following
`eq:entropy-continuation`:

`J̃_{p_h}(u) = J̃_{p_*}(u) + Λ_h u + C_h`,  `Λ_h = ℓ(p_h) - ℓ(p_*)`,
`C_h = J_{p_h}(0) - J_{p_*}(0)`.

The displacement is the exact identity `eq:entropy-parameter-shift`, not an approximation, so on
`[0,1]` this is `J_{p_h}` itself (`JpTildeH_eq_Jp`) while on `(1,4]` it is the continuation
`J̃_{p_*}` of `SingularEndpoint/JpTilde.lean` moved by the same affine function. -/
noncomputable def JpTildeH (B : KKTFamily d) (h u : ℝ) : ℝ :=
  JpTilde d u + (ell (B.p h) - ell (pStar d)) * u + (Jp (B.p h) 0 - Jp (pStar d) 0)

/-- **The continuation agrees with `J_{p_h}` on `[0,1]`.**  The continued entropy agrees
with `J_{p_*}` there (`JpTilde_of_le_one`) and the displacement is exactly
`eq:entropy-parameter-shift` (`Jp_eq_Jp_pStar_add`). -/
theorem JpTildeH_eq_Jp (hd : 2 ≤ d) {B : KKTFamily d} {h : ℝ} (hh : |h| < B.h₀)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : B.JpTildeH h u = Jp (B.p h) u := by
  have hp := B.p_mem h hh
  rw [JpTildeH, JpTilde_of_le_one hu1, ← Jp_eq_Jp_pStar_add hd hp.1 hp.2 hu0 hu1]

/-- At the singular endpoint the displacement vanishes, since `p_0 = p_*`. -/
theorem JpTildeH_zero (B : KKTFamily d) (u : ℝ) : B.JpTildeH 0 u = JpTilde d u := by
  rw [JpTildeH, B.p_zero]
  ring

/-! ## The tilde dual potential -/

/-- **The one-point dual potential `eq:first-variation` through the continuation.**
Identical to `KKTFamily.Psi` except that the entropy is the continued `J̃_{p_h}`, which
makes the definition meaningful for every `x ∈ [0,2]` and not only while `x s_h, x t_h ≤ 1`.
The normalising constant `κ_h` is the same one, so `PsiT_eq_Psi` needs no correction. -/
noncomputable def PsiT (B : KKTFamily d) (h x : ℝ) : ℝ :=
  2 * (B.alph h * B.JpTildeH h (x * B.sVal h) + (1 - B.alph h) * B.JpTildeH h (x * B.tVal h))
    - B.etaVal h * x ^ d - B.kappaVal h

/-- **The two potentials agree** wherever `KKTFamily.Psi` is meaningful, that is
wherever both products `x s_h`, `x t_h` lie in `[0,1]`.  In particular the four contact
conditions of `SingularEndpoint/FirstVariation.lean` and the quartic bound
`KKTFamily.exists_firstVariation_lower` transfer verbatim to `PsiT`. -/
theorem PsiT_eq_Psi (hd : 2 ≤ d) {B : KKTFamily d} {h x : ℝ} (hh : |h| < B.h₀)
    (hs0 : 0 ≤ x * B.sVal h) (hs1 : x * B.sVal h ≤ 1)
    (ht0 : 0 ≤ x * B.tVal h) (ht1 : x * B.tVal h ≤ 1) : B.PsiT h x = B.Psi h x := by
  rw [PsiT, Psi, JpTildeH_eq_Jp hd hh hs0 hs1, JpTildeH_eq_Jp hd hh ht0 ht1]

/-- **`eq:endpoint-first-variation`**, in the form the paper states it: at the coalescing
singular endpoint the dual potential is twice the *continued* singular endpoint gap, rescaled,
`Ψ_0(x) = 2Γ̃_d(u_* x)`, now for every real `x` and not only where `u_* x ≤ 1`.

The `J_{p_*}(r_*)` and `β_d r_*^d` terms of `J̃_{p_*}` cancel against `κ_0`
(`kappaVal_zero`), and the `β_d u_*^d x^d` term against `η_0 x^d` (`etaVal_zero`). -/
theorem PsiT_zero (hd : 2 ≤ d) (B : KKTFamily d) (x : ℝ) :
    B.PsiT 0 x = 2 * GamTilde d (uStar d * x) := by
  have hxu : (uStar d * x) ^ d = uStar d ^ d * x ^ d := mul_pow _ _ _
  rw [PsiT, sVal_zero, tVal_zero, B.alph_zero, etaVal_zero hd, kappaVal_zero hd,
    JpTildeH_zero, mul_comm x (uStar d), JpTilde, hxu]
  ring

/-! ## Continuity of the collapsed potential -/

/-- `x ↦ Ψ_0(x)` is continuous on the law interval `[0,2]`: by `PsiT_zero` it is
`2Γ̃_d ∘ (u_* ·)`, and `x ↦ u_* x` maps `[0,2]` into `[0,2] ⊆ [0,4]` because `u_* < 1`, which
is where `continuousOn_GamTilde` lives. -/
private theorem continuousOn_PsiT_zero (hd : 2 ≤ d) (B : KKTFamily d) :
    ContinuousOn (fun x : ℝ => B.PsiT 0 x) (Set.Icc 0 2) := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  have hmaps : Set.MapsTo (fun x : ℝ => uStar d * x) (Set.Icc (0 : ℝ) 2) (Set.Icc (0 : ℝ) 4) := by
    intro x hx
    refine ⟨mul_nonneg hu0.le hx.1, ?_⟩
    have := mul_le_mul_of_nonneg_right hu1.le hx.1
    linarith [hx.2]
  have hlin : ContinuousOn (fun x : ℝ => uStar d * x) (Set.Icc (0 : ℝ) 2) := by fun_prop
  have hcomp : ContinuousOn (fun x : ℝ => GamTilde d (uStar d * x)) (Set.Icc (0 : ℝ) 2) :=
    (continuousOn_GamTilde hd).comp hlin hmaps
  exact (continuousOn_const.mul hcomp).congr (fun x _ => PsiT_zero hd B x)

/-- `Ψ_0 > 0` off the coalescence point: by `PsiT_zero` and `GamTilde_pos_of_ne`, since
`u_* x = r_*` forces `x = u_*` (`uStar_sq`). -/
private theorem PsiT_zero_pos (hd : 2 ≤ d) (B : KKTFamily d) {x : ℝ} (hx0 : 0 ≤ x)
    (hne : x ≠ uStar d) : 0 < B.PsiT 0 x := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hz : uStar d * x ≠ rStar d := by
    intro hz
    have hsq : uStar d * x = uStar d * uStar d := by rw [hz, ← uStar_sq hd]; ring
    exact hne (mul_left_cancel₀ (ne_of_gt hu0) hsq)
  have := GamTilde_pos_of_ne hd (mul_nonneg hu0.le hx0) hz
  rw [PsiT_zero hd]
  linarith

/-! ## The uniform comparison of `Ψ_h` with `Ψ_0`

The family scalars are continuous at `h = 0`; those facts, including
`kappaVal_continuousAt`, live in `SingularEndpoint/FamilyContinuity.lean`. -/

/-- **The scalar drift.**  A function of `h` alone dominating the part of the
`h`-dependence of `Ψ_h` that does not sit inside the continued entropy: the affine
displacement `Λ_h, C_h` of `eq:entropy-parameter-shift` weighted by `|x| ≤ 2`, the multiplier
`η_h` weighted by `|x^d| ≤ 2^d`, and the normalising constant `κ_h`. -/
private noncomputable def psiDrift (B : KKTFamily d) (h : ℝ) : ℝ :=
  4 * |ell (B.p h) - ell (pStar d)| + 2 * |Jp (B.p h) 0 - Jp (pStar d) 0|
    + (2 : ℝ) ^ d * |B.etaVal h - B.etaVal 0| + |B.kappaVal h - B.kappaVal 0|

private theorem psiDrift_zero (B : KKTFamily d) : B.psiDrift 0 = 0 := by
  simp [psiDrift, B.p_zero]

/-- The drift tends to `0`: every summand is a continuous function of `h` vanishing at
`h = 0`. -/
private theorem tendsto_psiDrift (hd : 2 ≤ d) (B : KKTFamily d) :
    Tendsto B.psiDrift (𝓝 0) (𝓝 0) := by
  have hcont : ContinuousAt B.psiDrift 0 := by
    have t1 : ContinuousAt (fun h : ℝ => 4 * |ell (B.p h) - ell (pStar d)|) 0 :=
      continuousAt_const.mul (((ell_p_continuousAt hd B).sub continuousAt_const).abs)
    have t2 : ContinuousAt (fun h : ℝ => 2 * |Jp (B.p h) 0 - Jp (pStar d) 0|) 0 :=
      continuousAt_const.mul (((Jp_p_zero_continuousAt hd B).sub continuousAt_const).abs)
    have t3 : ContinuousAt
        (fun h : ℝ => (2 : ℝ) ^ d * |B.etaVal h - B.etaVal 0|) 0 :=
      continuousAt_const.mul (((etaVal_continuousAt B).sub continuousAt_const).abs)
    have t4 : ContinuousAt (fun h : ℝ => |B.kappaVal h - B.kappaVal 0|) 0 :=
      ((kappaVal_continuousAt hd B).sub continuousAt_const).abs
    have h : ContinuousAt (fun h : ℝ =>
        4 * |ell (B.p h) - ell (pStar d)| + 2 * |Jp (B.p h) 0 - Jp (pStar d) 0|
          + (2 : ℝ) ^ d * |B.etaVal h - B.etaVal 0| + |B.kappaVal h - B.kappaVal 0|) 0 :=
      ((t1.add t2).add t3).add t4
    exact h
  rw [ContinuousAt, psiDrift_zero] at hcont
  exact hcont

/-- **The pointwise comparison.**  On `[0,2]` the whole `h`-dependence of `Ψ_h` splits into
two entropy increments at displaced arguments and the scalar `psiDrift`. -/
private theorem abs_PsiT_sub_le (_hd : 2 ≤ d) {B : KKTFamily d} {h : ℝ}
    (hh : |h| < B.h₀) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    |B.PsiT h x - B.PsiT 0 x|
      ≤ 2 * |JpTilde d (x * B.sVal h) - JpTilde d (x * uStar d)|
        + 2 * |JpTilde d (x * B.tVal h) - JpTilde d (x * uStar d)| + B.psiDrift h := by
  have ha := B.alph_mem h hh
  have hs0 := sVal_pos hh
  have hs1 := sVal_lt_one hh
  have ht0 := tVal_pos hh
  have ht1 := tVal_lt_one hh
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hx2 : x ≤ 2 := hx.2
  have hxs0 : (0 : ℝ) ≤ x * B.sVal h := mul_nonneg hx0 hs0.le
  have hxs2 : x * B.sVal h ≤ 2 := by
    have := mul_le_mul_of_nonneg_left hs1.le hx0
    linarith
  have hxt0 : (0 : ℝ) ≤ x * B.tVal h := mul_nonneg hx0 ht0.le
  have hxt2 : x * B.tVal h ≤ 2 := by
    have := mul_le_mul_of_nonneg_left ht1.le hx0
    linarith
  have hm0 : (0 : ℝ) ≤ B.alph h * (x * B.sVal h) + (1 - B.alph h) * (x * B.tVal h) :=
    add_nonneg (mul_nonneg ha.1.le hxs0) (mul_nonneg (by linarith [ha.2]) hxt0)
  have hm2 : B.alph h * (x * B.sVal h) + (1 - B.alph h) * (x * B.tVal h) ≤ 2 := by
    have e1 := mul_le_mul_of_nonneg_left hxs2 ha.1.le
    have e2 := mul_le_mul_of_nonneg_left hxt2 (by linarith [ha.2] : (0 : ℝ) ≤ 1 - B.alph h)
    linarith
  -- the exact splitting of the difference
  have key : B.PsiT h x - B.PsiT 0 x
      = 2 * B.alph h * (JpTilde d (x * B.sVal h) - JpTilde d (x * uStar d))
        + 2 * (1 - B.alph h) * (JpTilde d (x * B.tVal h) - JpTilde d (x * uStar d))
        + 2 * (ell (B.p h) - ell (pStar d))
            * (B.alph h * (x * B.sVal h) + (1 - B.alph h) * (x * B.tVal h))
        + 2 * (Jp (B.p h) 0 - Jp (pStar d) 0)
        - (B.etaVal h - B.etaVal 0) * x ^ d
        - (B.kappaVal h - B.kappaVal 0) := by
    simp only [PsiT, JpTildeH, B.p_zero, B.alph_zero, sVal_zero, tVal_zero]
    ring
  -- the six summands
  have b1 : |2 * B.alph h * (JpTilde d (x * B.sVal h) - JpTilde d (x * uStar d))|
      ≤ 2 * |JpTilde d (x * B.sVal h) - JpTilde d (x * uStar d)| := by
    rw [abs_mul, abs_of_nonneg (by linarith [ha.1] : (0 : ℝ) ≤ 2 * B.alph h)]
    exact mul_le_mul_of_nonneg_right (by linarith [ha.2]) (abs_nonneg _)
  have b2 : |2 * (1 - B.alph h) * (JpTilde d (x * B.tVal h) - JpTilde d (x * uStar d))|
      ≤ 2 * |JpTilde d (x * B.tVal h) - JpTilde d (x * uStar d)| := by
    rw [abs_mul, abs_of_nonneg (by linarith [ha.2] : (0 : ℝ) ≤ 2 * (1 - B.alph h))]
    exact mul_le_mul_of_nonneg_right (by linarith [ha.1]) (abs_nonneg _)
  have b3 : |2 * (ell (B.p h) - ell (pStar d))
        * (B.alph h * (x * B.sVal h) + (1 - B.alph h) * (x * B.tVal h))|
      ≤ 4 * |ell (B.p h) - ell (pStar d)| := by
    rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hm0]
    nlinarith [abs_nonneg (ell (B.p h) - ell (pStar d)),
      mul_nonneg (abs_nonneg (ell (B.p h) - ell (pStar d)))
        (by linarith : (0 : ℝ) ≤ 2 - (B.alph h * (x * B.sVal h)
          + (1 - B.alph h) * (x * B.tVal h)))]
  have b4 : |2 * (Jp (B.p h) 0 - Jp (pStar d) 0)|
      ≤ 2 * |Jp (B.p h) 0 - Jp (pStar d) 0| := by
    rw [abs_mul, abs_two]
  have hxd : |x ^ d| ≤ (2 : ℝ) ^ d := by
    rw [abs_of_nonneg (pow_nonneg hx0 d)]
    exact pow_le_pow_left₀ hx0 hx2 d
  have b5 : |(B.etaVal h - B.etaVal 0) * x ^ d|
      ≤ (2 : ℝ) ^ d * |B.etaVal h - B.etaVal 0| := by
    rw [abs_mul]
    calc |B.etaVal h - B.etaVal 0| * |x ^ d|
        ≤ |B.etaVal h - B.etaVal 0| * (2 : ℝ) ^ d :=
          mul_le_mul_of_nonneg_left hxd (abs_nonneg _)
      _ = _ := mul_comm _ _
  rw [key, psiDrift, abs_le]
  constructor <;>
    linarith [(abs_le.mp b1).1, (abs_le.mp b1).2, (abs_le.mp b2).1, (abs_le.mp b2).2,
      (abs_le.mp b3).1, (abs_le.mp b3).2, (abs_le.mp b4).1, (abs_le.mp b4).2,
      (abs_le.mp b5).1, (abs_le.mp b5).2,
      neg_abs_le (B.kappaVal h - B.kappaVal 0), le_abs_self (B.kappaVal h - B.kappaVal 0)]

/-- **Heine–Cantor for the continued entropy.**  `J̃_{p_*}` is continuous on the compact
`[0,4]` (`continuousOn_JpTilde`), hence uniformly continuous there. -/
private theorem exists_JpTilde_unif (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Set.Icc (0 : ℝ) 4, ∀ z ∈ Set.Icc (0 : ℝ) 4,
      |y - z| < δ → |JpTilde d y - JpTilde d z| < ε := by
  have hunif : UniformContinuousOn (JpTilde d) (Set.Icc (0 : ℝ) 4) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (continuousOn_JpTilde hd)
  obtain ⟨δ, hδ, hbd⟩ := Metric.uniformContinuousOn_iff.mp hunif ε hε
  refine ⟨δ, hδ, fun y hy z hz hyz => ?_⟩
  have h := hbd y hy z hz (by rwa [Real.dist_eq])
  rwa [Real.dist_eq] at h

/-- **Uniform convergence `Ψ_h → Ψ_0` on `[0,2]`.**  The two entropy increments of
`abs_PsiT_sub_le` are controlled by uniform continuity of `J̃_{p_*}` on `[0,4]` together
with `|x s_h - x u_*| ≤ 2|s_h - u_*|`, and the rest by `tendsto_psiDrift`. -/
private theorem exists_PsiT_unif (hd : 2 ≤ d) (B : KKTFamily d) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → |h| < B.h₀ →
      ∀ x ∈ Set.Icc (0 : ℝ) 2, |B.PsiT h x - B.PsiT 0 x| ≤ ε := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  obtain ⟨δ₁, hδ₁, hunif⟩ := exists_JpTilde_unif (d := d) hd (show (0 : ℝ) < ε / 8 by linarith)
  have hsw : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), |B.sVal h - uStar d| < δ₁ / 3 := by
    have h := Metric.tendsto_nhds.mp (sVal_continuousAt B) (δ₁ / 3) (by linarith)
    simpa [Real.dist_eq, sVal_zero] using h
  have htw : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), |B.tVal h - uStar d| < δ₁ / 3 := by
    have h := Metric.tendsto_nhds.mp (tVal_continuousAt B) (δ₁ / 3) (by linarith)
    simpa [Real.dist_eq, tVal_zero] using h
  obtain ⟨δ₂, hδ₂, hnode⟩ := Metric.eventually_nhds_iff.mp (hsw.and htw)
  obtain ⟨δ₃, hδ₃, hdr⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp (tendsto_psiDrift hd B) (ε / 2) (by linarith))
  refine ⟨min δ₂ δ₃, lt_min hδ₂ hδ₃, ?_⟩
  intro h hhδ hh x hx
  have hd2 : dist h (0 : ℝ) < δ₂ := by
    rw [Real.dist_eq, sub_zero]
    exact lt_of_lt_of_le hhδ (min_le_left _ _)
  have hd3 : dist h (0 : ℝ) < δ₃ := by
    rw [Real.dist_eq, sub_zero]
    exact lt_of_lt_of_le hhδ (min_le_right _ _)
  obtain ⟨hns, hnt⟩ := hnode hd2
  have hdrift : B.psiDrift h ≤ ε / 2 := by
    have h' := hdr hd3
    rw [Real.dist_eq, sub_zero] at h'
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) h')
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hx2 : x ≤ 2 := hx.2
  have hs0 := sVal_pos hh
  have hs1 := sVal_lt_one hh
  have ht0 := tVal_pos hh
  have ht1 := tVal_lt_one hh
  -- the four evaluation points lie in `[0,4]`
  have mems : x * B.sVal h ∈ Set.Icc (0 : ℝ) 4 := by
    refine ⟨mul_nonneg hx0 hs0.le, ?_⟩
    have := mul_le_mul_of_nonneg_left hs1.le hx0
    linarith
  have memt : x * B.tVal h ∈ Set.Icc (0 : ℝ) 4 := by
    refine ⟨mul_nonneg hx0 ht0.le, ?_⟩
    have := mul_le_mul_of_nonneg_left ht1.le hx0
    linarith
  have memu : x * uStar d ∈ Set.Icc (0 : ℝ) 4 := by
    refine ⟨mul_nonneg hx0 hu0.le, ?_⟩
    have := mul_le_mul_of_nonneg_left hu1.le hx0
    linarith
  -- the displaced arguments are uniformly close
  have gaps : |x * B.sVal h - x * uStar d| < δ₁ := by
    have e : x * B.sVal h - x * uStar d = x * (B.sVal h - uStar d) := by ring
    rw [e, abs_mul, abs_of_nonneg hx0]
    have h1 := mul_le_mul_of_nonneg_left hns.le hx0
    have h2 : x * (δ₁ / 3) ≤ 2 * (δ₁ / 3) :=
      mul_le_mul_of_nonneg_right hx2 (by linarith)
    linarith
  have gapt : |x * B.tVal h - x * uStar d| < δ₁ := by
    have e : x * B.tVal h - x * uStar d = x * (B.tVal h - uStar d) := by ring
    rw [e, abs_mul, abs_of_nonneg hx0]
    have h1 := mul_le_mul_of_nonneg_left hnt.le hx0
    have h2 : x * (δ₁ / 3) ≤ 2 * (δ₁ / 3) :=
      mul_le_mul_of_nonneg_right hx2 (by linarith)
    linarith
  have es := hunif _ mems _ memu gaps
  have et := hunif _ memt _ memu gapt
  have hmain := abs_PsiT_sub_le hd hh hx
  linarith

/-! ## The companion bound and the uniform sup bound -/

/-- **The second lower bound of `lem:first-variation-bound`**: for every `ρ > 0`
there are `b_ρ > 0` and `h_ρ > 0` such that

`Ψ_h(x) ≥ b_ρ`  for all `x ∈ [0,2]` with `|x - u_*| ≥ ρ` and all `|h| < h_ρ`.

Together with `KKTFamily.exists_firstVariation_lower` — which bounds the same function, by
`PsiT_eq_Psi` — this is the first-variation pair of the lemma.

The proof is the paper's: at `h = 0` the collapsed form `eq:endpoint-first-variation` and
strict positivity of the continued gap away from `r_*` (`GamTilde_pos_of_ne`) give
`Ψ_0 > 0` on the compact set `T_ρ = {x ∈ [0,2] : |x - u_*| ≥ ρ}`, hence `Ψ_0 ≥ 2b` there by
the extreme value theorem; the uniform convergence `Ψ_h → Ψ_0` of `exists_PsiT_unif` then
gives `Ψ_h ≥ 2b - b` for small `h`.  When `T_ρ` is empty the statement is vacuous. -/
theorem exists_firstVariation_upperGap (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ0 : 0 < ρ) :
    ∃ b : ℝ, 0 < b ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → |h| < B.h₀ →
      ∀ x ∈ Set.Icc (0 : ℝ) 2, ρ ≤ |x - uStar d| → b ≤ B.PsiT h x := by
  have hcl : IsClosed {x : ℝ | ρ ≤ |x - uStar d|} := by
    refine isClosed_le continuous_const ?_
    fun_prop
  have hcomp : IsCompact (Set.Icc (0 : ℝ) 2 ∩ {x : ℝ | ρ ≤ |x - uStar d|}) :=
    isCompact_Icc.inter_right hcl
  by_cases hne : (Set.Icc (0 : ℝ) 2 ∩ {x : ℝ | ρ ≤ |x - uStar d|}).Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := hcomp.exists_isMinOn hne
      ((continuousOn_PsiT_zero hd B).mono Set.inter_subset_left)
    have hpos : 0 < B.PsiT 0 x₀ := by
      refine PsiT_zero_pos hd B hx₀.1.1 ?_
      intro hx
      have : ρ ≤ |x₀ - uStar d| := hx₀.2
      rw [hx, sub_self, abs_zero] at this
      linarith
    obtain ⟨δ, hδ, hunif⟩ := exists_PsiT_unif hd B (show (0 : ℝ) < B.PsiT 0 x₀ / 2 by linarith)
    refine ⟨B.PsiT 0 x₀ / 2, by linarith, δ, hδ, ?_⟩
    intro h hhδ hh x hx hgap
    have hmem : x ∈ Set.Icc (0 : ℝ) 2 ∩ {x : ℝ | ρ ≤ |x - uStar d|} := ⟨hx, hgap⟩
    have hlow := isMinOn_iff.mp hmin x hmem
    have hcl' := hunif h hhδ hh x hx
    have := (abs_le.mp hcl').1
    linarith
  · exact ⟨1, one_pos, 1, one_pos, fun h _ _ x hx hgap => absurd ⟨x, hx, hgap⟩ hne⟩

/-- **The uniform sup bound of `lem:first-variation-bound`**: `sup_{[0,2]}|Ψ_h|`
is bounded uniformly in `h` near `0`.  The bound is the maximum of `|Ψ_0|` on `[0,2]`, which
exists by the extreme value theorem, plus the `1` allowed by `exists_PsiT_unif`. -/
theorem exists_PsiT_sup_bound (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → |h| < B.h₀ →
      ∀ x ∈ Set.Icc (0 : ℝ) 2, |B.PsiT h x| ≤ M := by
  obtain ⟨x₀, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 2))
    ((continuousOn_PsiT_zero hd B).abs)
  obtain ⟨δ, hδ, hunif⟩ := exists_PsiT_unif hd B (show (0 : ℝ) < 1 by norm_num)
  refine ⟨|B.PsiT 0 x₀| + 1, by positivity, δ, hδ, ?_⟩
  intro h hhδ hh x hx
  have hup := isMaxOn_iff.mp hmax x hx
  have hcl := hunif h hhδ hh x hx
  have h1 := abs_sub_abs_le_abs_sub (B.PsiT h x) (B.PsiT 0 x)
  linarith

end KKTFamily

end SingularEndpoint

end UpperTailOptimizers
