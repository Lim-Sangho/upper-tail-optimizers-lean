import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilyExists
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.LogOdds
import UpperTailOptimizers.LZBoundary.AnalyticImplicitUnique

/-!
# Symmetry of the coalescing scalar family (Section 5, `paper/sections/singular.tex`)

`SingularEndpoint/RankOneStationaryFamily/FamilyExists.lean` produces the analytic family `h ↦ (u_h, ℓ_h, γ_h)` of
`lem:rank-one-kkt-family` from the analytic implicit function theorem, but says
nothing about how it behaves under `h ↦ -h`.  In the paper, `B(u,h)` is even in `h`, so
uniqueness in the implicit function theorem gives `u_{-h} = u_h`, and `γ_h`, `p_h` are then
even by their formulas.  Here the same idea is applied to the whole desingularized system,
giving `u_{-h} = u_h`, `ℓ_{-h} = ℓ_h`, `γ_{-h} = γ_h` at once: the system is *even* in `h`,
so `h ↦ z_{-h}` is a second solution family through the same base point, and local
uniqueness in the implicit function theorem forces the two to agree.  This file carries out
both halves.

**Evenness.**  With `s = u - h` and `t = u + h`, replacing `h` by `-h` exchanges `s` and
`t`.  The middle root `s t` is symmetric in the two, so `E₁` is unchanged outright.  The
difference `𝓛(t²) - 𝓛(s²)` changes sign, but so does the extracted factor `h`, so the
quotient `E₂ = (𝓛(t²) - 𝓛(s²))/h` is unchanged; the sum `𝓛(t²) + 𝓛(s²) - 2𝓛(st)` and the
factor `h²` are both unchanged, so `E₂` and `E₃` are even as well.  The proofs cancel `h`
and `h²` in the exact factorisations `Lell_sub_eq_mul` and `Lell_add_sub_two_eq_mul` of
`SingularEndpoint/RankOneStationaryFamily/FamilySystem.lean`, which is legitimate for `h ≠ 0`; at `h = 0` there is nothing
to prove because `-0 = 0`.

**Uniqueness.**  `analytic_implicit_locally_unique` (`LZBoundary/AnalyticImplicitUnique.lean`)
is applied exactly as `exists_scalar_family` applies `analytic_implicit`, and the reflected
family `h ↦ z_{-h}` is fed into its uniqueness clause.  The side conditions that `Fsys_neg`
needs hold near `h = 0` by continuity, in the two-sided form `0 < u_h - |h|` and
`u_h + |h| < 1`, which is exactly what makes them available at `-h` as well as at `h`.  The
finitely many `∀ᶠ` statements are then collapsed into a single radius `h₀` by
`Metric.eventually_nhds_iff`.

The last clause recovers the ambient density `p_h = 1/(1 + e^{ℓ_h})` of
`lem:rank-one-kkt-family` from `ℓ_h` through `pOf` of `SingularEndpoint/RankOneStationaryFamily/LogOdds.lean`; it
inherits analyticity and the `h ↦ -h` symmetry from `ℓ_h`.

**What this is not.**  The block weight `α_h` and its antisymmetry `α_{-h} = 1 - α_h`, local
exhaustiveness, and the expansions `eq:rank-one-parameter-expansions` are not proved here; they
are `SingularEndpoint/RankOneStationaryFamily/Alpha.lean`, `SingularEndpoint/RankOneStationaryFamily/FamilyUnique.lean` and `SingularEndpoint/ConstantGraphonComparison/Expansions.lean`, and
`SingularEndpoint/RankOneStationaryFamily/FamilyBuild.lean` assembles them all into `exists_kktFamily`.

## Contents

* `Esys1_neg`, `Esys2_neg`, `Esys3_neg` — the three components of the desingularized system
  of `lem:rank-one-kkt-family` are even in `h`;
* `Fsys_neg` — the packaged system is even in `h`;
* `exists_scalar_family_symm` — the coalescing family on an explicit interval `|h| < h₀`,
  with the symmetries `u_{-h} = u_h`, `ℓ_{-h} = ℓ_h`, `γ_{-h} = γ_h` and the three KKT
  equations `eq:three-value-kkt` for `h ≠ 0`;
* `exists_scalar_family_density` — the same family carrying the density `p_h` with
  `ℓ(p_h) = ℓ_h`, `p_0 = p_*` and `p_{-h} = p_h`.
-/

namespace UpperTailOptimizers

open Filter Topology

variable {d : ℕ}

/-! ## The desingularized system is even in `h`

Replacing `h` by `-h` exchanges `s_h = u - h` with `t_h = u + h`.  `E₁` depends on the pair
only through the symmetric product `s_h t_h`; `E₂` and `E₃` are quotients whose numerator
and denominator pick up matching signs. -/

/-- **`E₁` is even in `h`** (`lem:rank-one-kkt-family`).  The middle root
`s_h t_h = (u - h)(u + h)` of `eq:three-value-kkt` is symmetric under `h ↦ -h`, so no
hypotheses are needed. -/
theorem Esys1_neg (d : ℕ) (lv g u h : ℝ) : Esys1 d lv g u (-h) = Esys1 d lv g u h := by
  have harg : (u - -h) * (u + -h) = (u - h) * (u + h) := by ring
  simp only [Esys1, harg]

/-- **`E₂` is even in `h`** (`lem:rank-one-kkt-family`).

`Lell_sub_eq_mul` reads `𝓛(t²) - 𝓛(s²) = h·E₂`.  At `-h` the roles of `s` and `t` are
exchanged, so the left-hand side changes sign while the extracted factor `h` does too;
cancelling `h ≠ 0` gives `E₂(u, -h) = E₂(u, h)`.  The five admissibility hypotheses at `-h`
are the five listed ones with `s` and `t` swapped. -/
theorem Esys2_neg (hd : 2 ≤ d) {u h : ℝ} (hs : 0 < u - h) (ht : 0 < u + h)
    (hs1 : (u - h) ^ 2 < 1) (ht1 : (u + h) ^ 2 < 1) (hst : (u - h) * (u + h) < 1) (g : ℝ) :
    Esys2 d g u (-h) = Esys2 d g u h := by
  rcases eq_or_ne h 0 with rfl | hne
  · rw [neg_zero]
  · have e1 : u - -h = u + h := by ring
    have e2 : u + -h = u - h := by ring
    have H1 := Lell_sub_eq_mul (d := d) (lv := (0 : ℝ)) (g := g) (u := u) (h := h)
      hd hs ht hs1 ht1 hst
    have H2 := Lell_sub_eq_mul (d := d) (lv := (0 : ℝ)) (g := g) (u := u) (h := -h)
      hd (by rw [e1]; exact ht) (by rw [e2]; exact hs) (by rw [e1]; exact ht1)
      (by rw [e2]; exact hs1) (by rw [e1, e2]; linarith [hst])
    rw [e1, e2] at H2
    have key : h * Esys2 d g u h = h * Esys2 d g u (-h) := by linear_combination -H1 - H2
    exact (mul_left_cancel₀ hne key).symm

/-- **`E₃` is even in `h`** (`lem:rank-one-kkt-family`).

`Lell_add_sub_two_eq_mul` reads `𝓛(t²) + 𝓛(s²) - 2𝓛(st) = h²·E₃`.  Exchanging `s` and `t`
leaves the left-hand side unchanged — the sum is symmetric and `st` is — and leaves `h²`
unchanged, so cancelling `h² ≠ 0` gives `E₃(u, -h) = E₃(u, h)`. -/
theorem Esys3_neg (hd : 2 ≤ d) {u h : ℝ} (hs : 0 < u - h) (ht : 0 < u + h)
    (hs1 : (u - h) ^ 2 < 1) (ht1 : (u + h) ^ 2 < 1) (hst : (u - h) * (u + h) < 1) (g : ℝ) :
    Esys3 d g u (-h) = Esys3 d g u h := by
  rcases eq_or_ne h 0 with rfl | hne
  · rw [neg_zero]
  · have e1 : u - -h = u + h := by ring
    have e2 : u + -h = u - h := by ring
    have H1 := Lell_add_sub_two_eq_mul (d := d) (lv := (0 : ℝ)) (g := g) (u := u) (h := h)
      hd hs ht hs1 ht1 hst
    have H2 := Lell_add_sub_two_eq_mul (d := d) (lv := (0 : ℝ)) (g := g) (u := u) (h := -h)
      hd (by rw [e1]; exact ht) (by rw [e2]; exact hs) (by rw [e1]; exact ht1)
      (by rw [e2]; exact hs1) (by rw [e1, e2]; linarith [hst])
    rw [e1, e2, mul_comm (u + h) (u - h)] at H2
    have key : h ^ 2 * Esys3 d g u h = h ^ 2 * Esys3 d g u (-h) := by
      linear_combination H2 - H1
    exact (mul_left_cancel₀ (pow_ne_zero 2 hne) key).symm

/-- **The packaged desingularized system is even in `h`**: `Fsys d z (-h) = Fsys d z h`.

This is the evenness that `lem:rank-one-kkt-family` feeds to local uniqueness in
the implicit function theorem: `h ↦ z_{-h}` solves the same system as `h ↦ z_h`. -/
theorem Fsys_neg (hd : 2 ≤ d) {z : ℝ × ℝ × ℝ} {h : ℝ}
    (hs : 0 < z.1 - h) (ht : 0 < z.1 + h) (hs1 : (z.1 - h) ^ 2 < 1) (ht1 : (z.1 + h) ^ 2 < 1)
    (hst : (z.1 - h) * (z.1 + h) < 1) :
    Fsys d z (-h) = Fsys d z h := by
  simp only [Fsys, Esys1_neg, Esys2_neg hd hs ht hs1 ht1 hst,
    Esys3_neg hd hs ht hs1 ht1 hst]

/-! ## The symmetric family

The two-sided bound `0 < u - |h|`, `u + |h| < 1` is the right form of admissibility here:
it is symmetric in `h ↦ -h`, so a single `∀ᶠ` statement supplies the side conditions of
`Fsys_neg` both at `h` and at `-h`. -/

/-- Admissibility from the two-sided bound: if `u - |h| > 0` and `u + |h| < 1` then both
`s = u - h` and `t = u + h` lie in `(0, 1)`, hence `s²`, `t²`, `st` all lie below `1` — the
five side conditions of `Lell_sub_eq_mul`, `Lell_add_sub_two_eq_mul` and
`lell_three_eq_iff`. -/
private theorem admis_of_abs {u h : ℝ} (h1 : 0 < u - |h|) (h2 : u + |h| < 1) :
    0 < u - h ∧ 0 < u + h ∧ (u - h) ^ 2 < 1 ∧ (u + h) ^ 2 < 1 ∧ (u - h) * (u + h) < 1 := by
  have hle := le_abs_self h
  have hle' := neg_abs_le h
  have hs : 0 < u - h := by linarith
  have ht : 0 < u + h := by linarith
  have hs' : u - h < 1 := by linarith
  have ht' : u + h < 1 := by linarith
  refine ⟨hs, ht, ?_, ?_, ?_⟩ <;> nlinarith

/-- **The coalescing scalar family, with its `h ↦ -h` symmetry**
(`lem:rank-one-kkt-family`).

On an explicit interval `|h| < h₀` there is a real-analytic family `h ↦ (u_h, ℓ_h, γ_h)`
through `(u_*, ℓ_*, γ_*)` which

* stays admissible, in the two-sided form `0 < u_h - |h|` and `u_h + |h| < 1`;
* is even, `u_{-h} = u_h`, `ℓ_{-h} = ℓ_h`, `γ_{-h} = γ_h`;
* satisfies the three rank-one KKT equations `eq:three-value-kkt` for `h ≠ 0`.

Evenness comes from `Fsys_neg` together with the local uniqueness clause of
`analytic_implicit_locally_unique`: the reflected family `h ↦ z_{-h}` is continuous at `0`,
passes through the same base point and solves the same system, so it agrees with `z` near
`0`. -/
theorem exists_scalar_family_symm (hd : 2 ≤ d) :
    ∃ (h0 : ℝ) (u lv g : ℝ → ℝ),
      0 < h0 ∧
      u 0 = uStar d ∧ lv 0 = ellStar d ∧ g 0 = gammaStar d ∧
      (∀ h : ℝ, |h| < h0 → AnalyticAt ℝ u h) ∧
      (∀ h : ℝ, |h| < h0 → AnalyticAt ℝ lv h) ∧
      (∀ h : ℝ, |h| < h0 → AnalyticAt ℝ g h) ∧
      (∀ h : ℝ, |h| < h0 → 0 < u h - |h| ∧ u h + |h| < 1) ∧
      (∀ h : ℝ, |h| < h0 → u (-h) = u h ∧ lv (-h) = lv h ∧ g (-h) = g h) ∧
      (∀ h : ℝ, |h| < h0 → h ≠ 0 →
        Lell d (lv h) (g h) ((u h - h) ^ 2) = 0 ∧
          Lell d (lv h) (g h) ((u h - h) * (u h + h)) = 0 ∧
          Lell d (lv h) (g h) ((u h + h) ^ 2) = 0) := by
  obtain ⟨a, b, c, e, hb, hc, hL⟩ := exists_hasStrictFDerivAt_Fsys hd
  obtain ⟨z, hz0, hzsol, hzan, huniq⟩ :=
    analytic_implicit_locally_unique (analyticAt_Fsys hd) (Fsys_base hd) (jac3 a b c e hb hc) hL
  -- the three coordinate projections are analytic wherever `z` is
  have hcomp1 : ∀ {w : ℝ}, AnalyticAt ℝ z w → AnalyticAt ℝ (fun k : ℝ => (z k).1) w := by
    intro w hw
    exact AnalyticAt.fun_comp_of_eq (g := fun p : ℝ × ℝ × ℝ => p.1) (f := z) analyticAt_fst hw rfl
  have hcompsnd : ∀ {w : ℝ}, AnalyticAt ℝ z w → AnalyticAt ℝ (fun k : ℝ => (z k).2) w := by
    intro w hw
    exact AnalyticAt.fun_comp_of_eq (g := fun p : ℝ × ℝ × ℝ => p.2) (f := z) analyticAt_snd hw rfl
  have hcomp2 : ∀ {w : ℝ}, AnalyticAt ℝ z w → AnalyticAt ℝ (fun k : ℝ => (z k).2.1) w := by
    intro w hw
    exact AnalyticAt.fun_comp_of_eq (g := fun p : ℝ × ℝ => p.1) (f := fun k : ℝ => (z k).2)
      analyticAt_fst (hcompsnd hw) rfl
  have hcomp3 : ∀ {w : ℝ}, AnalyticAt ℝ z w → AnalyticAt ℝ (fun k : ℝ => (z k).2.2) w := by
    intro w hw
    exact AnalyticAt.fun_comp_of_eq (g := fun p : ℝ × ℝ => p.2) (f := fun k : ℝ => (z k).2)
      analyticAt_snd (hcompsnd hw) rfl
  have hzanev : ∀ᶠ h in 𝓝 (0 : ℝ), AnalyticAt ℝ z h := AnalyticAt.eventually_analyticAt hzan
  -- admissibility near `h = 0`
  have hu0 : (z 0).1 = uStar d := by rw [hz0]; rfl
  have htu : Tendsto (fun k : ℝ => (z k).1) (𝓝 0) (𝓝 (uStar d)) := by
    have := (hcomp1 hzan).continuousAt.tendsto
    rwa [hu0] at this
  have habs : Tendsto (fun k : ℝ => |k|) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ))
  have hadm : ∀ᶠ h in 𝓝 (0 : ℝ), 0 < (z h).1 - |h| ∧ (z h).1 + |h| < 1 := by
    have hA : ∀ᶠ h in 𝓝 (0 : ℝ), 0 < (z h).1 - |h| := by
      have : Tendsto (fun k : ℝ => (z k).1 - |k|) (𝓝 0) (𝓝 (uStar d)) := by
        simpa using htu.sub habs
      exact this.eventually_const_lt (uStar_pos hd)
    have hB : ∀ᶠ h in 𝓝 (0 : ℝ), (z h).1 + |h| < 1 := by
      have : Tendsto (fun k : ℝ => (z k).1 + |k|) (𝓝 0) (𝓝 (uStar d)) := by
        simpa using htu.add habs
      exact this.eventually_lt_const (uStar_lt_one hd)
    exact hA.and hB
  -- the reflected family solves the same system, hence coincides with `z`
  have hnegtend : Tendsto (fun k : ℝ => -k) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : ℝ))
  have hadmneg : ∀ᶠ h in 𝓝 (0 : ℝ), 0 < (z (-h)).1 - |h| ∧ (z (-h)).1 + |h| < 1 := by
    have := hnegtend.eventually hadm
    simpa using this
  have hz'sol : ∀ᶠ h in 𝓝 (0 : ℝ), Fsys d (z (-h)) h = 0 := by
    filter_upwards [hnegtend.eventually hzsol, hadmneg] with h hsol hah
    obtain ⟨hs, ht, hs1, ht1, hst⟩ := admis_of_abs hah.1 hah.2
    rwa [Fsys_neg hd hs ht hs1 ht1 hst] at hsol
  have hz'cont : ContinuousAt (fun k : ℝ => z (-k)) 0 := by
    have hz' : ContinuousAt z (-(0 : ℝ)) := by rw [neg_zero]; exact hzan.continuousAt
    exact hz'.comp continuous_neg.continuousAt
  have hz'0 : z (-(0 : ℝ)) = zBase d := by rw [neg_zero]; exact hz0
  have hsymm : ∀ᶠ h in 𝓝 (0 : ℝ), z (-h) = z h :=
    huniq (fun k : ℝ => z (-k)) hz'cont hz'0 hz'sol
  -- the three KKT equations for `h ≠ 0`
  have hkkt : ∀ᶠ h in 𝓝 (0 : ℝ), h ≠ 0 →
      Lell d (z h).2.1 (z h).2.2 (((z h).1 - h) ^ 2) = 0 ∧
        Lell d (z h).2.1 (z h).2.2 (((z h).1 - h) * ((z h).1 + h)) = 0 ∧
        Lell d (z h).2.1 (z h).2.2 (((z h).1 + h) ^ 2) = 0 := by
    filter_upwards [hzsol, hadm] with h hsol hah hne
    obtain ⟨hs, ht, hs1, ht1, hst⟩ := admis_of_abs hah.1 hah.2
    refine (lell_three_eq_iff hd hne hs ht hs1 ht1 hst).mpr ?_
    have hsplit := congrArg (fun w : ℝ × ℝ × ℝ => (w.1, w.2.1, w.2.2)) hsol
    simp only [Fsys, Prod.mk.injEq] at hsplit
    exact ⟨hsplit.1, hsplit.2.1, hsplit.2.2⟩
  -- one radius for all of the above
  have hall : ∀ᶠ h in 𝓝 (0 : ℝ),
      AnalyticAt ℝ z h ∧ (0 < (z h).1 - |h| ∧ (z h).1 + |h| < 1) ∧ z (-h) = z h ∧
        (h ≠ 0 →
          Lell d (z h).2.1 (z h).2.2 (((z h).1 - h) ^ 2) = 0 ∧
            Lell d (z h).2.1 (z h).2.2 (((z h).1 - h) * ((z h).1 + h)) = 0 ∧
            Lell d (z h).2.1 (z h).2.2 (((z h).1 + h) ^ 2) = 0) := by
    filter_upwards [hzanev, hadm, hsymm, hkkt] with h e1 e2 e3 e4 using ⟨e1, e2, e3, e4⟩
  rw [Metric.eventually_nhds_iff] at hall
  obtain ⟨ε, hε, hball⟩ := hall
  have hkey : ∀ h : ℝ, |h| < ε →
      AnalyticAt ℝ z h ∧ (0 < (z h).1 - |h| ∧ (z h).1 + |h| < 1) ∧ z (-h) = z h ∧
        (h ≠ 0 →
          Lell d (z h).2.1 (z h).2.2 (((z h).1 - h) ^ 2) = 0 ∧
            Lell d (z h).2.1 (z h).2.2 (((z h).1 - h) * ((z h).1 + h)) = 0 ∧
            Lell d (z h).2.1 (z h).2.2 (((z h).1 + h) ^ 2) = 0) := by
    intro h hh
    exact hball (by rw [Real.dist_eq, sub_zero]; exact hh)
  refine ⟨ε, fun k => (z k).1, fun k => (z k).2.1, fun k => (z k).2.2, hε, hu0, ?_, ?_,
    fun h hh => hcomp1 (hkey h hh).1, fun h hh => hcomp2 (hkey h hh).1,
    fun h hh => hcomp3 (hkey h hh).1, fun h hh => (hkey h hh).2.1, ?_,
    fun h hh => (hkey h hh).2.2.2⟩
  · show (z 0).2.1 = ellStar d
    rw [hz0]; rfl
  · show (z 0).2.2 = gammaStar d
    rw [hz0]; rfl
  · intro h hh
    have hs := (hkey h hh).2.2.1
    exact ⟨congrArg Prod.fst hs, congrArg (fun w : ℝ × ℝ × ℝ => w.2.1) hs,
      congrArg (fun w : ℝ × ℝ × ℝ => w.2.2) hs⟩

/-- **The symmetric family, carrying the ambient density `p_h`**
(`lem:rank-one-kkt-family`).

`exists_scalar_family_symm` with the fourth coordinate `p_h = 1/(1 + e^{ℓ_h})` of
`SingularEndpoint/RankOneStationaryFamily/LogOdds.lean` adjoined.  It is analytic because `pOf` is analytic everywhere, it
lies in `(0, 1)` by `pOf_pos` and `pOf_lt_one`, it inverts the log-odds by `ell_pOf`, it
starts at `p_*` by `pOf_ellStar`, and it is even because `ℓ_h` is. -/
theorem exists_scalar_family_density (hd : 2 ≤ d) :
    ∃ (h0 : ℝ) (u lv g p : ℝ → ℝ),
      0 < h0 ∧
      u 0 = uStar d ∧ lv 0 = ellStar d ∧ g 0 = gammaStar d ∧ p 0 = pStar d ∧
      (∀ h : ℝ, |h| < h0 → AnalyticAt ℝ u h) ∧
      (∀ h : ℝ, |h| < h0 → AnalyticAt ℝ lv h) ∧
      (∀ h : ℝ, |h| < h0 → AnalyticAt ℝ g h) ∧
      (∀ h : ℝ, |h| < h0 → AnalyticAt ℝ p h) ∧
      (∀ h : ℝ, |h| < h0 → 0 < u h - |h| ∧ u h + |h| < 1) ∧
      (∀ h : ℝ, |h| < h0 → 0 < p h ∧ p h < 1) ∧
      (∀ h : ℝ, |h| < h0 → ell (p h) = lv h) ∧
      (∀ h : ℝ, |h| < h0 → u (-h) = u h ∧ lv (-h) = lv h ∧ g (-h) = g h ∧ p (-h) = p h) ∧
      (∀ h : ℝ, |h| < h0 → h ≠ 0 →
        Lell d (lv h) (g h) ((u h - h) ^ 2) = 0 ∧
          Lell d (lv h) (g h) ((u h - h) * (u h + h)) = 0 ∧
          Lell d (lv h) (g h) ((u h + h) ^ 2) = 0) := by
  obtain ⟨h0, u, lv, g, hh0, hu0, hlv0, hg0, hua, hlva, hga, hadm, hsym, hkkt⟩ :=
    exists_scalar_family_symm hd
  refine ⟨h0, u, lv, g, fun k => pOf (lv k), hh0, hu0, hlv0, hg0, ?_, hua, hlva, hga, ?_,
    hadm, ?_, ?_, ?_, hkkt⟩
  · show pOf (lv 0) = pStar d
    rw [hlv0]
    exact pOf_ellStar hd
  · intro h hh
    exact AnalyticAt.fun_comp_of_eq (g := pOf) (f := lv) (analyticAt_pOf (lv h)) (hlva h hh) rfl
  · intro h _
    exact ⟨pOf_pos _, pOf_lt_one _⟩
  · intro h _
    exact ell_pOf _
  · intro h hh
    exact ⟨(hsym h hh).1, (hsym h hh).2.1, (hsym h hh).2.2,
      congrArg pOf (hsym h hh).2.1⟩

end UpperTailOptimizers
