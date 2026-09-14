import UpperTailOptimizers.LZBoundary.Curve

/-!
# Section 3 in the paper's form

`LZBoundary/PhiDeriv.lean`, `LZBoundary/Existence.lean` and `LZBoundary/Curve.lean` prove the
results of `sec:lz-boundary` with the zeros of `h_{p,d}` and the two contact points produced
existentially (`convexity_defect`, `lz_boundary_contacts`) or carried by a `GlobalContacts`
datum, and with (M1)–(M5) of Theorem 3.1 packaged on boundary arcs
(`lz_boundary_arcs`).  This file states `lem:convexity-defect`, `lem:contact-points`,
`lem:contact-point-limits` and Theorem 3.1 as the paper does, with named
functions:

* `uMinus p d`, `uPlus p d` — the zeros `u₋(p)`, `u₊(p)` of `h_{p,d}`: the infimum and the
  supremum of its zero set in `(0,1)`;
* `contactXa d p`, `contactXb d p` — the contact points `x_a(p)`, `x_b(p)`: the infimum and the
  supremum of the set of `x ∈ (0,1)` where the convex minorant of `φ_{p,d}` is strictly below
  `φ_{p,d}`;
* `pcGlobal d`, `smGlobal d` (`LZBoundary/Curve.lean`) — the boundary curve `pc` and the second
  contact `sm`.

The convex minorant of the footnote of Section 3 is `lce 0 1 (phi p d)`
(`lce_phi_convexMinorant`).

The contact points are identified with the `d`-th powers of the contacts `u_a(p)`, `u_b(p)` of
`exists_globalContacts` (`contactXa_eq_gc`): for `0 < p < p_*` the detached set of the convex
minorant is exactly `(u_a(p)^d, u_b(p)^d)` (`gc_lce_eq_outside`, `contact_bundle`).  Analyticity,
the signs of the derivatives, the limits and monotonicity transfer from `GlobalContacts`, and
uniqueness of the contact pair is `contact_unique`.  (M5) for an arbitrary compact
`K ⊆ (0,1) ∖ {r_*}` follows from the arc-wise `quadSep` field by covering `K` with closed balls
inside arcs (`lz_boundary_quadSep`).

## Contents

* `uMinus_uPlus_eq_of_zeros`, `convexity_defect_zeros` — `lem:convexity-defect`;
* `lce_phi_convexMinorant` — `lce 0 1 (phi p d)` is the convex minorant of `φ_{p,d}`;
* `gc_lce_eq_outside`, `contactXa_eq_gc`, `contact_points` — `lem:contact-points`;
* `contact_point_limits` — `lem:contact-point-limits`;
* `lz_boundary_M2_lce`, `LZBoundaryArc.quadSep_x`, `lz_boundary_quadSep`,
  `lz_boundary` — Theorem 3.1.
-/

namespace UpperTailOptimizers

open Real Set Filter Topology

/-! ### `lem:convexity-defect` with named zeros -/

/-- The left zero `u₋(p)` of the convexity defect `h_{p,d}` (`lem:convexity-defect`): the
infimum of the zero set of `h_{p,d}` in `(0,1)`.  For `0 < p < p_*` the zero set is exactly
`{u₋(p), u₊(p)}` (`convexity_defect_zeros`). -/
noncomputable def uMinus (p : ℝ) (d : ℕ) : ℝ :=
  sInf {u : ℝ | u ∈ Set.Ioo (0:ℝ) 1 ∧ hpd p d u = 0}

/-- The right zero `u₊(p)` of the convexity defect `h_{p,d}` (`lem:convexity-defect`): the
supremum of the zero set of `h_{p,d}` in `(0,1)`. -/
noncomputable def uPlus (p : ℝ) (d : ℕ) : ℝ :=
  sSup {u : ℝ | u ∈ Set.Ioo (0:ℝ) 1 ∧ hpd p d u = 0}

/-- If the zero set of `h_{p,d}` in `(0,1)` is `{um, up}` with `um < up`, then `uMinus` and
`uPlus` are `um` and `up`. -/
theorem uMinus_uPlus_eq_of_zeros {d : ℕ} {p um up : ℝ}
    (hum0 : 0 < um) (humup : um < up) (hup1 : up < 1)
    (hzero : ∀ u : ℝ, 0 < u → u < 1 → (hpd p d u = 0 ↔ u = um ∨ u = up)) :
    uMinus p d = um ∧ uPlus p d = up := by
  have hup0 : 0 < up := hum0.trans humup
  have hum1 : um < 1 := humup.trans hup1
  have hset : {u : ℝ | u ∈ Set.Ioo (0:ℝ) 1 ∧ hpd p d u = 0} = {um, up} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h0, h1⟩, hz⟩
      exact (hzero u h0 h1).mp hz
    · rintro (h | h)
      · exact ⟨⟨h ▸ hum0, h ▸ hum1⟩, (hzero u (h ▸ hum0) (h ▸ hum1)).mpr (Or.inl h)⟩
      · exact ⟨⟨h ▸ hup0, h ▸ hup1⟩, (hzero u (h ▸ hup0) (h ▸ hup1)).mpr (Or.inr h)⟩
  refine ⟨?_, ?_⟩
  · rw [uMinus, hset, csInf_pair]; exact min_eq_left humup.le
  · rw [uPlus, hset, csSup_pair]; exact max_eq_right humup.le

/-- **`lem:convexity-defect`**, with the two zeros named `uMinus p d`, `uPlus p d`.

For every `p ∈ (0,1)`:
* `h_{p,d}'(z) = d(z - r_*)/(z(1-z)²)` on `(0,1)` and
  `h_{p,d}(r_*) = d - (d-1) log((d-1)(1-p)/p)`;
* `h_{p,d}` is strictly decreasing on `(0,r_*)`, strictly increasing on `(r_*,1)`, with its
  unique minimum at `r_*`;
* for `x ∈ (0,1)` and `z = x^{1/d}`, the second derivative of `φ_{p,d}` at `x` is
  `h_{p,d}(z)/(d² z^{2d-1})` (as a `HasDerivAt` statement for `deriv φ_{p,d}`), so
  `φ_{p,d}''(x)` and `h_{p,d}(z)` have the same sign;
* if `p ≥ p_*` then `h_{p,d} ≥ 0` and `φ_{p,d}` is convex on `[0,1]`;
* if `p < p_*` then `h_{p,d}` has exactly the two zeros `u₋(p) < r_* < u₊(p)`, is positive on
  `(0,u₋(p)) ∪ (u₊(p),1)` and negative on `(u₋(p),u₊(p))`, and `φ_{p,d}` is strictly convex on
  `[0,u₋(p)^d]` and `[u₊(p)^d,1]` and strictly concave on `[u₋(p)^d,u₊(p)^d]` (the closed
  intervals contain the paper's open ones). -/
theorem convexity_defect_zeros {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ z : ℝ, 0 < z → z < 1 →
        HasDerivAt (hpd p d) (((d : ℝ) * (z - rStar d)) / (z * (1 - z) ^ 2)) z) ∧
      hpd p d (rStar d)
          = (d : ℝ) - ((d : ℝ) - 1) * Real.log (((d : ℝ) - 1) * (1 - p) / p) ∧
      StrictAntiOn (hpd p d) (Set.Ioo 0 (rStar d)) ∧
      StrictMonoOn (hpd p d) (Set.Ioo (rStar d) 1) ∧
      (∀ z : ℝ, 0 < z → z < 1 → z ≠ rStar d → hpd p d (rStar d) < hpd p d z) ∧
      (∀ x : ℝ, 0 < x → x < 1 →
        HasDerivAt (deriv (phi p d))
          (hpd p d (x ^ (1 / (d : ℝ))) / ((d : ℝ) ^ 2 * (x ^ (1 / (d : ℝ))) ^ (2 * d - 1))) x ∧
        (0 < deriv (deriv (phi p d)) x ↔ 0 < hpd p d (x ^ (1 / (d : ℝ)))) ∧
        (deriv (deriv (phi p d)) x < 0 ↔ hpd p d (x ^ (1 / (d : ℝ))) < 0) ∧
        (deriv (deriv (phi p d)) x = 0 ↔ hpd p d (x ^ (1 / (d : ℝ))) = 0)) ∧
      (pStar d ≤ p → (∀ z : ℝ, 0 < z → z < 1 → 0 ≤ hpd p d z) ∧
        ConvexOn ℝ (Set.Icc 0 1) (phi p d)) ∧
      (p < pStar d →
        0 < uMinus p d ∧ uMinus p d < rStar d ∧ rStar d < uPlus p d ∧ uPlus p d < 1 ∧
          hpd p d (uMinus p d) = 0 ∧ hpd p d (uPlus p d) = 0 ∧
          (∀ z : ℝ, 0 < z → z < 1 → (hpd p d z = 0 ↔ z = uMinus p d ∨ z = uPlus p d)) ∧
          (∀ z : ℝ, 0 < z → z < uMinus p d → 0 < hpd p d z) ∧
          (∀ z : ℝ, uMinus p d < z → z < uPlus p d → hpd p d z < 0) ∧
          (∀ z : ℝ, uPlus p d < z → z < 1 → 0 < hpd p d z) ∧
          StrictConvexOn ℝ (Set.Icc 0 (uMinus p d ^ d)) (phi p d) ∧
          StrictConcaveOn ℝ (Set.Icc (uMinus p d ^ d) (uPlus p d ^ d)) (phi p d) ∧
          StrictConvexOn ℝ (Set.Icc (uPlus p d ^ d) 1) (phi p d)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := convexity_defect hd hp0 hp1
  refine ⟨h1, h2, h3, h4, h5, fun x hx0 hx1 => ?_, h8, fun hp => ?_⟩
  · have hH := h6 x hx0 hx1
    have hdd : deriv (deriv (phi p d)) x = phi'' p d x := hH.deriv
    have hden : 0 < (d : ℝ) ^ 2 * (x ^ (1 / (d : ℝ))) ^ (2 * d - 1) := by
      have := dpos hd
      have : 0 < x ^ (1 / (d : ℝ)) := Real.rpow_pos_of_pos hx0 _
      positivity
    refine ⟨hH, ?_, ?_, ?_⟩
    · rw [hdd]; exact (h7 x hx0).1
    · rw [hdd]; exact (h7 x hx0).2
    · rw [hdd]
      show hpd p d (x ^ (1 / (d : ℝ))) / ((d : ℝ) ^ 2 * (x ^ (1 / (d : ℝ))) ^ (2 * d - 1)) = 0 ↔ _
      rw [div_eq_zero_iff]
      exact ⟨fun h => h.resolve_right hden.ne', Or.inl⟩
  · obtain ⟨um, up, hum0, humus, hupus, hup1, humz, hupz, hzero, hpos1, hneg, hpos2,
      hc1, hc2, hc3⟩ := h9 hp
    obtain ⟨hU, hV⟩ := uMinus_uPlus_eq_of_zeros hum0 (humus.trans hupus) hup1 hzero
    rw [hU, hV]
    exact ⟨hum0, humus, hupus, hup1, humz, hupz, hzero, hpos1, hneg, hpos2, hc1, hc2, hc3⟩

/-! ### The convex minorant -/

/-- **`lce 0 1 φ_{p,d}` is the convex minorant of `φ_{p,d}`** in the sense of the footnote of
Section 3: it is convex on `[0,1]`, lies below `φ_{p,d}` there, and every convex `g ≤ φ_{p,d}`
on `[0,1]` lies below it on `[0,1]`.  This is what licenses reading "the convex minorant" in
`lem:contact-points` and Theorem 3.1 as `lce 0 1 (phi p d)`. -/
theorem lce_phi_convexMinorant {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ConvexOn ℝ (Set.Icc 0 1) (lce 0 1 (phi p d)) ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, lce 0 1 (phi p d) x ≤ phi p d x) ∧
      ∀ g : ℝ → ℝ, ConvexOn ℝ (Set.Icc 0 1) g → (∀ x ∈ Set.Icc (0:ℝ) 1, g x ≤ phi p d x) →
        ∀ x ∈ Set.Icc (0:ℝ) 1, g x ≤ lce 0 1 (phi p d) x := by
  have hf := phi_continuousOn_Icc hd hp0 hp1
  refine ⟨convexOn_lce zero_le_one hf, fun x hx => lce_le_self zero_le_one hf hx,
    fun g hg hgf x hx => ?_⟩
  rcases hx.1.lt_or_eq with hx0 | hx0
  · rcases hx.2.lt_or_eq with hx1 | hx1
    · exact lce_largest hg hgf ⟨hx0, hx1⟩
    · rw [hx1, lce_right_eq one_pos hf]; exact hgf 1 ⟨zero_le_one, le_rfl⟩
  · rw [← hx0, lce_left_eq one_pos hf]; exact hgf 0 ⟨le_rfl, zero_le_one⟩

/-! ### `lem:contact-points` with named contact points -/

/-- The left contact point `x_a(p)` (`lem:contact-points`): the infimum of the set of
`x ∈ (0,1)` at which the convex minorant of `φ_{p,d}` lies strictly below `φ_{p,d}`.  For
`0 < p < p_*` that set is the open interval `(x_a(p), x_b(p))` (`contactXa_eq_gc`). -/
noncomputable def contactXa (d : ℕ) (p : ℝ) : ℝ :=
  sInf {x : ℝ | x ∈ Set.Ioo (0:ℝ) 1 ∧ lce 0 1 (phi p d) x < phi p d x}

/-- The right contact point `x_b(p)` (`lem:contact-points`): the supremum of the set of
`x ∈ (0,1)` at which the convex minorant of `φ_{p,d}` lies strictly below `φ_{p,d}`. -/
noncomputable def contactXb (d : ℕ) (p : ℝ) : ℝ :=
  sSup {x : ℝ | x ∈ Set.Ioo (0:ℝ) 1 ∧ lce 0 1 (phi p d) x < phi p d x}

/-- For `0 < p < p_*` the convex minorant of `φ_{p,d}` agrees with `φ_{p,d}` at every
`x ∈ [0,1]` outside the open interval between the contacts `u_a(p)^d`, `u_b(p)^d` of a
`GlobalContacts` datum: at `0` and `1` by `lce_left_eq`/`lce_right_eq`, at the contacts by
`gc_lce_at_contacts`, and on the two strictly convex pieces through the supporting lines of
`supportingLine_left_of_convex`/`supportingLine_right_of_convex`. -/
theorem gc_lce_eq_outside {d : ℕ} (hd : 2 ≤ d) (G : GlobalContacts d) {p : ℝ}
    (hp0 : 0 < p) (hp : p < pStar d) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, (x ≤ (G.ua p) ^ d ∨ (G.ub p) ^ d ≤ x) →
      lce 0 1 (phi p d) x = phi p d x := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  have hf := phi_continuousOn_Icc hd hp0 hp1
  obtain ⟨hxa0, hxa_xb, hxb1, -, -, -, -, hconvL, hconvR, -, -, -⟩ := contact_bundle hd G hp0 hp
  obtain ⟨hLa, hLb, -⟩ := gc_lce_at_contacts hd G hp0 hp
  have hxa1 : (G.ua p) ^ d < 1 := hxa_xb.trans hxb1
  have hxb0 : 0 < (G.ub p) ^ d := hxa0.trans hxa_xb
  have hsupp : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      (∀ t ∈ Set.Icc (0:ℝ) 1, phi p d x + deriv (phi p d) x * (t - x) ≤ phi p d t) →
        lce 0 1 (phi p d) x = phi p d x :=
    fun x hx h => (exists_supportingLine_iff_lce_eq (by norm_num) hf hx).mp ⟨_, h⟩
  intro x hx hout
  rcases hout with hle | hge
  · rcases hle.lt_or_eq with hlt | heq
    · rcases hx.1.lt_or_eq with hx0 | hx0
      · exact hsupp x ⟨hx0, hlt.trans hxa1⟩
          (supportingLine_left_of_convex hd hp0 hp1 hx0 hlt hxa1 hconvL (G.support_ua p hp0 hp))
      · rw [← hx0]; exact lce_left_eq (by norm_num) hf
    · rw [heq]; exact hLa
  · rcases hge.lt_or_eq with hlt | heq
    · rcases hx.2.lt_or_eq with hx1 | hx1
      · exact hsupp x ⟨hxb0.trans hlt, hx1⟩
          (supportingLine_right_of_convex hd hp0 hp1 hxb0 hlt hx1 hconvR (G.support_ub p hp0 hp))
      · rw [hx1]; exact lce_right_eq (by norm_num) hf
    · rw [← heq]; exact hLb

/-- For `0 < p < p_*` the named contact points are the `d`-th powers of the contacts of any
`GlobalContacts` datum: the set `{x ∈ (0,1) | lce φ_{p,d} x < φ_{p,d} x}` is exactly the open
interval `(u_a(p)^d, u_b(p)^d)`. -/
theorem contactXa_eq_gc {d : ℕ} (hd : 2 ≤ d) (G : GlobalContacts d) {p : ℝ}
    (hp0 : 0 < p) (hp : p < pStar d) :
    contactXa d p = (G.ua p) ^ d ∧ contactXb d p = (G.ub p) ^ d := by
  obtain ⟨hxa0, hxa_xb, hxb1, -, -, -, -, -, -, hlce, -, -⟩ := contact_bundle hd G hp0 hp
  have hout := gc_lce_eq_outside hd G hp0 hp
  have hset : {x : ℝ | x ∈ Set.Ioo (0:ℝ) 1 ∧ lce 0 1 (phi p d) x < phi p d x}
      = Set.Ioo ((G.ua p) ^ d) ((G.ub p) ^ d) := by
    ext x
    constructor
    · rintro ⟨⟨hx0, hx1⟩, hlt⟩
      by_contra hcon
      rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hcon
      exact absurd (hout x ⟨hx0.le, hx1.le⟩ hcon) hlt.ne
    · rintro ⟨h1, h2⟩
      exact ⟨⟨hxa0.trans h1, h2.trans hxb1⟩, hlce x ⟨h1, h2⟩⟩
  exact ⟨by rw [contactXa, hset, csInf_Ioo hxa_xb], by rw [contactXb, hset, csSup_Ioo hxa_xb]⟩

/-- **`lem:contact-points`**, with the contact points named `contactXa d p`, `contactXb d p`
and the zeros of `h_{p,d}` named `uMinus p d`, `uPlus p d`.

For every `p ∈ (0,p_*)`:
* `0 < x_a(p) < u₋(p)^d < u₊(p)^d < x_b(p) < 1`;
* the equal-slope equation `eq:contact-equal-slopes` and the chord identity
  `eq:contact-chord-identity` hold;
* `(x_a(p), x_b(p))` is the only pair with `0 < x₁ < u₋(p)^d`, `u₊(p)^d < x₂ < 1` satisfying
  these two equations;
* the convex minorant `lce 0 1 φ_{p,d}` agrees with `φ_{p,d}` at every `x ∈ [0,1]` with
  `x ≤ x_a(p)` or `x_b(p) ≤ x` (the contact points themselves included), is the straight
  segment joining `(x_a(p), φ_{p,d}(x_a(p)))` and `(x_b(p), φ_{p,d}(x_b(p)))` on
  `[x_a(p), x_b(p)]`, and lies strictly below `φ_{p,d}` on `(x_a(p), x_b(p))`.

Moreover `p ↦ x_a(p)` and `p ↦ x_b(p)` are analytic on `(0,p_*)` with `dx_a/dp > 0` and
`dx_b/dp < 0`. -/
theorem contact_points {d : ℕ} (hd : 2 ≤ d) :
    (∀ p : ℝ, 0 < p → p < pStar d →
      (0 < contactXa d p ∧ contactXa d p < uMinus p d ^ d ∧ uMinus p d ^ d < uPlus p d ^ d ∧
        uPlus p d ^ d < contactXb d p ∧ contactXb d p < 1) ∧
      deriv (phi p d) (contactXa d p) = deriv (phi p d) (contactXb d p) ∧
      phi p d (contactXb d p) - phi p d (contactXa d p)
        = deriv (phi p d) (contactXa d p) * (contactXb d p - contactXa d p) ∧
      (∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < uMinus p d ^ d → uPlus p d ^ d < x₂ → x₂ < 1 →
        deriv (phi p d) x₁ = deriv (phi p d) x₂ →
        phi p d x₂ - phi p d x₁ = deriv (phi p d) x₁ * (x₂ - x₁) →
        x₁ = contactXa d p ∧ x₂ = contactXb d p) ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, (x ≤ contactXa d p ∨ contactXb d p ≤ x) →
        lce 0 1 (phi p d) x = phi p d x) ∧
      (∀ x ∈ Set.Icc (contactXa d p) (contactXb d p),
        lce 0 1 (phi p d) x = phi p d (contactXa d p) +
          (phi p d (contactXb d p) - phi p d (contactXa d p)) /
            (contactXb d p - contactXa d p) * (x - contactXa d p)) ∧
      (∀ x ∈ Set.Ioo (contactXa d p) (contactXb d p), lce 0 1 (phi p d) x < phi p d x)) ∧
    AnalyticOnNhd ℝ (contactXa d) (Set.Ioo 0 (pStar d)) ∧
    AnalyticOnNhd ℝ (contactXb d) (Set.Ioo 0 (pStar d)) ∧
    (∀ p ∈ Set.Ioo 0 (pStar d), 0 < deriv (contactXa d) p) ∧
    (∀ p ∈ Set.Ioo 0 (pStar d), deriv (contactXb d) p < 0) := by
  obtain ⟨G⟩ := exists_globalContacts hd
  have hd0 : d ≠ 0 := by omega
  have hevA : ∀ p ∈ Set.Ioo 0 (pStar d), contactXa d =ᶠ[𝓝 p] (fun q => G.ua q ^ d) := by
    intro p hp
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with q hq
    exact (contactXa_eq_gc hd G hq.1 hq.2).1
  have hevB : ∀ p ∈ Set.Ioo 0 (pStar d), contactXb d =ᶠ[𝓝 p] (fun q => G.ub q ^ d) := by
    intro p hp
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with q hq
    exact (contactXa_eq_gc hd G hq.1 hq.2).2
  refine ⟨fun p hp0 hp => ?_,
    fun p hp => ((G.analytic_ua p hp.1 hp.2).pow d).congr (hevA p hp).symm,
    fun p hp => ((G.analytic_ub p hp.1 hp.2).pow d).congr (hevB p hp).symm, fun p hp => ?_,
    fun p hp => ?_⟩
  · have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
    have hf := phi_continuousOn_Icc hd hp0 hp1
    obtain ⟨hXa, hXb⟩ := contactXa_eq_gc hd G hp0 hp
    have hout := gc_lce_eq_outside hd G hp0 hp
    rw [hXa, hXb]
    obtain ⟨hxa0, hxa_xb, hxb1, -, hHxb, hchord, -, -, -, hlce, -, -⟩ := contact_bundle hd G hp0 hp
    obtain ⟨hLa, hLb, -⟩ := gc_lce_at_contacts hd G hp0 hp
    obtain ⟨hua0, huas, hubs, hub1, hcfG, hhua, hhub⟩ := G.contact p hp0 hp
    obtain ⟨-, -, -, -, -, -, -, hZ⟩ := convexity_defect_zeros hd hp0 hp1
    obtain ⟨hum0, humus, hupus, hup1, humz, hupz, -, hpos1, hneg, hpos2, -, -, -⟩ := hZ hp
    have hup0 : 0 < uPlus p d := hum0.trans (humus.trans hupus)
    have hua_um : G.ua p < uMinus p d := by
      by_contra hcon
      push Not at hcon
      rcases hcon.lt_or_eq with h | h
      · linarith [hneg (G.ua p) h (huas.trans hupus)]
      · rw [← h] at hhua; linarith
    have hup_ub : uPlus p d < G.ub p := by
      by_contra hcon
      push Not at hcon
      rcases hcon.lt_or_eq with h | h
      · linarith [hneg (G.ub p) (humus.trans hubs) h]
      · rw [h] at hhub; linarith
    have humup : uMinus p d ^ d < uPlus p d ^ d :=
      pow_lt_pow_left₀ (humus.trans hupus) hum0.le hd0
    refine ⟨⟨hxa0, pow_lt_pow_left₀ hua_um hua0.le hd0, humup,
      pow_lt_pow_left₀ hup_ub hup0.le hd0, hxb1⟩, hHxb.deriv.symm, by linarith [hchord], ?_,
      hout, ?_, hlce⟩
    · intro x₁ x₂ hx₁0 hx₁m hx₂p hx₂1 hslope hchord'
      have hzpos : (0:ℝ) < 1 / (d:ℝ) := by have := dpos hd; positivity
      have hx₂0 : 0 < x₂ := (pow_pos hup0 d).trans hx₂p
      have hum_eq : Real.rpow (uMinus p d ^ d) (1/(d:ℝ)) = uMinus p d := by
        rw [one_div]; exact Real.pow_rpow_inv_natCast hum0.le hd0
      have hup_eq : Real.rpow (uPlus p d ^ d) (1/(d:ℝ)) = uPlus p d := by
        rw [one_div]; exact Real.pow_rpow_inv_natCast hup0.le hd0
      have ha0 : 0 < Real.rpow x₁ (1/(d:ℝ)) := Real.rpow_pos_of_pos hx₁0 _
      have ha_um : Real.rpow x₁ (1/(d:ℝ)) < uMinus p d := by
        rw [← hum_eq]; exact Real.rpow_lt_rpow hx₁0.le hx₁m hzpos
      have hup_b : uPlus p d < Real.rpow x₂ (1/(d:ℝ)) := by
        rw [← hup_eq]; exact Real.rpow_lt_rpow (pow_nonneg hup0.le d) hx₂p hzpos
      have hb1 : Real.rpow x₂ (1/(d:ℝ)) < 1 := by
        have h : Real.rpow x₂ (1/(d:ℝ)) < Real.rpow 1 (1/(d:ℝ)) :=
          Real.rpow_lt_rpow hx₂0.le hx₂1 hzpos
        simpa using h
      have h12 : x₁ < x₂ := hx₁m.trans (humup.trans hx₂p)
      have hcf := contactF_of_phi_contacts hd hp0 hp1 hx₁0 h12 hx₂1 hslope hchord'
      obtain ⟨hae, hbe⟩ := contact_unique hd hp0 hp ha0 (ha_um.trans humus)
        (hupus.trans hup_b) hb1 hcf (hpos1 _ ha0 ha_um) (hpos2 _ hup_b hb1)
        hua0 huas hubs hub1 hcfG hhua hhub
      have hpa : (Real.rpow x₁ (1/(d:ℝ))) ^ d = x₁ := by
        rw [one_div]; exact Real.rpow_inv_natCast_pow hx₁0.le hd0
      have hpb : (Real.rpow x₂ (1/(d:ℝ))) ^ d = x₂ := by
        rw [one_div]; exact Real.rpow_inv_natCast_pow hx₂0.le hd0
      exact ⟨by rw [← hpa, hae], by rw [← hpb, hbe]⟩
    · intro x hx
      rw [lce_affine_on_component hf hxa_xb hxa0 hxb1 hlce hLa hLb x hx, hLa, hLb]
  · obtain ⟨hua0, -⟩ := G.contact p hp.1 hp.2
    have hH : HasDerivAt (fun q => G.ua q ^ d) ((d:ℝ) * G.ua p ^ (d - 1) * deriv G.ua p) p :=
      (G.analytic_ua p hp.1 hp.2).differentiableAt.hasDerivAt.pow d
    rw [(hevA p hp).deriv_eq, hH.deriv]
    exact mul_pos (mul_pos (dpos hd) (pow_pos hua0 _)) (G.deriv_ua_pos p hp.1 hp.2)
  · obtain ⟨-, -, hubs, -⟩ := G.contact p hp.1 hp.2
    have hub0 : 0 < G.ub p := (rStar_pos hd).trans hubs
    have hH : HasDerivAt (fun q => G.ub q ^ d) ((d:ℝ) * G.ub p ^ (d - 1) * deriv G.ub p) p :=
      (G.analytic_ub p hp.1 hp.2).differentiableAt.hasDerivAt.pow d
    rw [(hevB p hp).deriv_eq, hH.deriv]
    exact mul_neg_of_pos_of_neg (mul_pos (dpos hd) (pow_pos hub0 _)) (G.deriv_ub_neg p hp.1 hp.2)

/-! ### `lem:contact-point-limits` -/

/-- **`lem:contact-point-limits`**, for `u_a(p) := x_a(p)^{1/d}` and `u_b(p) := x_b(p)^{1/d}`
built from the named contact points: as `p ↑ p_*` both tend to `r_*`; as `p ↓ 0`, `u_a(p) → 0`
and `u_b(p) → 1`.  The monotone approach (`u_a ↓ 0`, `u_b ↑ 1`) is recorded as strict
monotonicity of `u_a` and strict antitonicity of `u_b` on `(0,p_*)`. -/
theorem contact_point_limits {d : ℕ} (hd : 2 ≤ d) :
    Tendsto (fun p => contactXa d p ^ (1 / (d:ℝ))) (𝓝[<] (pStar d)) (𝓝 (rStar d)) ∧
    Tendsto (fun p => contactXb d p ^ (1 / (d:ℝ))) (𝓝[<] (pStar d)) (𝓝 (rStar d)) ∧
    Tendsto (fun p => contactXa d p ^ (1 / (d:ℝ))) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun p => contactXb d p ^ (1 / (d:ℝ))) (𝓝[>] 0) (𝓝 1) ∧
    StrictMonoOn (fun p => contactXa d p ^ (1 / (d:ℝ))) (Set.Ioo 0 (pStar d)) ∧
    StrictAntiOn (fun p => contactXb d p ^ (1 / (d:ℝ))) (Set.Ioo 0 (pStar d)) := by
  obtain ⟨G⟩ := exists_globalContacts hd
  have hd0 : d ≠ 0 := by omega
  have hEa : Set.EqOn G.ua (fun p => contactXa d p ^ (1 / (d:ℝ))) (Set.Ioo 0 (pStar d)) := by
    intro p hp
    obtain ⟨hua0, -⟩ := G.contact p hp.1 hp.2
    simp only
    rw [(contactXa_eq_gc hd G hp.1 hp.2).1, one_div, Real.pow_rpow_inv_natCast hua0.le hd0]
  have hEb : Set.EqOn G.ub (fun p => contactXb d p ^ (1 / (d:ℝ))) (Set.Ioo 0 (pStar d)) := by
    intro p hp
    obtain ⟨-, -, hubs, -⟩ := G.contact p hp.1 hp.2
    simp only
    rw [(contactXa_eq_gc hd G hp.1 hp.2).2, one_div,
      Real.pow_rpow_inv_natCast ((rStar_pos hd).trans hubs).le hd0]
  have hlt : Set.Ioo 0 (pStar d) ∈ 𝓝[<] (pStar d) := Ioo_mem_nhdsLT (pStar_pos hd)
  have hgt : Set.Ioo 0 (pStar d) ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (pStar_pos hd)
  exact ⟨G.ua_lim_pStar.congr' (eventuallyEq_of_mem hlt hEa),
    G.ub_lim_pStar.congr' (eventuallyEq_of_mem hlt hEb),
    G.ua_lim_zero.congr' (eventuallyEq_of_mem hgt hEa),
    G.ub_lim_zero.congr' (eventuallyEq_of_mem hgt hEb),
    G.mono_ua.congr hEa, G.mono_ub.congr hEb⟩

/-! ### Theorem 3.1 -/

/-- Condition (M2) of Theorem 3.1 in its convex-minorant form, for every
`r ∈ (0,1)` (the exceptional density included): `(r^d, J_p(r))` lies on the convex minorant
`lce 0 1 φ_{p,d}` iff `p ≥ pcGlobal d r`.  This is `lz_boundary_M2_global` read through
`exists_supportingLine_iff_lce_eq`. -/
theorem lz_boundary_M2_lce {d : ℕ} (hd : 2 ≤ d) {r p : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    lce 0 1 (phi p d) (r ^ d) = Jp p r ↔ pcGlobal d r ≤ p := by
  have hrIoo : r ^ d ∈ Set.Ioo (0:ℝ) 1 := ⟨pow_pos hr0 d, pow_lt_one₀ hr0.le hr1 (by omega)⟩
  rw [← lz_boundary_M2_global hd hr0 hr1 hp0 hp1, Jp_eq_phi_pow hd hr0.le,
    ← exists_supportingLine_iff_lce_eq (by norm_num) (phi_continuousOn_Icc hd hp0 hp1) hrIoo]

/-- The `quadSep` field of a Lubetzky–Zhao boundary arc ((M5) of Theorem 3.1 on
compact subsets of the arc), rewritten in the `x`-coordinate with the tangent line
`ℓ_r(x) = φ_{pc(r),d}(r^d) + φ_{pc(r),d}'(r^d)(x - r^d)` and the global maps `pcGlobal`,
`smGlobal`. -/
theorem LZBoundaryArc.quadSep_x {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {K : Set ℝ}
    (hKU : K ⊆ M.U) (hK : IsCompact K) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ r ∈ K, ∀ x ∈ Set.Icc (0:ℝ) 1,
      γ * (min |x - r ^ d| |x - smGlobal d r ^ d|) ^ 2 ≤
        phi (pcGlobal d r) d x - (phi (pcGlobal d r) d (r ^ d) +
          deriv (phi (pcGlobal d r) d) (r ^ d) * (x - r ^ d)) := by
  obtain ⟨γ, hγ, hq⟩ := M.quadSep K hKU hK
  refine ⟨γ, hγ, fun r hr x hx => ?_⟩
  have hrU := hKU hr
  obtain ⟨hpc0, hpcr, hr1, -⟩ := M.ordering r hrU
  have hr0 : 0 < r := hpc0.trans hpcr
  have hd0 : d ≠ 0 := by omega
  have hu0 : (0:ℝ) ≤ Real.rpow x (1/(d:ℝ)) := Real.rpow_nonneg hx.1 _
  have hu1 : Real.rpow x (1/(d:ℝ)) ≤ 1 := Real.rpow_le_one hx.1 hx.2 (by positivity)
  have hud : (Real.rpow x (1/(d:ℝ))) ^ d = x := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow hx.1 hd0
  have h := hq r hr (Real.rpow x (1/(d:ℝ))) ⟨hu0, hu1⟩
  rw [hud, ← phi_eq_Jp_rpow, Jp_eq_phi_pow hd hr0.le,
    slope_eq_deriv_phi (pc := M.pc) hd hpc0 (hpcr.trans hr1) hr0 hr1] at h
  rwa [pcGlobal_eq_pc hd M hrU, smGlobal_eq_sm hd M hrU]

/-- Condition (M5) of Theorem 3.1 for an arbitrary compact
`K ⊆ (0,1) ∖ {r_*}`: cover `K` by closed balls lying inside boundary arcs
(`lz_boundary_arcs`), apply `LZBoundaryArc.quadSep_x` on each, and take the smallest
constant (`IsCompact.induction_on`). -/
theorem lz_boundary_quadSep {d : ℕ} (hd : 2 ≤ d) {K : Set ℝ}
    (hKS : K ⊆ Set.Ioo 0 1 \ {rStar d}) (hK : IsCompact K) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ r ∈ K, ∀ x ∈ Set.Icc (0:ℝ) 1,
      γ * (min |x - r ^ d| |x - smGlobal d r ^ d|) ^ 2 ≤
        phi (pcGlobal d r) d x - (phi (pcGlobal d r) d (r ^ d) +
          deriv (phi (pcGlobal d r) d) (r ^ d) * (x - r ^ d)) := by
  refine hK.induction_on (p := fun s => ∃ γ : ℝ, 0 < γ ∧ ∀ r ∈ s, ∀ x ∈ Set.Icc (0:ℝ) 1,
      γ * (min |x - r ^ d| |x - smGlobal d r ^ d|) ^ 2 ≤
        phi (pcGlobal d r) d x - (phi (pcGlobal d r) d (r ^ d) +
          deriv (phi (pcGlobal d r) d) (r ^ d) * (x - r ^ d))) ?_ ?_ ?_ ?_
  · exact ⟨1, one_pos, fun r hr => hr.elim⟩
  · rintro s t hst ⟨γ, hγ, h⟩
    exact ⟨γ, hγ, fun r hr => h r (hst hr)⟩
  · rintro s t ⟨γ₁, hγ₁, h₁⟩ ⟨γ₂, hγ₂, h₂⟩
    refine ⟨min γ₁ γ₂, lt_min hγ₁ hγ₂, fun r hr x hx => ?_⟩
    have hsq : 0 ≤ (min |x - r ^ d| |x - smGlobal d r ^ d|) ^ 2 := sq_nonneg _
    rcases hr with hr | hr
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hsq) (h₁ r hr x hx)
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hsq) (h₂ r hr x hx)
  · intro r hr
    obtain ⟨⟨hr0, hr1⟩, hexc⟩ := hKS hr
    obtain ⟨M, hrU, -⟩ := lz_boundary_arcs hd hr0 hr1 hexc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp M.isOpen_U r hrU
    exact ⟨Metric.closedBall r (ε / 2),
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds r (half_pos hε)),
      M.quadSep_x hd ((Metric.closedBall_subset_ball (half_lt_self hε)).trans hball)
        (isCompact_closedBall r (ε / 2))⟩

/-- **Theorem 3.1 (Lubetzky–Zhao boundary)**, for the named global maps
`pc = pcGlobal d` and `sm = smGlobal d`.  Write `S = (0,1) ∖ {r_*}`.

* `pc` and `sm` are analytic on `S` and map `S` into `(0,1)`.
* For every `r ∈ S`, with `x_r = r^d`, `x_s = sm(r)^d` and the tangent line
  `ℓ_r(x) = φ_{pc(r),d}(x_r) + φ_{pc(r),d}'(x_r)(x - x_r)`:
  (M1) `0 < pc(r) < min(r, p_*)` and `sm(r) ≠ r`;
  (M2) for every `p ∈ (0,1)`, the point `(r^d, J_p(r))` lies on the convex minorant of
  `φ_{p,d}` (i.e. `lce 0 1 φ_{p,d}` takes the value `J_p(r)` at `r^d`, see
  `lce_phi_convexMinorant`) iff `p ≥ pc(r)`;
  (M3) `ℓ_r(x) ≤ φ_{pc(r),d}(x)` for all `x ∈ [0,1]`;
  (M4) equality in (M3) holds exactly when `x ∈ {x_r, x_s}`.
* (M5) For every compact `K ⊆ S` there is `γ_K > 0` with
  `φ_{pc(r),d}(x) - ℓ_r(x) ≥ γ_K dist(x, {r^d, sm(r)^d})²` for all `r ∈ K`, `x ∈ [0,1]`
  (the distance to the two-point set is `min |x - r^d| |x - sm(r)^d|`).  (M5) does not refer to
  the `r` of (M1)–(M4), so it is stated as a separate conjunct.
* The continuous extension: `pc(r_*) = p_*`, `sm(r_*) = r_*`, both maps are continuous on
  `(0,1)`, and (M2) holds for every `r ∈ (0,1)`. -/
theorem lz_boundary {d : ℕ} (hd : 2 ≤ d) :
    AnalyticOnNhd ℝ (pcGlobal d) (Set.Ioo 0 1 \ {rStar d}) ∧
    AnalyticOnNhd ℝ (smGlobal d) (Set.Ioo 0 1 \ {rStar d}) ∧
    Set.MapsTo (pcGlobal d) (Set.Ioo 0 1 \ {rStar d}) (Set.Ioo 0 1) ∧
    Set.MapsTo (smGlobal d) (Set.Ioo 0 1 \ {rStar d}) (Set.Ioo 0 1) ∧
    (∀ r ∈ Set.Ioo (0:ℝ) 1 \ {rStar d},
      -- (M1)
      (0 < pcGlobal d r ∧ pcGlobal d r < min r (pStar d) ∧ smGlobal d r ≠ r) ∧
      -- (M2)
      (∀ p ∈ Set.Ioo (0:ℝ) 1, lce 0 1 (phi p d) (r ^ d) = Jp p r ↔ pcGlobal d r ≤ p) ∧
      -- (M3)
      (∀ x ∈ Set.Icc (0:ℝ) 1,
        phi (pcGlobal d r) d (r ^ d) + deriv (phi (pcGlobal d r) d) (r ^ d) * (x - r ^ d)
          ≤ phi (pcGlobal d r) d x) ∧
      -- (M4)
      (∀ x ∈ Set.Icc (0:ℝ) 1,
        phi (pcGlobal d r) d (r ^ d) + deriv (phi (pcGlobal d r) d) (r ^ d) * (x - r ^ d)
          = phi (pcGlobal d r) d x ↔ x = r ^ d ∨ x = smGlobal d r ^ d)) ∧
    -- (M5)
    (∀ K : Set ℝ, K ⊆ Set.Ioo 0 1 \ {rStar d} → IsCompact K →
      ∃ γ : ℝ, 0 < γ ∧ ∀ r ∈ K, ∀ x ∈ Set.Icc (0:ℝ) 1,
        γ * (min |x - r ^ d| |x - smGlobal d r ^ d|) ^ 2 ≤
          phi (pcGlobal d r) d x - (phi (pcGlobal d r) d (r ^ d) +
            deriv (phi (pcGlobal d r) d) (r ^ d) * (x - r ^ d))) ∧
    -- the continuous extension to `r_*`
    pcGlobal d (rStar d) = pStar d ∧ smGlobal d (rStar d) = rStar d ∧
    ContinuousOn (pcGlobal d) (Set.Ioo 0 1) ∧ ContinuousOn (smGlobal d) (Set.Ioo 0 1) ∧
    (∀ r ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ Set.Ioo (0:ℝ) 1,
      lce 0 1 (phi p d) (r ^ d) = Jp p r ↔ pcGlobal d r ≤ p) := by
  have hM2 : ∀ r ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ Set.Ioo (0:ℝ) 1,
      lce 0 1 (phi p d) (r ^ d) = Jp p r ↔ pcGlobal d r ≤ p :=
    fun r hr p hp => lz_boundary_M2_lce hd hr.1 hr.2 hp.1 hp.2
  refine ⟨fun r hr => analyticAt_pcGlobal hd hr.1.1 hr.1.2 hr.2,
    fun r hr => analyticAt_smGlobal hd hr.1.1 hr.1.2 hr.2,
    fun r hr => ⟨(pcGlobal_pos_le hd hr.1.1 hr.1.2).1,
      (pcGlobal_pos_le hd hr.1.1 hr.1.2).2.trans_lt (pStar_lt_one hd)⟩,
    fun r hr => smGlobal_mem_Ioo hd hr.1.1 hr.1.2, fun r hr => ?_,
    fun K hKS hK => lz_boundary_quadSep hd hKS hK, pcGlobal_rStar hd, smGlobal_rStar hd,
    continuousOn_pcGlobal hd, continuousOn_smGlobal hd, hM2⟩
  obtain ⟨⟨hr0, hr1⟩, hexc⟩ := hr
  obtain ⟨M, hrU, -⟩ := lz_boundary_arcs hd hr0 hr1 hexc
  obtain ⟨hpc0, hpcr, -, hsmne, -, -⟩ := M.ordering r hrU
  have hpcs := M.pcLtPStar r hrU
  obtain ⟨hsupp, htouch⟩ := M.contact_data hd hrU
  rw [slope_eq_deriv_phi (pc := M.pc) hd hpc0 (hpcr.trans hr1) hr0 hr1] at hsupp htouch
  obtain ⟨γ, hγ, hq⟩ := M.quadSep_x hd (K := {r}) (Set.singleton_subset_iff.mpr hrU)
    isCompact_singleton
  have hq' := hq r rfl
  refine ⟨⟨?_, ?_, ?_⟩, hM2 r ⟨hr0, hr1⟩, ?_, ?_⟩
  · rw [pcGlobal_eq_pc hd M hrU]; exact hpc0
  · rw [pcGlobal_eq_pc hd M hrU]; exact lt_min hpcr hpcs
  · rw [smGlobal_eq_sm hd M hrU]; exact hsmne
  · rw [pcGlobal_eq_pc hd M hrU]; exact hsupp
  · rw [pcGlobal_eq_pc hd M hrU, smGlobal_eq_sm hd M hrU] at hq' ⊢
    intro x hx
    constructor
    · intro heq
      have h := hq' x hx
      rw [heq, sub_self] at h
      have hm0 : 0 ≤ min |x - r ^ d| |x - M.sm r ^ d| := le_min (abs_nonneg _) (abs_nonneg _)
      have hsq : (min |x - r ^ d| |x - M.sm r ^ d|) ^ 2 = 0 :=
        le_antisymm (by nlinarith [h, hγ, hm0]) (sq_nonneg _)
      have hmin0 : min |x - r ^ d| |x - M.sm r ^ d| = 0 := pow_eq_zero_iff two_ne_zero |>.mp hsq
      rcases min_cases |x - r ^ d| |x - M.sm r ^ d| with ⟨he, -⟩ | ⟨he, -⟩
      · left; rwa [he, abs_eq_zero, sub_eq_zero] at hmin0
      · right; rwa [he, abs_eq_zero, sub_eq_zero] at hmin0
    · rintro (h | h) <;> subst h
      · ring
      · exact htouch

end UpperTailOptimizers
