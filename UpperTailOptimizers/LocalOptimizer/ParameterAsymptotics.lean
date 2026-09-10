import UpperTailOptimizers.LocalOptimizer.Analytic

/-!
# Section 6, `rmk:bipodal-parameter-expansions`: the shape of the optimizer near the phase boundary

`rmk:bipodal-parameter-expansions` of `paper/bipodal_optimizer.tex` describes how the exceptional (small) pode of
the bipodal optimizer `W_{p,r}` appears as `p` drops below the Lubetzky–Zhao boundary `pc(r)`.
Writing `δ_*(p,r) = r - e(W_{p,r})` for the edge-density deficit and `z = ζ_d(r)` for the
boundary value of the Kenyon–Radin–Ren–Sadun cross density, the remark asserts

* `c(p,r) = λ(p,r) / (2 D_d(r,z) A_H(r)) + O(λ²)`         (eq. `c-expansion-paper`),
* `q₂₂(p,r) = r - (z^d - r^d)/(d r^{d-1} D_d(r,z) A_H(r)) · λ(p,r) + O(λ²)`
  (eq. `q22-expansion-paper`),
* `q₁₂(p,r) = z + O(λ)` and `q₁₁(p,r) = q₁₁⁰(r) + O(λ)`.

The derivation has four steps, mirrored by the five scalar lemmas of this file.

1. **`krrs_edge_linearization`** (eq. `remark-edge-linearization`).  The two-block edge-density
   formula is *exact*, `e = c²q₁₁ + 2c(1-c)q₁₂ + (1-c)²q₂₂`; rewriting it as
   `q₂₂ + 2c(q₁₂-q₂₂) + c²(q₁₁-2q₁₂+q₂₂)` and using the a-priori bounds
   `|c|, |q₂₂-r|, |q₁₂-z| = O(δ_*)` gives `-δ_* = (q₂₂-r) + 2(z-r)c + O(δ_*²)`.
2. **`krrs_H_linearization`** (eq. `remark-H-linearization`).  The `H`-density constraint is
   linearised with the Section-5 polynomial estimate `tBip_linearization`; the only extra step
   is the swap `q₁₂^d → z^d`, which costs `n d L² δ_*²`.
3. **`krrs_eliminate`**.  Eliminating `q₂₂ - r` between the two linearisations, using the
   handshake `n d = 2m`, produces the paper's `δ_* = 2 D_d(r,z) c + O(δ_*²)`.
4. **`c_expansion_bound` / `q22_expansion_bound`**.  Substituting
   `δ_* = λ/A_H + O(λ²)` (`thm:local-optimizer-structure`) converts the `δ_*`-expansions into the `λ`-expansions.

`parameter_asymptotics` is the assembly.  Everything it needs about the Kenyon–Radin–Ren–Sadun
parameter maps — that they exist as *analytic* maps of `(ε, τ-ε^m)`, that their boundary values
are `c(r,0)=0`, `q₂₂(r,0)=r`, `q₁₂(r,0)=ζ_d(r) ≠ r`, that they describe a *concrete* optimizer,
and the a-priori Lipschitz bounds — is exported by `bipodal_family`, so this file adds no axiom
and calls the Section-5 chart only through that theorem.

**Two conventions inherited from `bipodal_family`.**  (i) `ζ_d(r)` and `q₁₁⁰(r)` have no
canonical name in the development: `kenyonRadinRenSadunAnalytic` returns the parameter maps
existentially, so the paper's boundary values are rendered as `q12 r 0` and `q11 r 0` *under the
same existential binder* as the maps themselves.  (ii) The optimizer is described through the
concrete two-block graphon `B` that realises the parameters, together with the exact edge
identity `e(W) = ε` valid for *every* optimizer.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set Filter Topology

/-! ### Scalar helpers -/

/-- `|a·b| ≤ A·B` from `|a| ≤ A`, `|b| ≤ B`. -/
private theorem abs_mul_le_mul {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) (le_trans (abs_nonneg a) ha)

/-- Triangle inequality in the form used to swap one summand for another. -/
private theorem abs_le_add_abs_sub (x y : ℝ) : |y| ≤ |x| + |x - y| := by
  have h : x - (x - y) = y := by ring
  calc |y| = |x - (x - y)| := by rw [h]
    _ ≤ |x| + |x - y| := abs_sub _ _

/-- From `|x| ≤ L·|δ|` one gets `x² ≤ L²·δ²`. -/
private theorem sq_le_of_abs_le {x L delta : ℝ} (h : |x| ≤ L * |delta|) :
    x ^ 2 ≤ L ^ 2 * delta ^ 2 := by
  have h2 : |x| * |x| ≤ (L * |delta|) * (L * |delta|) :=
    mul_self_le_mul_self (abs_nonneg x) h
  rw [abs_mul_abs_self] at h2
  have hq : (L * |delta|) * (L * |delta|) = L ^ 2 * delta ^ 2 := by
    rw [show (L * |delta|) * (L * |delta|) = L ^ 2 * |delta| ^ 2 by ring, sq_abs]
  rw [hq, ← pow_two] at h2
  exact h2

/-! ### Step 1: the edge-density linearisation -/

/-- **Eq. `remark-edge-linearization`.**  The two-block edge-density identity
`e = c²q₁₁ + 2c(1-c)q₁₂ + (1-c)²q₂₂`, combined with the a-priori bounds
`|c| ≤ L|δ|`, `|q₂₂-r| ≤ L|δ|`, `|q₁₂-z| ≤ L|δ|` and `e = r - δ`, gives

`-δ = (q₂₂ - r) + 2(z - r)c + O(δ²)`,

with the explicit constant `8L²`.  The edge-density formula being exact, the only "expansion"
is the discarding of the two second-order terms `2c((q₁₂-z)-(q₂₂-r))` and
`c²(q₁₁-2q₁₂+q₂₂)`. -/
theorem krrs_edge_linearization {r delta z c q11 q12 q22 L E : ℝ}
    (h11 : q11 ∈ Set.Icc (0:ℝ) 1) (h12 : q12 ∈ Set.Icc (0:ℝ) 1)
    (h22 : q22 ∈ Set.Icc (0:ℝ) 1)
    (hcb : |c| ≤ L * |delta|) (h22b : |q22 - r| ≤ L * |delta|) (h12b : |q12 - z| ≤ L * |delta|)
    (hedge : c ^ 2 * q11 + 2 * c * (1 - c) * q12 + (1 - c) ^ 2 * q22 = r - delta)
    (hE : 8 * L ^ 2 ≤ E) :
    |(-delta) - ((q22 - r) + 2 * (z - r) * c)| ≤ E * delta ^ 2 := by
  have hkey : (-delta) - ((q22 - r) + 2 * (z - r) * c)
      = 2 * c * ((q12 - z) - (q22 - r)) + c * c * (q11 - 2 * q12 + q22) := by
    linear_combination -hedge
  -- the two second-order terms
  have hb1 : |2 * c * ((q12 - z) - (q22 - r))| ≤ 4 * L ^ 2 * delta ^ 2 := by
    have ha : |2 * c| ≤ 2 * (L * |delta|) := by
      rw [abs_mul, abs_two]; linarith
    have hb : |(q12 - z) - (q22 - r)| ≤ 2 * (L * |delta|) :=
      le_trans (abs_sub _ _) (by linarith)
    have := abs_mul_le_mul ha hb
    calc |2 * c * ((q12 - z) - (q22 - r))| ≤ 2 * (L * |delta|) * (2 * (L * |delta|)) := by
          rw [show 2 * c * ((q12 - z) - (q22 - r)) = (2 * c) * ((q12 - z) - (q22 - r)) by ring]
          exact this
      _ = 4 * L ^ 2 * |delta| ^ 2 := by ring
      _ = 4 * L ^ 2 * delta ^ 2 := by rw [sq_abs]
  have hb2 : |c * c * (q11 - 2 * q12 + q22)| ≤ 4 * L ^ 2 * delta ^ 2 := by
    have ha : |c * c| ≤ (L * |delta|) * (L * |delta|) := abs_mul_le_mul hcb hcb
    have hb : |q11 - 2 * q12 + q22| ≤ 4 := by
      have := abs_le.mpr (⟨by linarith [h11.1, h11.2, h12.1, h12.2, h22.1, h22.2],
        by linarith [h11.1, h11.2, h12.1, h12.2, h22.1, h22.2]⟩ :
          -(4:ℝ) ≤ q11 - 2 * q12 + q22 ∧ q11 - 2 * q12 + q22 ≤ 4)
      exact this
    have := abs_mul_le_mul ha hb
    calc |c * c * (q11 - 2 * q12 + q22)| ≤ (L * |delta|) * (L * |delta|) * 4 := this
      _ = 4 * L ^ 2 * |delta| ^ 2 := by ring
      _ = 4 * L ^ 2 * delta ^ 2 := by rw [sq_abs]
  rw [hkey]
  calc |2 * c * ((q12 - z) - (q22 - r)) + c * c * (q11 - 2 * q12 + q22)|
      ≤ |2 * c * ((q12 - z) - (q22 - r))| + |c * c * (q11 - 2 * q12 + q22)| := abs_add_le _ _
    _ ≤ 8 * L ^ 2 * delta ^ 2 := by linarith
    _ ≤ E * delta ^ 2 := by nlinarith [sq_nonneg delta]

/-! ### Step 2: the `H`-density linearisation -/

/-- **Eq. `remark-H-linearization`.**  With the constraint `t(H, ·) = r^m` imposed, the
Section-5 polynomial estimate `tBip_linearization` says

`m r^{m-1}(q₂₂ - r) + n(z^d r^{m-d} - r^m) c = O(δ²)`,

where `n = |V(H)|`, `m = |E(H)|`.  (Since `n d = 2m` for a `d`-regular `H`, the second
coefficient is the paper's `(2m/d) r^{m-d}(z^d - r^d)`.)

The difference from the Section-5 model `tBip_linearization` is the last step: there the cross
density was *fixed*, whereas here `q₁₂` is itself a Kenyon–Radin–Ren–Sadun parameter moving with
`δ`, so the cross factor has to be swapped from `q₁₂^d` to its boundary value `z^d`, at the cost
of `n d L² δ²` (`abs_pow_sub_pow_le`). -/
theorem krrs_H_linearization {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d)
    {r delta z c q11 q12 q22 L E : ℝ}
    (h11 : q11 ∈ Set.Icc (0:ℝ) 1) (h12 : q12 ∈ Set.Icc (0:ℝ) 1)
    (h22 : q22 ∈ Set.Icc (0:ℝ) 1) (hr : r ∈ Set.Icc (0:ℝ) 1) (hz : z ∈ Set.Icc (0:ℝ) 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hcb : c ≤ L * |delta|) (h22b : |q22 - r| ≤ L * |delta|) (h12b : |q12 - z| ≤ L * |delta|)
    (ht : tBip H q11 q12 q22 c = r ^ H.edgeFinset.card)
    (hE : ((H.edgeFinset.card : ℝ) ^ 2
            + 2 * (Fintype.card V : ℝ) * (H.edgeFinset.card : ℝ)
            + 2 * (Fintype.card V : ℝ) ^ 2 + 2 ^ (Fintype.card V)
            + (Fintype.card V : ℝ) * (d : ℝ)) * L ^ 2 ≤ E) :
    |(H.edgeFinset.card : ℝ) * r ^ (H.edgeFinset.card - 1) * (q22 - r)
        + (Fintype.card V : ℝ)
          * (z ^ d * r ^ (H.edgeFinset.card - d) - r ^ H.edgeFinset.card) * c|
      ≤ E * delta ^ 2 := by
  have hT := tBip_linearization H hreg h11 h12 h22 hr hc0 hc1
  rw [ht] at hT
  set n := Fintype.card V with hn_def
  set m := H.edgeFinset.card with hm_def
  have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hLd0 : 0 ≤ L * |delta| := le_trans hc0 hcb
  -- the three a-priori square bounds
  have b1 : (q22 - r) ^ 2 ≤ L ^ 2 * delta ^ 2 := sq_le_of_abs_le h22b
  have b3 : c ^ 2 ≤ L ^ 2 * delta ^ 2 := sq_le_of_abs_le (by rwa [abs_of_nonneg hc0])
  have b2 : c * |q22 - r| ≤ L ^ 2 * delta ^ 2 := by
    have h := mul_le_mul hcb h22b (abs_nonneg _) hLd0
    calc c * |q22 - r| ≤ (L * |delta|) * (L * |delta|) := h
      _ = L ^ 2 * |delta| ^ 2 := by ring
      _ = L ^ 2 * delta ^ 2 := by rw [sq_abs]
  -- the linearisation with the moving cross density `q₁₂`
  have habs : |(m:ℝ) * r ^ (m - 1) * (q22 - r)
      + (n:ℝ) * c * (q12 ^ d * r ^ (m - d) - r ^ m)|
      ≤ (m:ℝ) ^ 2 * (q22 - r) ^ 2 + 2 * (n:ℝ) * (m:ℝ) * c * |q22 - r|
        + (2 * (n:ℝ) ^ 2 + 2 ^ n) * c ^ 2 := by
    have he : r ^ m - r ^ m - ((m:ℝ) * r ^ (m - 1) * (q22 - r)
        + (n:ℝ) * c * (q12 ^ d * r ^ (m - d) - r ^ m))
        = -((m:ℝ) * r ^ (m - 1) * (q22 - r)
          + (n:ℝ) * c * (q12 ^ d * r ^ (m - d) - r ^ m)) := by ring
    rw [he, abs_neg] at hT
    exact hT
  -- swapping `q₁₂^d` for its boundary value `z^d`
  have hswap : |(n:ℝ) * c * (q12 ^ d * r ^ (m - d) - r ^ m)
      - (n:ℝ) * (z ^ d * r ^ (m - d) - r ^ m) * c|
      ≤ (n:ℝ) * (d:ℝ) * (L ^ 2 * delta ^ 2) := by
    have he : (n:ℝ) * c * (q12 ^ d * r ^ (m - d) - r ^ m)
        - (n:ℝ) * (z ^ d * r ^ (m - d) - r ^ m) * c
        = ((n:ℝ) * c) * ((q12 ^ d - z ^ d) * r ^ (m - d)) := by ring
    rw [he]
    have h1 : |(n:ℝ) * c| ≤ (n:ℝ) * (L * |delta|) := by
      rw [abs_mul, abs_of_nonneg hn0, abs_of_nonneg hc0]
      exact mul_le_mul_of_nonneg_left hcb hn0
    have h2 : |(q12 ^ d - z ^ d) * r ^ (m - d)| ≤ (d:ℝ) * (L * |delta|) := by
      rw [abs_mul]
      have hp : |r ^ (m - d)| ≤ 1 := by
        rw [abs_of_nonneg (pow_nonneg hr.1 _)]; exact pow_le_one₀ hr.1 hr.2
      have hq : |q12 ^ d - z ^ d| ≤ (d:ℝ) * (L * |delta|) :=
        le_trans (abs_pow_sub_pow_le h12 hz d)
          (mul_le_mul_of_nonneg_left h12b (Nat.cast_nonneg d))
      calc |q12 ^ d - z ^ d| * |r ^ (m - d)| ≤ ((d:ℝ) * (L * |delta|)) * 1 :=
            mul_le_mul hq hp (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg d) hLd0)
        _ = (d:ℝ) * (L * |delta|) := mul_one _
    calc |(n:ℝ) * c * ((q12 ^ d - z ^ d) * r ^ (m - d))|
        ≤ ((n:ℝ) * (L * |delta|)) * ((d:ℝ) * (L * |delta|)) := abs_mul_le_mul h1 h2
      _ = (n:ℝ) * (d:ℝ) * (L ^ 2 * |delta| ^ 2) := by ring
      _ = (n:ℝ) * (d:ℝ) * (L ^ 2 * delta ^ 2) := by rw [sq_abs]
  -- assembly
  have hstep1 : (m:ℝ) ^ 2 * (q22 - r) ^ 2 ≤ (m:ℝ) ^ 2 * (L ^ 2 * delta ^ 2) :=
    mul_le_mul_of_nonneg_left b1 (sq_nonneg _)
  have hstep2 : 2 * (n:ℝ) * (m:ℝ) * c * |q22 - r| ≤ 2 * (n:ℝ) * (m:ℝ) * (L ^ 2 * delta ^ 2) := by
    calc 2 * (n:ℝ) * (m:ℝ) * c * |q22 - r| = 2 * (n:ℝ) * (m:ℝ) * (c * |q22 - r|) := by ring
      _ ≤ 2 * (n:ℝ) * (m:ℝ) * (L ^ 2 * delta ^ 2) :=
          mul_le_mul_of_nonneg_left b2 (by positivity)
  have hstep3 : (2 * (n:ℝ) ^ 2 + 2 ^ n) * c ^ 2
      ≤ (2 * (n:ℝ) ^ 2 + 2 ^ n) * (L ^ 2 * delta ^ 2) :=
    mul_le_mul_of_nonneg_left b3 (by positivity)
  calc |(m:ℝ) * r ^ (m - 1) * (q22 - r) + (n:ℝ) * (z ^ d * r ^ (m - d) - r ^ m) * c|
      ≤ |(m:ℝ) * r ^ (m - 1) * (q22 - r) + (n:ℝ) * c * (q12 ^ d * r ^ (m - d) - r ^ m)|
        + |(n:ℝ) * c * (q12 ^ d * r ^ (m - d) - r ^ m)
          - (n:ℝ) * (z ^ d * r ^ (m - d) - r ^ m) * c| := by
        have := abs_le_add_abs_sub
          ((m:ℝ) * r ^ (m - 1) * (q22 - r) + (n:ℝ) * c * (q12 ^ d * r ^ (m - d) - r ^ m))
          ((m:ℝ) * r ^ (m - 1) * (q22 - r) + (n:ℝ) * (z ^ d * r ^ (m - d) - r ^ m) * c)
        have he : (m:ℝ) * r ^ (m - 1) * (q22 - r)
            + (n:ℝ) * c * (q12 ^ d * r ^ (m - d) - r ^ m)
            - ((m:ℝ) * r ^ (m - 1) * (q22 - r)
              + (n:ℝ) * (z ^ d * r ^ (m - d) - r ^ m) * c)
            = (n:ℝ) * c * (q12 ^ d * r ^ (m - d) - r ^ m)
              - (n:ℝ) * (z ^ d * r ^ (m - d) - r ^ m) * c := by ring
        rw [he] at this
        linarith
    _ ≤ ((m:ℝ) ^ 2 * (L ^ 2 * delta ^ 2) + 2 * (n:ℝ) * (m:ℝ) * (L ^ 2 * delta ^ 2)
        + (2 * (n:ℝ) ^ 2 + 2 ^ n) * (L ^ 2 * delta ^ 2))
        + (n:ℝ) * (d:ℝ) * (L ^ 2 * delta ^ 2) := by
        have := habs
        linarith
    _ = ((m:ℝ) ^ 2 + 2 * (n:ℝ) * (m:ℝ) + 2 * (n:ℝ) ^ 2 + 2 ^ n + (n:ℝ) * (d:ℝ))
        * L ^ 2 * delta ^ 2 := by ring
    _ ≤ E * delta ^ 2 := mul_le_mul_of_nonneg_right hE (sq_nonneg delta)

/-! ### Step 3: eliminating `q₂₂ - r` -/

/-- **The 2×2 elimination.**  From the two linearisations

`-δ = X + 2(z-r)c + O(δ²)`  and  `m r^{m-1} X + n(z^d r^{m-d} - r^m)c = O(δ²)`

(with `X = q₂₂ - r` and `n d = 2m`) one eliminates `X` and obtains the paper's

`δ = 2 D_d(r,z) c + O(δ²)`,

together with the companion relation `X = -2(z^d-r^d)/(d r^{d-1}) c + O(δ²)` used for the
`q₂₂`-expansion.  Dividing the second linearisation by `m r^{m-1}` is what forces the uniform
lower bound `rlo ≤ r`: the constant `1/(m r^{m-1})` must not degenerate over the window.

This is pure scalar algebra; the exponent bookkeeping `r^{m-1} = r^{d-1} r^{m-d}`,
`r^m = r^d r^{m-d}` needs `1 ≤ d ≤ m`. -/
theorem krrs_eliminate {d m n : ℕ} (hd1 : 1 ≤ d) (hdm : d ≤ m) (hnd : n * d = 2 * m)
    {r z c X delta rlo E1 E2 E3 : ℝ}
    (hrlo : 0 < rlo) (hrle : rlo ≤ r) (hE2 : 0 ≤ E2)
    (h1 : |(-delta) - (X + 2 * (z - r) * c)| ≤ E1 * delta ^ 2)
    (h2 : |(m : ℝ) * r ^ (m - 1) * X
            + (n : ℝ) * (z ^ d * r ^ (m - d) - r ^ m) * c| ≤ E2 * delta ^ 2)
    (hE3 : E1 + E2 / ((m : ℝ) * rlo ^ (m - 1)) ≤ E3) :
    |X + 2 * (z ^ d - r ^ d) / ((d : ℝ) * r ^ (d - 1)) * c|
        ≤ E2 / ((m : ℝ) * rlo ^ (m - 1)) * delta ^ 2 ∧
      |delta - 2 * Dd d r z * c| ≤ E3 * delta ^ 2 := by
  have hr0 : 0 < r := lt_of_lt_of_le hrlo hrle
  have hm1 : 1 ≤ m := le_trans hd1 hdm
  have hdR : (0:ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hmR : (0:ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hden : (0:ℝ) < (m : ℝ) * r ^ (m - 1) := mul_pos hmR (pow_pos hr0 _)
  have hdenD : (0:ℝ) < (d : ℝ) * r ^ (d - 1) := mul_pos hdR (pow_pos hr0 _)
  have hne : ((d : ℝ) * r ^ (d - 1)) ≠ 0 := ne_of_gt hdenD
  have hrlom : (0:ℝ) < (m : ℝ) * rlo ^ (m - 1) := mul_pos hmR (pow_pos hrlo _)
  have hlow : (m : ℝ) * rlo ^ (m - 1) ≤ (m : ℝ) * r ^ (m - 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrlo.le hrle _) hmR.le
  -- exponent bookkeeping
  have hA : r ^ (m - 1) = r ^ (d - 1) * r ^ (m - d) := by rw [← pow_add]; congr 1; omega
  have hB : r ^ m = r ^ d * r ^ (m - d) := by rw [← pow_add]; congr 1; omega
  have hndR : (n : ℝ) * (d : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hnd
  -- the normalised coefficient
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 2 * (z ^ d - r ^ d) / ((d : ℝ) * r ^ (d - 1)) := ⟨_, rfl⟩
  have hQmul : ((d : ℝ) * r ^ (d - 1)) * Q = 2 * (z ^ d - r ^ d) := by
    rw [hQ]; field_simp
  have hMQ : (m : ℝ) * r ^ (m - 1) * Q = (n : ℝ) * (z ^ d * r ^ (m - d) - r ^ m) := by
    refine mul_left_cancel₀ hne ?_
    calc ((d : ℝ) * r ^ (d - 1)) * ((m : ℝ) * r ^ (m - 1) * Q)
        = ((m : ℝ) * r ^ (m - 1)) * (((d : ℝ) * r ^ (d - 1)) * Q) := by ring
      _ = ((m : ℝ) * r ^ (m - 1)) * (2 * (z ^ d - r ^ d)) := by rw [hQmul]
      _ = ((d : ℝ) * r ^ (d - 1)) * ((n : ℝ) * (z ^ d * r ^ (m - d) - r ^ m)) := by
          rw [hA, hB]
          linear_combination (-(r ^ (d - 1) * r ^ (m - d) * (z ^ d - r ^ d))) * hndR
  have hPeq : (m : ℝ) * r ^ (m - 1) * (X + Q * c)
      = (m : ℝ) * r ^ (m - 1) * X + (n : ℝ) * (z ^ d * r ^ (m - d) - r ^ m) * c := by
    rw [← hMQ]; ring
  -- first conclusion: the `q₂₂` companion relation
  have hfst : |X + Q * c| ≤ E2 / ((m : ℝ) * rlo ^ (m - 1)) * delta ^ 2 := by
    have habs : |(m : ℝ) * r ^ (m - 1)| * |X + Q * c|
        = |(m : ℝ) * r ^ (m - 1) * X + (n : ℝ) * (z ^ d * r ^ (m - d) - r ^ m) * c| := by
      rw [← abs_mul, hPeq]
    rw [abs_of_pos hden] at habs
    have hle : |X + Q * c| * ((m : ℝ) * r ^ (m - 1)) ≤ E2 * delta ^ 2 := by
      rw [mul_comm, habs]; exact h2
    have hdiv : |X + Q * c| ≤ E2 * delta ^ 2 / ((m : ℝ) * r ^ (m - 1)) :=
      (le_div_iff₀ hden).mpr hle
    have hmono : E2 * delta ^ 2 / ((m : ℝ) * r ^ (m - 1))
        ≤ E2 * delta ^ 2 / ((m : ℝ) * rlo ^ (m - 1)) := by
      gcongr
    have hshape : E2 * delta ^ 2 / ((m : ℝ) * rlo ^ (m - 1))
        = E2 / ((m : ℝ) * rlo ^ (m - 1)) * delta ^ 2 := by
      field_simp
    linarith [hdiv, hmono, hshape.le, hshape.ge]
  refine ⟨by rwa [← hQ], ?_⟩
  -- second conclusion: the paper's `δ = 2 D_d(r,z) c + O(δ²)`
  have hid2 : delta - 2 * Dd d r z * c
      = -(X + Q * c) - ((-delta) - (X + 2 * (z - r) * c)) := by
    rw [hQ]; simp only [Dd]; ring
  have hfinal : |delta - 2 * Dd d r z * c|
      ≤ |X + Q * c| + |(-delta) - (X + 2 * (z - r) * c)| := by
    rw [hid2]
    have h := abs_sub (-(X + Q * c)) ((-delta) - (X + 2 * (z - r) * c))
    rwa [abs_neg] at h
  have hmul := mul_le_mul_of_nonneg_right hE3 (sq_nonneg delta)
  linarith [hfinal, hfst, h1, hmul]

/-! ### A uniform positive floor for `D_d(r, ζ_d(r))` -/

/-- **`D_d(r, z(r))` has a positive floor on a compact `r`-interval.**  `rmk:bipodal-parameter-expansions` divides by
`D_d(r, ζ_d(r))`, so the pointwise positivity supplied by `Dd_pos` (from the
Kenyon–Radin–Ren–Sadun input `ζ_d(r) ≠ r`) has to be upgraded to a bound uniform in `r`.  This is
the usual compactness upgrade, in the style of `arc_uniform_bounds`. -/
theorem exists_Dd_floor {d : ℕ} (hd : 2 ≤ d) {z : ℝ → ℝ} {r₀ s : ℝ} (hs : 0 < s)
    (hz : ContinuousOn z (Set.Icc (r₀ - s) (r₀ + s)))
    (hr0 : ∀ r ∈ Set.Icc (r₀ - s) (r₀ + s), 0 < r)
    (hz0 : ∀ r ∈ Set.Icc (r₀ - s) (r₀ + s), 0 ≤ z r)
    (hne : ∀ r ∈ Set.Icc (r₀ - s) (r₀ + s), z r ≠ r) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ r ∈ Set.Icc (r₀ - s) (r₀ + s), kappa ≤ Dd d r (z r) := by
  have hdR : (0:ℝ) < (d : ℝ) := dpos hd
  have hKne : (Set.Icc (r₀ - s) (r₀ + s)).Nonempty := ⟨r₀, by constructor <;> linarith⟩
  have hcont : ContinuousOn (fun r => Dd d r (z r)) (Set.Icc (r₀ - s) (r₀ + s)) := by
    simp only [Dd]
    refine ContinuousOn.sub (ContinuousOn.div ((hz.pow d).sub (continuous_pow d).continuousOn)
      (continuous_const.mul (continuous_pow (d - 1))).continuousOn ?_)
      (hz.sub continuous_id.continuousOn)
    intro x hx
    exact ne_of_gt (mul_pos hdR (pow_pos (hr0 x hx) _))
  obtain ⟨x, hxK, hmin⟩ := isCompact_Icc.exists_isMinOn hKne hcont
  rw [isMinOn_iff] at hmin
  exact ⟨Dd d x (z x), Dd_pos hd (hr0 x hxK) (hz0 x hxK) (hne x hxK), hmin⟩

/-! ### Step 4: from `δ_*`-expansions to `λ`-expansions -/

/-- **Eq. `c-expansion-paper`.**  Combining `δ = 2 D c + O(δ²)` (`krrs_eliminate`) with
`δ = λ/A + O(λ²)` (`thm:local-optimizer-structure`) and `δ ≤ Cd λ` gives `c = λ/(2DA) + O(λ²)`.  The uniform floor
`κ ≤ D` is what makes the constant uniform over the window. -/
private theorem c_expansion_bound {D kappa A c delta lam Cd Cdel E C : ℝ}
    (hkappa : 0 < kappa) (hD : kappa ≤ D) (hA0 : 0 < A)
    (hE0 : 0 ≤ E) (hlam0 : 0 < lam) (hdel0 : 0 < delta)
    (hdelb : delta ≤ Cd * lam)
    (helim : |delta - 2 * D * c| ≤ E * delta ^ 2)
    (hstar : |delta - lam / A| ≤ Cdel * lam ^ 2)
    (hC : (E * Cd ^ 2 + Cdel) / (2 * kappa) ≤ C) :
    |c - lam / (2 * D * A)| ≤ C * lam ^ 2 := by
  have hD0 : 0 < D := lt_of_lt_of_le hkappa hD
  have hlamsq : (0:ℝ) < lam ^ 2 := pow_pos hlam0 2
  have hCdel0 : 0 ≤ Cdel := by
    have h0 : (0:ℝ) ≤ Cdel * lam ^ 2 := le_trans (abs_nonneg _) hstar
    by_contra hcon
    push Not at hcon
    nlinarith [h0, hlamsq, hcon]
  have hkey : c - lam / (2 * D * A)
      = ((2 * D * c - delta) + (delta - lam / A)) / (2 * D) := by
    field_simp
    ring
  have hnum : |(2 * D * c - delta) + (delta - lam / A)| ≤ E * delta ^ 2 + Cdel * lam ^ 2 := by
    refine le_trans (abs_add_le _ _) (add_le_add ?_ hstar)
    rw [show 2 * D * c - delta = -(delta - 2 * D * c) by ring, abs_neg]
    exact helim
  have hdsq : E * delta ^ 2 ≤ E * Cd ^ 2 * lam ^ 2 := by
    have h : delta ^ 2 ≤ (Cd * lam) ^ 2 := by nlinarith [hdel0, hdelb]
    nlinarith [hE0, h]
  have hnn : (0:ℝ) ≤ E * Cd ^ 2 * lam ^ 2 + Cdel * lam ^ 2 := by positivity
  rw [hkey, abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * D)]
  calc |(2 * D * c - delta) + (delta - lam / A)| / (2 * D)
      ≤ (E * Cd ^ 2 * lam ^ 2 + Cdel * lam ^ 2) / (2 * D) := by
        gcongr
        linarith [hnum, hdsq]
    _ ≤ (E * Cd ^ 2 * lam ^ 2 + Cdel * lam ^ 2) / (2 * kappa) := by gcongr
    _ = (E * Cd ^ 2 + Cdel) / (2 * kappa) * lam ^ 2 := by field_simp
    _ ≤ C * lam ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg lam)

/-- **Eq. `q22-expansion-paper`.**  Substituting the `c`-expansion into the companion relation
`X = -2(z^d-r^d)/(d r^{d-1}) c + O(δ²)` of `krrs_eliminate` gives, for `X = q₂₂ - r`,

`q₂₂ = r - (z^d - r^d)/(d r^{d-1} D A) · λ + O(λ²)`. -/
private theorem q22_expansion_bound {d : ℕ} {r z D A X c delta lam rlo Cd E2' Cc C : ℝ}
    (hd1 : 1 ≤ d)
    (hrlo : 0 < rlo) (hrle : rlo ≤ r) (hr1 : r ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hD0 : 0 < D) (hA0 : 0 < A)
    (hE2'0 : 0 ≤ E2') (hdel0 : 0 < delta) (hlam0 : 0 < lam)
    (hdelb : delta ≤ Cd * lam)
    (hlin : |X + 2 * (z ^ d - r ^ d) / ((d : ℝ) * r ^ (d - 1)) * c| ≤ E2' * delta ^ 2)
    (hc : |c - lam / (2 * D * A)| ≤ Cc * lam ^ 2)
    (hC : E2' * Cd ^ 2 + 2 * Cc / ((d : ℝ) * rlo ^ (d - 1)) ≤ C) :
    |X + (z ^ d - r ^ d) / ((d : ℝ) * r ^ (d - 1) * D * A) * lam| ≤ C * lam ^ 2 := by
  have hr0 : 0 < r := lt_of_lt_of_le hrlo hrle
  have hlamsq : (0:ℝ) < lam ^ 2 := pow_pos hlam0 2
  have hCc0 : 0 ≤ Cc := by
    have h0 : (0:ℝ) ≤ Cc * lam ^ 2 := le_trans (abs_nonneg _) hc
    by_contra hcon
    push Not at hcon
    nlinarith [h0, hlamsq, hcon]
  have hdR : (0:ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hdenD : (0:ℝ) < (d : ℝ) * r ^ (d - 1) := mul_pos hdR (pow_pos hr0 _)
  have hdenlo : (0:ℝ) < (d : ℝ) * rlo ^ (d - 1) := mul_pos hdR (pow_pos hrlo _)
  have hdenmono : (d : ℝ) * rlo ^ (d - 1) ≤ (d : ℝ) * r ^ (d - 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrlo.le hrle _) hdR.le
  -- the normalised coefficient and its size
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (z ^ d - r ^ d) / ((d : ℝ) * r ^ (d - 1)) := ⟨_, rfl⟩
  have hKabs : |K| ≤ 1 / ((d : ℝ) * rlo ^ (d - 1)) := by
    rw [hK, abs_div, abs_of_pos hdenD]
    have hnum : |z ^ d - r ^ d| ≤ 1 := by
      rw [abs_le]
      constructor
      · nlinarith [pow_le_one₀ hz0 hz1 (n := d), pow_nonneg hz0 d,
          pow_le_one₀ hr0.le hr1 (n := d), pow_nonneg hr0.le d]
      · nlinarith [pow_le_one₀ hz0 hz1 (n := d), pow_nonneg hz0 d,
          pow_le_one₀ hr0.le hr1 (n := d), pow_nonneg hr0.le d]
    gcongr
  -- the algebraic substitution
  have hid : X + (z ^ d - r ^ d) / ((d : ℝ) * r ^ (d - 1) * D * A) * lam
      = (X + 2 * K * c) - 2 * K * (c - lam / (2 * D * A)) := by
    rw [hK]
    field_simp
    ring
  have hlin' : |X + 2 * K * c| ≤ E2' * delta ^ 2 := by
    rw [hK]
    have he : X + 2 * ((z ^ d - r ^ d) / ((d : ℝ) * r ^ (d - 1))) * c
        = X + 2 * (z ^ d - r ^ d) / ((d : ℝ) * r ^ (d - 1)) * c := by ring
    rw [he]; exact hlin
  have hdsq : E2' * delta ^ 2 ≤ E2' * Cd ^ 2 * lam ^ 2 := by
    have h : delta ^ 2 ≤ (Cd * lam) ^ 2 := by nlinarith [hdel0, hdelb]
    nlinarith [hE2'0, h]
  have hsecond : |2 * K * (c - lam / (2 * D * A))|
      ≤ 2 * Cc / ((d : ℝ) * rlo ^ (d - 1)) * lam ^ 2 := by
    rw [show 2 * K * (c - lam / (2 * D * A)) = (2 * K) * (c - lam / (2 * D * A)) by ring,
      abs_mul]
    have h1 : |2 * K| ≤ 2 * (1 / ((d : ℝ) * rlo ^ (d - 1))) := by
      rw [abs_mul, abs_two]; linarith
    calc |2 * K| * |c - lam / (2 * D * A)|
        ≤ (2 * (1 / ((d : ℝ) * rlo ^ (d - 1)))) * (Cc * lam ^ 2) :=
          mul_le_mul h1 hc (abs_nonneg _) (by positivity)
      _ = 2 * Cc / ((d : ℝ) * rlo ^ (d - 1)) * lam ^ 2 := by field_simp
  rw [hid]
  calc |(X + 2 * K * c) - 2 * K * (c - lam / (2 * D * A))|
      ≤ |X + 2 * K * c| + |2 * K * (c - lam / (2 * D * A))| := abs_sub _ _
    _ ≤ E2' * Cd ^ 2 * lam ^ 2 + 2 * Cc / ((d : ℝ) * rlo ^ (d - 1)) * lam ^ 2 := by
        linarith [hlin', hdsq, hsecond]
    _ = (E2' * Cd ^ 2 + 2 * Cc / ((d : ℝ) * rlo ^ (d - 1))) * lam ^ 2 := by ring
    _ ≤ C * lam ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg lam)

/-! ### `rmk:bipodal-parameter-expansions` -/

/-- **`rmk:bipodal-parameter-expansions`: the shape of the optimizer near the phase
boundary.**  On a window `|r - r₀| < ρ`, `pc(r) - η < p < pc(r)` there are an edge-density
deficit `Δ = Dl` and the four Kenyon–Radin–Ren–Sadun parameter maps such that, with
`ε = r - Δ(p,r) = e(W_{p,r})`, `θ = r^m - ε^m` and `z = ζ_d(r) = q₁₂(r,0)`:

* `Δ(p,r) = λ(p,r)/A_H(r) + O(λ²)`   (`thm:local-optimizer-structure`, restated here for reference);
* `c(p,r) = λ(p,r)/(2 D_d(r,z) A_H(r)) + O(λ²)`      — eq. `c-expansion-paper`;
* `q₂₂(p,r) = r - (z^d - r^d)/(d r^{d-1} D_d(r,z) A_H(r))·λ(p,r) + O(λ²)`
  — eq. `q22-expansion-paper`;
* `q₁₂(p,r) = z + O(λ)` and `q₁₁(p,r) = q₁₁⁰(r) + O(λ)`.

All the `O`-constants are collected in the single `C`, uniform over the window; the
finiteness of the two displayed coefficients is the conclusion `0 < D_d(r, ζ_d(r))`, which comes
from the Kenyon–Radin–Ren–Sadun input `ζ_d(r) ≠ r` via `Dd_pos` and is made uniform by
`exists_Dd_floor`.

The optimizer itself enters through two clauses: *every* optimizer has edge density exactly `ε`,
and the concrete two-block graphon `B` with first pode `[0, c(ε,θ)]` and densities
`q₁₁(ε,θ), q₁₂(ε,θ), q₂₂(ε,θ)` is an optimizer.  Both come from `bipodal_family`. -/
theorem parameter_asymptotics {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ : ℝ} (hr₀U : r₀ ∈ M.U) (hr₀ex : r₀ ≠ rStar d) :
    ∃ ρ η C : ℝ, 0 < ρ ∧ 0 < η ∧ 0 ≤ C ∧
      ∃ (Dl : ℝ × ℝ → ℝ) (q11 q12 q22 cc : ℝ → ℝ → ℝ),
        (∀ r : ℝ, |r - r₀| < ρ → q12 r 0 ≠ r ∧ 0 < Dd d r (q12 r 0)) ∧
        ∀ r : ℝ, |r - r₀| < ρ → ∀ p : ℝ, M.pc r - η < p → p < M.pc r →
          0 < AH H M r ∧ 0 < lambdaDisp M p r ∧ 0 < Dl (p, r) ∧
          |Dl (p, r) - lambdaDisp M p r / AH H M r| ≤ C * lambdaDisp M p r ^ 2 ∧
          ∃ ε θ : ℝ, ε = r - Dl (p, r) ∧
            θ = r ^ H.edgeFinset.card - ε ^ H.edgeFinset.card ∧
            (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
              W.edgeDensity = ε) ∧
            (∃ B : Graphon, Feasible H r B ∧ B.Ip p = phiVar H p r ∧
              (∀ᵐ x ∂gμ, B.toFun x.1 x.2
                = bipodalValue (Set.Icc 0 (cc ε θ)) (q11 ε θ) (q12 ε θ) (q22 ε θ) x)) ∧
            |cc ε θ - lambdaDisp M p r / (2 * Dd d r (q12 r 0) * AH H M r)|
              ≤ C * lambdaDisp M p r ^ 2 ∧
            |q22 ε θ - (r - (q12 r 0 ^ d - r ^ d)
                / ((d : ℝ) * r ^ (d - 1) * Dd d r (q12 r 0) * AH H M r)
                * lambdaDisp M p r)| ≤ C * lambdaDisp M p r ^ 2 ∧
            |q12 ε θ - q12 r 0| ≤ C * lambdaDisp M p r ∧
            |q11 ε θ - q11 r 0| ≤ C * lambdaDisp M p r := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hdm : d ≤ H.edgeFinset.card := degree_le_card_edges H hreg hm
  have hnd : Fintype.card V * d = 2 * H.edgeFinset.card := regular_handshake H hreg
  obtain ⟨ρ1, η, L, Cd, hρ10, hη0, hL0, hCd0, Dl, q11, q12, q22, cc, hbdry, hmain⟩ :=
    bipodal_family hd M H hreg hm hr₀U hr₀ex
  -- ### The shrunken window and its compact closure
  obtain ⟨ρ, hρ_def⟩ : ∃ x : ℝ, x = ρ1 / 2 := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ_def]; linarith
  have hρlt : ρ < ρ1 := by rw [hρ_def]; linarith
  have hKmem : ∀ x : ℝ, x ∈ Set.Icc (r₀ - ρ) (r₀ + ρ) → |x - r₀| < ρ1 := by
    intro x hx
    rw [abs_lt]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmemK : ∀ r : ℝ, |r - r₀| < ρ → r ∈ Set.Icc (r₀ - ρ) (r₀ + ρ) := by
    intro r hr
    have h := abs_lt.mp hr
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hbd : ∀ x : ℝ, x ∈ Set.Icc (r₀ - ρ) (r₀ + ρ) →
      x ∈ M.U ∧ 0 < x ∧ x < 1 ∧ q12 x 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 x 0 ≠ x ∧
      AnalyticAt ℝ (fun s : ℝ => q12 s 0) x := by
    intro x hx
    obtain ⟨h1, -, h3, h4, -, -, -, h8, h9, h10⟩ := hbdry x (hKmem x hx)
    exact ⟨h1, h3, h4, h8, h9, h10⟩
  have hrlo0 : 0 < r₀ - ρ := (hbd (r₀ - ρ) ⟨le_refl _, by linarith⟩).2.1
  -- ### The uniform floor for `D_d(r, ζ_d(r))`
  obtain ⟨kappa, hkappa0, hkappa⟩ := exists_Dd_floor (z := fun s : ℝ => q12 s 0)
    (r₀ := r₀) (s := ρ) hd hρ0
    (fun x hx => ((hbd x hx).2.2.2.2.2.continuousAt).continuousWithinAt)
    (fun x hx => (hbd x hx).2.1)
    (fun x hx => (hbd x hx).2.2.2.1.1.le)
    (fun x hx => (hbd x hx).2.2.2.2.1)
  -- ### The constants
  have hmR : (0:ℝ) < (H.edgeFinset.card : ℝ) := Nat.cast_pos.mpr (by omega)
  have hdR : (0:ℝ) < (d : ℝ) := dpos hd
  have hdenM : (0:ℝ) < (H.edgeFinset.card : ℝ) * (r₀ - ρ) ^ (H.edgeFinset.card - 1) :=
    mul_pos hmR (pow_pos hrlo0 _)
  have hdenD : (0:ℝ) < (d : ℝ) * (r₀ - ρ) ^ (d - 1) := mul_pos hdR (pow_pos hrlo0 _)
  obtain ⟨E1, hE1_def⟩ : ∃ x : ℝ, x = 8 * L ^ 2 := ⟨_, rfl⟩
  obtain ⟨E2, hE2_def⟩ : ∃ x : ℝ, x = ((H.edgeFinset.card : ℝ) ^ 2
    + 2 * (Fintype.card V : ℝ) * (H.edgeFinset.card : ℝ)
    + 2 * (Fintype.card V : ℝ) ^ 2 + 2 ^ (Fintype.card V)
    + (Fintype.card V : ℝ) * (d : ℝ)) * L ^ 2 := ⟨_, rfl⟩
  obtain ⟨E2', hE2'_def⟩ : ∃ x : ℝ,
      x = E2 / ((H.edgeFinset.card : ℝ) * (r₀ - ρ) ^ (H.edgeFinset.card - 1)) := ⟨_, rfl⟩
  obtain ⟨E3, hE3_def⟩ : ∃ x : ℝ, x = E1 + E2' := ⟨_, rfl⟩
  obtain ⟨Cc, hCc_def⟩ : ∃ x : ℝ, x = (E3 * Cd ^ 2 + Cd) / (2 * kappa) := ⟨_, rfl⟩
  obtain ⟨Cq, hCq_def⟩ : ∃ x : ℝ,
      x = E2' * Cd ^ 2 + 2 * Cc / ((d : ℝ) * (r₀ - ρ) ^ (d - 1)) := ⟨_, rfl⟩
  obtain ⟨C, hC_def⟩ : ∃ x : ℝ, x = max (max Cd (L * Cd)) (max Cc Cq) := ⟨_, rfl⟩
  have hE10 : 0 ≤ E1 := by rw [hE1_def]; positivity
  have hE20 : 0 ≤ E2 := by rw [hE2_def]; positivity
  have hE2'0 : 0 ≤ E2' := by rw [hE2'_def]; exact div_nonneg hE20 hdenM.le
  have hE30 : 0 ≤ E3 := by rw [hE3_def]; linarith
  have hCc0 : 0 ≤ Cc := by
    rw [hCc_def]
    exact div_nonneg (by linarith [mul_nonneg hE30 (sq_nonneg Cd)]) (by linarith)
  have hCq0 : 0 ≤ Cq := by
    rw [hCq_def]
    have h1 : (0:ℝ) ≤ E2' * Cd ^ 2 := mul_nonneg hE2'0 (sq_nonneg Cd)
    have h2 : (0:ℝ) ≤ 2 * Cc / ((d : ℝ) * (r₀ - ρ) ^ (d - 1)) :=
      div_nonneg (by linarith) hdenD.le
    linarith
  have hCdC : Cd ≤ C := by rw [hC_def]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hLCdC : L * Cd ≤ C := by rw [hC_def]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCcC : Cc ≤ C := by rw [hC_def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCqC : Cq ≤ C := by rw [hC_def]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hC0 : 0 ≤ C := le_trans hCd0 hCdC
  refine ⟨ρ, η, C, hρ0, hη0, hC0, Dl, q11, q12, q22, cc, ?_, ?_⟩
  · intro r hrρ
    obtain ⟨-, hr0, -, hq12Ioo, hq12ne, -⟩ := hbd r (hmemK r hrρ)
    exact ⟨hq12ne, Dd_pos hd hr0 hq12Ioo.1.le hq12ne⟩
  intro r hrρ p hp_lo hp_hi
  have hrK : r ∈ Set.Icc (r₀ - ρ) (r₀ + ρ) := hmemK r hrρ
  have hrρ1 : |r - r₀| < ρ1 := hKmem r hrK
  obtain ⟨hrU, hr0, hr1, hq12Ioo, hq12ne, -⟩ := hbd r hrK
  obtain ⟨hp0, hpr, hAH0, hlam0, hDl0, -, -, -, -, -, -, -,
    hedgeAll, -, hDlexp, hDlC,
    ε, θ, hε, hθ, hI11, hI12, hI22, hccIcc, hLc, hL22, hL12, hL11,
    B, hBfeas, hBopt, hBe, hBt, hBae⟩ := hmain r hrρ1 p hp_lo hp_hi
  have habsdel : |Dl (p, r)| = Dl (p, r) := abs_of_pos hDl0
  have hrlor : r₀ - ρ ≤ r := hrK.1
  have hDdpos : 0 < Dd d r (q12 r 0) := Dd_pos hd hr0 hq12Ioo.1.le hq12ne
  have hDdfloor : kappa ≤ Dd d r (q12 r 0) := hkappa r hrK
  -- ### The exact two-block relations satisfied by the concrete optimizer `B`
  have hBB : ∀ᵐ x ∂gμ, B.toFun x.1 x.2
      = (bipodalGraphon (Set.Icc 0 (cc ε θ)) measurableSet_Icc (q11 ε θ) (q12 ε θ) (q22 ε θ)
          hI11 hI12 hI22).toFun x.1 x.2 := by
    filter_upwards [hBae] with x hx
    rw [hx]
    rfl
  have hEdgePoly : (cc ε θ) ^ 2 * (q11 ε θ)
      + 2 * (cc ε θ) * (1 - cc ε θ) * (q12 ε θ)
      + (1 - cc ε θ) ^ 2 * (q22 ε θ) = r - Dl (p, r) := by
    have h := bipodalGraphon_edgeDensity (Set.Icc 0 (cc ε θ)) measurableSet_Icc
      (q11 ε θ) (q12 ε θ) (q22 ε θ) hI11 hI12 hI22
    rw [unitμ_Icc_toReal hccIcc.1 hccIcc.2] at h
    have hB' : q11 ε θ * cc ε θ ^ 2
        + q12 ε θ * (2 * cc ε θ * (1 - cc ε θ))
        + q22 ε θ * (1 - cc ε θ) ^ 2 = ε := by
      rw [← h, ← edgeDensity_congr_ae hBB]; exact hBe
    rw [← hε]
    linear_combination hB'
  have hTPoly : tBip H (q11 ε θ) (q12 ε θ) (q22 ε θ) (cc ε θ) = r ^ H.edgeFinset.card := by
    rw [← tBip_eq_tDensity H hI11 hI12 hI22 hccIcc.1 hccIcc.2, ← tDensity_congr_ae H hBB]
    exact hBt
  -- ### The two linearisations and the elimination
  have hedgeLin : |(-(Dl (p, r))) - ((q22 ε θ - r) + 2 * (q12 r 0 - r) * (cc ε θ))|
      ≤ E1 * Dl (p, r) ^ 2 :=
    krrs_edge_linearization hI11 hI12 hI22
      (by rw [habsdel]; exact hLc) (by rw [habsdel]; exact hL22)
      (by rw [habsdel]; exact hL12) hEdgePoly hE1_def.ge
  have hHLin : |(H.edgeFinset.card : ℝ) * r ^ (H.edgeFinset.card - 1) * (q22 ε θ - r)
      + (Fintype.card V : ℝ)
        * (q12 r 0 ^ d * r ^ (H.edgeFinset.card - d) - r ^ H.edgeFinset.card) * (cc ε θ)|
      ≤ E2 * Dl (p, r) ^ 2 :=
    krrs_H_linearization H hreg hI11 hI12 hI22 ⟨hr0.le, hr1.le⟩
      ⟨hq12Ioo.1.le, hq12Ioo.2.le⟩ hccIcc.1 hccIcc.2
      (by rw [habsdel]; exact le_trans (le_abs_self _) hLc)
      (by rw [habsdel]; exact hL22) (by rw [habsdel]; exact hL12) hTPoly hE2_def.ge
  obtain ⟨helim1, helim2⟩ :=
    krrs_eliminate (E3 := E3) hd1 hdm hnd hrlo0 hrlor hE20 hedgeLin hHLin
      (le_of_eq (by rw [hE3_def, hE2'_def]))
  rw [← hE2'_def] at helim1
  -- ### The two `λ`-expansions
  have hcexp : |cc ε θ - lambdaDisp M p r / (2 * Dd d r (q12 r 0) * AH H M r)|
      ≤ Cc * lambdaDisp M p r ^ 2 :=
    c_expansion_bound hkappa0 hDdfloor hAH0 hE30 hlam0 hDl0 hDlC helim2 hDlexp hCc_def.ge
  have hq22exp : |(q22 ε θ - r) + (q12 r 0 ^ d - r ^ d)
        / ((d : ℝ) * r ^ (d - 1) * Dd d r (q12 r 0) * AH H M r) * lambdaDisp M p r|
      ≤ Cq * lambdaDisp M p r ^ 2 :=
    q22_expansion_bound hd1 hrlo0 hrlor hr1.le hq12Ioo.1.le hq12Ioo.2.le hDdpos hAH0
      hE2'0 hDl0 hlam0 hDlC helim1 hcexp hCq_def.ge
  -- ### The output
  refine ⟨hAH0, hlam0, hDl0,
    le_trans hDlexp (mul_le_mul_of_nonneg_right hCdC (sq_nonneg _)),
    ε, θ, hε, hθ,
    fun W hW hI => by rw [hedgeAll W hW hI]; exact hε.symm,
    ⟨B, hBfeas, hBopt, hBae⟩,
    le_trans hcexp (mul_le_mul_of_nonneg_right hCcC (sq_nonneg _)), ?_, ?_, ?_⟩
  · have hrw : q22 ε θ - (r - (q12 r 0 ^ d - r ^ d)
        / ((d : ℝ) * r ^ (d - 1) * Dd d r (q12 r 0) * AH H M r) * lambdaDisp M p r)
        = (q22 ε θ - r) + (q12 r 0 ^ d - r ^ d)
          / ((d : ℝ) * r ^ (d - 1) * Dd d r (q12 r 0) * AH H M r) * lambdaDisp M p r := by
      ring
    rw [hrw]
    exact le_trans hq22exp (mul_le_mul_of_nonneg_right hCqC (sq_nonneg _))
  · calc |q12 ε θ - q12 r 0| ≤ L * Dl (p, r) := hL12
      _ ≤ L * (Cd * lambdaDisp M p r) := mul_le_mul_of_nonneg_left hDlC hL0
      _ = L * Cd * lambdaDisp M p r := by ring
      _ ≤ C * lambdaDisp M p r := mul_le_mul_of_nonneg_right hLCdC hlam0.le
  · calc |q11 ε θ - q11 r 0| ≤ L * Dl (p, r) := hL11
      _ ≤ L * (Cd * lambdaDisp M p r) := mul_le_mul_of_nonneg_left hDlC hL0
      _ = L * Cd * lambdaDisp M p r := by ring
      _ ≤ C * lambdaDisp M p r := mul_le_mul_of_nonneg_right hLCdC hlam0.le

end UpperTailOptimizers
