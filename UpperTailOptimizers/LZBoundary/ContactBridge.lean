import UpperTailOptimizers.LZBoundary.ContactMaps
import UpperTailOptimizers.LZBoundary.PhiConvex

/-!
# Bridge between `φ_{p,d}` and the contact slope `sCM`

Coordinate infrastructure for Section 3 of `paper/bipodal_optimizer.tex` (`sec:lz-boundary`, `thm:scalar-lz-boundary`):
structural facts tying the Lubetzky–Zhao one-variable function
`phi p d x = Jp p (x^{1/d})` to the contact slope `sCM d p u = J_p'(u)/(d u^{d-1})`:

* `phi_eq_Jp_rpow` — unfolds the definition of `phi`;
* `deriv_phi_eq_sCM` — the *slope bridge* `φ'_{p,d}(x) = sCM d p (x^{1/d})`;
* `pStar_lt_rStar` — the threshold ordering `p_* < r_*`;
* `contactF_of_phi_contacts` — the *coordinate bridge*: a double tangent of
  `φ_{p,d}` in the `x`-coordinate yields a zero of the contact system
  `contactF` in the `u`-coordinate (`u = x^{1/d}`);
* `phi_pow_eq_Jp`, `deriv_phi_pow_eq_sCM` — the `x^d`-form restatements used
  when entering from the `u`-coordinate.
-/

namespace UpperTailOptimizers

open Real

/-- Definitional unfolding: `φ_{p,d}(x) = J_p(x^{1/d})`. -/
theorem phi_eq_Jp_rpow {p : ℝ} {d : ℕ} {x : ℝ} :
    phi p d x = Jp p (Real.rpow x (1/(d:ℝ))) := rfl

/-- **Slope bridge.**  `φ'_{p,d}(x) = sCM d p (x^{1/d})`, i.e. the derivative of
the one-variable function in the `x`-coordinate equals the contact slope evaluated
at `u = x^{1/d}`. -/
theorem deriv_phi_eq_sCM {p : ℝ} {d : ℕ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    deriv (phi p d) x = sCM d p (Real.rpow x (1/(d:ℝ))) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := dpos hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  -- value of the derivative from `hasDerivAt_phi`
  have hderiv : deriv (phi p d) x
      = Jp' p (Real.rpow x (1/(d:ℝ))) * ((1/(d:ℝ)) * Real.rpow x (1/(d:ℝ) - 1)) :=
    (hasDerivAt_phi hd hp0 hp1 hx0 hx1).deriv
  rw [hderiv, sCM]
  -- identify the nat-power denominator with an `rpow`
  have hpow : (Real.rpow x (1/(d:ℝ))) ^ (d - 1) = Real.rpow x (((d:ℝ) - 1)/(d:ℝ)) := by
    have h1 : 1 ≤ d := by omega
    have hexp2 : (1:ℝ)/(d:ℝ) * ((d - 1 : ℕ) : ℝ) = ((d:ℝ) - 1)/(d:ℝ) := by
      rw [Nat.cast_sub h1, Nat.cast_one, div_mul_eq_mul_div, one_mul]
    rw [show (Real.rpow x (1/(d:ℝ))) = x ^ ((1:ℝ)/(d:ℝ)) from rfl,
       show Real.rpow x (((d:ℝ) - 1)/(d:ℝ)) = x ^ (((d:ℝ) - 1)/(d:ℝ)) from rfl,
       ← Real.rpow_natCast (x ^ ((1:ℝ)/(d:ℝ))) (d - 1), ← Real.rpow_mul hx0.le, hexp2]
  have hpowpos : 0 < Real.rpow x (((d:ℝ) - 1)/(d:ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hpowne : Real.rpow x (((d:ℝ) - 1)/(d:ℝ)) ≠ 0 := ne_of_gt hpowpos
  -- express `x^{1/d - 1}` as the inverse of the denominator's `rpow`
  have hAinv : Real.rpow x (1/(d:ℝ) - 1) = (Real.rpow x (((d:ℝ) - 1)/(d:ℝ)))⁻¹ := by
    have hexp : (1:ℝ)/(d:ℝ) - 1 = -(((d:ℝ) - 1)/(d:ℝ)) := by field_simp; ring
    rw [hexp]
    exact Real.rpow_neg hx0.le _
  rw [hpow, hAinv]
  field_simp

/-- **Threshold ordering.**  `p_* < r_*`, i.e.
`(d-1)/((d-1) + exp(d/(d-1))) < (d-1)/d`. -/
theorem pStar_lt_rStar {d : ℕ} (hd : 2 ≤ d) : pStar d < rStar d := by
  unfold pStar rStar
  have hd1 : (0 : ℝ) < (d:ℝ) - 1 := by have := one_lt_d hd; linarith
  have hdpos : (0 : ℝ) < (d:ℝ) := dpos hd
  -- the exponential exceeds `1`, since its argument is positive
  have hargpos : 0 < (d:ℝ) / ((d:ℝ) - 1) := div_pos hdpos hd1
  have hexp1 : 1 < Real.exp ((d:ℝ) / ((d:ℝ) - 1)) := by
    have := Real.add_one_le_exp ((d:ℝ) / ((d:ℝ) - 1))
    linarith
  -- hence the denominator exceeds `d`
  have hdenom : (d:ℝ) < ((d:ℝ) - 1) + Real.exp ((d:ℝ) / ((d:ℝ) - 1)) := by linarith
  exact div_lt_div_of_pos_left hd1 hdpos hdenom

/-- **Coordinate bridge for the Lubetzky–Zhao contacts** (x-coordinate → u-coordinate).  If
`x_a < x_b` in `(0,1)` satisfy the common-tangent equations of `φ_{p,d}` — equal slope
`φ'(x_a)=φ'(x_b)` and the chord equation — then in `u`-coordinates `a = x_a^{1/d}`,
`b = x_b^{1/d}` solve the contact system `contactF d (a,b) p = 0` (equal `sCM` slope +
chord in `J_p`).  This transports the existence-form `lz_boundary_contacts` into the form
`contacts_analytic`/`contact_deriv_*` consume (the keystone `exists_globalContacts`). -/
theorem contactF_of_phi_contacts {d : ℕ} (hd : 2 ≤ d) {p xa xb : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hxa0 : 0 < xa) (hab : xa < xb) (hxb1 : xb < 1)
    (hslope : deriv (phi p d) xa = deriv (phi p d) xb)
    (hchord : phi p d xb - phi p d xa = deriv (phi p d) xa * (xb - xa)) :
    contactF d (Real.rpow xa (1/(d:ℝ)), Real.rpow xb (1/(d:ℝ))) p = 0 := by
  have hdne : d ≠ 0 := by omega
  have hxb0 : 0 < xb := lt_trans hxa0 hab
  have hxa1 : xa < 1 := lt_trans hab hxb1
  set a₀ := Real.rpow xa (1/(d:ℝ)) with ha₀
  set b₀ := Real.rpow xb (1/(d:ℝ)) with hb₀
  -- slope bridge `sCM d p (x^{1/d}) = φ'(x)`
  have hsa : sCM d p a₀ = deriv (phi p d) xa := by
    rw [ha₀]; exact (deriv_phi_eq_sCM hd hp0 hp1 hxa0 hxa1).symm
  have hsb : sCM d p b₀ = deriv (phi p d) xb := by
    rw [hb₀]; exact (deriv_phi_eq_sCM hd hp0 hp1 hxb0 hxb1).symm
  -- value bridge `J_p (x^{1/d}) = φ(x)`
  have hja : Jp p a₀ = phi p d xa := by rw [ha₀]; exact phi_eq_Jp_rpow.symm
  have hjb : Jp p b₀ = phi p d xb := by rw [hb₀]; exact phi_eq_Jp_rpow.symm
  -- `(x^{1/d})^d = x`
  have hpa : a₀ ^ d = xa := by rw [ha₀, one_div]; exact Real.rpow_inv_natCast_pow hxa0.le hdne
  have hpb : b₀ ^ d = xb := by rw [hb₀, one_div]; exact Real.rpow_inv_natCast_pow hxb0.le hdne
  -- both components of `contactF` vanish
  have h1 : sCM d p a₀ - sCM d p b₀ = 0 := by rw [hsa, hsb, hslope]; ring
  have h2 : Jp p b₀ - Jp p a₀ - sCM d p a₀ * (b₀ ^ d - a₀ ^ d) = 0 := by
    rw [hja, hjb, hsa, hpa, hpb]; linarith [hchord]
  unfold contactF
  exact Prod.ext_iff.mpr ⟨h1, h2⟩

/-- `φ_{p,d}(x^d) = J_p(x)` for `0 < x` (the `x^d`-form of `phi_eq_Jp_rpow`). -/
theorem phi_pow_eq_Jp {p : ℝ} {d : ℕ} (hd : 2 ≤ d) {x : ℝ} (hx0 : 0 < x) :
    phi p d (x ^ d) = Jp p x := by
  have hinv : Real.rpow (x ^ d) (1/(d:ℝ)) = x := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hx0.le (by omega)
  rw [phi_eq_Jp_rpow, hinv]

/-- `φ'_{p,d}(x^d) = sCM d p x` for `0 < x < 1` (the `x^d`-form of the slope bridge). -/
theorem deriv_phi_pow_eq_sCM {p : ℝ} {d : ℕ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    deriv (phi p d) (x ^ d) = sCM d p x := by
  have hxd0 : 0 < x ^ d := pow_pos hx0 d
  have hxd1 : x ^ d < 1 := pow_lt_one₀ hx0.le hx1 (by omega)
  have hinv : Real.rpow (x ^ d) (1/(d:ℝ)) = x := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hx0.le (by omega)
  rw [deriv_phi_eq_sCM hd hp0 hp1 hxd0 hxd1, hinv]

end UpperTailOptimizers
