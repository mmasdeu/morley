import M2C

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

noncomputable section
open scoped Real RealInnerProductSpace ComplexConjugate Matrix
open Function Set

namespace XamboMorley

universe u

namespace OrientedTriangle

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-! ### The exact-algebra certificate engine

The cross-conjugate identity `star A * B = A * star B` that makes a ratio real is, after
`star` is rewritten to inversion and `R` is eliminated through `P Q R = ω`, a Laurent
identity in the free variables `P`, `Q` and the fixed primitive cube root `ω`. The only
remaining input is `ω^3 = 1`, which is supplied by the power table below, so the whole
certificate is closed by `field_simp` and `ring`. -/

/-- `R = ω / (P Q)`, the elimination of the third exponential through `P Q R = ω`. -/
theorem m2_R_eq (T : OrientedTriangle E o) :
    m1R T = (omega : ℂ) / (m1P T * m1Q T) := by
  rw [eq_div_iff (mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T))]
  linear_combination m1_PQR T


theorem m2_sigma_ne (l : TrisectorLabel) : m1sigma l ≠ 0 := by
  have h : ‖m1sigma l‖ = 1 := m3c_norm_sigma l
  intro h0
  rw [h0, norm_zero] at h
  norm_num at h

theorem m2_sigma_mul_inv (l : TrisectorLabel) : m1sigma l * (m1sigma l)⁻¹ = 1 :=
  mul_inv_cancel₀ (m2_sigma_ne l)

theorem m2_sigma_inv_mul (l : TrisectorLabel) : (m1sigma l)⁻¹ * m1sigma l = 1 :=
  inv_mul_cancel₀ (m2_sigma_ne l)

theorem m2_star_div (x y : ℂ) : star (x / y) = star x / star y := by simp
theorem m2_star_inv (x : ℂ) : star x⁻¹ = (star x)⁻¹ := by simp
theorem m2_star_ofNat (n : ℕ) : star ((n : ℂ)) = (n : ℂ) := by simp

theorem m2_star_omega : star (omega : ℂ) = (omega : ℂ) ^ 2 := by
  rw [m3c_star_eq_inv omega_norm_one, omega_inv']

/-- The nine `ZMod 3` label sums, normalised to numerals. -/
theorem m2_sum00 : ((0 : TrisectorLabel) + 0) = 0 := by decide
theorem m2_sum01 : ((0 : TrisectorLabel) + 1) = 1 := by decide
theorem m2_sum02 : ((0 : TrisectorLabel) + 2) = 2 := by decide
theorem m2_sum10 : ((1 : TrisectorLabel) + 0) = 1 := by decide
theorem m2_sum11 : ((1 : TrisectorLabel) + 1) = 2 := by decide
theorem m2_sum12 : ((1 : TrisectorLabel) + 2) = 0 := by decide
theorem m2_sum20 : ((2 : TrisectorLabel) + 0) = 2 := by decide
theorem m2_sum21 : ((2 : TrisectorLabel) + 1) = 0 := by decide
theorem m2_sum22 : ((2 : TrisectorLabel) + 2) = 1 := by decide

/-! ### The power table for `ω`

`ω ^ k` is tabulated for `0 ≤ k ≤ 48`; every power arising from a certificate of this
development lies in that range. -/


end OrientedTriangle

end XamboMorley
