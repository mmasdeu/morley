import XamboMorleyBase
import M8KLocal

/-! ### The tangent / exponential bridge for the sum-one clause

For `a = tan (u/2)` we have `Usq a / Usqc a = exp (2 i u)`, where `Usq a = (1+ai)^2`,
`Usqc a = (1-ai)^2` (the M8K half-angle quantities). -/

namespace M5
open M8K

theorem Usq_eq_sq (t : ℝ) : Usq t = (1 + (t:ℂ)*Complex.I)^2 := by
  rw [show (1 + (t:ℂ)*Complex.I)^2 = 1 + 2*((t:ℂ)*Complex.I) + ((t:ℂ)*Complex.I)^2 from by ring]
  rw [show ((t:ℂ)*Complex.I)^2 = -((t:ℂ)^2) from by rw [mul_pow, Complex.I_sq]; ring]
  simp only [Usq]
  push_cast
  ring

theorem Usqc_eq_sq (t : ℝ) : Usqc t = (1 - (t:ℂ)*Complex.I)^2 := by
  rw [show (1 - (t:ℂ)*Complex.I)^2 = 1 - 2*((t:ℂ)*Complex.I) + ((t:ℂ)*Complex.I)^2 from by ring]
  rw [show ((t:ℂ)*Complex.I)^2 = -((t:ℂ)^2) from by rw [mul_pow, Complex.I_sq]; ring]
  simp only [Usqc]
  push_cast
  ring

theorem exp_half_eq (u : ℝ) :
    (Circle.exp (u/2) : ℂ) = (Real.cos (u/2) : ℂ) + (Real.sin (u/2) : ℂ) * Complex.I := by
  rw [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem exp_neg_half_eq (u : ℝ) :
    (Circle.exp (-(u/2)) : ℂ) = (Real.cos (u/2) : ℂ) - (Real.sin (u/2) : ℂ) * Complex.I := by
  rw [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem one_add_tan_exp (u : ℝ) (hu : Real.cos (u/2) ≠ 0) :
    (1 : ℂ) + (Real.tan (u/2) : ℂ) * Complex.I
      = ((Real.cos (u/2) : ℂ))⁻¹ * (Circle.exp (u/2) : ℂ) := by
  have hc : (Real.cos (u/2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
  rw [exp_half_eq, Real.tan_eq_sin_div_cos, Complex.ofReal_div]
  field_simp

theorem one_sub_tan_exp (u : ℝ) (hu : Real.cos (u/2) ≠ 0) :
    (1 : ℂ) - (Real.tan (u/2) : ℂ) * Complex.I
      = ((Real.cos (u/2) : ℂ))⁻¹ * (Circle.exp (-(u/2)) : ℂ) := by
  have hc : (Real.cos (u/2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
  rw [exp_neg_half_eq, Real.tan_eq_sin_div_cos, Complex.ofReal_div]
  field_simp

/-- **The bridge**: `Usq (tan (u/2)) / Usqc (tan (u/2)) = exp (2 i u)`. -/
theorem usq_exp (u : ℝ) (hu : Real.cos (u/2) ≠ 0) :
    (Circle.exp (2*u) : ℂ) = Usq (Real.tan (u/2)) / Usqc (Real.tan (u/2)) := by
  have h1 := one_add_tan_exp u hu
  have h2 := one_sub_tan_exp u hu
  have hc : ((Real.cos (u/2) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
  have hcc : ((Real.cos (u/2) : ℂ))⁻¹ ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero hc)
  have hE : (Circle.exp (u/2) : ℂ) ^ 2 = (Circle.exp u : ℂ) := by
    rw [pow_two, ← Circle.coe_mul, ← Circle.exp_add]
    rw [show u/2 + u/2 = u from by ring]
  have hE' : (Circle.exp (-(u/2)) : ℂ) ^ 2 = (Circle.exp (-u) : ℂ) := by
    rw [pow_two, ← Circle.coe_mul, ← Circle.exp_add]
    rw [show -(u/2) + -(u/2) = -u from by ring]
  have hEu' : (Circle.exp (-u) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hkey : (Circle.exp (u/2) : ℂ) ^ 2 / (Circle.exp (-(u/2)) : ℂ) ^ 2
      = (Circle.exp (2*u) : ℂ) := by
    rw [hE, hE', div_eq_iff hEu', ← Circle.coe_mul, ← Circle.exp_add]
    rw [show 2*u + -u = u from by ring]
  rw [Usq_eq_sq, Usqc_eq_sq, h1, h2, mul_pow, mul_pow, ← hkey]
  rw [mul_div_mul_left _ _ hcc]

end M5

#print axioms M5.usq_exp
