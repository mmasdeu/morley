import XamboMorleyBase
import M8KLocal
import M5Tan
import M5Trig

namespace M5
open M8K
open XamboMorley XamboMorley.OrientedTriangle
open scoped Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-! #### Accessors for the trigonometric bookkeeping -/

theorem s_cos_ne (x : ℝ) (h0 : 0 < x) (h1 : x < Real.pi/3) (s : TrisectorLabel) :
    Real.cos ((x - labelAngle s / 2) / 2) ≠ 0 := (shift_trig x h0 h1 s).1

theorem s_tan_ne (x : ℝ) (h0 : 0 < x) (h1 : x < Real.pi/3) (s : TrisectorLabel) :
    Real.tan ((x - labelAngle s / 2) / 2) ≠ 0 := (shift_trig x h0 h1 s).2.1

theorem s_tan31 (x : ℝ) (h0 : 0 < x) (h1 : x < Real.pi/3) (s : TrisectorLabel) :
    3 * Real.tan ((x - labelAngle s / 2) / 2) ^ 2 - 1 ≠ 0 := (shift_trig x h0 h1 s).2.2.1

theorem s_tan13 (x : ℝ) (h0 : 0 < x) (h1 : x < Real.pi/3) (s : TrisectorLabel) :
    Real.tan ((x - labelAngle s / 2) / 2) ^ 2 - 3 ≠ 0 := (shift_trig x h0 h1 s).2.2.2.1

theorem s_sin_pos_iff (x : ℝ) (h0 : 0 < x) (h1 : x < Real.pi/3) (s : TrisectorLabel) :
    0 < Real.sin (x - labelAngle s / 2) ↔ s = 0 := (shift_trig x h0 h1 s).2.2.2.2.1

theorem s_sin_ne (x : ℝ) (h0 : 0 < x) (h1 : x < Real.pi/3) (s : TrisectorLabel) :
    Real.sin (x - labelAngle s / 2) ≠ 0 := (shift_trig x h0 h1 s).2.2.2.2.2

/-! #### Label arithmetic on the sum-one class -/

theorem sum_one_vals (q : TricolorIndex) (hq : q.i + q.j + q.k = 1) :
    q.i.val + q.j.val + q.k.val = 1 ∨ q.i.val + q.j.val + q.k.val = 4 := by
  revert hq
  revert q
  decide

/-- The three shifted angles sum to `0` or `-π` on the sum-one class. -/
theorem sum_one_uvw (T : OrientedTriangle E o) (q : TricolorIndex)
    (hq : q.i + q.j + q.k = 1) :
    (T.alpha - labelAngle q.k / 2) + (T.beta - labelAngle q.i / 2) +
        (T.gamma - labelAngle q.j / 2) = 0 ∨
      (T.alpha - labelAngle q.k / 2) + (T.beta - labelAngle q.i / 2) +
        (T.gamma - labelAngle q.j / 2) = -Real.pi := by
  have h3 : 3 * T.alpha + 3 * T.beta + 3 * T.gamma = Real.pi := T.angle_sum
  have hk := m2_labelAngle_half q.k
  have hi := m2_labelAngle_half q.i
  have hj := m2_labelAngle_half q.j
  have hlab : labelAngle q.k / 2 + labelAngle q.i / 2 + labelAngle q.j / 2
      = ((q.i.val + q.j.val + q.k.val : ℕ) : ℝ) * (Real.pi / 3) := by
    rw [hk, hi, hj]; push_cast; ring
  have hnat : ((q.i.val + q.j.val + q.k.val : ℕ) : ℝ) = (1:ℝ) ∨
      ((q.i.val + q.j.val + q.k.val : ℕ) : ℝ) = (4:ℝ) := by
    rcases sum_one_vals q hq with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  rcases hnat with h | h
  · left; rw [h] at hlab; linarith
  · right; rw [h] at hlab; linarith

/-- `exp (2i·)` bookkeeping: the three shifted exponentials are `m1R σ_k`, `m1P σ_i`, `m1Q σ_j`. -/
theorem exp_shift_R (T : OrientedTriangle E o) (s : TrisectorLabel) :
    T.m1R * m1sigma s = (Circle.exp (2 * T.alpha - labelAngle s) : ℂ) := by
  simp only [m1R, m1sigma, ← Circle.coe_mul, ← Circle.exp_add, sub_eq_add_neg]

theorem exp_shift_P (T : OrientedTriangle E o) (s : TrisectorLabel) :
    T.m1P * m1sigma s = (Circle.exp (2 * T.beta - labelAngle s) : ℂ) := by
  simp only [m1P, m1sigma, ← Circle.coe_mul, ← Circle.exp_add, sub_eq_add_neg]

theorem exp_shift_Q (T : OrientedTriangle E o) (s : TrisectorLabel) :
    T.m1Q * m1sigma s = (Circle.exp (2 * T.gamma - labelAngle s) : ℂ) := by
  simp only [m1Q, m1sigma, ← Circle.coe_mul, ← Circle.exp_add, sub_eq_add_neg]

/-- `R σ_k = Usq a / Usqc a` with `a = tan(u/2)`, `u = α - labelAngle k/2`. -/
theorem xi_eq (T : OrientedTriangle E o) (s : TrisectorLabel) :
    T.m1R * m1sigma s =
      Usq (Real.tan ((T.alpha - labelAngle s / 2) / 2)) /
        Usqc (Real.tan ((T.alpha - labelAngle s / 2) / 2)) := by
  rw [exp_shift_R]
  have h : 2 * T.alpha - labelAngle s = 2 * ((T.alpha - labelAngle s / 2)) := by ring
  rw [h]
  exact usq_exp _ (s_cos_ne T.alpha (m3_alpha_pos T) (alpha_lt T) s)

theorem eta_eq (T : OrientedTriangle E o) (s : TrisectorLabel) :
    T.m1P * m1sigma s =
      Usq (Real.tan ((T.beta - labelAngle s / 2) / 2)) /
        Usqc (Real.tan ((T.beta - labelAngle s / 2) / 2)) := by
  rw [exp_shift_P]
  have h : 2 * T.beta - labelAngle s = 2 * ((T.beta - labelAngle s / 2)) := by ring
  rw [h]
  exact usq_exp _ (s_cos_ne T.beta (m6_beta_pos T) (m6_beta_lt T) s)

end M5

#print axioms M5.sum_one_uvw
