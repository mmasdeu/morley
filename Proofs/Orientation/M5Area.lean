import M5Pre
import M5Tan

namespace M5
open M8K
open XamboMorley XamboMorley.OrientedTriangle
open scoped Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

theorem U6_eq_pow (a : ℝ) : U6 a = (1 + (a:ℂ)*Complex.I)^6 := by
  have ht : ((a:ℂ)*Complex.I)^2 = -((a:ℂ)^2) := by rw [mul_pow, Complex.I_sq]; ring
  have e3 : ((a:ℂ)*Complex.I)^3 = -(((a:ℂ)^2)*((a:ℂ)*Complex.I)) := by
    rw [show (3:ℕ) = 2+1 from rfl, pow_add, ht, pow_one]; ring
  have e4 : ((a:ℂ)*Complex.I)^4 = ((a:ℂ)^4) := by
    rw [show (4:ℕ) = 2+2 from rfl, pow_add, ht]; ring
  have e5 : ((a:ℂ)*Complex.I)^5 = ((a:ℂ)^4)*((a:ℂ)*Complex.I) := by
    rw [show (5:ℕ) = 4+1 from rfl, pow_add, e4, pow_one]
  have e6 : ((a:ℂ)*Complex.I)^6 = -((a:ℂ)^6) := by
    rw [show (6:ℕ) = 4+2 from rfl, pow_add, e4, ht]; ring
  rw [show (1 + (a:ℂ)*Complex.I)^6 = 1 + 6*((a:ℂ)*Complex.I) + 15*((a:ℂ)*Complex.I)^2
      + 20*((a:ℂ)*Complex.I)^3 + 15*((a:ℂ)*Complex.I)^4 + 6*((a:ℂ)*Complex.I)^5
      + ((a:ℂ)*Complex.I)^6 from by ring]
  rw [e3, e4, e5, e6, ht]
  simp only [U6]
  push_cast
  ring

theorem Usq_cube (a : ℝ) : (Usq a)^3 = U6 a := by
  rw [U6_eq_pow, Usq_eq_sq, ← pow_mul]

theorem Usqc_cube (a : ℝ) : (Usqc a)^3 = U6c a := by
  have hU : U6c a = U6 (-a) := by simp only [U6c, U6]; push_cast; ring
  rw [hU, U6_eq_pow, Usqc_eq_sq]
  rw [show (1 - (a:ℂ)*Complex.I) = (1 + ((-a:ℝ):ℂ)*Complex.I) by push_cast; ring]
  rw [← pow_mul]

/-- `mm a b ≠ 0` on the sum-one class. -/
theorem mm_ne (T : OrientedTriangle E o) (q : TricolorIndex) (hq : q.i + q.j + q.k = 1) :
    mm (Real.tan ((T.alpha - labelAngle q.k / 2) / 2))
        (Real.tan ((T.beta - labelAngle q.i / 2) / 2)) ≠ 0 := by
  set u := T.alpha - labelAngle q.k / 2 with hu
  set v := T.beta - labelAngle q.i / 2 with hv
  set w := T.gamma - labelAngle q.j / 2 with hw
  have huc : Real.cos (u/2) ≠ 0 := s_cos_ne T.alpha (m3_alpha_pos T) (alpha_lt T) q.k
  have hvc : Real.cos (v/2) ≠ 0 := s_cos_ne T.beta (m6_beta_pos T) (m6_beta_lt T) q.i
  have hwz : Real.sin w ≠ 0 := s_sin_ne T.gamma (m6_gamma_pos T) (m6_gamma_lt T) q.j
  intro h
  have hts := M8K.tan_sum_prod u v huc hvc
  have h0 : (Real.tan (u/2) + Real.tan (v/2)) * (Real.tan (u/2) * Real.tan (v/2) - 1) = 0 := by
    have h' : mm (Real.tan (u/2)) (Real.tan (v/2)) = 0 := h
    simpa only [mm] using h'
  rw [h0] at hts
  have hden : (2 * Real.cos (u/2) ^ 2 * Real.cos (v/2) ^ 2) ≠ 0 := by positivity
  have hs : Real.sin (u + v) = 0 := by
    have h2 : -Real.sin (u + v) / (2 * Real.cos (u/2) ^ 2 * Real.cos (v/2) ^ 2) = 0 := hts.symm
    rcases div_eq_zero_iff.mp h2 with h3 | h3
    · linarith
    · exact absurd h3 hden
  rcases sum_one_uvw T q hq with hsum | hsum
  · rw [← hu, ← hv, ← hw] at hsum
    have h4 : u + v = -w := by linarith
    rw [h4, Real.sin_neg] at hs
    exact hwz (by linarith)
  · rw [← hu, ← hv, ← hw] at hsum
    have h4 : u + v = -(w + Real.pi) := by linarith
    rw [h4, Real.sin_neg, Real.sin_add_pi] at hs
    exact hwz (by linarith)

/-- **The area formula on the sum-one class.** -/
theorem area_sum_one (T : OrientedTriangle E o) (q : TricolorIndex)
    (hq : q.i + q.j + q.k = 1) :
    orientedArea o ((T.tricolorTriangle q).second - (T.tricolorTriangle q).first)
        ((T.tricolorTriangle q).third - (T.tricolorTriangle q).first)
      = Complex.normSq (toComplex o (T.B - T.C)) *
          Lamab (Real.tan ((T.alpha - labelAngle q.k / 2) / 2))
                (Real.tan ((T.beta - labelAngle q.i / 2) / 2)) := by
  set a := Real.tan ((T.alpha - labelAngle q.k / 2) / 2) with ha
  set b := Real.tan ((T.beta - labelAngle q.i / 2) / 2) with hb
  set X : ℂ := toComplex o (T.B - T.C) with hX
  set Y : ℂ := toComplex o (T.C - T.A) with hY
  have ha0 : a ≠ 0 := by rw [ha]; exact s_tan_ne T.alpha (m3_alpha_pos T) (alpha_lt T) q.k
  have hb0 : b ≠ 0 := by rw [hb]; exact s_tan_ne T.beta (m6_beta_pos T) (m6_beta_lt T) q.i
  have ha31 : 3*a^2 - 1 ≠ 0 := by rw [ha]; exact s_tan31 T.alpha (m3_alpha_pos T) (alpha_lt T) q.k
  have ha13 : a^2 - 3 ≠ 0 := by rw [ha]; exact s_tan13 T.alpha (m3_alpha_pos T) (alpha_lt T) q.k
  have hb31 : 3*b^2 - 1 ≠ 0 := by rw [hb]; exact s_tan31 T.beta (m6_beta_pos T) (m6_beta_lt T) q.i
  have hb13 : b^2 - 3 ≠ 0 := by rw [hb]; exact s_tan13 T.beta (m6_beta_pos T) (m6_beta_lt T) q.i
  have hmm : mm a b ≠ 0 := by rw [ha, hb]; exact mm_ne T q hq
  have hsig : m1sigma q.i * m1sigma q.j * m1sigma q.k = (omega : ℂ) ^ 2 := by
    rw [← m1sigma_mul q.i q.j, ← m1sigma_mul (q.i + q.j) q.k, hq, m1sigma_one]
  have htrip : (T.m1P * m1sigma q.i) * (T.m1Q * m1sigma q.j) * (T.m1R * m1sigma q.k) = 1 := by
    rw [show (T.m1P * m1sigma q.i) * (T.m1Q * m1sigma q.j) * (T.m1R * m1sigma q.k)
        = (T.m1P * T.m1Q * T.m1R) * (m1sigma q.i * m1sigma q.j * m1sigma q.k) from by ring,
      m1_PQR, hsig, omega_mul_sq]
  have hxi : T.m1R * m1sigma q.k = Usq a / Usqc a := by
    have h := xi_eq T q.k
    rw [← ha] at h
    exact h
  have heta : T.m1P * m1sigma q.i = Usq b / Usqc b := by
    have h := eta_eq T q.i
    rw [← hb] at h
    exact h
  have hzeta : T.m1Q * m1sigma q.j = 1/((Usq a / Usqc a) * (Usq b / Usqc b)) := by
    rw [eq_div_iff (mul_ne_zero (div_ne_zero (Usq_ne a) (Usqc_ne a))
      (div_ne_zero (Usq_ne b) (Usqc_ne b)))]
    rw [← hxi, ← heta]
    linear_combination htrip
  have hD1 : T.m1P * T.m1Q * m1sigma (q.i + q.j) = 1/(Usq a / Usqc a) := by
    rw [eq_div_iff (div_ne_zero (Usq_ne a) (Usqc_ne a))]
    have hk : T.m1P * T.m1Q * m1sigma (q.i + q.j)
        = (T.m1P * m1sigma q.i) * (T.m1Q * m1sigma q.j) := by rw [m1sigma_mul]; ring
    rw [hk, ← hxi]
    linear_combination htrip
  have hD2 : T.m1Q * T.m1R * m1sigma (q.j + q.k) = 1/(Usq b / Usqc b) := by
    rw [eq_div_iff (div_ne_zero (Usq_ne b) (Usqc_ne b))]
    have hk : T.m1Q * T.m1R * m1sigma (q.j + q.k)
        = (T.m1Q * m1sigma q.j) * (T.m1R * m1sigma q.k) := by rw [m1sigma_mul]; ring
    rw [hk, ← heta]
    linear_combination htrip
  have hD3 : T.m1R * T.m1P * m1sigma (q.k + q.i)
      = 1/(1/((Usq a / Usqc a) * (Usq b / Usqc b))) := by
    rw [one_div_one_div]
    have hk : T.m1R * T.m1P * m1sigma (q.k + q.i)
        = (T.m1R * m1sigma q.k) * (T.m1P * m1sigma q.i) := by rw [m1sigma_mul]; ring
    rw [hk, hxi, heta]
  have hc1 : (1 - T.m1P * m1sigma q.i) / (1 - T.m1P * T.m1Q * m1sigma (q.i + q.j)) = Z1 a b := by
    rw [heta, hD1]
    exact M8K.c1_half a b ha0
  have hc2 : (1 - T.m1Q * m1sigma q.j) / (1 - T.m1Q * T.m1R * m1sigma (q.j + q.k)) = Z2 a b := by
    rw [hzeta, hD2]
    exact M8K.c2_half a b hb0
  have hc3 : (1 - T.m1R * m1sigma q.k) / (1 - T.m1R * T.m1P * m1sigma (q.k + q.i)) = Z3 a b := by
    rw [hxi, hD3]
    exact M8K.c3_half a b ha0 hmm
  have hr : toComplex o (T.constellationPoint ⟨.red, q.i, q.j⟩) = toComplex o T.C + X * Z1 a b := by
    rw [m1_red_nf T q.i q.j, hc1]
  have hA : toComplex o T.A = toComplex o T.C - Y := by rw [hY, toComplex_sub] <;> ring
  have hB : toComplex o T.B = toComplex o T.C + X := by rw [hX, toComplex_sub] <;> ring
  have hAB : toComplex o (T.A - T.B) = -(X + Y) := by rw [toComplex_sub, hA, hB] <;> ring
  have hg : toComplex o (T.constellationPoint ⟨.green, q.j, q.k⟩)
      = toComplex o T.C + Y * (Z2 a b - 1) := by
    rw [m1_green_nf T q.j q.k, hc2, hA] <;> ring
  have hbo : toComplex o (T.constellationPoint ⟨.blue, q.k, q.i⟩)
      = toComplex o T.C + X - (X + Y) * Z3 a b := by
    rw [m1_blue_nf T q.k q.i, hc3, hAB, hB] <;> ring
  have hxi3 : ((Circle.exp (2 * T.alpha - labelAngle q.k) : ℂ))^3 = U6 a / U6c a := by
    rw [← exp_shift_R T q.k, hxi, div_pow, Usq_cube, Usqc_cube]
  have heta3 : ((Circle.exp (2 * T.beta - labelAngle q.i) : ℂ))^3 = U6 b / U6c b := by
    rw [← exp_shift_P T q.i, heta, div_pow, Usq_cube, Usqc_cube]
  have hU6ne : U6 a / U6c a - 1 ≠ 0 := by
    rw [M8K.U6_div_sub_one a (U6c_ne a), M8K.U6_sub_U6c]
    refine div_ne_zero ?_ (U6c_ne a)
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) ?_) Complex.I_ne_zero
    · exact_mod_cast ha0
    · exact_mod_cast ha31
    · exact_mod_cast ha13
  have hlam : Y = X * Zl a b := by
    have hp := m4d_p_rel T q.i q.j q.k
    rw [hxi3, heta3] at hp
    have h1 : (U6 a / U6c a - 1) * Y = X * ((U6 a / U6c a) * ((U6 b / U6c b) - 1)) := by
      rw [← hp] <;> ring
    have h2 : Y = X * (((U6 a / U6c a) * ((U6 b / U6c b) - 1)) / (U6 a / U6c a - 1)) := by
      rw [← mul_div_assoc, eq_div_iff hU6ne, mul_comm Y, h1]
    rw [h2]
    congr 1
    exact M8K.lam_half a b ha0 hb0 ha31 ha13 hb31 hb13
  have hgr : toComplex o (T.constellationPoint ⟨.green, q.j, q.k⟩)
      - toComplex o (T.constellationPoint ⟨.red, q.i, q.j⟩) = X * Ap a b := by
    rw [hg, hr, hlam]
    simp only [Ap]
    ring
  have hbr : toComplex o (T.constellationPoint ⟨.blue, q.k, q.i⟩)
      - toComplex o (T.constellationPoint ⟨.red, q.i, q.j⟩) = X * Bp a b := by
    rw [hbo, hr, hlam]
    simp only [Bp]
    ring
  show orientedArea o ((T.constellationPoint ⟨.green, q.j, q.k⟩) - (T.constellationPoint ⟨.red, q.i, q.j⟩))
      ((T.constellationPoint ⟨.blue, q.k, q.i⟩) - (T.constellationPoint ⟨.red, q.i, q.j⟩))
      = Complex.normSq X * Lamab a b
  rw [orientedArea, areaForm_complex, toComplex_sub, toComplex_sub, hgr, hbr,
    M8K.im_scale, M8K.im_key a b ha0 hb0 hmm ha31 ha13]

end M5

#print axioms M5.area_sum_one
