import M5Area

namespace M5
open M8K
open XamboMorley XamboMorley.OrientedTriangle
open scoped Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

theorem v0 : ((0:ZMod 3)).val = 0 := by decide
theorem v1 : ((1:ZMod 3)).val = 1 := by decide
theorem v2 : ((2:ZMod 3)).val = 2 := by decide

theorem la0 : labelAngle (0:ZMod 3) / 2 = 0 := by rw [m2_labelAngle_half, v0]; push_cast; ring
theorem la1 : labelAngle (1:ZMod 3) / 2 = Real.pi/3 := by rw [m2_labelAngle_half, v1]; push_cast; ring
theorem la2 : labelAngle (2:ZMod 3) / 2 = 2*Real.pi/3 := by rw [m2_labelAngle_half, v2]; push_cast; ring

/-- Sign of one half-angle sine, positively. -/
theorem s_sin_pos (x : ℝ) (h0 : 0 < x) (h1 : x < Real.pi/3) (s : TrisectorLabel) (hs : s = 0) :
    0 < Real.sin (x - labelAngle s / 2) := (s_sin_pos_iff x h0 h1 s).mpr hs

/-- Sign of one half-angle sine, negatively. -/
theorem s_sin_neg (x : ℝ) (h0 : 0 < x) (h1 : x < Real.pi/3) (s : TrisectorLabel) (hs : s ≠ 0) :
    Real.sin (x - labelAngle s / 2) < 0 :=
  lt_of_le_of_ne (le_of_not_gt (fun hh => hs ((s_sin_pos_iff x h0 h1 s).mp hh)))
    (s_sin_ne x h0 h1 s)

/-- `Λ ≠ 0` on the sum-one class. -/
theorem Lamab_ne' (T : OrientedTriangle E o) (q : TricolorIndex) (hq : q.i + q.j + q.k = 1) :
    Lamab (Real.tan ((T.alpha - labelAngle q.k / 2) / 2))
      (Real.tan ((T.beta - labelAngle q.i / 2) / 2)) ≠ 0 := by
  have ha0 : Real.tan ((T.alpha - labelAngle q.k / 2) / 2) ≠ 0 :=
    s_tan_ne T.alpha (m3_alpha_pos T) (alpha_lt T) q.k
  have hb0 : Real.tan ((T.beta - labelAngle q.i / 2) / 2) ≠ 0 :=
    s_tan_ne T.beta (m6_beta_pos T) (m6_beta_lt T) q.i
  have ha31 : 3 * Real.tan ((T.alpha - labelAngle q.k / 2) / 2) ^ 2 - 1 ≠ 0 :=
    s_tan31 T.alpha (m3_alpha_pos T) (alpha_lt T) q.k
  have ha13 : Real.tan ((T.alpha - labelAngle q.k / 2) / 2) ^ 2 - 3 ≠ 0 :=
    s_tan13 T.alpha (m3_alpha_pos T) (alpha_lt T) q.k
  have hP : 0 < Pab (Real.tan ((T.alpha - labelAngle q.k / 2) / 2))
      (Real.tan ((T.beta - labelAngle q.i / 2) / 2)) :=
    M8K.Pab_pos _ _ (by intro h; exact ha13 (by linarith)) (by intro h; exact ha31 (by linarith))
  rw [M8K.Lamab_fac _ _ ha0 ha31 ha13]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (ne_of_gt hP)
  · have : (0:ℝ) < 6*(1+Real.tan ((T.alpha - labelAngle q.k / 2)/2)^2)^2 /
        ((Real.tan ((T.alpha - labelAngle q.k / 2)/2)^2 - 3)^2
         * (3*Real.tan ((T.alpha - labelAngle q.k / 2)/2)^2 - 1)^2
         * (1+Real.tan ((T.beta - labelAngle q.i / 2)/2)^2)^4) := by positivity
    linarith
  · have hb : Real.tan ((T.beta - labelAngle q.i / 2) / 2) *
        (Real.tan ((T.alpha - labelAngle q.k / 2) / 2) + Real.tan ((T.beta - labelAngle q.i / 2) / 2)) *
        (Real.tan ((T.alpha - labelAngle q.k / 2) / 2) * Real.tan ((T.beta - labelAngle q.i / 2) / 2) - 1)
        = Real.tan ((T.beta - labelAngle q.i / 2) / 2) *
          mm (Real.tan ((T.alpha - labelAngle q.k / 2) / 2))
             (Real.tan ((T.beta - labelAngle q.i / 2) / 2)) := by
      simp only [mm]; ring
    rw [hb]
    exact div_ne_zero (mul_ne_zero hb0 (mm_ne T q hq)) ha0

/-- The four sign transfers from `M8K`. -/
theorem Lamab_pos_of_sum0 (T : OrientedTriangle E o) (q : TricolorIndex)
    (hsum : (T.alpha - labelAngle q.k / 2) + (T.beta - labelAngle q.i / 2) +
      (T.gamma - labelAngle q.j / 2) = 0)
    (hS : 0 < Real.sin (T.alpha - labelAngle q.k / 2) * Real.sin (T.beta - labelAngle q.i / 2)
      * Real.sin (T.gamma - labelAngle q.j / 2)) :
    0 < Lamab (Real.tan ((T.alpha - labelAngle q.k / 2) / 2))
      (Real.tan ((T.beta - labelAngle q.i / 2) / 2)) :=
  (M8K.Lamab_pos_of_sum_zero _ _ _ (s_cos_ne T.alpha (m3_alpha_pos T) (alpha_lt T) q.k)
    (s_cos_ne T.beta (m6_beta_pos T) (m6_beta_lt T) q.i)
    (s_tan_ne T.alpha (m3_alpha_pos T) (alpha_lt T) q.k)
    (s_tan31 T.alpha (m3_alpha_pos T) (alpha_lt T) q.k)
    (s_tan13 T.alpha (m3_alpha_pos T) (alpha_lt T) q.k) hsum).mpr hS

theorem Lamab_neg_of_sum0 (T : OrientedTriangle E o) (q : TricolorIndex)
    (hq : q.i + q.j + q.k = 1)
    (hsum : (T.alpha - labelAngle q.k / 2) + (T.beta - labelAngle q.i / 2) +
      (T.gamma - labelAngle q.j / 2) = 0)
    (hS : Real.sin (T.alpha - labelAngle q.k / 2) * Real.sin (T.beta - labelAngle q.i / 2)
      * Real.sin (T.gamma - labelAngle q.j / 2) < 0) :
    Lamab (Real.tan ((T.alpha - labelAngle q.k / 2) / 2))
      (Real.tan ((T.beta - labelAngle q.i / 2) / 2)) < 0 := by
  have hiff := (M8K.Lamab_pos_of_sum_zero _ _ _ (s_cos_ne T.alpha (m3_alpha_pos T) (alpha_lt T) q.k)
    (s_cos_ne T.beta (m6_beta_pos T) (m6_beta_lt T) q.i)
    (s_tan_ne T.alpha (m3_alpha_pos T) (alpha_lt T) q.k)
    (s_tan31 T.alpha (m3_alpha_pos T) (alpha_lt T) q.k)
    (s_tan13 T.alpha (m3_alpha_pos T) (alpha_lt T) q.k) hsum)
  exact lt_of_le_of_ne (le_of_not_gt (fun hh => absurd (hiff.mp hh) (not_lt.mpr (le_of_lt hS))))
    (Lamab_ne' T q hq)

theorem Lamab_pos_of_npi (T : OrientedTriangle E o) (q : TricolorIndex)
    (hsum : (T.alpha - labelAngle q.k / 2) + (T.beta - labelAngle q.i / 2) +
      (T.gamma - labelAngle q.j / 2) = -Real.pi)
    (hS : Real.sin (T.alpha - labelAngle q.k / 2) * Real.sin (T.beta - labelAngle q.i / 2)
      * Real.sin (T.gamma - labelAngle q.j / 2) < 0) :
    0 < Lamab (Real.tan ((T.alpha - labelAngle q.k / 2) / 2))
      (Real.tan ((T.beta - labelAngle q.i / 2) / 2)) :=
  (M8K.Lamab_pos_of_sum_neg_pi _ _ _ (s_cos_ne T.alpha (m3_alpha_pos T) (alpha_lt T) q.k)
    (s_cos_ne T.beta (m6_beta_pos T) (m6_beta_lt T) q.i)
    (s_tan_ne T.alpha (m3_alpha_pos T) (alpha_lt T) q.k)
    (s_tan31 T.alpha (m3_alpha_pos T) (alpha_lt T) q.k)
    (s_tan13 T.alpha (m3_alpha_pos T) (alpha_lt T) q.k) hsum).mpr (by linarith)

theorem Lamab_neg_of_npi (T : OrientedTriangle E o) (q : TricolorIndex)
    (hq : q.i + q.j + q.k = 1)
    (hsum : (T.alpha - labelAngle q.k / 2) + (T.beta - labelAngle q.i / 2) +
      (T.gamma - labelAngle q.j / 2) = -Real.pi)
    (hS : 0 < Real.sin (T.alpha - labelAngle q.k / 2) * Real.sin (T.beta - labelAngle q.i / 2)
      * Real.sin (T.gamma - labelAngle q.j / 2)) :
    Lamab (Real.tan ((T.alpha - labelAngle q.k / 2) / 2))
      (Real.tan ((T.beta - labelAngle q.i / 2) / 2)) < 0 := by
  have hiff := (M8K.Lamab_pos_of_sum_neg_pi _ _ _ (s_cos_ne T.alpha (m3_alpha_pos T) (alpha_lt T) q.k)
    (s_cos_ne T.beta (m6_beta_pos T) (m6_beta_lt T) q.i)
    (s_tan_ne T.alpha (m3_alpha_pos T) (alpha_lt T) q.k)
    (s_tan31 T.alpha (m3_alpha_pos T) (alpha_lt T) q.k)
    (s_tan13 T.alpha (m3_alpha_pos T) (alpha_lt T) q.k) hsum)
  exact lt_of_le_of_ne (le_of_not_gt (fun hh => absurd (hiff.mp hh) (by linarith [hS])))
    (Lamab_ne' T q hq)


theorem normSq_BC_pos (T : OrientedTriangle E o) :
    0 < Complex.normSq (toComplex o (T.B - T.C)) := by
  have hnorm : ‖toComplex o (T.B - T.C)‖ = T.aLength := by
    rw [show ‖toComplex o (T.B - T.C)‖ = ‖T.B - T.C‖ from (complexIsometryEquiv o).norm_map _]
    rw [aLength, show T.a = T.C - T.B from rfl, norm_sub_rev]
  rw [Complex.normSq_eq_norm_sq, hnorm]
  exact pow_pos T.aLength_pos 2

/-- The sign of `Λ` on all nine sum-one labels. -/
theorem sum_one_sign (T : OrientedTriangle E o) (q : TricolorIndex) (hq : q.i + q.j + q.k = 1) :
    (q.i * q.j * q.k ≠ 0 → 0 < Lamab (Real.tan ((T.alpha - labelAngle q.k / 2) / 2))
        (Real.tan ((T.beta - labelAngle q.i / 2) / 2))) ∧
    (q.i * q.j * q.k = 0 → Lamab (Real.tan ((T.alpha - labelAngle q.k / 2) / 2))
        (Real.tan ((T.beta - labelAngle q.i / 2) / 2)) < 0) := by
  rcases m7c_sum_one_cases q hq with
    ⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩ |
    ⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩
  · -- (0,0,1)
    refine ⟨fun hnz => absurd hnz (by rw [hi, hj, hk]; decide), fun _ => ?_⟩
    refine Lamab_neg_of_sum0 T q hq ?_ ?_
    · rw [hi, hj, hk, la1, la0]
      linarith [T.angle_sum]
    · have hu := s_sin_neg T.alpha (m3_alpha_pos T) (alpha_lt T) q.k (by rw [hk] <;> decide)
      have hv := s_sin_pos T.beta (m6_beta_pos T) (m6_beta_lt T) q.i (by rw [hi] <;> decide)
      have hw := s_sin_pos T.gamma (m6_gamma_pos T) (m6_gamma_lt T) q.j (by rw [hj] <;> decide)
      nlinarith [mul_neg_of_neg_of_pos hu (mul_pos hv hw)]
  · -- (1,0,0)
    refine ⟨fun hnz => absurd hnz (by rw [hi, hj, hk]; decide), fun _ => ?_⟩
    refine Lamab_neg_of_sum0 T q hq ?_ ?_
    · rw [hi, hj, hk, la0, la1]
      linarith [T.angle_sum]
    · have hu := s_sin_pos T.alpha (m3_alpha_pos T) (alpha_lt T) q.k (by rw [hk] <;> decide)
      have hv := s_sin_neg T.beta (m6_beta_pos T) (m6_beta_lt T) q.i (by rw [hi] <;> decide)
      have hw := s_sin_pos T.gamma (m6_gamma_pos T) (m6_gamma_lt T) q.j (by rw [hj] <;> decide)
      nlinarith [mul_neg_of_pos_of_neg (mul_pos hu hw) hv]
  · -- (0,1,0)
    refine ⟨fun hnz => absurd hnz (by rw [hi, hj, hk]; decide), fun _ => ?_⟩
    refine Lamab_neg_of_sum0 T q hq ?_ ?_
    · rw [hi, hj, hk, la0, la1]
      linarith [T.angle_sum]
    · have hu := s_sin_pos T.alpha (m3_alpha_pos T) (alpha_lt T) q.k (by rw [hk] <;> decide)
      have hv := s_sin_pos T.beta (m6_beta_pos T) (m6_beta_lt T) q.i (by rw [hi] <;> decide)
      have hw := s_sin_neg T.gamma (m6_gamma_pos T) (m6_gamma_lt T) q.j (by rw [hj] <;> decide)
      nlinarith [mul_neg_of_pos_of_neg (mul_pos hu hv) hw]
  · -- (0,2,2)
    refine ⟨fun hnz => absurd hnz (by rw [hi, hj, hk]; decide), fun _ => ?_⟩
    refine Lamab_neg_of_npi T q hq ?_ ?_
    · rw [hi, hj, hk, la2, la0]
      linarith [T.angle_sum]
    · have hu := s_sin_neg T.alpha (m3_alpha_pos T) (alpha_lt T) q.k (by rw [hk] <;> decide)
      have hv := s_sin_pos T.beta (m6_beta_pos T) (m6_beta_lt T) q.i (by rw [hi] <;> decide)
      have hw := s_sin_neg T.gamma (m6_gamma_pos T) (m6_gamma_lt T) q.j (by rw [hj] <;> decide)
      nlinarith [mul_pos (mul_pos_of_neg_of_neg hu hw) hv]
  · -- (2,0,2)
    refine ⟨fun hnz => absurd hnz (by rw [hi, hj, hk]; decide), fun _ => ?_⟩
    refine Lamab_neg_of_npi T q hq ?_ ?_
    · rw [hi, hj, hk, la2, la0]
      linarith [T.angle_sum]
    · have hu := s_sin_neg T.alpha (m3_alpha_pos T) (alpha_lt T) q.k (by rw [hk] <;> decide)
      have hv := s_sin_neg T.beta (m6_beta_pos T) (m6_beta_lt T) q.i (by rw [hi] <;> decide)
      have hw := s_sin_pos T.gamma (m6_gamma_pos T) (m6_gamma_lt T) q.j (by rw [hj] <;> decide)
      nlinarith [mul_pos (mul_pos_of_neg_of_neg hu hv) hw]
  · -- (2,2,0)
    refine ⟨fun hnz => absurd hnz (by rw [hi, hj, hk]; decide), fun _ => ?_⟩
    refine Lamab_neg_of_npi T q hq ?_ ?_
    · rw [hi, hj, hk, la0, la2]
      linarith [T.angle_sum]
    · have hu := s_sin_pos T.alpha (m3_alpha_pos T) (alpha_lt T) q.k (by rw [hk] <;> decide)
      have hv := s_sin_neg T.beta (m6_beta_pos T) (m6_beta_lt T) q.i (by rw [hi] <;> decide)
      have hw := s_sin_neg T.gamma (m6_gamma_pos T) (m6_gamma_lt T) q.j (by rw [hj] <;> decide)
      nlinarith [mul_pos hu (mul_pos_of_neg_of_neg hv hw)]
  · -- (1,1,2)
    refine ⟨fun _ => ?_, fun hz => absurd hz (by rw [hi, hj, hk]; decide)⟩
    refine Lamab_pos_of_npi T q ?_ ?_
    · rw [hi, hj, hk, la2, la1]
      linarith [T.angle_sum]
    · have hu := s_sin_neg T.alpha (m3_alpha_pos T) (alpha_lt T) q.k (by rw [hk] <;> decide)
      have hv := s_sin_neg T.beta (m6_beta_pos T) (m6_beta_lt T) q.i (by rw [hi] <;> decide)
      have hw := s_sin_neg T.gamma (m6_gamma_pos T) (m6_gamma_lt T) q.j (by rw [hj] <;> decide)
      nlinarith [mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hu hv) hw]
  · -- (2,1,1)
    refine ⟨fun _ => ?_, fun hz => absurd hz (by rw [hi, hj, hk]; decide)⟩
    refine Lamab_pos_of_npi T q ?_ ?_
    · rw [hi, hj, hk, la1, la2]
      linarith [T.angle_sum]
    · have hu := s_sin_neg T.alpha (m3_alpha_pos T) (alpha_lt T) q.k (by rw [hk] <;> decide)
      have hv := s_sin_neg T.beta (m6_beta_pos T) (m6_beta_lt T) q.i (by rw [hi] <;> decide)
      have hw := s_sin_neg T.gamma (m6_gamma_pos T) (m6_gamma_lt T) q.j (by rw [hj] <;> decide)
      nlinarith [mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hu hv) hw]
  · -- (1,2,1)
    refine ⟨fun _ => ?_, fun hz => absurd hz (by rw [hi, hj, hk]; decide)⟩
    refine Lamab_pos_of_npi T q ?_ ?_
    · rw [hi, hj, hk, la1, la2]
      linarith [T.angle_sum]
    · have hu := s_sin_neg T.alpha (m3_alpha_pos T) (alpha_lt T) q.k (by rw [hk] <;> decide)
      have hv := s_sin_neg T.beta (m6_beta_pos T) (m6_beta_lt T) q.i (by rw [hi] <;> decide)
      have hw := s_sin_neg T.gamma (m6_gamma_pos T) (m6_gamma_lt T) q.j (by rw [hj] <;> decide)
      nlinarith [mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hu hv) hw]

/-- Positive orientation of the `112` family. -/
theorem sum_one_pos (T : OrientedTriangle E o) (q : TricolorIndex)
    (hq : q.i + q.j + q.k = 1) (hnz : q.i * q.j * q.k ≠ 0) :
    PositivelyOriented (o := o) (T.tricolorTriangle q) := by
  have hA := area_sum_one T q hq
  have hL := (sum_one_sign T q hq).1 hnz
  have hns := normSq_BC_pos (o := o) T
  show 0 < orientedArea o ((T.tricolorTriangle q).second - (T.tricolorTriangle q).first)
    ((T.tricolorTriangle q).third - (T.tricolorTriangle q).first)
  rw [hA]
  exact mul_pos hns hL

/-- Negative orientation of the `001` and `022` families. -/
theorem sum_one_neg (T : OrientedTriangle E o) (q : TricolorIndex)
    (hq : q.i + q.j + q.k = 1) (hz : q.i * q.j * q.k = 0) :
    NegativelyOriented (o := o) (T.tricolorTriangle q) := by
  have hA := area_sum_one T q hq
  have hL := (sum_one_sign T q hq).2 hz
  have hns := normSq_BC_pos (o := o) T
  show orientedArea o ((T.tricolorTriangle q).second - (T.tricolorTriangle q).first)
    ((T.tricolorTriangle q).third - (T.tricolorTriangle q).first) < 0
  rw [hA]
  exact mul_neg_of_pos_of_neg hns hL

/-- **`tricolor_orientation`**, complete. -/
theorem tricolor_orientation_full (T : OrientedTriangle E o)
    (h : Function.Injective (fun q : ConstellationIndex => T.constellationPoint q)) (q : TricolorIndex) :
    (q.i + q.j + q.k = 0 → PositivelyOriented (o := o) (T.tricolorTriangle q)) ∧
    (q.i + q.j + q.k = 2 → NegativelyOriented (o := o) (T.tricolorTriangle q)) ∧
    (q.i + q.j + q.k = 1 →
      (q.i * q.j * q.k ≠ 0 ∧ PositivelyOriented (o := o) (T.tricolorTriangle q)) ∨
      (q.i * q.j * q.k = 0 ∧ NegativelyOriented (o := o) (T.tricolorTriangle q))) := by
  obtain ⟨h0, h2⟩ := m4d_tricolor_orientation_zero_two (o := o) T h
  refine ⟨h0 q, h2 q, fun hq => ?_⟩
  by_cases hz : q.i * q.j * q.k = 0
  · exact Or.inr ⟨hz, sum_one_neg (o := o) T q hq hz⟩
  · exact Or.inl ⟨hz, sum_one_pos (o := o) T q hq hz⟩

end M5

#print axioms M5.tricolor_orientation_full
#print axioms M5.sum_one_sign
