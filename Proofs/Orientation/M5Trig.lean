import XamboMorleyBase
import M8KLocal

/-! ### Trigonometric bookkeeping for the half-angle parameters

For `x ∈ (0, π/3)` and a label `s : Fin 3`, set `u = x - labelAngle s / 2 = x - s.val·π/3`.
Then `cos (u/2) ≠ 0`, `tan (u/2) ≠ 0`, `3 tan²(u/2) ≠ 1`, `tan²(u/2) ≠ 3`, `sin u ≠ 0`, and
`sin u > 0` exactly when `s = 0`. -/

namespace M5
open XamboMorley XamboMorley.OrientedTriangle
open scoped Real

theorem s3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)

theorem one_div_s3_pos : (0:ℝ) < 1 / Real.sqrt 3 := by positivity

theorem s3_pos : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

theorem one_div_s3_sq : (1 / Real.sqrt 3) ^ 2 = (1/3 : ℝ) := by
  rw [div_pow, one_pow, Real.sq_sqrt]; norm_num

theorem tan_bounds_zero {x : ℝ} (h0 : 0 < x) (h1 : x < Real.pi / 3) :
    Real.cos (x/2) ≠ 0 ∧ 0 < Real.tan (x/2) ∧ Real.tan (x/2) ^ 2 < 1/3 := by
  have hx2 : 0 < x/2 := by linarith
  have hx6 : x/2 < Real.pi / 6 := by linarith
  have hpi : x/2 < Real.pi / 2 := by linarith [Real.pi_pos]
  refine ⟨?_, Real.tan_pos_of_pos_of_lt_pi_div_two hx2 hpi, ?_⟩
  · exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi⟩)
  · have hlt : Real.tan (x/2) < 1 / Real.sqrt 3 := by
      have := Real.tan_lt_tan_of_lt_of_lt_pi_div_two (x := x/2) (y := Real.pi/6)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hx6
      rwa [Real.tan_pi_div_six] at this
    have hpos := Real.tan_pos_of_pos_of_lt_pi_div_two hx2 hpi
    nlinarith [one_div_s3_sq]

theorem tan_bounds_one {x : ℝ} (h0 : 0 < x) (h1 : x < Real.pi / 3) :
    Real.cos (x/2 - Real.pi/6) ≠ 0 ∧ Real.tan (x/2 - Real.pi/6) ≠ 0 ∧
      Real.tan (x/2 - Real.pi/6) ^ 2 < 1/3 := by
  have hx2 : 0 < x/2 := by linarith
  have hx6 : x/2 < Real.pi / 6 := by linarith
  set θ := x/2 - Real.pi/6 with hθ
  have hθ0 : θ < 0 := by simp [hθ]; linarith
  have hθ1 : -(Real.pi/6) < θ := by simp [hθ]; linarith
  have hθup : θ < Real.pi / 2 := by linarith [Real.pi_pos]
  have hθlo : -(Real.pi/2) < θ := by linarith [Real.pi_pos]
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨hθlo, hθup⟩)
  have htneg : Real.tan θ < 0 := by
    have := Real.tan_lt_tan_of_lt_of_lt_pi_div_two (x := θ) (y := 0) hθlo
      (by linarith [Real.pi_pos]) hθ0
    simpa using this
  have htlow : -(1 / Real.sqrt 3) < Real.tan θ := by
    have h := Real.tan_lt_tan_of_lt_of_lt_pi_div_two (x := -(Real.pi/6)) (y := θ)
      (by linarith [Real.pi_pos]) hθup hθ1
    rw [Real.tan_neg, Real.tan_pi_div_six] at h
    linarith
  refine ⟨hcos, by linarith, ?_⟩
  nlinarith [one_div_s3_sq]

theorem tan_bounds_two {x : ℝ} (h0 : 0 < x) (h1 : x < Real.pi / 3) :
    Real.cos (x/2 - Real.pi/3) ≠ 0 ∧ Real.tan (x/2 - Real.pi/3) ≠ 0 ∧
      1/3 < Real.tan (x/2 - Real.pi/3) ^ 2 ∧ Real.tan (x/2 - Real.pi/3) ^ 2 < 3 := by
  have hx2 : 0 < x/2 := by linarith
  have hx6 : x/2 < Real.pi / 6 := by linarith
  set θ := x/2 - Real.pi/3 with hθ
  have hθ0 : θ < -(Real.pi/6) := by simp [hθ]; linarith
  have hθ1 : -(Real.pi/3) < θ := by simp [hθ]; linarith
  have hθup : θ < Real.pi / 2 := by linarith [Real.pi_pos]
  have hθlo : -(Real.pi/2) < θ := by linarith [Real.pi_pos]
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨hθlo, hθup⟩)
  have htupper : Real.tan θ < -(1 / Real.sqrt 3) := by
    have h := Real.tan_lt_tan_of_lt_of_lt_pi_div_two (x := θ) (y := -(Real.pi/6)) hθlo
      (by linarith [Real.pi_pos]) hθ0
    rw [Real.tan_neg, Real.tan_pi_div_six] at h
    linarith
  have htlow : -(Real.sqrt 3) < Real.tan θ := by
    have h := Real.tan_lt_tan_of_lt_of_lt_pi_div_two (x := -(Real.pi/3)) (y := θ)
      (by linarith [Real.pi_pos]) hθup hθ1
    rw [Real.tan_neg, Real.tan_pi_div_three] at h
    linarith
  have hs3 := one_div_s3_pos
  refine ⟨hcos, by linarith, ?_, ?_⟩
  · nlinarith [one_div_s3_sq, s3_sq, sq_nonneg (Real.tan θ)]
  · nlinarith [s3_sq, sq_nonneg (Real.tan θ)]

/-- The combined bookkeeping for one angle. -/
theorem shift_trig (x : ℝ) (h0 : 0 < x) (h1 : x < Real.pi / 3) (s : TrisectorLabel) :
    Real.cos ((x - labelAngle s / 2) / 2) ≠ 0 ∧
    Real.tan ((x - labelAngle s / 2) / 2) ≠ 0 ∧
    3 * Real.tan ((x - labelAngle s / 2) / 2) ^ 2 - 1 ≠ 0 ∧
    Real.tan ((x - labelAngle s / 2) / 2) ^ 2 - 3 ≠ 0 ∧
    (0 < Real.sin (x - labelAngle s / 2) ↔ s = 0) ∧
    Real.sin (x - labelAngle s / 2) ≠ 0 := by
  have hcast := m2_labelAngle_half s
  have hsv : s.val = 0 ∨ s.val = 1 ∨ s.val = 2 := by
    have := ZMod.val_lt (n := 3) s; omega
  rcases hsv with h | h | h
  · -- s.val = 0 : u = x
    obtain ⟨hc1, hc2, hc3⟩ := tan_bounds_zero h0 h1
    have hsval : (s.val : ℝ) = 0 := by rw [h]; norm_num
    have hu : x - labelAngle s / 2 = x := by rw [hcast, hsval]; ring
    have hs0 : s = 0 := by
      have h2 := (ZMod.natCast_zmod_val s).symm
      rw [h] at h2; simpa using h2
    have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
    rw [hu]
    exact ⟨hc1, ne_of_gt hc2, by nlinarith, by nlinarith,
      ⟨fun _ => hs0, fun _ => hsin⟩, ne_of_gt hsin⟩
  · -- s.val = 1 : u = 2·(x/2 - π/6)
    obtain ⟨hc1, hc2, hc3⟩ := tan_bounds_one h0 h1
    have hsval : (s.val : ℝ) = 1 := by rw [h]; norm_num
    have hu : x - labelAngle s / 2 = 2 * (x/2 - Real.pi/6) := by rw [hcast, hsval]; ring
    have hth : (2 * (x/2 - Real.pi/6))/2 = x/2 - Real.pi/6 := by ring
    have hsne : s ≠ 0 := by
      intro hh; rw [hh] at h; simp at h
    have hsin : Real.sin (2 * (x/2 - Real.pi/6)) < 0 := by
      rw [show 2 * (x/2 - Real.pi/6) = -(Real.pi/3 - x) by ring, Real.sin_neg]
      have hp := Real.sin_pos_of_pos_of_lt_pi (x := Real.pi/3 - x) (by linarith) (by linarith)
      linarith
    rw [hu, hth]
    exact ⟨hc1, hc2, by nlinarith, by nlinarith,
      ⟨fun hh => absurd hh (by linarith), fun hh => absurd hh hsne⟩, by linarith⟩
  · -- s.val = 2 : u = 2·(x/2 - π/3)
    obtain ⟨hc1, hc2, hc3, hc4⟩ := tan_bounds_two h0 h1
    have hsval : (s.val : ℝ) = 2 := by rw [h]; norm_num
    have hu : x - labelAngle s / 2 = 2 * (x/2 - Real.pi/3) := by rw [hcast, hsval]; ring
    have hth : (2 * (x/2 - Real.pi/3))/2 = x/2 - Real.pi/3 := by ring
    have hsne : s ≠ 0 := by
      intro hh; rw [hh] at h; simp at h
    have hsin : Real.sin (2 * (x/2 - Real.pi/3)) < 0 := by
      rw [show 2 * (x/2 - Real.pi/3) = -(2*Real.pi/3 - x) by ring, Real.sin_neg]
      have hp := Real.sin_pos_of_pos_of_lt_pi (x := 2*Real.pi/3 - x) (by linarith) (by linarith)
      linarith
    rw [hu, hth]
    exact ⟨hc1, hc2, by nlinarith, by nlinarith,
      ⟨fun hh => absurd hh (by linarith), fun hh => absurd hh hsne⟩, by linarith⟩

end M5

#print axioms M5.shift_trig
