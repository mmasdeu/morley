import M2T

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

/-! ### The realness-to-parallelism bridge -/

theorem m2_toComplex_sub_ne {X Y : E} (h : X ≠ Y) : toComplex o (X - Y) ≠ 0 := by
  rw [toComplex_sub]
  intro h0
  exact h (toComplex_injective o (sub_eq_zero.mp h0))

theorem m2_cp_ne_same (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {c : TrisectorColor} {a b a' b' : TrisectorLabel}
    (hne : (⟨c, a, b⟩ : ConstellationIndex) ≠ ⟨c, a', b'⟩) :
    T.constellationPoint ⟨c, a, b⟩ ≠ T.constellationPoint ⟨c, a', b'⟩ := by
  intro hh
  exact hne (h hh)

theorem m2_W_ne (T : OrientedTriangle E o) : toComplex o (T.C - T.A) ≠ 0 :=
  m2_toComplex_sub_ne (o := o) T.A_ne_C.symm

theorem m2_pMS_side (T : OrientedTriangle E o) (s : TrisectorLabel) :
    T.parallelToMorleySide (OrientedTriangle.m3pSide T s) := by
  rcases zmod3_cases s with rfl | rfl | rfl
  · rw [OrientedTriangle.m3p_side_zero]; exact Or.inl ⟨1, by simp⟩
  · rw [OrientedTriangle.m3p_side_one]; exact Or.inr (Or.inl ⟨1, by simp⟩)
  · rw [OrientedTriangle.m3p_side_two]; exact Or.inr (Or.inr ⟨1, by simp⟩)

theorem m2_pMS_of_par (T : OrientedTriangle E o) {v w : E}
    (hp : T.parallelToMorleySide v) (h : Parallel v w) : T.parallelToMorleySide w :=
  m3c_pMS_of_parallel_trans T hp h

theorem m2_pMS_neg (T : OrientedTriangle E o) {v : E}
    (h : T.parallelToMorleySide v) : T.parallelToMorleySide (-v) := by
  simpa using m3c_pMS_smul T (-1) h

/-! ### The eighteen first sides -/

/-- The first side of the tricolour triangle `(0,0,0)` is parallel to a Morley side;
the red equal-sum join used is that of `(0,0)` with `(2,1)`. -/
theorem m2_first_000 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 0, 0⟩ - T.constellationPoint ⟨.red, 0, 0⟩) := by
  have hne : T.constellationPoint ⟨.green, 0, 0⟩ ≠
      T.constellationPoint ⟨.red, 0, 0⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 0, 0⟩ -
      T.constellationPoint ⟨.red, 0, 0⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 0, 0⟩ -
      T.constellationPoint ⟨.red, 0, 0⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 0, 0⟩ ≠
      T.constellationPoint ⟨.red, 2, 1⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 0, 0⟩ -
      T.constellationPoint ⟨.red, 2, 1⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 0, 0⟩ -
      T.constellationPoint ⟨.red, 2, 1⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 0 0 0 2 1 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 0 0 0 2 1
  have h2 := m3c_red_mul_eq T 0 0 0 2 1 (by decide)
  have hNA : m3cNA T 0 0 0 2 1 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 0, 0⟩ -
        T.constellationPoint ⟨.red, 0, 0⟩) * m3cD T 0 0 0 2 1 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 0 0 0 2 1)
    (B := -(m3cNA T 0 0 0 2 1)) (by simpa using hNA)
    (m2_cross_000_21 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 0, 0⟩ -
      T.constellationPoint ⟨.red, 0, 0⟩)
      (T.constellationPoint ⟨.red, 0, 0⟩ - T.constellationPoint ⟨.red, 2, 1⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 0, 0⟩ - T.constellationPoint ⟨.red, 0, 0⟩)
      (w := T.constellationPoint ⟨.red, 0, 0⟩ - T.constellationPoint ⟨.red, 2, 1⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 0, 0⟩ -
          T.constellationPoint ⟨.red, 2, 1⟩) * m3cD T 0 0 0 2 1
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 0, 0⟩ -
            T.constellationPoint ⟨.red, 0, 0⟩)) * m3cD T 0 0 0 2 1 := by
      calc toComplex o (T.constellationPoint ⟨.red, 0, 0⟩ -
            T.constellationPoint ⟨.red, 2, 1⟩) * m3cD T 0 0 0 2 1
          = m3cNBp T 0 0 0 2 1 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 0 0 0 2 1)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 0, 0⟩ -
              T.constellationPoint ⟨.red, 0, 0⟩)) * m3cD T 0 0 0 2 1 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 0, 0⟩ - T.constellationPoint ⟨.red, 2, 1⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 0, 0⟩ -
          T.constellationPoint ⟨.red, 2, 1⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 0) (OrientedTriangle.m3p_red_par31 T 0)
    simpa only [neg_sub, show ((0 : TrisectorLabel) + 1) = 1 from by decide, show ((0 : TrisectorLabel) + 2) = 2 from by decide] using h0
  exact m3c_hfirst_of_collinear T 0 0 0 2 1 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(0,0,2)` is parallel to a Morley side;
the red equal-sum join used is that of `(0,0)` with `(1,2)`. -/
theorem m2_first_002 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 0, 2⟩ - T.constellationPoint ⟨.red, 0, 0⟩) := by
  have hne : T.constellationPoint ⟨.green, 0, 2⟩ ≠
      T.constellationPoint ⟨.red, 0, 0⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 0, 2⟩ -
      T.constellationPoint ⟨.red, 0, 0⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 0, 2⟩ -
      T.constellationPoint ⟨.red, 0, 0⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 0, 0⟩ ≠
      T.constellationPoint ⟨.red, 1, 2⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 0, 0⟩ -
      T.constellationPoint ⟨.red, 1, 2⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 0, 0⟩ -
      T.constellationPoint ⟨.red, 1, 2⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 0 0 2 1 2 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 0 0 2 1 2
  have h2 := m3c_red_mul_eq T 0 0 2 1 2 (by decide)
  have hNA : m3cNA T 0 0 2 1 2 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 0, 2⟩ -
        T.constellationPoint ⟨.red, 0, 0⟩) * m3cD T 0 0 2 1 2 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 0 0 2 1 2)
    (B := -(m3cNA T 0 0 2 1 2)) (by simpa using hNA)
    (m2_cross_002_12 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 0, 2⟩ -
      T.constellationPoint ⟨.red, 0, 0⟩)
      (T.constellationPoint ⟨.red, 0, 0⟩ - T.constellationPoint ⟨.red, 1, 2⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 0, 2⟩ - T.constellationPoint ⟨.red, 0, 0⟩)
      (w := T.constellationPoint ⟨.red, 0, 0⟩ - T.constellationPoint ⟨.red, 1, 2⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 0, 0⟩ -
          T.constellationPoint ⟨.red, 1, 2⟩) * m3cD T 0 0 2 1 2
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 0, 2⟩ -
            T.constellationPoint ⟨.red, 0, 0⟩)) * m3cD T 0 0 2 1 2 := by
      calc toComplex o (T.constellationPoint ⟨.red, 0, 0⟩ -
            T.constellationPoint ⟨.red, 1, 2⟩) * m3cD T 0 0 2 1 2
          = m3cNBp T 0 0 2 1 2 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 0 0 2 1 2)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 0, 2⟩ -
              T.constellationPoint ⟨.red, 0, 0⟩)) * m3cD T 0 0 2 1 2 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 0, 0⟩ - T.constellationPoint ⟨.red, 1, 2⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 1, 2⟩ -
          T.constellationPoint ⟨.red, 0, 0⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 2) (OrientedTriangle.m3p_red_par12 T 0)
    simpa only [neg_sub, show ((0 : TrisectorLabel) + 1) = 1 from by decide, show ((0 : TrisectorLabel) + 2) = 2 from by decide] using m2_pMS_neg T h0
  exact m3c_hfirst_of_collinear T 0 0 2 1 2 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(0,1,1)` is parallel to a Morley side;
the red equal-sum join used is that of `(0,1)` with `(1,0)`. -/
theorem m2_first_011 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 1, 1⟩ - T.constellationPoint ⟨.red, 0, 1⟩) := by
  have hne : T.constellationPoint ⟨.green, 1, 1⟩ ≠
      T.constellationPoint ⟨.red, 0, 1⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 1, 1⟩ -
      T.constellationPoint ⟨.red, 0, 1⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 1, 1⟩ -
      T.constellationPoint ⟨.red, 0, 1⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 0, 1⟩ ≠
      T.constellationPoint ⟨.red, 1, 0⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 0, 1⟩ -
      T.constellationPoint ⟨.red, 1, 0⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 0, 1⟩ -
      T.constellationPoint ⟨.red, 1, 0⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 0 1 1 1 0 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 0 1 1 1 0
  have h2 := m3c_red_mul_eq T 0 1 1 1 0 (by decide)
  have hNA : m3cNA T 0 1 1 1 0 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 1, 1⟩ -
        T.constellationPoint ⟨.red, 0, 1⟩) * m3cD T 0 1 1 1 0 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 0 1 1 1 0)
    (B := -(m3cNA T 0 1 1 1 0)) (by simpa using hNA)
    (m2_cross_011_10 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 1, 1⟩ -
      T.constellationPoint ⟨.red, 0, 1⟩)
      (T.constellationPoint ⟨.red, 0, 1⟩ - T.constellationPoint ⟨.red, 1, 0⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 1, 1⟩ - T.constellationPoint ⟨.red, 0, 1⟩)
      (w := T.constellationPoint ⟨.red, 0, 1⟩ - T.constellationPoint ⟨.red, 1, 0⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 0, 1⟩ -
          T.constellationPoint ⟨.red, 1, 0⟩) * m3cD T 0 1 1 1 0
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 1, 1⟩ -
            T.constellationPoint ⟨.red, 0, 1⟩)) * m3cD T 0 1 1 1 0 := by
      calc toComplex o (T.constellationPoint ⟨.red, 0, 1⟩ -
            T.constellationPoint ⟨.red, 1, 0⟩) * m3cD T 0 1 1 1 0
          = m3cNBp T 0 1 1 1 0 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 0 1 1 1 0)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 1, 1⟩ -
              T.constellationPoint ⟨.red, 0, 1⟩)) * m3cD T 0 1 1 1 0 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 0, 1⟩ - T.constellationPoint ⟨.red, 1, 0⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 1, 0⟩ -
          T.constellationPoint ⟨.red, 0, 1⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 1) (OrientedTriangle.m3p_red_par31 T 1)
    simpa only [neg_sub, show ((1 : TrisectorLabel) + 1) = 2 from by decide, show ((1 : TrisectorLabel) + 2) = 0 from by decide] using m2_pMS_neg T h0
  exact m3c_hfirst_of_collinear T 0 1 1 1 0 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(0,1,2)` is parallel to a Morley side;
the red equal-sum join used is that of `(0,1)` with `(2,2)`. -/
theorem m2_first_012 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 1, 2⟩ - T.constellationPoint ⟨.red, 0, 1⟩) := by
  have hne : T.constellationPoint ⟨.green, 1, 2⟩ ≠
      T.constellationPoint ⟨.red, 0, 1⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 1, 2⟩ -
      T.constellationPoint ⟨.red, 0, 1⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 1, 2⟩ -
      T.constellationPoint ⟨.red, 0, 1⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 0, 1⟩ ≠
      T.constellationPoint ⟨.red, 2, 2⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 0, 1⟩ -
      T.constellationPoint ⟨.red, 2, 2⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 0, 1⟩ -
      T.constellationPoint ⟨.red, 2, 2⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 0 1 2 2 2 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 0 1 2 2 2
  have h2 := m3c_red_mul_eq T 0 1 2 2 2 (by decide)
  have hNA : m3cNA T 0 1 2 2 2 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 1, 2⟩ -
        T.constellationPoint ⟨.red, 0, 1⟩) * m3cD T 0 1 2 2 2 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 0 1 2 2 2)
    (B := -(m3cNA T 0 1 2 2 2)) (by simpa using hNA)
    (m2_cross_012_22 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 1, 2⟩ -
      T.constellationPoint ⟨.red, 0, 1⟩)
      (T.constellationPoint ⟨.red, 0, 1⟩ - T.constellationPoint ⟨.red, 2, 2⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 1, 2⟩ - T.constellationPoint ⟨.red, 0, 1⟩)
      (w := T.constellationPoint ⟨.red, 0, 1⟩ - T.constellationPoint ⟨.red, 2, 2⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 0, 1⟩ -
          T.constellationPoint ⟨.red, 2, 2⟩) * m3cD T 0 1 2 2 2
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 1, 2⟩ -
            T.constellationPoint ⟨.red, 0, 1⟩)) * m3cD T 0 1 2 2 2 := by
      calc toComplex o (T.constellationPoint ⟨.red, 0, 1⟩ -
            T.constellationPoint ⟨.red, 2, 2⟩) * m3cD T 0 1 2 2 2
          = m3cNBp T 0 1 2 2 2 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 0 1 2 2 2)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 1, 2⟩ -
              T.constellationPoint ⟨.red, 0, 1⟩)) * m3cD T 0 1 2 2 2 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 0, 1⟩ - T.constellationPoint ⟨.red, 2, 2⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 0, 1⟩ -
          T.constellationPoint ⟨.red, 2, 2⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 2) (OrientedTriangle.m3p_red_par23 T 1)
    simpa only [neg_sub, show ((1 : TrisectorLabel) + 1) = 2 from by decide, show ((1 : TrisectorLabel) + 2) = 0 from by decide] using h0
  exact m3c_hfirst_of_collinear T 0 1 2 2 2 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(0,2,0)` is parallel to a Morley side;
the red equal-sum join used is that of `(0,2)` with `(1,1)`. -/
theorem m2_first_020 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 2, 0⟩ - T.constellationPoint ⟨.red, 0, 2⟩) := by
  have hne : T.constellationPoint ⟨.green, 2, 0⟩ ≠
      T.constellationPoint ⟨.red, 0, 2⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 2, 0⟩ -
      T.constellationPoint ⟨.red, 0, 2⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 2, 0⟩ -
      T.constellationPoint ⟨.red, 0, 2⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 0, 2⟩ ≠
      T.constellationPoint ⟨.red, 1, 1⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 0, 2⟩ -
      T.constellationPoint ⟨.red, 1, 1⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 0, 2⟩ -
      T.constellationPoint ⟨.red, 1, 1⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 0 2 0 1 1 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 0 2 0 1 1
  have h2 := m3c_red_mul_eq T 0 2 0 1 1 (by decide)
  have hNA : m3cNA T 0 2 0 1 1 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 2, 0⟩ -
        T.constellationPoint ⟨.red, 0, 2⟩) * m3cD T 0 2 0 1 1 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 0 2 0 1 1)
    (B := -(m3cNA T 0 2 0 1 1)) (by simpa using hNA)
    (m2_cross_020_11 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 2, 0⟩ -
      T.constellationPoint ⟨.red, 0, 2⟩)
      (T.constellationPoint ⟨.red, 0, 2⟩ - T.constellationPoint ⟨.red, 1, 1⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 2, 0⟩ - T.constellationPoint ⟨.red, 0, 2⟩)
      (w := T.constellationPoint ⟨.red, 0, 2⟩ - T.constellationPoint ⟨.red, 1, 1⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 0, 2⟩ -
          T.constellationPoint ⟨.red, 1, 1⟩) * m3cD T 0 2 0 1 1
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 2, 0⟩ -
            T.constellationPoint ⟨.red, 0, 2⟩)) * m3cD T 0 2 0 1 1 := by
      calc toComplex o (T.constellationPoint ⟨.red, 0, 2⟩ -
            T.constellationPoint ⟨.red, 1, 1⟩) * m3cD T 0 2 0 1 1
          = m3cNBp T 0 2 0 1 1 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 0 2 0 1 1)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 2, 0⟩ -
              T.constellationPoint ⟨.red, 0, 2⟩)) * m3cD T 0 2 0 1 1 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 0, 2⟩ - T.constellationPoint ⟨.red, 1, 1⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 1, 1⟩ -
          T.constellationPoint ⟨.red, 0, 2⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 0) (OrientedTriangle.m3p_red_par23 T 2)
    simpa only [neg_sub, show ((2 : TrisectorLabel) + 1) = 0 from by decide, show ((2 : TrisectorLabel) + 2) = 1 from by decide] using m2_pMS_neg T h0
  exact m3c_hfirst_of_collinear T 0 2 0 1 1 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(0,2,1)` is parallel to a Morley side;
the red equal-sum join used is that of `(0,2)` with `(2,0)`. -/
theorem m2_first_021 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 2, 1⟩ - T.constellationPoint ⟨.red, 0, 2⟩) := by
  have hne : T.constellationPoint ⟨.green, 2, 1⟩ ≠
      T.constellationPoint ⟨.red, 0, 2⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 2, 1⟩ -
      T.constellationPoint ⟨.red, 0, 2⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 2, 1⟩ -
      T.constellationPoint ⟨.red, 0, 2⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 0, 2⟩ ≠
      T.constellationPoint ⟨.red, 2, 0⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 0, 2⟩ -
      T.constellationPoint ⟨.red, 2, 0⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 0, 2⟩ -
      T.constellationPoint ⟨.red, 2, 0⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 0 2 1 2 0 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 0 2 1 2 0
  have h2 := m3c_red_mul_eq T 0 2 1 2 0 (by decide)
  have hNA : m3cNA T 0 2 1 2 0 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 2, 1⟩ -
        T.constellationPoint ⟨.red, 0, 2⟩) * m3cD T 0 2 1 2 0 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 0 2 1 2 0)
    (B := -(m3cNA T 0 2 1 2 0)) (by simpa using hNA)
    (m2_cross_021_20 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 2, 1⟩ -
      T.constellationPoint ⟨.red, 0, 2⟩)
      (T.constellationPoint ⟨.red, 0, 2⟩ - T.constellationPoint ⟨.red, 2, 0⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 2, 1⟩ - T.constellationPoint ⟨.red, 0, 2⟩)
      (w := T.constellationPoint ⟨.red, 0, 2⟩ - T.constellationPoint ⟨.red, 2, 0⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 0, 2⟩ -
          T.constellationPoint ⟨.red, 2, 0⟩) * m3cD T 0 2 1 2 0
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 2, 1⟩ -
            T.constellationPoint ⟨.red, 0, 2⟩)) * m3cD T 0 2 1 2 0 := by
      calc toComplex o (T.constellationPoint ⟨.red, 0, 2⟩ -
            T.constellationPoint ⟨.red, 2, 0⟩) * m3cD T 0 2 1 2 0
          = m3cNBp T 0 2 1 2 0 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 0 2 1 2 0)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 2, 1⟩ -
              T.constellationPoint ⟨.red, 0, 2⟩)) * m3cD T 0 2 1 2 0 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 0, 2⟩ - T.constellationPoint ⟨.red, 2, 0⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 0, 2⟩ -
          T.constellationPoint ⟨.red, 2, 0⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 1) (OrientedTriangle.m3p_red_par12 T 2)
    simpa only [neg_sub, show ((2 : TrisectorLabel) + 1) = 0 from by decide, show ((2 : TrisectorLabel) + 2) = 1 from by decide] using h0
  exact m3c_hfirst_of_collinear T 0 2 1 2 0 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(1,0,1)` is parallel to a Morley side;
the red equal-sum join used is that of `(1,0)` with `(2,2)`. -/
theorem m2_first_101 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 0, 1⟩ - T.constellationPoint ⟨.red, 1, 0⟩) := by
  have hne : T.constellationPoint ⟨.green, 0, 1⟩ ≠
      T.constellationPoint ⟨.red, 1, 0⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 0, 1⟩ -
      T.constellationPoint ⟨.red, 1, 0⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 0, 1⟩ -
      T.constellationPoint ⟨.red, 1, 0⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 1, 0⟩ ≠
      T.constellationPoint ⟨.red, 2, 2⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 1, 0⟩ -
      T.constellationPoint ⟨.red, 2, 2⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 1, 0⟩ -
      T.constellationPoint ⟨.red, 2, 2⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 1 0 1 2 2 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 1 0 1 2 2
  have h2 := m3c_red_mul_eq T 1 0 1 2 2 (by decide)
  have hNA : m3cNA T 1 0 1 2 2 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 0, 1⟩ -
        T.constellationPoint ⟨.red, 1, 0⟩) * m3cD T 1 0 1 2 2 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 1 0 1 2 2)
    (B := -(m3cNA T 1 0 1 2 2)) (by simpa using hNA)
    (m2_cross_101_22 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 0, 1⟩ -
      T.constellationPoint ⟨.red, 1, 0⟩)
      (T.constellationPoint ⟨.red, 1, 0⟩ - T.constellationPoint ⟨.red, 2, 2⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 0, 1⟩ - T.constellationPoint ⟨.red, 1, 0⟩)
      (w := T.constellationPoint ⟨.red, 1, 0⟩ - T.constellationPoint ⟨.red, 2, 2⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 1, 0⟩ -
          T.constellationPoint ⟨.red, 2, 2⟩) * m3cD T 1 0 1 2 2
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 0, 1⟩ -
            T.constellationPoint ⟨.red, 1, 0⟩)) * m3cD T 1 0 1 2 2 := by
      calc toComplex o (T.constellationPoint ⟨.red, 1, 0⟩ -
            T.constellationPoint ⟨.red, 2, 2⟩) * m3cD T 1 0 1 2 2
          = m3cNBp T 1 0 1 2 2 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 1 0 1 2 2)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 0, 1⟩ -
              T.constellationPoint ⟨.red, 1, 0⟩)) * m3cD T 1 0 1 2 2 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 1, 0⟩ - T.constellationPoint ⟨.red, 2, 2⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 2, 2⟩ -
          T.constellationPoint ⟨.red, 1, 0⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 0) (OrientedTriangle.m3p_red_par12 T 1)
    simpa only [neg_sub, show ((1 : TrisectorLabel) + 1) = 2 from by decide, show ((1 : TrisectorLabel) + 2) = 0 from by decide] using m2_pMS_neg T h0
  exact m3c_hfirst_of_collinear T 1 0 1 2 2 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(1,0,2)` is parallel to a Morley side;
the red equal-sum join used is that of `(1,0)` with `(0,1)`. -/
theorem m2_first_102 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 0, 2⟩ - T.constellationPoint ⟨.red, 1, 0⟩) := by
  have hne : T.constellationPoint ⟨.green, 0, 2⟩ ≠
      T.constellationPoint ⟨.red, 1, 0⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 0, 2⟩ -
      T.constellationPoint ⟨.red, 1, 0⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 0, 2⟩ -
      T.constellationPoint ⟨.red, 1, 0⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 1, 0⟩ ≠
      T.constellationPoint ⟨.red, 0, 1⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 1, 0⟩ -
      T.constellationPoint ⟨.red, 0, 1⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 1, 0⟩ -
      T.constellationPoint ⟨.red, 0, 1⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 1 0 2 0 1 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 1 0 2 0 1
  have h2 := m3c_red_mul_eq T 1 0 2 0 1 (by decide)
  have hNA : m3cNA T 1 0 2 0 1 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 0, 2⟩ -
        T.constellationPoint ⟨.red, 1, 0⟩) * m3cD T 1 0 2 0 1 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 1 0 2 0 1)
    (B := -(m3cNA T 1 0 2 0 1)) (by simpa using hNA)
    (m2_cross_102_01 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 0, 2⟩ -
      T.constellationPoint ⟨.red, 1, 0⟩)
      (T.constellationPoint ⟨.red, 1, 0⟩ - T.constellationPoint ⟨.red, 0, 1⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 0, 2⟩ - T.constellationPoint ⟨.red, 1, 0⟩)
      (w := T.constellationPoint ⟨.red, 1, 0⟩ - T.constellationPoint ⟨.red, 0, 1⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 1, 0⟩ -
          T.constellationPoint ⟨.red, 0, 1⟩) * m3cD T 1 0 2 0 1
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 0, 2⟩ -
            T.constellationPoint ⟨.red, 1, 0⟩)) * m3cD T 1 0 2 0 1 := by
      calc toComplex o (T.constellationPoint ⟨.red, 1, 0⟩ -
            T.constellationPoint ⟨.red, 0, 1⟩) * m3cD T 1 0 2 0 1
          = m3cNBp T 1 0 2 0 1 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 1 0 2 0 1)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 0, 2⟩ -
              T.constellationPoint ⟨.red, 1, 0⟩)) * m3cD T 1 0 2 0 1 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 1, 0⟩ - T.constellationPoint ⟨.red, 0, 1⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 1, 0⟩ -
          T.constellationPoint ⟨.red, 0, 1⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 1) (OrientedTriangle.m3p_red_par31 T 1)
    simpa only [neg_sub, show ((1 : TrisectorLabel) + 1) = 2 from by decide, show ((1 : TrisectorLabel) + 2) = 0 from by decide] using h0
  exact m3c_hfirst_of_collinear T 1 0 2 0 1 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(1,1,0)` is parallel to a Morley side;
the red equal-sum join used is that of `(1,1)` with `(2,0)`. -/
theorem m2_first_110 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 1, 0⟩ - T.constellationPoint ⟨.red, 1, 1⟩) := by
  have hne : T.constellationPoint ⟨.green, 1, 0⟩ ≠
      T.constellationPoint ⟨.red, 1, 1⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 1, 0⟩ -
      T.constellationPoint ⟨.red, 1, 1⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 1, 0⟩ -
      T.constellationPoint ⟨.red, 1, 1⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 1, 1⟩ ≠
      T.constellationPoint ⟨.red, 2, 0⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 1, 1⟩ -
      T.constellationPoint ⟨.red, 2, 0⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 1, 1⟩ -
      T.constellationPoint ⟨.red, 2, 0⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 1 1 0 2 0 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 1 1 0 2 0
  have h2 := m3c_red_mul_eq T 1 1 0 2 0 (by decide)
  have hNA : m3cNA T 1 1 0 2 0 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 1, 0⟩ -
        T.constellationPoint ⟨.red, 1, 1⟩) * m3cD T 1 1 0 2 0 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 1 1 0 2 0)
    (B := -(m3cNA T 1 1 0 2 0)) (by simpa using hNA)
    (m2_cross_110_20 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 1, 0⟩ -
      T.constellationPoint ⟨.red, 1, 1⟩)
      (T.constellationPoint ⟨.red, 1, 1⟩ - T.constellationPoint ⟨.red, 2, 0⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 1, 0⟩ - T.constellationPoint ⟨.red, 1, 1⟩)
      (w := T.constellationPoint ⟨.red, 1, 1⟩ - T.constellationPoint ⟨.red, 2, 0⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 1, 1⟩ -
          T.constellationPoint ⟨.red, 2, 0⟩) * m3cD T 1 1 0 2 0
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 1, 0⟩ -
            T.constellationPoint ⟨.red, 1, 1⟩)) * m3cD T 1 1 0 2 0 := by
      calc toComplex o (T.constellationPoint ⟨.red, 1, 1⟩ -
            T.constellationPoint ⟨.red, 2, 0⟩) * m3cD T 1 1 0 2 0
          = m3cNBp T 1 1 0 2 0 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 1 1 0 2 0)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 1, 0⟩ -
              T.constellationPoint ⟨.red, 1, 1⟩)) * m3cD T 1 1 0 2 0 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 1, 1⟩ - T.constellationPoint ⟨.red, 2, 0⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 2, 0⟩ -
          T.constellationPoint ⟨.red, 1, 1⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 2) (OrientedTriangle.m3p_red_par31 T 2)
    simpa only [neg_sub, show ((2 : TrisectorLabel) + 1) = 0 from by decide, show ((2 : TrisectorLabel) + 2) = 1 from by decide] using m2_pMS_neg T h0
  exact m3c_hfirst_of_collinear T 1 1 0 2 0 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(1,1,1)` is parallel to a Morley side;
the red equal-sum join used is that of `(1,1)` with `(0,2)`. -/
theorem m2_first_111 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 1, 1⟩ - T.constellationPoint ⟨.red, 1, 1⟩) := by
  have hne : T.constellationPoint ⟨.green, 1, 1⟩ ≠
      T.constellationPoint ⟨.red, 1, 1⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 1, 1⟩ -
      T.constellationPoint ⟨.red, 1, 1⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 1, 1⟩ -
      T.constellationPoint ⟨.red, 1, 1⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 1, 1⟩ ≠
      T.constellationPoint ⟨.red, 0, 2⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 1, 1⟩ -
      T.constellationPoint ⟨.red, 0, 2⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 1, 1⟩ -
      T.constellationPoint ⟨.red, 0, 2⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 1 1 1 0 2 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 1 1 1 0 2
  have h2 := m3c_red_mul_eq T 1 1 1 0 2 (by decide)
  have hNA : m3cNA T 1 1 1 0 2 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 1, 1⟩ -
        T.constellationPoint ⟨.red, 1, 1⟩) * m3cD T 1 1 1 0 2 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 1 1 1 0 2)
    (B := -(m3cNA T 1 1 1 0 2)) (by simpa using hNA)
    (m2_cross_111_02 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 1, 1⟩ -
      T.constellationPoint ⟨.red, 1, 1⟩)
      (T.constellationPoint ⟨.red, 1, 1⟩ - T.constellationPoint ⟨.red, 0, 2⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 1, 1⟩ - T.constellationPoint ⟨.red, 1, 1⟩)
      (w := T.constellationPoint ⟨.red, 1, 1⟩ - T.constellationPoint ⟨.red, 0, 2⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 1, 1⟩ -
          T.constellationPoint ⟨.red, 0, 2⟩) * m3cD T 1 1 1 0 2
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 1, 1⟩ -
            T.constellationPoint ⟨.red, 1, 1⟩)) * m3cD T 1 1 1 0 2 := by
      calc toComplex o (T.constellationPoint ⟨.red, 1, 1⟩ -
            T.constellationPoint ⟨.red, 0, 2⟩) * m3cD T 1 1 1 0 2
          = m3cNBp T 1 1 1 0 2 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 1 1 1 0 2)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 1, 1⟩ -
              T.constellationPoint ⟨.red, 1, 1⟩)) * m3cD T 1 1 1 0 2 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 1, 1⟩ - T.constellationPoint ⟨.red, 0, 2⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 1, 1⟩ -
          T.constellationPoint ⟨.red, 0, 2⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 0) (OrientedTriangle.m3p_red_par23 T 2)
    simpa only [neg_sub, show ((2 : TrisectorLabel) + 1) = 0 from by decide, show ((2 : TrisectorLabel) + 2) = 1 from by decide] using h0
  exact m3c_hfirst_of_collinear T 1 1 1 0 2 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(1,2,0)` is parallel to a Morley side;
the red equal-sum join used is that of `(1,2)` with `(0,0)`. -/
theorem m2_first_120 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 2, 0⟩ - T.constellationPoint ⟨.red, 1, 2⟩) := by
  have hne : T.constellationPoint ⟨.green, 2, 0⟩ ≠
      T.constellationPoint ⟨.red, 1, 2⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 2, 0⟩ -
      T.constellationPoint ⟨.red, 1, 2⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 2, 0⟩ -
      T.constellationPoint ⟨.red, 1, 2⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 1, 2⟩ ≠
      T.constellationPoint ⟨.red, 0, 0⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 1, 2⟩ -
      T.constellationPoint ⟨.red, 0, 0⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 1, 2⟩ -
      T.constellationPoint ⟨.red, 0, 0⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 1 2 0 0 0 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 1 2 0 0 0
  have h2 := m3c_red_mul_eq T 1 2 0 0 0 (by decide)
  have hNA : m3cNA T 1 2 0 0 0 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 2, 0⟩ -
        T.constellationPoint ⟨.red, 1, 2⟩) * m3cD T 1 2 0 0 0 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 1 2 0 0 0)
    (B := -(m3cNA T 1 2 0 0 0)) (by simpa using hNA)
    (m2_cross_120_00 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 2, 0⟩ -
      T.constellationPoint ⟨.red, 1, 2⟩)
      (T.constellationPoint ⟨.red, 1, 2⟩ - T.constellationPoint ⟨.red, 0, 0⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 2, 0⟩ - T.constellationPoint ⟨.red, 1, 2⟩)
      (w := T.constellationPoint ⟨.red, 1, 2⟩ - T.constellationPoint ⟨.red, 0, 0⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 1, 2⟩ -
          T.constellationPoint ⟨.red, 0, 0⟩) * m3cD T 1 2 0 0 0
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 2, 0⟩ -
            T.constellationPoint ⟨.red, 1, 2⟩)) * m3cD T 1 2 0 0 0 := by
      calc toComplex o (T.constellationPoint ⟨.red, 1, 2⟩ -
            T.constellationPoint ⟨.red, 0, 0⟩) * m3cD T 1 2 0 0 0
          = m3cNBp T 1 2 0 0 0 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 1 2 0 0 0)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 2, 0⟩ -
              T.constellationPoint ⟨.red, 1, 2⟩)) * m3cD T 1 2 0 0 0 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 1, 2⟩ - T.constellationPoint ⟨.red, 0, 0⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 1, 2⟩ -
          T.constellationPoint ⟨.red, 0, 0⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 2) (OrientedTriangle.m3p_red_par12 T 0)
    simpa only [neg_sub, show ((0 : TrisectorLabel) + 1) = 1 from by decide, show ((0 : TrisectorLabel) + 2) = 2 from by decide] using h0
  exact m3c_hfirst_of_collinear T 1 2 0 0 0 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(1,2,2)` is parallel to a Morley side;
the red equal-sum join used is that of `(1,2)` with `(2,1)`. -/
theorem m2_first_122 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 2, 2⟩ - T.constellationPoint ⟨.red, 1, 2⟩) := by
  have hne : T.constellationPoint ⟨.green, 2, 2⟩ ≠
      T.constellationPoint ⟨.red, 1, 2⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 2, 2⟩ -
      T.constellationPoint ⟨.red, 1, 2⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 2, 2⟩ -
      T.constellationPoint ⟨.red, 1, 2⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 1, 2⟩ ≠
      T.constellationPoint ⟨.red, 2, 1⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 1, 2⟩ -
      T.constellationPoint ⟨.red, 2, 1⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 1, 2⟩ -
      T.constellationPoint ⟨.red, 2, 1⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 1 2 2 2 1 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 1 2 2 2 1
  have h2 := m3c_red_mul_eq T 1 2 2 2 1 (by decide)
  have hNA : m3cNA T 1 2 2 2 1 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 2, 2⟩ -
        T.constellationPoint ⟨.red, 1, 2⟩) * m3cD T 1 2 2 2 1 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 1 2 2 2 1)
    (B := -(m3cNA T 1 2 2 2 1)) (by simpa using hNA)
    (m2_cross_122_21 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 2, 2⟩ -
      T.constellationPoint ⟨.red, 1, 2⟩)
      (T.constellationPoint ⟨.red, 1, 2⟩ - T.constellationPoint ⟨.red, 2, 1⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 2, 2⟩ - T.constellationPoint ⟨.red, 1, 2⟩)
      (w := T.constellationPoint ⟨.red, 1, 2⟩ - T.constellationPoint ⟨.red, 2, 1⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 1, 2⟩ -
          T.constellationPoint ⟨.red, 2, 1⟩) * m3cD T 1 2 2 2 1
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 2, 2⟩ -
            T.constellationPoint ⟨.red, 1, 2⟩)) * m3cD T 1 2 2 2 1 := by
      calc toComplex o (T.constellationPoint ⟨.red, 1, 2⟩ -
            T.constellationPoint ⟨.red, 2, 1⟩) * m3cD T 1 2 2 2 1
          = m3cNBp T 1 2 2 2 1 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 1 2 2 2 1)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 2, 2⟩ -
              T.constellationPoint ⟨.red, 1, 2⟩)) * m3cD T 1 2 2 2 1 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 1, 2⟩ - T.constellationPoint ⟨.red, 2, 1⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 2, 1⟩ -
          T.constellationPoint ⟨.red, 1, 2⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 1) (OrientedTriangle.m3p_red_par23 T 0)
    simpa only [neg_sub, show ((0 : TrisectorLabel) + 1) = 1 from by decide, show ((0 : TrisectorLabel) + 2) = 2 from by decide] using m2_pMS_neg T h0
  exact m3c_hfirst_of_collinear T 1 2 2 2 1 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(2,0,0)` is parallel to a Morley side;
the red equal-sum join used is that of `(2,0)` with `(0,2)`. -/
theorem m2_first_200 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 0, 0⟩ - T.constellationPoint ⟨.red, 2, 0⟩) := by
  have hne : T.constellationPoint ⟨.green, 0, 0⟩ ≠
      T.constellationPoint ⟨.red, 2, 0⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 0, 0⟩ -
      T.constellationPoint ⟨.red, 2, 0⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 0, 0⟩ -
      T.constellationPoint ⟨.red, 2, 0⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 2, 0⟩ ≠
      T.constellationPoint ⟨.red, 0, 2⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 2, 0⟩ -
      T.constellationPoint ⟨.red, 0, 2⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 2, 0⟩ -
      T.constellationPoint ⟨.red, 0, 2⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 2 0 0 0 2 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 2 0 0 0 2
  have h2 := m3c_red_mul_eq T 2 0 0 0 2 (by decide)
  have hNA : m3cNA T 2 0 0 0 2 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 0, 0⟩ -
        T.constellationPoint ⟨.red, 2, 0⟩) * m3cD T 2 0 0 0 2 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 2 0 0 0 2)
    (B := -(m3cNA T 2 0 0 0 2)) (by simpa using hNA)
    (m2_cross_200_02 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 0, 0⟩ -
      T.constellationPoint ⟨.red, 2, 0⟩)
      (T.constellationPoint ⟨.red, 2, 0⟩ - T.constellationPoint ⟨.red, 0, 2⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 0, 0⟩ - T.constellationPoint ⟨.red, 2, 0⟩)
      (w := T.constellationPoint ⟨.red, 2, 0⟩ - T.constellationPoint ⟨.red, 0, 2⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 2, 0⟩ -
          T.constellationPoint ⟨.red, 0, 2⟩) * m3cD T 2 0 0 0 2
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 0, 0⟩ -
            T.constellationPoint ⟨.red, 2, 0⟩)) * m3cD T 2 0 0 0 2 := by
      calc toComplex o (T.constellationPoint ⟨.red, 2, 0⟩ -
            T.constellationPoint ⟨.red, 0, 2⟩) * m3cD T 2 0 0 0 2
          = m3cNBp T 2 0 0 0 2 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 2 0 0 0 2)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 0, 0⟩ -
              T.constellationPoint ⟨.red, 2, 0⟩)) * m3cD T 2 0 0 0 2 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 2, 0⟩ - T.constellationPoint ⟨.red, 0, 2⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 0, 2⟩ -
          T.constellationPoint ⟨.red, 2, 0⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 1) (OrientedTriangle.m3p_red_par12 T 2)
    simpa only [neg_sub, show ((2 : TrisectorLabel) + 1) = 0 from by decide, show ((2 : TrisectorLabel) + 2) = 1 from by decide] using m2_pMS_neg T h0
  exact m3c_hfirst_of_collinear T 2 0 0 0 2 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(2,0,1)` is parallel to a Morley side;
the red equal-sum join used is that of `(2,0)` with `(1,1)`. -/
theorem m2_first_201 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 0, 1⟩ - T.constellationPoint ⟨.red, 2, 0⟩) := by
  have hne : T.constellationPoint ⟨.green, 0, 1⟩ ≠
      T.constellationPoint ⟨.red, 2, 0⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 0, 1⟩ -
      T.constellationPoint ⟨.red, 2, 0⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 0, 1⟩ -
      T.constellationPoint ⟨.red, 2, 0⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 2, 0⟩ ≠
      T.constellationPoint ⟨.red, 1, 1⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 2, 0⟩ -
      T.constellationPoint ⟨.red, 1, 1⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 2, 0⟩ -
      T.constellationPoint ⟨.red, 1, 1⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 2 0 1 1 1 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 2 0 1 1 1
  have h2 := m3c_red_mul_eq T 2 0 1 1 1 (by decide)
  have hNA : m3cNA T 2 0 1 1 1 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 0, 1⟩ -
        T.constellationPoint ⟨.red, 2, 0⟩) * m3cD T 2 0 1 1 1 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 2 0 1 1 1)
    (B := -(m3cNA T 2 0 1 1 1)) (by simpa using hNA)
    (m2_cross_201_11 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 0, 1⟩ -
      T.constellationPoint ⟨.red, 2, 0⟩)
      (T.constellationPoint ⟨.red, 2, 0⟩ - T.constellationPoint ⟨.red, 1, 1⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 0, 1⟩ - T.constellationPoint ⟨.red, 2, 0⟩)
      (w := T.constellationPoint ⟨.red, 2, 0⟩ - T.constellationPoint ⟨.red, 1, 1⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 2, 0⟩ -
          T.constellationPoint ⟨.red, 1, 1⟩) * m3cD T 2 0 1 1 1
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 0, 1⟩ -
            T.constellationPoint ⟨.red, 2, 0⟩)) * m3cD T 2 0 1 1 1 := by
      calc toComplex o (T.constellationPoint ⟨.red, 2, 0⟩ -
            T.constellationPoint ⟨.red, 1, 1⟩) * m3cD T 2 0 1 1 1
          = m3cNBp T 2 0 1 1 1 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 2 0 1 1 1)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 0, 1⟩ -
              T.constellationPoint ⟨.red, 2, 0⟩)) * m3cD T 2 0 1 1 1 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 2, 0⟩ - T.constellationPoint ⟨.red, 1, 1⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 2, 0⟩ -
          T.constellationPoint ⟨.red, 1, 1⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 2) (OrientedTriangle.m3p_red_par31 T 2)
    simpa only [neg_sub, show ((2 : TrisectorLabel) + 1) = 0 from by decide, show ((2 : TrisectorLabel) + 2) = 1 from by decide] using h0
  exact m3c_hfirst_of_collinear T 2 0 1 1 1 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(2,1,0)` is parallel to a Morley side;
the red equal-sum join used is that of `(2,1)` with `(1,2)`. -/
theorem m2_first_210 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 1, 0⟩ - T.constellationPoint ⟨.red, 2, 1⟩) := by
  have hne : T.constellationPoint ⟨.green, 1, 0⟩ ≠
      T.constellationPoint ⟨.red, 2, 1⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 1, 0⟩ -
      T.constellationPoint ⟨.red, 2, 1⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 1, 0⟩ -
      T.constellationPoint ⟨.red, 2, 1⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 2, 1⟩ ≠
      T.constellationPoint ⟨.red, 1, 2⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 2, 1⟩ -
      T.constellationPoint ⟨.red, 1, 2⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 2, 1⟩ -
      T.constellationPoint ⟨.red, 1, 2⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 2 1 0 1 2 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 2 1 0 1 2
  have h2 := m3c_red_mul_eq T 2 1 0 1 2 (by decide)
  have hNA : m3cNA T 2 1 0 1 2 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 1, 0⟩ -
        T.constellationPoint ⟨.red, 2, 1⟩) * m3cD T 2 1 0 1 2 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 2 1 0 1 2)
    (B := -(m3cNA T 2 1 0 1 2)) (by simpa using hNA)
    (m2_cross_210_12 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 1, 0⟩ -
      T.constellationPoint ⟨.red, 2, 1⟩)
      (T.constellationPoint ⟨.red, 2, 1⟩ - T.constellationPoint ⟨.red, 1, 2⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 1, 0⟩ - T.constellationPoint ⟨.red, 2, 1⟩)
      (w := T.constellationPoint ⟨.red, 2, 1⟩ - T.constellationPoint ⟨.red, 1, 2⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 2, 1⟩ -
          T.constellationPoint ⟨.red, 1, 2⟩) * m3cD T 2 1 0 1 2
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 1, 0⟩ -
            T.constellationPoint ⟨.red, 2, 1⟩)) * m3cD T 2 1 0 1 2 := by
      calc toComplex o (T.constellationPoint ⟨.red, 2, 1⟩ -
            T.constellationPoint ⟨.red, 1, 2⟩) * m3cD T 2 1 0 1 2
          = m3cNBp T 2 1 0 1 2 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 2 1 0 1 2)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 1, 0⟩ -
              T.constellationPoint ⟨.red, 2, 1⟩)) * m3cD T 2 1 0 1 2 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 2, 1⟩ - T.constellationPoint ⟨.red, 1, 2⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 2, 1⟩ -
          T.constellationPoint ⟨.red, 1, 2⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 1) (OrientedTriangle.m3p_red_par23 T 0)
    simpa only [neg_sub, show ((0 : TrisectorLabel) + 1) = 1 from by decide, show ((0 : TrisectorLabel) + 2) = 2 from by decide] using h0
  exact m3c_hfirst_of_collinear T 2 1 0 1 2 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(2,1,2)` is parallel to a Morley side;
the red equal-sum join used is that of `(2,1)` with `(0,0)`. -/
theorem m2_first_212 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 1, 2⟩ - T.constellationPoint ⟨.red, 2, 1⟩) := by
  have hne : T.constellationPoint ⟨.green, 1, 2⟩ ≠
      T.constellationPoint ⟨.red, 2, 1⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 1, 2⟩ -
      T.constellationPoint ⟨.red, 2, 1⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 1, 2⟩ -
      T.constellationPoint ⟨.red, 2, 1⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 2, 1⟩ ≠
      T.constellationPoint ⟨.red, 0, 0⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 2, 1⟩ -
      T.constellationPoint ⟨.red, 0, 0⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 2, 1⟩ -
      T.constellationPoint ⟨.red, 0, 0⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 2 1 2 0 0 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 2 1 2 0 0
  have h2 := m3c_red_mul_eq T 2 1 2 0 0 (by decide)
  have hNA : m3cNA T 2 1 2 0 0 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 1, 2⟩ -
        T.constellationPoint ⟨.red, 2, 1⟩) * m3cD T 2 1 2 0 0 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 2 1 2 0 0)
    (B := -(m3cNA T 2 1 2 0 0)) (by simpa using hNA)
    (m2_cross_212_00 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 1, 2⟩ -
      T.constellationPoint ⟨.red, 2, 1⟩)
      (T.constellationPoint ⟨.red, 2, 1⟩ - T.constellationPoint ⟨.red, 0, 0⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 1, 2⟩ - T.constellationPoint ⟨.red, 2, 1⟩)
      (w := T.constellationPoint ⟨.red, 2, 1⟩ - T.constellationPoint ⟨.red, 0, 0⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 2, 1⟩ -
          T.constellationPoint ⟨.red, 0, 0⟩) * m3cD T 2 1 2 0 0
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 1, 2⟩ -
            T.constellationPoint ⟨.red, 2, 1⟩)) * m3cD T 2 1 2 0 0 := by
      calc toComplex o (T.constellationPoint ⟨.red, 2, 1⟩ -
            T.constellationPoint ⟨.red, 0, 0⟩) * m3cD T 2 1 2 0 0
          = m3cNBp T 2 1 2 0 0 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 2 1 2 0 0)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 1, 2⟩ -
              T.constellationPoint ⟨.red, 2, 1⟩)) * m3cD T 2 1 2 0 0 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 2, 1⟩ - T.constellationPoint ⟨.red, 0, 0⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 0, 0⟩ -
          T.constellationPoint ⟨.red, 2, 1⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 0) (OrientedTriangle.m3p_red_par31 T 0)
    simpa only [neg_sub, show ((0 : TrisectorLabel) + 1) = 1 from by decide, show ((0 : TrisectorLabel) + 2) = 2 from by decide] using m2_pMS_neg T h0
  exact m3c_hfirst_of_collinear T 2 1 2 0 0 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(2,2,1)` is parallel to a Morley side;
the red equal-sum join used is that of `(2,2)` with `(0,1)`. -/
theorem m2_first_221 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 2, 1⟩ - T.constellationPoint ⟨.red, 2, 2⟩) := by
  have hne : T.constellationPoint ⟨.green, 2, 1⟩ ≠
      T.constellationPoint ⟨.red, 2, 2⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 2, 1⟩ -
      T.constellationPoint ⟨.red, 2, 2⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 2, 1⟩ -
      T.constellationPoint ⟨.red, 2, 2⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 2, 2⟩ ≠
      T.constellationPoint ⟨.red, 0, 1⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 2, 2⟩ -
      T.constellationPoint ⟨.red, 0, 1⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 2, 2⟩ -
      T.constellationPoint ⟨.red, 0, 1⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 2 2 1 0 1 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 2 2 1 0 1
  have h2 := m3c_red_mul_eq T 2 2 1 0 1 (by decide)
  have hNA : m3cNA T 2 2 1 0 1 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 2, 1⟩ -
        T.constellationPoint ⟨.red, 2, 2⟩) * m3cD T 2 2 1 0 1 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 2 2 1 0 1)
    (B := -(m3cNA T 2 2 1 0 1)) (by simpa using hNA)
    (m2_cross_221_01 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 2, 1⟩ -
      T.constellationPoint ⟨.red, 2, 2⟩)
      (T.constellationPoint ⟨.red, 2, 2⟩ - T.constellationPoint ⟨.red, 0, 1⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 2, 1⟩ - T.constellationPoint ⟨.red, 2, 2⟩)
      (w := T.constellationPoint ⟨.red, 2, 2⟩ - T.constellationPoint ⟨.red, 0, 1⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 2, 2⟩ -
          T.constellationPoint ⟨.red, 0, 1⟩) * m3cD T 2 2 1 0 1
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 2, 1⟩ -
            T.constellationPoint ⟨.red, 2, 2⟩)) * m3cD T 2 2 1 0 1 := by
      calc toComplex o (T.constellationPoint ⟨.red, 2, 2⟩ -
            T.constellationPoint ⟨.red, 0, 1⟩) * m3cD T 2 2 1 0 1
          = m3cNBp T 2 2 1 0 1 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 2 2 1 0 1)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 2, 1⟩ -
              T.constellationPoint ⟨.red, 2, 2⟩)) * m3cD T 2 2 1 0 1 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 2, 2⟩ - T.constellationPoint ⟨.red, 0, 1⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 0, 1⟩ -
          T.constellationPoint ⟨.red, 2, 2⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 2) (OrientedTriangle.m3p_red_par23 T 1)
    simpa only [neg_sub, show ((1 : TrisectorLabel) + 1) = 2 from by decide, show ((1 : TrisectorLabel) + 2) = 0 from by decide] using m2_pMS_neg T h0
  exact m3c_hfirst_of_collinear T 2 2 1 0 1 hRV
    (parallel_comm hVs0 hVr0 hpar)

/-- The first side of the tricolour triangle `(2,2,2)` is parallel to a Morley side;
the red equal-sum join used is that of `(2,2)` with `(1,0)`. -/
theorem m2_first_222 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, 2, 2⟩ - T.constellationPoint ⟨.red, 2, 2⟩) := by
  have hne : T.constellationPoint ⟨.green, 2, 2⟩ ≠
      T.constellationPoint ⟨.red, 2, 2⟩ :=
    m7c_cp_ne_color T h (by decide) _ _ _ _
  have hVs : toComplex o (T.constellationPoint ⟨.green, 2, 2⟩ -
      T.constellationPoint ⟨.red, 2, 2⟩) ≠ 0 := m2_toComplex_sub_ne hne
  have hVs0 : (T.constellationPoint ⟨.green, 2, 2⟩ -
      T.constellationPoint ⟨.red, 2, 2⟩) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hne2 : T.constellationPoint ⟨.red, 2, 2⟩ ≠
      T.constellationPoint ⟨.red, 1, 0⟩ :=
    m2_cp_ne_same T h (by decide)
  have hVr : toComplex o (T.constellationPoint ⟨.red, 2, 2⟩ -
      T.constellationPoint ⟨.red, 1, 0⟩) ≠ 0 := m2_toComplex_sub_ne hne2
  have hVr0 : (T.constellationPoint ⟨.red, 2, 2⟩ -
      T.constellationPoint ⟨.red, 1, 0⟩) ≠ 0 := fun h0 => hne2 (sub_eq_zero.mp h0)
  have hD : m3cD T 2 2 2 1 0 ≠ 0 := m3c_D_ne T _ _ _ _ _
  have h1 := m3c_first_mul T 2 2 2 1 0
  have h2 := m3c_red_mul_eq T 2 2 2 1 0 (by decide)
  have hNA : m3cNA T 2 2 2 1 0 ≠ 0 := by
    intro h0
    have hzero : toComplex o (T.constellationPoint ⟨.green, 2, 2⟩ -
        T.constellationPoint ⟨.red, 2, 2⟩) * m3cD T 2 2 2 1 0 = 0 := by
      rw [h1, h0]; ring
    exact hVs ((mul_eq_zero.mp hzero).resolve_right hD)
  obtain ⟨r, hr⟩ := m3c_real_div (A := m3cNBp T 2 2 2 1 0)
    (B := -(m3cNA T 2 2 2 1 0)) (by simpa using hNA)
    (m2_cross_222_10 T)
  have hpar : Parallel (T.constellationPoint ⟨.green, 2, 2⟩ -
      T.constellationPoint ⟨.red, 2, 2⟩)
      (T.constellationPoint ⟨.red, 2, 2⟩ - T.constellationPoint ⟨.red, 1, 0⟩) := by
    refine OrientedTriangle.m3p_parallel_of_toComplex (o := o)
      (v := T.constellationPoint ⟨.green, 2, 2⟩ - T.constellationPoint ⟨.red, 2, 2⟩)
      (w := T.constellationPoint ⟨.red, 2, 2⟩ - T.constellationPoint ⟨.red, 1, 0⟩) ⟨r, ?_⟩
    have key : toComplex o (T.constellationPoint ⟨.red, 2, 2⟩ -
          T.constellationPoint ⟨.red, 1, 0⟩) * m3cD T 2 2 2 1 0
        = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 2, 2⟩ -
            T.constellationPoint ⟨.red, 2, 2⟩)) * m3cD T 2 2 2 1 0 := by
      calc toComplex o (T.constellationPoint ⟨.red, 2, 2⟩ -
            T.constellationPoint ⟨.red, 1, 0⟩) * m3cD T 2 2 2 1 0
          = m3cNBp T 2 2 2 1 0 * toComplex o (T.C - T.A) := h2
        _ = ((r : ℂ) * -(m3cNA T 2 2 2 1 0)) * toComplex o (T.C - T.A) := by
            rw [hr]
        _ = ((r : ℂ) * toComplex o (T.constellationPoint ⟨.green, 2, 2⟩ -
              T.constellationPoint ⟨.red, 2, 2⟩)) * m3cD T 2 2 2 1 0 := by
            rw [mul_assoc, ← h1]; ring
    exact mul_right_cancel₀ hD key
  have hRV : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, 2, 2⟩ - T.constellationPoint ⟨.red, 1, 0⟩) := by
    have h0 : T.parallelToMorleySide
        (T.constellationPoint ⟨.red, 2, 2⟩ -
          T.constellationPoint ⟨.red, 1, 0⟩) :=
      m2_pMS_of_par T (m2_pMS_side T 0) (OrientedTriangle.m3p_red_par12 T 1)
    simpa only [neg_sub, show ((1 : TrisectorLabel) + 1) = 2 from by decide, show ((1 : TrisectorLabel) + 2) = 0 from by decide] using h0
  exact m3c_hfirst_of_collinear T 2 2 2 1 0 hRV
    (parallel_comm hVs0 hVr0 hpar)
/-- The first conjunct of the root's `tricolor_sides_parallel`, for all eighteen labels. -/
theorem m2_hfirst (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    ∀ q : TricolorIndex, q.i + q.j + q.k ≠ 1 →
      T.parallelToMorleySide ((T.tricolorTriangle q).second - (T.tricolorTriangle q).first) := by
  intro q hq
  obtain ⟨i, j, k⟩ := q
  rcases zmod3_cases i with rfl | rfl | rfl <;>
    rcases zmod3_cases j with rfl | rfl | rfl <;>
      rcases zmod3_cases k with rfl | rfl | rfl
  · exact m2_first_000 T h
  · exact absurd (by decide) hq
  · exact m2_first_002 T h
  · exact absurd (by decide) hq
  · exact m2_first_011 T h
  · exact m2_first_012 T h
  · exact m2_first_020 T h
  · exact m2_first_021 T h
  · exact absurd (by decide) hq
  · exact absurd (by decide) hq
  · exact m2_first_101 T h
  · exact m2_first_102 T h
  · exact m2_first_110 T h
  · exact m2_first_111 T h
  · exact absurd (by decide) hq
  · exact m2_first_120 T h
  · exact absurd (by decide) hq
  · exact m2_first_122 T h
  · exact m2_first_200 T h
  · exact m2_first_201 T h
  · exact absurd (by decide) hq
  · exact m2_first_210 T h
  · exact absurd (by decide) hq
  · exact m2_first_212 T h
  · exact absurd (by decide) hq
  · exact m2_first_221 T h
  · exact m2_first_222 T h

/-- **`tricolor_sides_parallel`**, proved: all eighteen equilateral tricolour triangles have
sides parallel to `XYZ`. -/
theorem m2_tricolor_sides_parallel (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (q : TricolorIndex)
    (hq : q.i + q.j + q.k ≠ 1) :
    let t := T.tricolorTriangle q
    T.parallelToMorleySide (t.second - t.first) ∧
      T.parallelToMorleySide (t.third - t.second) ∧
        T.parallelToMorleySide (t.first - t.third) :=
  m3c_tricolor_sides_parallel T h (m2_hfirst T h) q hq

end OrientedTriangle

end XamboMorley
