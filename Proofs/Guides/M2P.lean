import M2S

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

/-! ### The 54 incidence certificates of the nine guide lines

For every label `(i,j,k)` and the red equal-sum partner `(i',j')` of `(i,j)`, the certificate
`m2_par_…` states the collinearity

`green(j,k) ∈ line(red(i,j), red(i',j'))`.

Cyclically permuting the colours (`T ↦ m7_cyclic T`, which sends red↦green↦blue↦red with
labels unchanged) transports that single family to `blue(j,k) ∈ line(green(i,j), green(i',j'))`
and `red(j,k) ∈ line(blue(i,j), blue(i',j'))`.  The 3 × 18 = 54 statements are exactly the
54 = 27 · 2 incidences of the nine guide lines with the 27 constellation points (two points of
every colour on every line), in the precise form the counting arguments of directions
d2/d3/d5/d6 need. -/

/-- The cyclic colour shift `red ↦ green ↦ blue ↦ red` on colours. -/
def m2ColorShift : TrisectorColor → TrisectorColor
  | .red => .green
  | .green => .blue
  | .blue => .red

/-- The induced shift of constellation indices (labels unchanged). -/
def m2IdxShift (q : ConstellationIndex) : ConstellationIndex :=
  ⟨m2ColorShift q.color, q.first, q.second⟩

theorem m2ColorShift_injective : Injective m2ColorShift := by
  intro a b h
  revert h
  revert a b
  decide

theorem m2IdxShift_injective : Injective m2IdxShift := by
  rintro ⟨c1, a1, b1⟩ ⟨c2, a2, b2⟩ h
  simp only [m2IdxShift, ConstellationIndex.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [m2ColorShift_injective h1, h2, h3]

/-- The cyclic constellation is the old one precomposed with the colour shift. -/
theorem m2_cp_cyclic_shift (T : OrientedTriangle E o) (q : ConstellationIndex) :
    (m7_cyclic T).constellationPoint q = T.constellationPoint (m2IdxShift q) := by
  obtain ⟨c, a, b⟩ := q
  cases c <;> rfl

/-- Injectivity survives the cyclic relabelling. -/
theorem m2_injective_cyclic (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Injective (m7_cyclic T).constellationPoint := by
  intro q1 q2 heq
  have h2 : T.constellationPoint (m2IdxShift q1) = T.constellationPoint (m2IdxShift q2) := by
    rw [← m2_cp_cyclic_shift, ← m2_cp_cyclic_shift]
    exact heq
  exact m2IdxShift_injective (h h2)

/-- `green(0,0)` lies on the red equal-sum join `red(0,0)--red(2,1)`. -/
theorem m2_par_000 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 0, 0⟩ - T.constellationPoint ⟨.red, 0, 0⟩)
      (T.constellationPoint ⟨.red, 0, 0⟩ - T.constellationPoint ⟨.red, 2, 1⟩) := by
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

/-- `green(0,2)` lies on the red equal-sum join `red(0,0)--red(1,2)`. -/
theorem m2_par_002 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 0, 2⟩ - T.constellationPoint ⟨.red, 0, 0⟩)
      (T.constellationPoint ⟨.red, 0, 0⟩ - T.constellationPoint ⟨.red, 1, 2⟩) := by
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

/-- `green(1,1)` lies on the red equal-sum join `red(0,1)--red(1,0)`. -/
theorem m2_par_011 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 1, 1⟩ - T.constellationPoint ⟨.red, 0, 1⟩)
      (T.constellationPoint ⟨.red, 0, 1⟩ - T.constellationPoint ⟨.red, 1, 0⟩) := by
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

/-- `green(1,2)` lies on the red equal-sum join `red(0,1)--red(2,2)`. -/
theorem m2_par_012 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 1, 2⟩ - T.constellationPoint ⟨.red, 0, 1⟩)
      (T.constellationPoint ⟨.red, 0, 1⟩ - T.constellationPoint ⟨.red, 2, 2⟩) := by
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

/-- `green(2,0)` lies on the red equal-sum join `red(0,2)--red(1,1)`. -/
theorem m2_par_020 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 2, 0⟩ - T.constellationPoint ⟨.red, 0, 2⟩)
      (T.constellationPoint ⟨.red, 0, 2⟩ - T.constellationPoint ⟨.red, 1, 1⟩) := by
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

/-- `green(2,1)` lies on the red equal-sum join `red(0,2)--red(2,0)`. -/
theorem m2_par_021 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 2, 1⟩ - T.constellationPoint ⟨.red, 0, 2⟩)
      (T.constellationPoint ⟨.red, 0, 2⟩ - T.constellationPoint ⟨.red, 2, 0⟩) := by
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

/-- `green(0,1)` lies on the red equal-sum join `red(1,0)--red(2,2)`. -/
theorem m2_par_101 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 0, 1⟩ - T.constellationPoint ⟨.red, 1, 0⟩)
      (T.constellationPoint ⟨.red, 1, 0⟩ - T.constellationPoint ⟨.red, 2, 2⟩) := by
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

/-- `green(0,2)` lies on the red equal-sum join `red(1,0)--red(0,1)`. -/
theorem m2_par_102 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 0, 2⟩ - T.constellationPoint ⟨.red, 1, 0⟩)
      (T.constellationPoint ⟨.red, 1, 0⟩ - T.constellationPoint ⟨.red, 0, 1⟩) := by
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

/-- `green(1,0)` lies on the red equal-sum join `red(1,1)--red(2,0)`. -/
theorem m2_par_110 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 1, 0⟩ - T.constellationPoint ⟨.red, 1, 1⟩)
      (T.constellationPoint ⟨.red, 1, 1⟩ - T.constellationPoint ⟨.red, 2, 0⟩) := by
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

/-- `green(1,1)` lies on the red equal-sum join `red(1,1)--red(0,2)`. -/
theorem m2_par_111 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 1, 1⟩ - T.constellationPoint ⟨.red, 1, 1⟩)
      (T.constellationPoint ⟨.red, 1, 1⟩ - T.constellationPoint ⟨.red, 0, 2⟩) := by
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

/-- `green(2,0)` lies on the red equal-sum join `red(1,2)--red(0,0)`. -/
theorem m2_par_120 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 2, 0⟩ - T.constellationPoint ⟨.red, 1, 2⟩)
      (T.constellationPoint ⟨.red, 1, 2⟩ - T.constellationPoint ⟨.red, 0, 0⟩) := by
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

/-- `green(2,2)` lies on the red equal-sum join `red(1,2)--red(2,1)`. -/
theorem m2_par_122 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 2, 2⟩ - T.constellationPoint ⟨.red, 1, 2⟩)
      (T.constellationPoint ⟨.red, 1, 2⟩ - T.constellationPoint ⟨.red, 2, 1⟩) := by
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

/-- `green(0,0)` lies on the red equal-sum join `red(2,0)--red(0,2)`. -/
theorem m2_par_200 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 0, 0⟩ - T.constellationPoint ⟨.red, 2, 0⟩)
      (T.constellationPoint ⟨.red, 2, 0⟩ - T.constellationPoint ⟨.red, 0, 2⟩) := by
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

/-- `green(0,1)` lies on the red equal-sum join `red(2,0)--red(1,1)`. -/
theorem m2_par_201 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 0, 1⟩ - T.constellationPoint ⟨.red, 2, 0⟩)
      (T.constellationPoint ⟨.red, 2, 0⟩ - T.constellationPoint ⟨.red, 1, 1⟩) := by
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

/-- `green(1,0)` lies on the red equal-sum join `red(2,1)--red(1,2)`. -/
theorem m2_par_210 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 1, 0⟩ - T.constellationPoint ⟨.red, 2, 1⟩)
      (T.constellationPoint ⟨.red, 2, 1⟩ - T.constellationPoint ⟨.red, 1, 2⟩) := by
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

/-- `green(1,2)` lies on the red equal-sum join `red(2,1)--red(0,0)`. -/
theorem m2_par_212 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 1, 2⟩ - T.constellationPoint ⟨.red, 2, 1⟩)
      (T.constellationPoint ⟨.red, 2, 1⟩ - T.constellationPoint ⟨.red, 0, 0⟩) := by
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

/-- `green(2,1)` lies on the red equal-sum join `red(2,2)--red(0,1)`. -/
theorem m2_par_221 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 2, 1⟩ - T.constellationPoint ⟨.red, 2, 2⟩)
      (T.constellationPoint ⟨.red, 2, 2⟩ - T.constellationPoint ⟨.red, 0, 1⟩) := by
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

/-- `green(2,2)` lies on the red equal-sum join `red(2,2)--red(1,0)`. -/
theorem m2_par_222 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.green, 2, 2⟩ - T.constellationPoint ⟨.red, 2, 2⟩)
      (T.constellationPoint ⟨.red, 2, 2⟩ - T.constellationPoint ⟨.red, 1, 0⟩) := by
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

/-- `blue(0,0)` lies on the green equal-sum join `green(0,0)--green(2,1)`
(cyclic transport of `m2_par_000`). -/
theorem m2_parB_000 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 0, 0⟩ - T.constellationPoint ⟨.green, 0, 0⟩)
      (T.constellationPoint ⟨.green, 0, 0⟩ - T.constellationPoint ⟨.green, 2, 1⟩) := by
  have h' := m2_par_000 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(0,2)` lies on the green equal-sum join `green(0,0)--green(1,2)`
(cyclic transport of `m2_par_002`). -/
theorem m2_parB_002 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 0, 2⟩ - T.constellationPoint ⟨.green, 0, 0⟩)
      (T.constellationPoint ⟨.green, 0, 0⟩ - T.constellationPoint ⟨.green, 1, 2⟩) := by
  have h' := m2_par_002 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(1,1)` lies on the green equal-sum join `green(0,1)--green(1,0)`
(cyclic transport of `m2_par_011`). -/
theorem m2_parB_011 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 1, 1⟩ - T.constellationPoint ⟨.green, 0, 1⟩)
      (T.constellationPoint ⟨.green, 0, 1⟩ - T.constellationPoint ⟨.green, 1, 0⟩) := by
  have h' := m2_par_011 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(1,2)` lies on the green equal-sum join `green(0,1)--green(2,2)`
(cyclic transport of `m2_par_012`). -/
theorem m2_parB_012 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 1, 2⟩ - T.constellationPoint ⟨.green, 0, 1⟩)
      (T.constellationPoint ⟨.green, 0, 1⟩ - T.constellationPoint ⟨.green, 2, 2⟩) := by
  have h' := m2_par_012 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(2,0)` lies on the green equal-sum join `green(0,2)--green(1,1)`
(cyclic transport of `m2_par_020`). -/
theorem m2_parB_020 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 2, 0⟩ - T.constellationPoint ⟨.green, 0, 2⟩)
      (T.constellationPoint ⟨.green, 0, 2⟩ - T.constellationPoint ⟨.green, 1, 1⟩) := by
  have h' := m2_par_020 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(2,1)` lies on the green equal-sum join `green(0,2)--green(2,0)`
(cyclic transport of `m2_par_021`). -/
theorem m2_parB_021 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 2, 1⟩ - T.constellationPoint ⟨.green, 0, 2⟩)
      (T.constellationPoint ⟨.green, 0, 2⟩ - T.constellationPoint ⟨.green, 2, 0⟩) := by
  have h' := m2_par_021 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(0,1)` lies on the green equal-sum join `green(1,0)--green(2,2)`
(cyclic transport of `m2_par_101`). -/
theorem m2_parB_101 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 0, 1⟩ - T.constellationPoint ⟨.green, 1, 0⟩)
      (T.constellationPoint ⟨.green, 1, 0⟩ - T.constellationPoint ⟨.green, 2, 2⟩) := by
  have h' := m2_par_101 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(0,2)` lies on the green equal-sum join `green(1,0)--green(0,1)`
(cyclic transport of `m2_par_102`). -/
theorem m2_parB_102 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 0, 2⟩ - T.constellationPoint ⟨.green, 1, 0⟩)
      (T.constellationPoint ⟨.green, 1, 0⟩ - T.constellationPoint ⟨.green, 0, 1⟩) := by
  have h' := m2_par_102 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(1,0)` lies on the green equal-sum join `green(1,1)--green(2,0)`
(cyclic transport of `m2_par_110`). -/
theorem m2_parB_110 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 1, 0⟩ - T.constellationPoint ⟨.green, 1, 1⟩)
      (T.constellationPoint ⟨.green, 1, 1⟩ - T.constellationPoint ⟨.green, 2, 0⟩) := by
  have h' := m2_par_110 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(1,1)` lies on the green equal-sum join `green(1,1)--green(0,2)`
(cyclic transport of `m2_par_111`). -/
theorem m2_parB_111 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 1, 1⟩ - T.constellationPoint ⟨.green, 1, 1⟩)
      (T.constellationPoint ⟨.green, 1, 1⟩ - T.constellationPoint ⟨.green, 0, 2⟩) := by
  have h' := m2_par_111 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(2,0)` lies on the green equal-sum join `green(1,2)--green(0,0)`
(cyclic transport of `m2_par_120`). -/
theorem m2_parB_120 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 2, 0⟩ - T.constellationPoint ⟨.green, 1, 2⟩)
      (T.constellationPoint ⟨.green, 1, 2⟩ - T.constellationPoint ⟨.green, 0, 0⟩) := by
  have h' := m2_par_120 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(2,2)` lies on the green equal-sum join `green(1,2)--green(2,1)`
(cyclic transport of `m2_par_122`). -/
theorem m2_parB_122 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 2, 2⟩ - T.constellationPoint ⟨.green, 1, 2⟩)
      (T.constellationPoint ⟨.green, 1, 2⟩ - T.constellationPoint ⟨.green, 2, 1⟩) := by
  have h' := m2_par_122 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(0,0)` lies on the green equal-sum join `green(2,0)--green(0,2)`
(cyclic transport of `m2_par_200`). -/
theorem m2_parB_200 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 0, 0⟩ - T.constellationPoint ⟨.green, 2, 0⟩)
      (T.constellationPoint ⟨.green, 2, 0⟩ - T.constellationPoint ⟨.green, 0, 2⟩) := by
  have h' := m2_par_200 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(0,1)` lies on the green equal-sum join `green(2,0)--green(1,1)`
(cyclic transport of `m2_par_201`). -/
theorem m2_parB_201 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 0, 1⟩ - T.constellationPoint ⟨.green, 2, 0⟩)
      (T.constellationPoint ⟨.green, 2, 0⟩ - T.constellationPoint ⟨.green, 1, 1⟩) := by
  have h' := m2_par_201 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(1,0)` lies on the green equal-sum join `green(2,1)--green(1,2)`
(cyclic transport of `m2_par_210`). -/
theorem m2_parB_210 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 1, 0⟩ - T.constellationPoint ⟨.green, 2, 1⟩)
      (T.constellationPoint ⟨.green, 2, 1⟩ - T.constellationPoint ⟨.green, 1, 2⟩) := by
  have h' := m2_par_210 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(1,2)` lies on the green equal-sum join `green(2,1)--green(0,0)`
(cyclic transport of `m2_par_212`). -/
theorem m2_parB_212 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 1, 2⟩ - T.constellationPoint ⟨.green, 2, 1⟩)
      (T.constellationPoint ⟨.green, 2, 1⟩ - T.constellationPoint ⟨.green, 0, 0⟩) := by
  have h' := m2_par_212 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(2,1)` lies on the green equal-sum join `green(2,2)--green(0,1)`
(cyclic transport of `m2_par_221`). -/
theorem m2_parB_221 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 2, 1⟩ - T.constellationPoint ⟨.green, 2, 2⟩)
      (T.constellationPoint ⟨.green, 2, 2⟩ - T.constellationPoint ⟨.green, 0, 1⟩) := by
  have h' := m2_par_221 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `blue(2,2)` lies on the green equal-sum join `green(2,2)--green(1,0)`
(cyclic transport of `m2_par_222`). -/
theorem m2_parB_222 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.blue, 2, 2⟩ - T.constellationPoint ⟨.green, 2, 2⟩)
      (T.constellationPoint ⟨.green, 2, 2⟩ - T.constellationPoint ⟨.green, 1, 0⟩) := by
  have h' := m2_par_222 (m7_cyclic T) (m2_injective_cyclic T h)
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green] using h'

/-- `red(0,0)` lies on the blue equal-sum join `blue(0,0)--blue(2,1)`
(cyclic transport of `m2_par_000`). -/
theorem m2_parR_000 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 0, 0⟩ - T.constellationPoint ⟨.blue, 0, 0⟩)
      (T.constellationPoint ⟨.blue, 0, 0⟩ - T.constellationPoint ⟨.blue, 2, 1⟩) := by
  have h' := m2_par_000 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(0,2)` lies on the blue equal-sum join `blue(0,0)--blue(1,2)`
(cyclic transport of `m2_par_002`). -/
theorem m2_parR_002 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 0, 2⟩ - T.constellationPoint ⟨.blue, 0, 0⟩)
      (T.constellationPoint ⟨.blue, 0, 0⟩ - T.constellationPoint ⟨.blue, 1, 2⟩) := by
  have h' := m2_par_002 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(1,1)` lies on the blue equal-sum join `blue(0,1)--blue(1,0)`
(cyclic transport of `m2_par_011`). -/
theorem m2_parR_011 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 1, 1⟩ - T.constellationPoint ⟨.blue, 0, 1⟩)
      (T.constellationPoint ⟨.blue, 0, 1⟩ - T.constellationPoint ⟨.blue, 1, 0⟩) := by
  have h' := m2_par_011 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(1,2)` lies on the blue equal-sum join `blue(0,1)--blue(2,2)`
(cyclic transport of `m2_par_012`). -/
theorem m2_parR_012 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 1, 2⟩ - T.constellationPoint ⟨.blue, 0, 1⟩)
      (T.constellationPoint ⟨.blue, 0, 1⟩ - T.constellationPoint ⟨.blue, 2, 2⟩) := by
  have h' := m2_par_012 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(2,0)` lies on the blue equal-sum join `blue(0,2)--blue(1,1)`
(cyclic transport of `m2_par_020`). -/
theorem m2_parR_020 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 2, 0⟩ - T.constellationPoint ⟨.blue, 0, 2⟩)
      (T.constellationPoint ⟨.blue, 0, 2⟩ - T.constellationPoint ⟨.blue, 1, 1⟩) := by
  have h' := m2_par_020 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(2,1)` lies on the blue equal-sum join `blue(0,2)--blue(2,0)`
(cyclic transport of `m2_par_021`). -/
theorem m2_parR_021 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 2, 1⟩ - T.constellationPoint ⟨.blue, 0, 2⟩)
      (T.constellationPoint ⟨.blue, 0, 2⟩ - T.constellationPoint ⟨.blue, 2, 0⟩) := by
  have h' := m2_par_021 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(0,1)` lies on the blue equal-sum join `blue(1,0)--blue(2,2)`
(cyclic transport of `m2_par_101`). -/
theorem m2_parR_101 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 0, 1⟩ - T.constellationPoint ⟨.blue, 1, 0⟩)
      (T.constellationPoint ⟨.blue, 1, 0⟩ - T.constellationPoint ⟨.blue, 2, 2⟩) := by
  have h' := m2_par_101 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(0,2)` lies on the blue equal-sum join `blue(1,0)--blue(0,1)`
(cyclic transport of `m2_par_102`). -/
theorem m2_parR_102 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 0, 2⟩ - T.constellationPoint ⟨.blue, 1, 0⟩)
      (T.constellationPoint ⟨.blue, 1, 0⟩ - T.constellationPoint ⟨.blue, 0, 1⟩) := by
  have h' := m2_par_102 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(1,0)` lies on the blue equal-sum join `blue(1,1)--blue(2,0)`
(cyclic transport of `m2_par_110`). -/
theorem m2_parR_110 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 1, 0⟩ - T.constellationPoint ⟨.blue, 1, 1⟩)
      (T.constellationPoint ⟨.blue, 1, 1⟩ - T.constellationPoint ⟨.blue, 2, 0⟩) := by
  have h' := m2_par_110 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(1,1)` lies on the blue equal-sum join `blue(1,1)--blue(0,2)`
(cyclic transport of `m2_par_111`). -/
theorem m2_parR_111 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 1, 1⟩ - T.constellationPoint ⟨.blue, 1, 1⟩)
      (T.constellationPoint ⟨.blue, 1, 1⟩ - T.constellationPoint ⟨.blue, 0, 2⟩) := by
  have h' := m2_par_111 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(2,0)` lies on the blue equal-sum join `blue(1,2)--blue(0,0)`
(cyclic transport of `m2_par_120`). -/
theorem m2_parR_120 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 2, 0⟩ - T.constellationPoint ⟨.blue, 1, 2⟩)
      (T.constellationPoint ⟨.blue, 1, 2⟩ - T.constellationPoint ⟨.blue, 0, 0⟩) := by
  have h' := m2_par_120 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(2,2)` lies on the blue equal-sum join `blue(1,2)--blue(2,1)`
(cyclic transport of `m2_par_122`). -/
theorem m2_parR_122 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 2, 2⟩ - T.constellationPoint ⟨.blue, 1, 2⟩)
      (T.constellationPoint ⟨.blue, 1, 2⟩ - T.constellationPoint ⟨.blue, 2, 1⟩) := by
  have h' := m2_par_122 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(0,0)` lies on the blue equal-sum join `blue(2,0)--blue(0,2)`
(cyclic transport of `m2_par_200`). -/
theorem m2_parR_200 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 0, 0⟩ - T.constellationPoint ⟨.blue, 2, 0⟩)
      (T.constellationPoint ⟨.blue, 2, 0⟩ - T.constellationPoint ⟨.blue, 0, 2⟩) := by
  have h' := m2_par_200 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(0,1)` lies on the blue equal-sum join `blue(2,0)--blue(1,1)`
(cyclic transport of `m2_par_201`). -/
theorem m2_parR_201 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 0, 1⟩ - T.constellationPoint ⟨.blue, 2, 0⟩)
      (T.constellationPoint ⟨.blue, 2, 0⟩ - T.constellationPoint ⟨.blue, 1, 1⟩) := by
  have h' := m2_par_201 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(1,0)` lies on the blue equal-sum join `blue(2,1)--blue(1,2)`
(cyclic transport of `m2_par_210`). -/
theorem m2_parR_210 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 1, 0⟩ - T.constellationPoint ⟨.blue, 2, 1⟩)
      (T.constellationPoint ⟨.blue, 2, 1⟩ - T.constellationPoint ⟨.blue, 1, 2⟩) := by
  have h' := m2_par_210 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(1,2)` lies on the blue equal-sum join `blue(2,1)--blue(0,0)`
(cyclic transport of `m2_par_212`). -/
theorem m2_parR_212 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 1, 2⟩ - T.constellationPoint ⟨.blue, 2, 1⟩)
      (T.constellationPoint ⟨.blue, 2, 1⟩ - T.constellationPoint ⟨.blue, 0, 0⟩) := by
  have h' := m2_par_212 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(2,1)` lies on the blue equal-sum join `blue(2,2)--blue(0,1)`
(cyclic transport of `m2_par_221`). -/
theorem m2_parR_221 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 2, 1⟩ - T.constellationPoint ⟨.blue, 2, 2⟩)
      (T.constellationPoint ⟨.blue, 2, 2⟩ - T.constellationPoint ⟨.blue, 0, 1⟩) := by
  have h' := m2_par_221 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

/-- `red(2,2)` lies on the blue equal-sum join `blue(2,2)--blue(1,0)`
(cyclic transport of `m2_par_222`). -/
theorem m2_parR_222 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (T.constellationPoint ⟨.red, 2, 2⟩ - T.constellationPoint ⟨.blue, 2, 2⟩)
      (T.constellationPoint ⟨.blue, 2, 2⟩ - T.constellationPoint ⟨.blue, 1, 0⟩) := by
  have h' := m2_par_222 ((m7_cyclic (m7_cyclic T))) (m2_injective_cyclic (m7_cyclic T) (m2_injective_cyclic T h))
  simpa only [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue] using h'

end OrientedTriangle

end XamboMorley
