import Mathlib

set_option backward.isDefEq.respectTransparency.types false

/-!
# Wessel's algebra and Morley's theorem

A Lean formalization of Sebastian Xambó-Descamps,
*Wessel's Algebra and Morley's Theorem* (Geometry 2026, 3, 9).

The mathematical declarations follow the paper in reading order, with supporting
proof lemmas interleaved where needed. All eight formerly open targets are now
proved, and the completed environment contains no `sorryAx` dependency. The
Wessel algebra is Mathlib's Clifford algebra of the inner product quadratic form;
ordinary complex numbers appear only as the even subalgebra and as a convenient
coordinate model of a two-dimensional oriented real inner-product space.
-/

noncomputable section

open scoped Real RealInnerProductSpace ComplexConjugate Matrix
open Function Set

namespace XamboMorley

universe u

section Plane

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]

/-- The quadratic form underlying Wessel's algebra. -/
def planeQuadraticForm : QuadraticForm ℝ E := LinearMap.BilinMap.toQuadraticMap (innerₗ E)

/-- Wessel's algebra `G`, implemented by Mathlib's Clifford algebra. -/
abbrev WesselAlgebra (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  CliffordAlgebra (planeQuadraticForm (E := E))

local notation "G[" E "]" => WesselAlgebra E

/-- Vectors embedded in the Wessel algebra. -/
def vec (v : E) : G[E] := CliffordAlgebra.ι (planeQuadraticForm (E := E)) v

/-- Scalars embedded in the Wessel algebra. -/
def scalar (r : ℝ) : G[E] := algebraMap ℝ G[E] r

/-- The chosen positive orthonormal basis, used only to expose coordinates. -/
def positiveBasis (o : Orientation ℝ E (Fin 2)) : OrthonormalBasis (Fin 2) ℝ E :=
  o.finOrthonormalBasis (by norm_num) Fact.out

/-- The first basis vector. -/
def e₁ (o : Orientation ℝ E (Fin 2)) : E := positiveBasis o 0

/-- The second basis vector. -/
def e₂ (o : Orientation ℝ E (Fin 2)) : E := positiveBasis o 1

/-- The unit area element, or pseudoscalar, `i = e₁e₂`. -/
def pseudoscalar (o : Orientation ℝ E (Fin 2)) : G[E] := vec (e₁ o) * vec (e₂ o)

/-- Exterior-algebra wedge, used to state the geometric-product formula. -/
def exteriorWedge (v w : E) : ExteriorAlgebra ℝ E :=
  ExteriorAlgebra.ι ℝ v * ExteriorAlgebra.ι ℝ w

/-- Re-embed an exterior multivector in the Clifford algebra. -/
def ofExterior (x : ExteriorAlgebra ℝ E) : G[E] :=
  (CliffordAlgebra.equivExterior (planeQuadraticForm (E := E))).symm x

/-- A wedge product viewed as a bivector in `G`. -/
def wedge (v w : E) : G[E] := ofExterior (exteriorWedge v w)

/-- The oriented area of the parallelogram spanned by two vectors. -/
def orientedArea (o : Orientation ℝ E (Fin 2)) (v w : E) : ℝ := o.areaForm v w

/-- The linear isometry between the oriented plane and its complex coordinates. -/
def complexIsometryEquiv (o : Orientation ℝ E (Fin 2)) : E ≃ₗᵢ[ℝ] ℂ :=
  (positiveBasis o).equiv Complex.orthonormalBasisOneI (Equiv.refl (Fin 2))

/-- Conversion from a vector to geometric complex coordinates. -/
def toComplex (o : Orientation ℝ E (Fin 2)) (v : E) : ℂ := complexIsometryEquiv o v

/-- Reconstruction of a vector from geometric complex coordinates. -/
def ofComplex (o : Orientation ℝ E (Fin 2)) (z : ℂ) : E := (complexIsometryEquiv o).symm z

@[simp] theorem ofComplex_toComplex (o : Orientation ℝ E (Fin 2)) (v : E) :
    ofComplex o (toComplex o v) = v := (complexIsometryEquiv o).symm_apply_apply v

@[simp] theorem toComplex_ofComplex (o : Orientation ℝ E (Fin 2)) (z : ℂ) :
    toComplex o (ofComplex o z) = z := (complexIsometryEquiv o).apply_symm_apply z

@[simp] theorem toComplex_norm (o : Orientation ℝ E (Fin 2)) (v : E) :
    ‖toComplex o v‖ = ‖v‖ := (complexIsometryEquiv o).norm_map v

@[simp] theorem ofComplex_norm (o : Orientation ℝ E (Fin 2)) (z : ℂ) :
    ‖ofComplex o z‖ = ‖z‖ := (complexIsometryEquiv o).symm.norm_map z

@[simp] theorem toComplex_add (o : Orientation ℝ E (Fin 2)) (v w : E) :
    toComplex o (v + w) = toComplex o v + toComplex o w := (complexIsometryEquiv o).map_add v w

@[simp] theorem toComplex_sub (o : Orientation ℝ E (Fin 2)) (v w : E) :
    toComplex o (v - w) = toComplex o v - toComplex o w := (complexIsometryEquiv o).map_sub v w

@[simp] theorem toComplex_zero (o : Orientation ℝ E (Fin 2)) : toComplex o 0 = 0 :=
  (complexIsometryEquiv o).map_zero
@[simp] theorem toComplex_neg (o : Orientation ℝ E (Fin 2)) (v : E) :
    toComplex o (-v) = -toComplex o v := (complexIsometryEquiv o).map_neg v

@[simp] theorem toComplex_smul (o : Orientation ℝ E (Fin 2)) (r : ℝ) (v : E) :
    toComplex o (r • v) = (r : ℂ) * toComplex o v := (complexIsometryEquiv o).map_smul r v

theorem toComplex_injective (o : Orientation ℝ E (Fin 2)) : Injective (toComplex o) :=
  (complexIsometryEquiv o).injective

@[simp] theorem ofComplex_zero (o : Orientation ℝ E (Fin 2)) : ofComplex o 0 = 0 :=
  (complexIsometryEquiv o).symm.map_zero

@[simp] theorem toComplex_eq_zero (o : Orientation ℝ E (Fin 2)) (v : E) :
    toComplex o v = 0 ↔ v = 0 := (complexIsometryEquiv o).map_eq_zero_iff

/-- Geometric complex numbers embedded in the even Wessel algebra. -/
def geometricComplex (o : Orientation ℝ E (Fin 2)) (z : ℂ) : G[E] :=
  scalar z.re + z.im • pseudoscalar o

/-- The unit geometric complex number `uφ = exp(iφ)`. -/
def unit (o : Orientation ℝ E (Fin 2)) (φ : ℝ) : G[E] :=
  geometricComplex o (Circle.exp φ)

/-- Rotation of a vector through `φ`, written `v * exp(iφ)` in the paper. -/
def rotateVector (o : Orientation ℝ E (Fin 2)) (v : E) (φ : ℝ) : E :=
  ofComplex o (toComplex o v * Circle.exp φ)

@[simp] theorem rotateVector_norm (o : Orientation ℝ E (Fin 2)) (v : E) (φ : ℝ) :
    ‖rotateVector o v φ‖ = ‖v‖ := by
  rw [rotateVector, ofComplex_norm, norm_mul, toComplex_norm, Circle.norm_coe, mul_one]

theorem rotateVector_ne_zero (o : Orientation ℝ E (Fin 2)) {v : E} (hv : v ≠ 0) (φ : ℝ) :
    rotateVector o v φ ≠ 0 := by
  intro h
  have : ‖v‖ = 0 := by rw [← rotateVector_norm o v φ, h, norm_zero]
  exact hv (norm_eq_zero.mp this)

@[simp] theorem toComplex_rotateVector (o : Orientation ℝ E (Fin 2)) (v : E) (φ : ℝ) :
    toComplex o (rotateVector o v φ) = toComplex o v * Circle.exp φ := by
  simp [rotateVector]

@[simp] theorem rotateVector_zero_angle (o : Orientation ℝ E (Fin 2)) (v : E) :
    rotateVector o v 0 = v := by
  simp [rotateVector]

@[simp] theorem rotateVector_add (o : Orientation ℝ E (Fin 2)) (v w : E) (φ : ℝ) :
    rotateVector o (v + w) φ = rotateVector o v φ + rotateVector o w φ := by
  apply toComplex_injective o
  change toComplex o _ = _
  simp only [toComplex_rotateVector, toComplex_add, add_mul]

@[simp] theorem rotateVector_sub (o : Orientation ℝ E (Fin 2)) (v w : E) (φ : ℝ) :
    rotateVector o (v - w) φ = rotateVector o v φ - rotateVector o w φ := by
  apply toComplex_injective o
  change toComplex o _ = _
  simp only [toComplex_rotateVector, toComplex_sub, sub_mul]

@[simp] theorem rotateVector_smul (o : Orientation ℝ E (Fin 2)) (r : ℝ) (v : E) (φ : ℝ) :
    rotateVector o (r • v) φ = r • rotateVector o v φ := by
  apply toComplex_injective o
  change toComplex o _ = _
  simp only [toComplex_rotateVector, toComplex_smul, mul_assoc]

@[simp] theorem rotateVector_add_angle (o : Orientation ℝ E (Fin 2)) (v : E) (φ ψ : ℝ) :
    rotateVector o v (φ + ψ) = rotateVector o (rotateVector o v ψ) φ := by
  apply toComplex_injective o
  change toComplex o _ = _
  simp only [toComplex_rotateVector, Circle.exp_add, mul_assoc]
  rw [Circle.coe_mul]
  ring

@[simp] theorem ofComplex_add (o : Orientation ℝ E (Fin 2)) (z w : ℂ) :
    ofComplex o (z + w) = ofComplex o z + ofComplex o w :=
  (complexIsometryEquiv o).symm.map_add z w
@[simp] theorem ofComplex_sub (o : Orientation ℝ E (Fin 2)) (z w : ℂ) :
    ofComplex o (z - w) = ofComplex o z - ofComplex o w :=
  (complexIsometryEquiv o).symm.map_sub z w
@[simp] theorem ofComplex_neg (o : Orientation ℝ E (Fin 2)) (z : ℂ) :
    ofComplex o (-z) = -ofComplex o z := (complexIsometryEquiv o).symm.map_neg z
@[simp] theorem ofComplex_smul (o : Orientation ℝ E (Fin 2)) (r : ℝ) (z : ℂ) :
    ofComplex o (r • z) = r • ofComplex o z := (complexIsometryEquiv o).symm.map_smul r z

/-- Multiplication of a vector by a geometric complex number, on the right. -/
def complexMulVector (o : Orientation ℝ E (Fin 2)) (z : ℂ) (v : E) : E :=
  ofComplex o (toComplex o v * z)

/-- The quarter-turn `v ↦ vi`. -/
def perp (o : Orientation ℝ E (Fin 2)) (v : E) : E := rotateVector o v (Real.pi / 2)

/-- Inverse of a nonzero vector in `G`; this totalized formula is zero at zero. -/
def vectorInverse (v : E) : G[E] := (‖v‖ ^ 2)⁻¹ • vec v

/-- The scalar, vector and bivector grades of `G`. -/
def gradeZero : Submodule ℝ G[E] := LinearMap.range (Algebra.linearMap ℝ G[E])
def gradeOne : Submodule ℝ G[E] := LinearMap.range (CliffordAlgebra.ι (planeQuadraticForm (E := E)))
def gradeTwo (o : Orientation ℝ E (Fin 2)) : Submodule ℝ G[E] := ℝ ∙ pseudoscalar o

/-- The even subalgebra `G⁺ = G⁰ ⊕ G²`. -/
abbrev evenWessel : Subalgebra ℝ G[E] := CliffordAlgebra.even _

/-- Translation by a vector. -/
def translation (v : E) : E → E := fun X => X + v

/-- Rotation of points about `P` through `φ`. -/
def rotation (o : Orientation ℝ E (Fin 2)) (P : E) (φ : ℝ) : E → E :=
  fun X => P + rotateVector o (X - P) φ

@[simp] theorem toComplex_rotation (o : Orientation ℝ E (Fin 2)) (P X : E) (φ : ℝ) :
    toComplex o (rotation o P φ X) =
      toComplex o P + (toComplex o X - toComplex o P) * Circle.exp φ := by
  simp [rotation, sub_mul]

@[simp] theorem toComplex_translation (v X : E) :
    toComplex o (translation v X) = toComplex o X + toComplex o v := by
  simp [translation, toComplex]

/-- Parallel vectors (including zero, as an algebraic convenience). -/
def Parallel (v w : E) : Prop := ∃ r : ℝ, w = r • v

/-- Orthogonality of vectors. -/
def Orthogonal (v w : E) : Prop := ⟪v, w⟫ = 0

/-- Component of `v` parallel to a nonzero vector `u`. -/
def parallelComponent (u v : E) : E := (⟪v, u⟫ / ⟪u, u⟫) • u

/-- Component of `v` perpendicular to `u`. -/
def perpComponent (u v : E) : E := v - parallelComponent u v

@[simp] theorem parallelComponent_add (u v w : E) :
    parallelComponent u (v + w) = parallelComponent u v + parallelComponent u w := by
  simp [parallelComponent, inner_add_left, add_div, add_smul]

@[simp] theorem parallelComponent_sub (u v w : E) :
    parallelComponent u (v - w) = parallelComponent u v - parallelComponent u w := by
  simp [parallelComponent, inner_sub_left, sub_div, sub_smul]

@[simp] theorem parallelComponent_smul (u : E) (r : ℝ) (v : E) :
    parallelComponent u (r • v) = r • parallelComponent u v := by
  simp [parallelComponent, inner_smul_left, mul_div_assoc, smul_smul]

@[simp] theorem perpComponent_add (u v w : E) :
    perpComponent u (v + w) = perpComponent u v + perpComponent u w := by
  simp only [perpComponent, parallelComponent_add]
  abel

@[simp] theorem perpComponent_sub (u v w : E) :
    perpComponent u (v - w) = perpComponent u v - perpComponent u w := by
  simp only [perpComponent, parallelComponent_sub]
  abel

@[simp] theorem perpComponent_smul (u : E) (r : ℝ) (v : E) :
    perpComponent u (r • v) = r • perpComponent u v := by
  simp only [perpComponent, parallelComponent_smul, smul_sub]

theorem perpComponent_inner (u v : E) (hu : u ≠ 0) : ⟪perpComponent u v, u⟫ = 0 := by
  simp only [perpComponent, parallelComponent, inner_sub_left, inner_smul_right,
    inner_smul_left, real_inner_comm v u, starRingEnd_apply, star_trivial]
  rw [div_mul_cancel₀ _ (inner_self_ne_zero.mpr hu), sub_self]

theorem perpComponent_eq_zero_iff {u v : E} (hu : u ≠ 0) :
    perpComponent u v = 0 ↔ Parallel u v := by
  constructor
  · intro h
    refine ⟨⟪v, u⟫ / ⟪u, u⟫, ?_⟩
    exact sub_eq_zero.mp h
  · rintro ⟨r, rfl⟩
    simp [perpComponent, parallelComponent, inner_smul_left]
    rw [mul_div_cancel_right₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)), sub_self]

theorem parallelComponent_add_perpComponent (u v : E) :
    parallelComponent u v + perpComponent u v = v := by
  simp [perpComponent]

/-! ### `Parallel` -/

theorem Parallel.zero_right (v : E) : Parallel v 0 := ⟨0, by simp⟩

theorem Parallel.refl {v : E} (hv : v ≠ 0) : Parallel v v := ⟨1, by simp⟩

theorem Parallel.trans {u v w : E} (h1 : Parallel u v) (h2 : Parallel v w) : Parallel u w := by
  obtain ⟨r, hr⟩ := h1
  obtain ⟨s, hs⟩ := h2
  exact ⟨s * r, by rw [hs, hr, smul_smul]⟩

theorem Parallel.smul_right {u v : E} (c : ℝ) (h : Parallel u v) : Parallel u (c • v) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨c * r, by rw [hr, smul_smul]⟩

theorem parallel_smul_left_iff {u v : E} {c : ℝ} (hc : c ≠ 0) :
    Parallel (c • u) v ↔ Parallel u v := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r * c, by rw [hr, smul_smul]⟩
  · rintro ⟨r, hr⟩
    exact ⟨r / c, by rw [hr, smul_smul, div_mul_cancel₀ _ hc]⟩

theorem parallel_comm {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) (h : Parallel u v) :
    Parallel v u := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hr
    exact hv hr
  exact ⟨r⁻¹, by rw [hr, smul_smul, inv_mul_cancel₀ hr0, one_smul]⟩

/-- A line represented by a point and a nonzero direction. -/
structure Line (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  base : E
  direction : E
  direction_ne_zero : direction ≠ 0

namespace Line

@[ext] theorem ext {ℓ ℓ' : Line E} (hbase : ℓ.base = ℓ'.base)
    (hdirection : ℓ.direction = ℓ'.direction) : ℓ = ℓ' := by
  cases ℓ
  cases ℓ'
  simp_all

variable {o : Orientation ℝ E (Fin 2)}

/-- Membership in `P + ⟨u⟩`. -/
def mem (ℓ : Line E) (X : E) : Prop := ∃ t : ℝ, X = ℓ.base + t • ℓ.direction

/-- The affine subspace determined by a line. -/
def toAffineSubspace (ℓ : Line E) : AffineSubspace ℝ E :=
  AffineSubspace.mk' ℓ.base (ℝ ∙ ℓ.direction)

/-- Translate a line by a vector. -/
def translate (ℓ : Line E) (v : E) : Line E where
  base := ℓ.base + v
  direction := ℓ.direction
  direction_ne_zero := ℓ.direction_ne_zero

/-- Reflection of a vector in the direction `u`, as `uvu⁻¹`. -/
def reflectVector (u v : E) : E := parallelComponent u v - perpComponent u v

/-- Reflection in a line. -/
def symmetry (ℓ : Line E) : E → E :=
  fun X => ℓ.base + reflectVector ℓ.direction (X - ℓ.base)

/-- A gliding symmetry, with glide parallel to the line. -/
def glide (ℓ : Line E) (w : E) : E → E := fun X => symmetry ℓ X + w

/-- Parallelism of lines, measured by their oriented area. -/
def parallel (o : Orientation ℝ E (Fin 2)) (ℓ ℓ' : Line E) : Prop :=
  orientedArea o ℓ.direction ℓ'.direction = 0

/-- The oriented angle between two unoriented lines, represented in `(0,π]`.
This is the paper's `φ(ℓ,ℓ')`; angles of lines are understood modulo `π`. -/
def angle (o : Orientation ℝ E (Fin 2)) (ℓ ℓ' : Line E) : ℝ :=
  let θ := (o.oangle ℓ.direction ℓ'.direction).toReal
  if 0 < θ then θ else θ + Real.pi

/-- The two-line intersection formula; it is the unique intersection when the
lines are nonparallel. -/
def intersection (o : Orientation ℝ E (Fin 2)) (ℓ ℓ' : Line E) : E :=
  ℓ.base + (orientedArea o (ℓ'.base - ℓ.base) ℓ'.direction /
    orientedArea o ℓ.direction ℓ'.direction) • ℓ.direction

end Line
/-! ### Membership in a line -/

namespace Line

theorem mem_base (ℓ : Line E) : ℓ.mem ℓ.base := ⟨0, by simp⟩

theorem mem_add_smul (ℓ : Line E) (t : ℝ) :
    ℓ.mem (ℓ.base + t • ℓ.direction) := ⟨t, rfl⟩

/-- `X` is on `ℓ` iff `X - ℓ.base` is parallel to the direction. -/
theorem mem_iff_parallel (ℓ : Line E) (X : E) :
    ℓ.mem X ↔ Parallel ℓ.direction (X - ℓ.base) := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, by rw [add_sub_cancel_left]⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by rw [← ht]; abel⟩

/-- Two points of a line: the segment between them is parallel to the direction. -/
theorem parallel_of_mem_sub {ℓ : Line E} {X Y : E} (hX : ℓ.mem X) (hY : ℓ.mem Y) :
    Parallel ℓ.direction (Y - X) := by
  obtain ⟨t, rfl⟩ := hX
  obtain ⟨s, hs⟩ := hY
  refine ⟨s - t, ?_⟩
  rw [hs, sub_smul]
  abel

/-- Two points determine the direction of any line through them. -/
theorem parallel_of_mem_sub' {ℓ ℓ' : Line E} {X Y : E} (hX : X ≠ Y)
    (h1 : ℓ.mem X) (h2 : ℓ.mem Y) (h3 : ℓ'.mem X) (h4 : ℓ'.mem Y) :
    Parallel ℓ.direction ℓ'.direction := by
  have h1' := ℓ.parallel_of_mem_sub h1 h2
  have h2' := ℓ'.parallel_of_mem_sub h3 h4
  obtain ⟨r, hr⟩ := h1'
  obtain ⟨s, hs⟩ := h2'
  have hne : Y - X ≠ 0 := sub_ne_zero.mpr hX.symm
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hs
    exact hne hs
  have hsr : s • ℓ'.direction = r • ℓ.direction := by rw [← hs, hr]
  refine ⟨s⁻¹ * r, ?_⟩
  calc ℓ'.direction = s⁻¹ • (s • ℓ'.direction) := by
        rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    _ = s⁻¹ • (r • ℓ.direction) := by rw [hsr]
    _ = (s⁻¹ * r) • ℓ.direction := by rw [smul_smul]

/-- Membership is invariant under translation of the point. -/
theorem translate_mem (ℓ : Line E) (v X : E) :
    (ℓ.translate v).mem X ↔ ℓ.mem (X - v) := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [show (ℓ.translate v).base = ℓ.base + v from rfl] at ht
    rw [ht]
    abel
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h2 : X = (ℓ.base + t • ℓ.direction) + v := by rw [← ht]; abel
    show X = (ℓ.base + v) + t • ℓ.direction
    rw [h2]; abel

/-- Two distinct lines with a common base point meet only there. -/
theorem eq_base_of_mem_of_mem {ℓ ℓ' : Line E} (hb : ℓ.base = ℓ'.base)
    (hpar : ¬ Parallel ℓ.direction ℓ'.direction) {X : E}
    (h1 : ℓ.mem X) (h2 : ℓ'.mem X) : X = ℓ.base := by
  obtain ⟨t, ht⟩ := h1
  obtain ⟨s, hs⟩ := h2
  rw [← hb] at hs
  have hts : t • ℓ.direction = s • ℓ'.direction := by
    rw [ht] at hs
    exact add_left_cancel hs
  by_cases ht0 : t = 0
  · rw [ht, ht0, zero_smul, add_zero]
  · exfalso
    apply hpar
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hts
      exact ℓ.direction_ne_zero ((smul_eq_zero.mp hts).resolve_left ht0)
    refine ⟨s⁻¹ * t, ?_⟩
    calc ℓ'.direction = s⁻¹ • (s • ℓ'.direction) := by
          rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
      _ = s⁻¹ • (t • ℓ.direction) := by rw [← hts]
      _ = (s⁻¹ * t) • ℓ.direction := by rw [smul_smul]

end Line

/-- Fixed-point formula for `rotation Q ψ ∘ rotation P φ`, totalized by complex
division.  Under the nondegeneracy hypotheses of the paper it is the unique fixed
point. -/
def rotationFixedPoint (o : Orientation ℝ E (Fin 2)) (P Q : E) (φ ψ : ℝ) : E :=
  P + ofComplex o (toComplex o (Q - P) *
    ((1 - Circle.exp ψ : ℂ) / (1 - (Circle.exp φ : ℂ) * Circle.exp ψ)))

/-! ## 1. Introduction -/

/-- Nondegenerate triangle with the orientation used in Figure 1. -/
structure OrientedTriangle (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2)) where
  A : E
  B : E
  C : E
  noncollinear : ¬Collinear ℝ ({A, B, C} : Set E)
  positive : 0 < orientedArea o (B - A) (C - A)

namespace OrientedTriangle

variable {o : Orientation ℝ E (Fin 2)}

/-- One third of the interior angle at `A`. -/
def alpha (T : OrientedTriangle E o) : ℝ := EuclideanGeometry.angle T.B T.A T.C / 3
/-- One third of the interior angle at `B`. -/
def beta (T : OrientedTriangle E o) : ℝ := EuclideanGeometry.angle T.C T.B T.A / 3
/-- One third of the interior angle at `C`. -/
def gamma (T : OrientedTriangle E o) : ℝ := EuclideanGeometry.angle T.A T.C T.B / 3

theorem A_ne_B (T : OrientedTriangle E o) : T.A ≠ T.B := ne₁₂_of_not_collinear T.noncollinear
theorem B_ne_C (T : OrientedTriangle E o) : T.B ≠ T.C := ne₂₃_of_not_collinear T.noncollinear
theorem A_ne_C (T : OrientedTriangle E o) : T.A ≠ T.C := ne₁₃_of_not_collinear T.noncollinear

/-- The three interior trisector lines, following Figure 1. -/
def AZ (T : OrientedTriangle E o) : Line E where
  base := T.A
  direction := rotateVector o (T.B - T.A) T.alpha
  direction_ne_zero := rotateVector_ne_zero o (sub_ne_zero.mpr T.A_ne_B.symm) _

def AY (T : OrientedTriangle E o) : Line E where
  base := T.A
  direction := rotateVector o (T.B - T.A) (2 * T.alpha)
  direction_ne_zero := rotateVector_ne_zero o (sub_ne_zero.mpr T.A_ne_B.symm) _

def BX (T : OrientedTriangle E o) : Line E where
  base := T.B
  direction := rotateVector o (T.C - T.B) T.beta
  direction_ne_zero := rotateVector_ne_zero o (sub_ne_zero.mpr T.B_ne_C.symm) _

def BZ (T : OrientedTriangle E o) : Line E where
  base := T.B
  direction := rotateVector o (T.C - T.B) (2 * T.beta)
  direction_ne_zero := rotateVector_ne_zero o (sub_ne_zero.mpr T.B_ne_C.symm) _

def CY (T : OrientedTriangle E o) : Line E where
  base := T.C
  direction := rotateVector o (T.A - T.C) T.gamma
  direction_ne_zero := rotateVector_ne_zero o (sub_ne_zero.mpr T.A_ne_C) _

def CX (T : OrientedTriangle E o) : Line E where
  base := T.C
  direction := rotateVector o (T.A - T.C) (2 * T.gamma)
  direction_ne_zero := rotateVector_ne_zero o (sub_ne_zero.mpr T.A_ne_C) _

/- The three vertices of the interior Morley triangle, defined by the fixed
point formulas explained in Theorem 3 and Corollary 1. -/
/-- The fixed point of `RB ∘ RC`, matching the two centres in Corollary 1. -/
def X (T : OrientedTriangle E o) : E :=
  rotationFixedPoint o T.C T.B (2 * T.gamma) (2 * T.beta)
-- The fixed point of `RC ∘ RA`.
def Y (T : OrientedTriangle E o) : E :=
  rotationFixedPoint o T.A T.C (2 * T.alpha) (2 * T.gamma)
-- The fixed point of `RA ∘ RB`.
def Z (T : OrientedTriangle E o) : E :=
  rotationFixedPoint o T.B T.A (2 * T.beta) (2 * T.alpha)

/-- Equality of all three side lengths; for a genuine triangle the common side
length is positive by the ambient noncollinearity hypotheses. -/
def Equilateral (P Q R : E) : Prop := dist P Q = dist Q R ∧ dist Q R = dist R P

/- Morley's Theorem 1 is stated below, after `morley_side_lengths`, where its proof is
available.  It is identical to the original statement in this namespace. -/

/-- The angle relations displayed in Figure 1. -/
def alphaBar (T : OrientedTriangle E o) : ℝ := 2 * Real.pi / 3 + T.alpha
def betaBar (T : OrientedTriangle E o) : ℝ := 2 * Real.pi / 3 + T.beta
def gammaBar (T : OrientedTriangle E o) : ℝ := 2 * Real.pi / 3 + T.gamma

theorem angle_sum (T : OrientedTriangle E o) :
    3 * T.alpha + 3 * T.beta + 3 * T.gamma = Real.pi := by
  have h := EuclideanGeometry.angle_add_angle_add_angle_eq_pi T.C T.A_ne_B
  dsimp [alpha, beta, gamma]
  linear_combination h
theorem alphaBar_eq (T : OrientedTriangle E o) :
    T.alphaBar = Real.pi - (T.beta + T.gamma) := by
  dsimp [alphaBar]
  have h := T.angle_sum
  linarith
theorem betaBar_eq (T : OrientedTriangle E o) :
    T.betaBar = Real.pi - (T.gamma + T.alpha) := by
  dsimp [betaBar]
  have h := T.angle_sum
  linarith
theorem gammaBar_eq (T : OrientedTriangle E o) :
    T.gammaBar = Real.pi - (T.alpha + T.beta) := by
  dsimp [gammaBar]
  have h := T.angle_sum
  linarith

end OrientedTriangle

/-! ## 2. The Wessel algebra -/

/-! ### `⋄1` Plane Euclidean geometry and geometric algebra -/

variable (o : Orientation ℝ E (Fin 2))

@[simp] theorem planeQuadraticForm_apply (v : E) :
    planeQuadraticForm v = ⟪v, v⟫ := rfl

theorem exteriorWedge_self (v : E) : exteriorWedge v v = 0 := ExteriorAlgebra.ι_sq_zero (R := ℝ) v
theorem exteriorWedge_swap (v w : E) : exteriorWedge w v = -exteriorWedge v w := by
  have h := ExteriorAlgebra.ι_add_mul_swap (R := ℝ) v w
  dsimp [exteriorWedge] at h ⊢
  exact eq_neg_of_add_eq_zero_right h
theorem exteriorWedge_coordinates (v w : E) :
    exteriorWedge v w = orientedArea o v w • exteriorWedge (e₁ o) (e₂ o) := by
  let b := (positiveBasis o).toBasis
  let L : E →ₗ[ℝ] E →ₗ[ℝ] ExteriorAlgebra ℝ E :=
    LinearMap.mk₂ ℝ (fun v w => exteriorWedge v w)
      (by intros; simp [exteriorWedge, add_mul])
      (by intros; simp [exteriorWedge, smul_mul_assoc])
      (by intros; simp [exteriorWedge, mul_add])
      (by intros; simp [exteriorWedge, mul_smul_comm])
  let R : E →ₗ[ℝ] E →ₗ[ℝ] ExteriorAlgebra ℝ E :=
    LinearMap.mk₂ ℝ (fun v w => orientedArea o v w • exteriorWedge (e₁ o) (e₂ o))
      (by
        intro m₁ m₂ n
        have h : orientedArea o (m₁ + m₂) n = orientedArea o m₁ n + orientedArea o m₂ n := by
          rw [orientedArea, LinearMap.map_add]
          rfl
        rw [h, add_smul])
      (by
        intro c m n
        have h : orientedArea o (c • m) n = c * orientedArea o m n := by
          rw [orientedArea, LinearMap.map_smul]
          exact LinearMap.smul_apply c (o.areaForm m) n
        rw [h, smul_smul])
      (by
        intro m n₁ n₂
        have h : orientedArea o m (n₁ + n₂) = orientedArea o m n₁ + orientedArea o m n₂ :=
          (o.areaForm m).map_add n₁ n₂
        rw [h, add_smul])
      (by
        intro c m n
        have h : orientedArea o m (c • n) = c * orientedArea o m n :=
          (o.areaForm m).map_smul c n
        rw [h, smul_smul])
  have hLR : L = R := by
    apply LinearMap.ext_basis b b
    intro i j
    dsimp [L, R]
    change exteriorWedge (b i) (b j) =
      o.areaForm (b i) (b j) • exteriorWedge (b 0) (b 1)
    rw [Orientation.areaForm_to_volumeForm,
      o.volumeForm_robust (positiveBasis o) (o.finOrthonormalBasis_orientation _ _)]
    rw [Module.Basis.det_apply]
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.det_fin_two, Module.Basis.det_apply, Module.Basis.toMatrix_apply, b,
        Module.Basis.repr_self,
        Finsupp.single_apply, Fin.zero_eta, Fin.mk_one, one_ne_zero, zero_ne_one,
        if_true, if_false, mul_zero, mul_one, zero_mul, sub_zero, zero_sub,
        one_smul, neg_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_fin_one, e₁, e₂]
    all_goals try rfl
    all_goals try rw [zero_smul]
    all_goals first
      | exact exteriorWedge_swap ((positiveBasis o).toBasis 0) ((positiveBasis o).toBasis 1)
      | rw [exteriorWedge_self]
  exact DFunLike.congr_fun (DFunLike.congr_fun hLR v) w
private theorem wedge_aux_e1_orth_e2 : ⟪e₁ o, e₂ o⟫ = 0 := by
  have h : ⟪e₁ o, e₂ o⟫ = (if (0 : Fin 2) = 1 then (1 : ℝ) else 0) :=
    orthonormal_iff_ite.mp (positiveBasis o).orthonormal 0 1
  rw [if_neg (by decide)] at h
  exact h

private theorem wedge_aux_associated_neg (v w : E) :
    (⅟2 : ℝ) • ((-planeQuadraticForm (E := E)) (v + w) -
      (-planeQuadraticForm (E := E)) v - (-planeQuadraticForm (E := E)) w) = -⟪v, w⟫ := by
  simp only [QuadraticMap.neg_apply, planeQuadraticForm_apply, invOf_eq_inv, smul_eq_mul]
  rw [inner_add_left, inner_add_right, inner_add_right, real_inner_comm w v]
  ring

private theorem wedge_aux_equivExterior_e1e2 :
    CliffordAlgebra.equivExterior (planeQuadraticForm (E := E))
        (vec (e₁ o) * vec (e₂ o)) = exteriorWedge (e₁ o) (e₂ o) := by
  simp only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply]
  rw [show vec (e₁ o) * vec (e₂ o) = CliffordAlgebra.ι (planeQuadraticForm (E := E)) (e₁ o) *
    CliffordAlgebra.ι (planeQuadraticForm (E := E)) (e₂ o) from rfl]
  rw [CliffordAlgebra.changeForm_ι_mul_ι]
  dsimp [exteriorWedge]
  simp only [sub_eq_iff_eq_add]
  have hB : (algebraMap ℝ (CliffordAlgebra (0 : QuadraticForm ℝ E)))
      ((QuadraticMap.associated (-planeQuadraticForm (E := E))) (e₁ o) (e₂ o)) = 0 := by
    have h1 := wedge_aux_associated_neg (E := E) (e₁ o) (e₂ o)
    rw [wedge_aux_e1_orth_e2, neg_zero] at h1
    have h3 := congrArg (algebraMap ℝ (CliffordAlgebra (0 : QuadraticForm ℝ E))) h1
    rwa [map_zero] at h3
  rw [hB, add_zero]

theorem wedge_eq_orientedArea (v w : E) :
    wedge v w = orientedArea o v w • pseudoscalar o := by
  have hbase : ofExterior (exteriorWedge (e₁ o) (e₂ o)) = pseudoscalar o := by
    apply (CliffordAlgebra.equivExterior (planeQuadraticForm (E := E))).injective
    simp only [ofExterior, pseudoscalar, LinearEquiv.apply_symm_apply,
      wedge_aux_equivExterior_e1e2]
  calc wedge v w = ofExterior (exteriorWedge v w) := rfl
    _ = ofExterior (orientedArea o v w • exteriorWedge (e₁ o) (e₂ o)) := by
        rw [exteriorWedge_coordinates]
    _ = orientedArea o v w • ofExterior (exteriorWedge (e₁ o) (e₂ o)) := by
        simp only [ofExterior, LinearEquiv.map_smul]
    _ = orientedArea o v w • pseudoscalar o := by rw [hbase]
private theorem aux_vec_sq (v : E) : vec v * vec v = scalar ⟪v, v⟫ := by
  simpa [vec, scalar, planeQuadraticForm_apply] using
    CliffordAlgebra.ι_sq_scalar (planeQuadraticForm (E := E)) v

private theorem aux_e1_norm : ‖e₁ o‖ = 1 := (positiveBasis o).orthonormal.1 0
private theorem aux_e2_norm : ‖e₂ o‖ = 1 := (positiveBasis o).orthonormal.1 1

private theorem aux_e1e1 : ⟪e₁ o, e₁ o⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, aux_e1_norm]; norm_num

private theorem aux_e2e2 : ⟪e₂ o, e₂ o⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, aux_e2_norm]; norm_num

private theorem aux_e1e2 : ⟪e₁ o, e₂ o⟫ = 0 := by
  have h : ⟪e₁ o, e₂ o⟫ = (if (0 : Fin 2) = 1 then (1 : ℝ) else 0) :=
    orthonormal_iff_ite.mp (positiveBasis o).orthonormal 0 1
  rw [if_neg (by decide)] at h
  exact h

private theorem aux_e2e1 : ⟪e₂ o, e₁ o⟫ = 0 := by
  have h : ⟪e₂ o, e₁ o⟫ = (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) :=
    orthonormal_iff_ite.mp (positiveBasis o).orthonormal 1 0
  rw [if_neg (by decide)] at h
  exact h

private theorem aux_vec_mul_add_swap (u v : E) :
    vec u * vec v + vec v * vec u = scalar (2 * ⟪u, v⟫) := by
  have hsq : vec (u + v) * vec (u + v) = scalar ⟪u + v, u + v⟫ := aux_vec_sq (u + v)
  have hexp : vec (u + v) * vec (u + v) =
      vec u * vec u + vec u * vec v + vec v * vec u + vec v * vec v := by
    rw [show vec (u + v) = vec u + vec v from by simp [vec], add_mul, mul_add, mul_add]
    abel
  rw [hexp, aux_vec_sq u, aux_vec_sq v] at hsq
  calc vec u * vec v + vec v * vec u
      = scalar ⟪u + v, u + v⟫ - scalar ⟪u, u⟫ - scalar ⟪v, v⟫ := by rw [← hsq]; abel
    _ = scalar (⟪u + v, u + v⟫ - ⟪u, u⟫ - ⟪v, v⟫) := by simp only [scalar, ← map_sub]
    _ = scalar (2 * ⟪u, v⟫) := by
        congr 1
        rw [inner_add_add_self, real_inner_comm v u]
        ring

private theorem aux_e1_sq : vec (e₁ o) * vec (e₁ o) = 1 := by
  rw [aux_vec_sq, aux_e1e1, scalar, map_one]

private theorem aux_e2_sq : vec (e₂ o) * vec (e₂ o) = 1 := by
  rw [aux_vec_sq, aux_e2e2, scalar, map_one]

private theorem aux_e1_mul_e2 : vec (e₁ o) * vec (e₂ o) = pseudoscalar o := rfl

private theorem aux_e2_mul_e1 : vec (e₂ o) * vec (e₁ o) = -pseudoscalar o := by
  have h := aux_vec_mul_add_swap (e₁ o) (e₂ o)
  rw [aux_e1e2, aux_e1_mul_e2] at h
  simp only [mul_zero, scalar, map_zero] at h
  exact (neg_eq_iff_add_eq_zero.mpr h).symm

private theorem aux_inner_eq (aa bb cc dd : ℝ) :
    ⟪aa • e₁ o + bb • e₂ o, cc • e₁ o + dd • e₂ o⟫ = aa * cc + bb * dd := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    aux_e1e1, aux_e2e2, aux_e1e2, aux_e2e1, mul_zero, mul_one]
  ring

private theorem aux_vec_mul_vec (aa bb cc dd : ℝ) :
    vec (aa • e₁ o + bb • e₂ o) * vec (cc • e₁ o + dd • e₂ o) =
      (aa * cc + bb * dd) • (1 : G[E]) + (aa * dd - bb * cc) • pseudoscalar o := by
  have hl : vec (aa • e₁ o + bb • e₂ o) = aa • vec (e₁ o) + bb • vec (e₂ o) := by
    simp [vec]
  have hr : vec (cc • e₁ o + dd • e₂ o) = cc • vec (e₁ o) + dd • vec (e₂ o) := by
    simp [vec]
  rw [hl, hr, add_mul, mul_add, mul_add]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  rw [mul_comm cc aa, mul_comm dd aa, mul_comm cc bb, mul_comm dd bb,
    aux_e1_sq, aux_e1_mul_e2, aux_e2_mul_e1, aux_e2_sq, smul_neg]
  module

/-- The pseudoscalar does not depend on the choice of positively oriented
orthonormal basis. -/
theorem pseudoscalar_independent_of_positive_basis
    (b : OrthonormalBasis (Fin 2) ℝ E)
    (hb : b.toBasis.orientation = o) :
    vec (b 0) * vec (b 1) = pseudoscalar o := by
  obtain ⟨aa, bb, cc, dd, hb0, hb1⟩ : ∃ aa bb cc dd : ℝ,
      b 0 = aa • e₁ o + bb • e₂ o ∧ b 1 = cc • e₁ o + dd • e₂ o := by
    refine ⟨⟪e₁ o, b 0⟫, ⟪e₂ o, b 0⟫, ⟪e₁ o, b 1⟫, ⟪e₂ o, b 1⟫, ?_, ?_⟩
    · have h : b 0 = ⟪positiveBasis o 0, b 0⟫ • positiveBasis o 0
          + ⟪positiveBasis o 1, b 0⟫ • positiveBasis o 1 := by
        conv_lhs => rw [← (positiveBasis o).sum_repr' (b 0), Fin.sum_univ_two]
      simpa [positiveBasis, e₁, e₂] using h
    · have h : b 1 = ⟪positiveBasis o 0, b 1⟫ • positiveBasis o 0
          + ⟪positiveBasis o 1, b 1⟫ • positiveBasis o 1 := by
        conv_lhs => rw [← (positiveBasis o).sum_repr' (b 1), Fin.sum_univ_two]
      simpa [positiveBasis, e₁, e₂] using h
  have hpos : o.areaForm (e₁ o) (e₂ o) = 1 := by
    rw [Orientation.areaForm_to_volumeForm,
      Orientation.volumeForm_robust o (positiveBasis o) (by simp [positiveBasis])]
    have hfam : (![e₁ o, e₂ o] : Fin 2 → E) = fun i => positiveBasis o i := by
      funext i
      fin_cases i <;> rfl
    rw [hfam]
    simpa using (positiveBasis o).toBasis.det_self
  have harea : o.areaForm (b 0) (b 1) = 1 := by
    rw [Orientation.areaForm_to_volumeForm, Orientation.volumeForm_robust o b hb]
    have hfam : (![b 0, b 1] : Fin 2 → E) = fun i => b i := by
      funext i
      fin_cases i <;> rfl
    rw [hfam]
    simpa using b.toBasis.det_self
  have he2e1 : o.areaForm (e₂ o) (e₁ o) = -1 := by
    rw [Orientation.areaForm_swap, hpos]
  have he1e1 : o.areaForm (e₁ o) (e₁ o) = 0 := Orientation.areaForm_apply_self o (e₁ o)
  have he2e2 : o.areaForm (e₂ o) (e₂ o) = 0 := Orientation.areaForm_apply_self o (e₂ o)
  have hform : o.areaForm (b 0) (b 1) = aa * dd - bb * cc := by
    rw [hb0, hb1]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hpos, he2e1,
      he1e1, he2e2, smul_eq_mul]
    ring
  have hcross : aa * dd - bb * cc = 1 := by rw [← hform, harea]
  have hdot : aa * cc + bb * dd = 0 := by
    have h : ⟪b 0, b 1⟫ = 0 := by simp
    rw [hb0, hb1, aux_inner_eq] at h
    exact h
  calc vec (b 0) * vec (b 1)
      = (aa * cc + bb * dd) • (1 : G[E]) + (aa * dd - bb * cc) • pseudoscalar o := by
        rw [hb0, hb1, aux_vec_mul_vec]
    _ = pseudoscalar o := by rw [hdot, hcross]; simp


/-! The remaining products among the four elements `1, e₁, e₂, i` used below. -/

private theorem aux_e1_mul_i : vec (e₁ o) * pseudoscalar o = vec (e₂ o) := by
  show vec (e₁ o) * (vec (e₁ o) * vec (e₂ o)) = vec (e₂ o)
  rw [← mul_assoc, aux_e1_sq, one_mul]

private theorem aux_i_mul_e2 : pseudoscalar o * vec (e₂ o) = vec (e₁ o) := by
  show vec (e₁ o) * vec (e₂ o) * vec (e₂ o) = vec (e₁ o)
  rw [mul_assoc, aux_e2_sq, mul_one]

private theorem aux_i_mul_e1 : pseudoscalar o * vec (e₁ o) = -vec (e₂ o) := by
  show vec (e₁ o) * vec (e₂ o) * vec (e₁ o) = -vec (e₂ o)
  rw [mul_assoc, aux_e2_mul_e1, mul_neg, aux_e1_mul_i]

private theorem aux_e2_mul_i : vec (e₂ o) * pseudoscalar o = -vec (e₁ o) := by
  show vec (e₂ o) * (vec (e₁ o) * vec (e₂ o)) = -vec (e₁ o)
  rw [← mul_assoc, aux_e2_mul_e1, neg_mul, aux_i_mul_e2]

private theorem aux_i_sq : pseudoscalar o * pseudoscalar o = -1 := by
  have h2 : vec (e₂ o) * (vec (e₁ o) * vec (e₂ o)) = -vec (e₁ o) := by
    rw [← mul_assoc, aux_e2_mul_e1, neg_mul, aux_i_mul_e2]
  calc pseudoscalar o * pseudoscalar o
      = vec (e₁ o) * (vec (e₂ o) * (vec (e₁ o) * vec (e₂ o))) := by
        simp only [pseudoscalar, mul_assoc]
    _ = vec (e₁ o) * -vec (e₁ o) := by rw [h2]
    _ = -(vec (e₁ o) * vec (e₁ o)) := by rw [mul_neg]
    _ = -1 := by rw [aux_e1_sq]
set_option linter.style.haveILetI false in
/-- Every multivector has the paper's unique representation `α + v + βi`. -/
theorem multivector_representation (x : G[E]) :
    ∃! (αβv : ℝ × ℝ × E),
      x = scalar αβv.1 + vec αβv.2.2 + αβv.2.1 • pseudoscalar o := by
  classical
  set T : Set G[E] := {1, vec (e₁ o), vec (e₂ o), pseudoscalar o} with hT
  set S : Submodule ℝ G[E] := Submodule.span ℝ T with hS
  have h1 : (1 : G[E]) ∈ S := Submodule.subset_span (by simp [hT])
  have h2 : vec (e₁ o) ∈ S := Submodule.subset_span (by simp [hT])
  have h3 : vec (e₂ o) ∈ S := Submodule.subset_span (by simp [hT])
  have h4 : pseudoscalar o ∈ S := Submodule.subset_span (by simp [hT])
  -- products of the four generators stay inside the span
  have hgen : ∀ g ∈ T, ∀ h ∈ T, g * h ∈ S := by
    intro g hg h hh
    simp only [hT, Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh
    rcases hg with rfl | rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl | rfl
    · simpa using h1
    · simpa using h2
    · simpa using h3
    · simpa using h4
    · simpa using h2
    · simpa [aux_e1_sq] using h1
    · rw [aux_e1_mul_e2]; exact h4
    · rw [aux_e1_mul_i]; exact h3
    · simpa using h3
    · simpa [aux_e2_mul_e1] using Submodule.smul_mem S (-1 : ℝ) h4
    · simpa [aux_e2_sq] using h1
    · simpa [aux_e2_mul_i] using Submodule.smul_mem S (-1 : ℝ) h2
    · simpa using h4
    · simpa [aux_i_mul_e1] using Submodule.smul_mem S (-1 : ℝ) h3
    · simpa [aux_i_mul_e2] using h2
    · simpa [aux_i_sq] using Submodule.smul_mem S (-1 : ℝ) h1
  -- multiplying a generator on the left preserves the span
  have hleft : ∀ g ∈ T, ∀ b ∈ S, g * b ∈ S := by
    intro g hg b hb
    induction hb using Submodule.span_induction with
    | mem y hy => exact hgen g hg y hy
    | zero => rw [mul_zero]; exact Submodule.zero_mem S
    | add y z _ _ hpy hpz => rw [mul_add]; exact Submodule.add_mem S hpy hpz
    | smul r y _ hpy => rw [mul_smul_comm]; exact Submodule.smul_mem S r hpy
  have hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx => exact hleft x hx
    | zero => intro b _; rw [zero_mul]; exact Submodule.zero_mem S
    | add x y _ _ hpx hpy =>
        intro b hb
        rw [add_mul]
        exact Submodule.add_mem S (hpx b hb) (hpy b hb)
    | smul r x _ hpx =>
        intro b hb
        rw [smul_mul_assoc]
        exact Submodule.smul_mem S r (hpx b hb)
  -- every vector of `E` lies in the span
  have hvec : ∀ v : E, vec v ∈ S := by
    intro v
    have hv : v = ⟪e₁ o, v⟫ • e₁ o + ⟪e₂ o, v⟫ • e₂ o := by
      have h := (positiveBasis o).sum_repr' v
      rw [Fin.sum_univ_two] at h
      simpa [e₁, e₂] using h.symm
    rw [hv]
    simp only [vec, map_add, map_smul]
    exact Submodule.add_mem S (Submodule.smul_mem S _ h2) (Submodule.smul_mem S _ h3)
  have hmem : ∀ y : G[E], y ∈ S := by
    intro y
    induction y using CliffordAlgebra.induction with
    | algebraMap r =>
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem S r h1
    | ι v => exact hvec v
    | mul a b ha hb => exact hmul a ha b hb
    | add a b ha hb => exact Submodule.add_mem S ha hb
  have hS_top : S = ⊤ := Submodule.eq_top_iff'.mpr hmem
  -- the linear map `α + v + βi`
  let Φ : (ℝ × ℝ × E) →ₗ[ℝ] G[E] :=
    (Algebra.linearMap ℝ G[E]).coprod
      ((LinearMap.toSpanSingleton ℝ G[E] (pseudoscalar o)).coprod
        (CliffordAlgebra.ι (planeQuadraticForm (E := E))))
  have hΦ : ∀ p : ℝ × ℝ × E,
      Φ p = scalar p.1 + vec p.2.2 + p.2.1 • pseudoscalar o := by
    intro p
    simp only [Φ, LinearMap.coprod_apply, Algebra.linearMap_apply,
      LinearMap.toSpanSingleton_apply, scalar, vec]
    abel
  have hgen_range : T ⊆ LinearMap.range Φ := by
    intro g hg
    simp only [hT, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨((1 : ℝ), (0 : ℝ), (0 : E)), by rw [hΦ]; simp [vec, scalar]⟩
    · exact ⟨((0 : ℝ), (0 : ℝ), e₁ o), by rw [hΦ]; simp [vec, scalar]⟩
    · exact ⟨((0 : ℝ), (0 : ℝ), e₂ o), by rw [hΦ]; simp [vec, scalar]⟩
    · exact ⟨((0 : ℝ), (1 : ℝ), (0 : E)), by rw [hΦ]; simp [vec, scalar]⟩
  have hsurj : LinearMap.range Φ = ⊤ := by
    rw [eq_top_iff, ← hS_top]
    exact Submodule.span_le.mpr hgen_range
  -- dimension count: both sides are four-dimensional
  have hcard : Fintype.card (Finset (Fin 2)) = 4 := by
    rw [Fintype.card_finset]; norm_num
  have hfinG : Module.finrank ℝ G[E] = 4 := by
    refine (LinearEquiv.finrank_eq
      (CliffordAlgebra.equivExterior (planeQuadraticForm (E := E)))).trans ?_
    rw [Module.finrank_eq_card_basis (Module.Basis.ExteriorAlgebra (positiveBasis o).toBasis)]
    exact hcard
  haveI hfdE : FiniteDimensional ℝ E :=
    FiniteDimensional.of_finrank_pos (by rw [(Fact.out : Module.finrank ℝ E = 2)]; norm_num)
  haveI : FiniteDimensional ℝ G[E] :=
    FiniteDimensional.of_finrank_pos (by rw [hfinG]; norm_num)
  have hfinP : Module.finrank ℝ (ℝ × ℝ × E) = 4 := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self,
      (Fact.out : Module.finrank ℝ E = 2)]
  have hinj : Function.Injective Φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := Φ) ?_).mpr ?_
    · rw [hfinP, hfinG]
    · rw [← LinearMap.range_eq_top]; exact hsurj
  obtain ⟨p, hp⟩ : ∃ p, Φ p = x := by
    have hx : x ∈ LinearMap.range Φ := by rw [hsurj]; exact Submodule.mem_top
    exact LinearMap.mem_range.mp hx
  refine ⟨p, ?_, ?_⟩
  · show x = scalar p.1 + vec p.2.2 + p.2.1 • pseudoscalar o
    rw [← hΦ p]; exact hp.symm
  · intro q hq
    have hq'' : x = scalar q.1 + vec q.2.2 + q.2.1 • pseudoscalar o := hq
    have hq' : Φ q = x := by rw [hΦ q]; exact hq''.symm
    exact hinj (hq'.trans hp.symm)

/-- The basis `{1,e₁,e₂,i}` of `G`. -/
def basisVectors : Fin 4 → G[E] := ![1, vec (e₁ o), vec (e₂ o), pseudoscalar o]
/-! ### Auxiliary lemmas for the basis `{1,e₁,e₂,i}`

The four vectors `1`, `vec e₁`, `vec e₂` and `pseudoscalar o` are shown to be linearly
independent (by applying the grade involution to a linear relation, which separates the
even and odd parts) and to span `G` (by induction over the Clifford algebra, the span being
closed under multiplication because the products of the four generators stay in it). -/


private theorem aux_e1_mul_pseudo : vec (e₁ o) * pseudoscalar o = vec (e₂ o) := by
  rw [pseudoscalar, ← mul_assoc, aux_e1_sq, one_mul]

private theorem aux_pseudo_mul_e2 : pseudoscalar o * vec (e₂ o) = vec (e₁ o) := by
  rw [pseudoscalar, mul_assoc, aux_e2_sq, mul_one]

private theorem aux_pseudo_mul_e1 : pseudoscalar o * vec (e₁ o) = - vec (e₂ o) := by
  rw [pseudoscalar, mul_assoc, aux_e2_mul_e1, mul_neg, aux_e1_mul_pseudo]

private theorem aux_e2_mul_pseudo : vec (e₂ o) * pseudoscalar o = - vec (e₁ o) := by
  rw [pseudoscalar, ← mul_assoc, aux_e2_mul_e1, neg_mul, aux_pseudo_mul_e2]

private theorem aux_pseudo_sq : pseudoscalar o * pseudoscalar o = -1 := by
  have h : vec (e₂ o) * vec (e₁ o) = -(vec (e₁ o) * vec (e₂ o)) := by
    rw [aux_e2_mul_e1, pseudoscalar]
  calc pseudoscalar o * pseudoscalar o
      = vec (e₁ o) * (vec (e₂ o) * vec (e₁ o)) * vec (e₂ o) := by
        simp only [pseudoscalar, mul_assoc]
    _ = vec (e₁ o) * (-(vec (e₁ o) * vec (e₂ o))) * vec (e₂ o) := by rw [h]
    _ = -((vec (e₁ o) * vec (e₁ o)) * (vec (e₂ o) * vec (e₂ o))) := by noncomm_ring
    _ = -1 := by rw [aux_e1_sq, aux_e2_sq, mul_one]

private theorem aux_pseudo_ne_zero : pseudoscalar o ≠ 0 := by
  intro h
  have h2 := aux_pseudo_sq o
  rw [h, zero_mul] at h2
  norm_num at h2

private theorem aux_even_norm (x y : ℝ) :
    (x • (1 : G[E]) - y • pseudoscalar o) * (x • (1 : G[E]) + y • pseudoscalar o)
      = (x ^ 2 + y ^ 2) • (1 : G[E]) := by
  have hp := aux_pseudo_sq o
  rw [sub_mul, mul_add, mul_add]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one, smul_smul, hp,
    smul_neg, mul_neg, neg_mul]
  module

private theorem aux_basisVectors_zero : basisVectors o 0 = (1 : G[E]) := rfl
private theorem aux_basisVectors_one : basisVectors o 1 = vec (e₁ o) := rfl
private theorem aux_basisVectors_two : basisVectors o 2 = vec (e₂ o) := rfl
private theorem aux_basisVectors_three : basisVectors o 3 = pseudoscalar o := rfl

private theorem aux_involute_vec (v : E) :
    CliffordAlgebra.involute (Q := planeQuadraticForm (E := E)) (vec v) = - vec v :=
  CliffordAlgebra.involute_ι (Q := planeQuadraticForm (E := E)) v

private theorem aux_involute_pseudo :
    CliffordAlgebra.involute (Q := planeQuadraticForm (E := E)) (pseudoscalar o)
      = pseudoscalar o := by
  rw [pseudoscalar, map_mul, aux_involute_vec, aux_involute_vec, neg_mul_neg]

private theorem aux_relation {a b c d : ℝ}
    (h : a • (1 : G[E]) + b • vec (e₁ o) + c • vec (e₂ o) + d • pseudoscalar o = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hinv' : CliffordAlgebra.involute (Q := planeQuadraticForm (E := E))
      (a • (1 : G[E]) + b • vec (e₁ o) + c • vec (e₂ o) + d • pseudoscalar o)
      = a • (1 : G[E]) - b • vec (e₁ o) - c • vec (e₂ o) + d • pseudoscalar o := by
    simp only [map_add, map_smul, map_one, aux_involute_vec, aux_involute_pseudo]
    module
  have hinv : a • (1 : G[E]) - b • vec (e₁ o) - c • vec (e₂ o) + d • pseudoscalar o = 0 := by
    rw [← hinv']
    simpa using congrArg (CliffordAlgebra.involute (Q := planeQuadraticForm (E := E))) h
  have hsum0 : (a • (1 : G[E]) + b • vec (e₁ o) + c • vec (e₂ o) + d • pseudoscalar o)
      + (a • (1 : G[E]) - b • vec (e₁ o) - c • vec (e₂ o) + d • pseudoscalar o) = 0 := by
    rw [h, hinv, add_zero]
  have hsum : (2 * a) • (1 : G[E]) + (2 * d) • pseudoscalar o = 0 := by
    rw [← hsum0]
    module
  have hsub0 : (a • (1 : G[E]) + b • vec (e₁ o) + c • vec (e₂ o) + d • pseudoscalar o)
      - (a • (1 : G[E]) - b • vec (e₁ o) - c • vec (e₂ o) + d • pseudoscalar o) = 0 := by
    rw [h, hinv, sub_zero]
  have hsub : (2 * b) • vec (e₁ o) + (2 * c) • vec (e₂ o) = 0 := by
    rw [← hsub0]
    module
  have heven : ((2 * a) ^ 2 + (2 * d) ^ 2) • (1 : G[E]) = 0 := by
    rw [← aux_even_norm o (2 * a) (2 * d), hsum, mul_zero]
  have hsq : (2 * a) ^ 2 + (2 * d) ^ 2 = 0 := by
    rcases smul_eq_zero.mp heven with h' | h'
    · exact h'
    · exact absurd h' one_ne_zero
  have ha : a = 0 := by nlinarith [sq_nonneg (2 * a), sq_nonneg (2 * d)]
  have hd : d = 0 := by nlinarith [sq_nonneg (2 * a), sq_nonneg (2 * d)]
  have hw : vec ((2 * b) • e₁ o + (2 * c) • e₂ o) = 0 := by
    rw [show vec ((2 * b) • e₁ o + (2 * c) • e₂ o)
        = (2 * b) • vec (e₁ o) + (2 * c) • vec (e₂ o) from by simp [vec]]
    exact hsub
  have hw0 : (2 * b) • e₁ o + (2 * c) • e₂ o = 0 := by
    have hsq2 := aux_vec_sq ((2 * b) • e₁ o + (2 * c) • e₂ o)
    rw [hw, zero_mul, scalar, Algebra.algebraMap_eq_smul_one] at hsq2
    rcases smul_eq_zero.mp hsq2.symm with h' | h'
    · exact inner_self_eq_zero.mp h'
    · exact absurd h' one_ne_zero
  have hb : b = 0 := by
    have h1 : ⟪(2 * b) • e₁ o + (2 * c) • e₂ o, e₁ o⟫ = 0 := by rw [hw0, inner_zero_left]
    have h2 : ⟪(2 * b) • e₁ o + (2 * c) • e₂ o, e₁ o⟫ = 2 * b := by
      simp only [inner_add_left, real_inner_smul_left, aux_e1e1, aux_e2e1, mul_zero, mul_one]
      ring
    linarith
  have hc : c = 0 := by
    have h1 : ⟪(2 * b) • e₁ o + (2 * c) • e₂ o, e₂ o⟫ = 0 := by rw [hw0, inner_zero_left]
    have h2 : ⟪(2 * b) • e₁ o + (2 * c) • e₂ o, e₂ o⟫ = 2 * c := by
      simp only [inner_add_left, real_inner_smul_left, aux_e1e2, aux_e2e2, mul_zero, mul_one]
      ring
    linarith
  exact ⟨ha, hb, hc, hd⟩

private theorem aux_linearIndependent : LinearIndependent ℝ (basisVectors o) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g hfg
  have hzero : ∑ j : Fin 4, (f j - g j) • basisVectors o j = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hfg, sub_self]
  rw [Fin.sum_univ_four, aux_basisVectors_zero o, aux_basisVectors_one o,
    aux_basisVectors_two o, aux_basisVectors_three o] at hzero
  obtain ⟨h0, h1, h2, h3⟩ := aux_relation o hzero
  intro i
  fin_cases i
  · show f 0 = g 0
    linarith
  · show f 1 = g 1
    linarith
  · show f 2 = g 2
    linarith
  · show f 3 = g 3
    linarith

open scoped Pointwise in
private theorem aux_span : Submodule.span ℝ (Set.range (basisVectors o)) = ⊤ := by
  set S : Submodule ℝ G[E] := Submodule.span ℝ (Set.range (basisVectors o)) with hS
  have hmem : ∀ i : Fin 4, basisVectors o i ∈ S := fun i =>
    Submodule.subset_span (Set.mem_range_self i)
  have h1 : (1 : G[E]) ∈ S := by
    rw [← aux_basisVectors_zero o]
    exact hmem 0
  have hA : vec (e₁ o) ∈ S := by
    rw [← aux_basisVectors_one o]
    exact hmem 1
  have hB : vec (e₂ o) ∈ S := by
    rw [← aux_basisVectors_two o]
    exact hmem 2
  have hi : pseudoscalar o ∈ S := by
    rw [← aux_basisVectors_three o]
    exact hmem 3
  have hTT : (Set.range (basisVectors o) * Set.range (basisVectors o)) ⊆ S := by
    rintro _ ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, rfl⟩
    fin_cases i <;> fin_cases j
    · simpa [basisVectors] using h1
    · simpa [basisVectors] using hA
    · simpa [basisVectors] using hB
    · simpa [basisVectors] using hi
    · simpa [basisVectors] using hA
    · simpa [basisVectors, aux_e1_sq] using h1
    · simpa [basisVectors, aux_e1_mul_e2] using hi
    · simpa [basisVectors, aux_e1_mul_pseudo] using hB
    · simpa [basisVectors] using hB
    · simpa [basisVectors, aux_e2_mul_e1] using neg_mem hi
    · simpa [basisVectors, aux_e2_sq] using h1
    · simpa [basisVectors, aux_e2_mul_pseudo] using neg_mem hA
    · simpa [basisVectors] using hi
    · simpa [basisVectors, aux_pseudo_mul_e1] using neg_mem hB
    · simpa [basisVectors, aux_pseudo_mul_e2] using hA
    · simpa [basisVectors, aux_pseudo_sq] using neg_mem h1
  have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    have hSS : S * S ≤ S := by
      rw [hS, Submodule.span_mul_span]
      exact Submodule.span_le.mpr hTT
    intro x hx y hy
    exact hSS (Submodule.mul_mem_mul hx hy)
  have hind : ∀ x : G[E], x ∈ S := by
    intro x
    induction x using CliffordAlgebra.induction with
    | algebraMap r =>
        rw [Algebra.algebraMap_eq_smul_one]
        exact S.smul_mem r h1
    | ι v =>
        change vec v ∈ S
        have hv : vec v = ⟪e₁ o, v⟫ • vec (e₁ o) + ⟪e₂ o, v⟫ • vec (e₂ o) := by
          conv_lhs => rw [← (positiveBasis o).sum_repr' v, Fin.sum_univ_two]
          simp [e₁, e₂, vec]
        rw [hv]
        exact S.add_mem (S.smul_mem _ hA) (S.smul_mem _ hB)
    | add x y hx hy => exact S.add_mem hx hy
    | mul x y hx hy => exact hmul x hx y hy
  exact eq_top_iff.mpr fun x _ => hind x
private theorem aux_basisVectors_exists :
    ∃ b : Module.Basis (Fin 4) ℝ G[E], (b : Fin 4 → G[E]) = basisVectors o :=
  ⟨Module.Basis.mk (aux_linearIndependent o) (le_of_eq (aux_span o).symm), Module.Basis.coe_mk _ _⟩


theorem basisVectors_isBasis : Nonempty (Module.Basis (Fin 4) ℝ G[E]) := by
  haveI : FiniteDimensional ℝ E :=
    FiniteDimensional.of_finrank_pos (by rw [(Fact.out : Module.finrank ℝ E = 2)]; norm_num)
  obtain ⟨bE⟩ : Nonempty (Module.Basis (Fin 2) ℝ E) :=
    ⟨(Module.finBasis ℝ E).reindex (finCongr (Fact.out : Module.finrank ℝ E = 2))⟩
  obtain ⟨b4, -⟩ := aux_basisVectors_exists bE.orientation
  exact ⟨b4⟩


theorem basisVectors_isBasis_exact :
    ∃ b : Module.Basis (Fin 4) ℝ G[E], (b : Fin 4 → G[E]) = basisVectors o :=
  aux_basisVectors_exists o


/-! ### `⋄2` The geometric product, Equation (1), and Table 1 -/

theorem geometric_product (v w : E) :
    vec v * vec w = scalar ⟪v, w⟫ + wedge v w := by
  apply (CliffordAlgebra.equivExterior (planeQuadraticForm (E := E))).injective
  show CliffordAlgebra.equivExterior (planeQuadraticForm (E := E)) (vec v * vec w) =
    CliffordAlgebra.equivExterior (planeQuadraticForm (E := E)) (scalar ⟪v, w⟫ + wedge v w)
  rw [map_add]
  have hw : CliffordAlgebra.equivExterior (planeQuadraticForm (E := E)) (wedge v w) =
      exteriorWedge v w := by
    exact (CliffordAlgebra.equivExterior (planeQuadraticForm (E := E))).apply_symm_apply _
  rw [hw]
  simp only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply]
  simp only [scalar]
  rw [CliffordAlgebra.changeForm_algebraMap]
  rw [show vec v * vec w = CliffordAlgebra.ι (planeQuadraticForm (E := E)) v *
    CliffordAlgebra.ι (planeQuadraticForm (E := E)) w from rfl]
  rw [CliffordAlgebra.changeForm_ι_mul_ι]
  dsimp [exteriorWedge]
  simp only [map_sub, sub_eq_iff_eq_add, map_add, map_mul, map_inv₀, map_ofNat]
  rw [QuadraticMap.associated_apply ℝ]
  have hscalar : (⅟2 : ℝ) • ((-planeQuadraticForm) (v + w) -
      (-planeQuadraticForm) v - (-planeQuadraticForm) w) = -⟪v, w⟫ := by
    simp only [QuadraticMap.neg_apply, planeQuadraticForm_apply, invOf_eq_inv, smul_eq_mul]
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_comm w v]
    ring
  have hm := congrArg (algebraMap ℝ (CliffordAlgebra (0 : QuadraticForm ℝ E))) hscalar
  rw [map_neg] at hm
  have hfinal :
      (algebraMap ℝ (CliffordAlgebra (0 : QuadraticForm ℝ E))) ⟪v, w⟫ +
        (ExteriorAlgebra.ι ℝ) v * (ExteriorAlgebra.ι ℝ) w +
        (algebraMap ℝ (CliffordAlgebra (0 : QuadraticForm ℝ E)))
          ((⅟2 : ℝ) • ((-planeQuadraticForm) (v + w) -
            (-planeQuadraticForm) v - (-planeQuadraticForm) w)) =
        (ExteriorAlgebra.ι ℝ) v * (ExteriorAlgebra.ι ℝ) w := by
    calc
      _ = (ExteriorAlgebra.ι ℝ) v * (ExteriorAlgebra.ι ℝ) w +
          ((algebraMap ℝ (CliffordAlgebra (0 : QuadraticForm ℝ E))) ⟪v, w⟫ +
           (algebraMap ℝ (CliffordAlgebra (0 : QuadraticForm ℝ E)))
             ((⅟2 : ℝ) • ((-planeQuadraticForm) (v + w) -
               (-planeQuadraticForm) v - (-planeQuadraticForm) w))) := by abel
      _ = _ := by rw [hm, add_neg_cancel, add_zero]
  exact hfinal.symm ▸ rfl
theorem vector_square (v : E) : vec v * vec v = scalar ⟪v, v⟫ := by
  simpa [vec, scalar] using CliffordAlgebra.ι_sq_scalar (planeQuadraticForm (E := E)) v
theorem vector_mul_eq_neg_of_orthogonal {v w : E} (h : Orthogonal v w) :
    vec w * vec v = -(vec v * vec w) := by
  -- the polar form of `planeQuadraticForm` is twice the inner product
  have polar_plane : ∀ a b : E,
      QuadraticMap.polar (planeQuadraticForm (E := E)) a b = 2 * ⟪a, b⟫ := by
    intro a b
    rw [planeQuadraticForm, LinearMap.BilinMap.polar_toQuadraticMap]
    simp [real_inner_comm a b, two_mul]
  have hsum : vec v * vec w + vec w * vec v = 0 := by
    have hh : vec v * vec w + vec w * vec v =
        algebraMap ℝ G[E] (QuadraticMap.polar (planeQuadraticForm (E := E)) v w) :=
      CliffordAlgebra.ι_mul_ι_add_swap (Q := planeQuadraticForm (E := E)) v w
    rw [polar_plane, h, mul_zero, Algebra.algebraMap_eq_smul_one, zero_smul] at hh
    exact hh
  exact eq_neg_of_add_eq_zero_right hsum
theorem vector_inverse {v : E} (hv : v ≠ 0) : vec v * vectorInverse v = 1 := by
  rw [vectorInverse, mul_smul_comm, vec, CliffordAlgebra.ι_sq_scalar]
  change (‖v‖ ^ 2)⁻¹ • algebraMap ℝ _ ⟪v, v⟫ = 1
  rw [Algebra.smul_def, ← map_mul]
  simp [real_inner_self_eq_norm_sq, pow_ne_zero, norm_ne_zero_iff.mpr hv]
theorem vector_inverse_formula {v : E} (hv : v ≠ 0) :
    vectorInverse v * vec v = 1 := by
  rw [vectorInverse, smul_mul_assoc, vec, CliffordAlgebra.ι_sq_scalar]
  change (‖v‖ ^ 2)⁻¹ • algebraMap ℝ _ ⟪v, v⟫ = 1
  rw [Algebra.smul_def, ← map_mul]
  simp [real_inner_self_eq_norm_sq, pow_ne_zero, norm_ne_zero_iff.mpr hv]

/-- Universal existence and uniqueness statement supplied by the Clifford
algebra; this is the coordinate-free content of the construction of the product. -/
theorem geometric_product_universal {A : Type*} [Ring A] [Algebra ℝ A]
    (f : E →ₗ[ℝ] A) (hf : ∀ v, f v * f v = algebraMap ℝ A ⟪v, v⟫) :
    ∃! g : G[E] →ₐ[ℝ] A, ∀ v, g (vec v) = f v := by
  let g : G[E] →ₐ[ℝ] A := CliffordAlgebra.lift _ ⟨f, hf⟩
  refine ⟨g, ?_, ?_⟩
  · intro v
    exact CliffordAlgebra.lift_ι_apply f hf v
  · intro g' hg'
    apply CliffordAlgebra.hom_ext
    ext v
    change g' (vec v) = g (vec v)
    rw [hg' v]
    exact (CliffordAlgebra.lift_ι_apply f hf v).symm

@[simp] theorem e1_mul_e1 : vec (e₁ o) * vec (e₁ o) = 1 := by
  rw [vector_square]
  simp [scalar, e₁, positiveBasis]
@[simp] theorem e2_mul_e2 : vec (e₂ o) * vec (e₂ o) = 1 := by
  rw [vector_square]
  simp [scalar, e₂, positiveBasis]
@[simp] theorem e1_mul_e2 : vec (e₁ o) * vec (e₂ o) = pseudoscalar o := rfl
@[simp] theorem e2_mul_e1 : vec (e₂ o) * vec (e₁ o) = -pseudoscalar o := by
  have polar_plane : ∀ a b : E,
      QuadraticMap.polar (planeQuadraticForm (E := E)) a b = 2 * ⟪a, b⟫ := by
    intro a b
    rw [planeQuadraticForm, LinearMap.BilinMap.polar_toQuadraticMap]
    simp [real_inner_comm a b, two_mul]
  have hortho : (planeQuadraticForm (E := E)).IsOrtho (e₁ o) (e₂ o) := by
    rw [← QuadraticMap.isOrtho_polarBilin, QuadraticMap.polarBilin_apply_apply, polar_plane]
    simp [e₁, e₂, positiveBasis]
  have h := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (Q := planeQuadraticForm (E := E)) hortho
  simp only [vec, pseudoscalar] at h ⊢
  exact (neg_eq_iff_eq_neg.mpr h).symm
@[simp] theorem pseudoscalar_sq : pseudoscalar o * pseudoscalar o = -1 := by
  have polar_plane : ∀ a b : E,
      QuadraticMap.polar (planeQuadraticForm (E := E)) a b = 2 * ⟪a, b⟫ := by
    intro a b
    rw [planeQuadraticForm, LinearMap.BilinMap.polar_toQuadraticMap]
    simp [real_inner_comm a b, two_mul]
  -- `e₁e₂e₁ = -e₂` is the vector identity `aba` of the Clifford algebra
  have h : vec (e₁ o) * vec (e₂ o) * vec (e₁ o) = -vec (e₂ o) := by
    have hh := CliffordAlgebra.ι_mul_ι_mul_ι (Q := planeQuadraticForm (E := E)) (e₁ o) (e₂ o)
    simp only [vec] at hh ⊢
    have hv : QuadraticMap.polar (planeQuadraticForm (E := E)) (e₁ o) (e₂ o) • (e₁ o) -
        planeQuadraticForm (e₁ o) • (e₂ o) = -e₂ o := by
      rw [polar_plane, planeQuadraticForm_apply]
      simp [e₁, e₂, positiveBasis]
    rw [hh, hv, map_neg]
  calc pseudoscalar o * pseudoscalar o
      = (vec (e₁ o) * vec (e₂ o) * vec (e₁ o)) * vec (e₂ o) := by
        simp only [pseudoscalar, mul_assoc]
    _ = (-vec (e₂ o)) * vec (e₂ o) := by rw [h]
    _ = -1 := by rw [neg_mul, e2_mul_e2]
@[simp] theorem e1_mul_i : vec (e₁ o) * pseudoscalar o = vec (e₂ o) := by
  rw [pseudoscalar, ← mul_assoc, e1_mul_e1, one_mul]
@[simp] theorem e2_mul_i : vec (e₂ o) * pseudoscalar o = -vec (e₁ o) := by
  have polar_plane : ∀ a b : E,
      QuadraticMap.polar (planeQuadraticForm (E := E)) a b = 2 * ⟪a, b⟫ := by
    intro a b
    rw [planeQuadraticForm, LinearMap.BilinMap.polar_toQuadraticMap]
    simp [real_inner_comm a b, two_mul]
  have h : vec (e₂ o) * vec (e₁ o) * vec (e₂ o) = -vec (e₁ o) := by
    have hh := CliffordAlgebra.ι_mul_ι_mul_ι (Q := planeQuadraticForm (E := E)) (e₂ o) (e₁ o)
    simp only [vec] at hh ⊢
    have hv : QuadraticMap.polar (planeQuadraticForm (E := E)) (e₂ o) (e₁ o) • (e₂ o) -
        planeQuadraticForm (e₂ o) • (e₁ o) = -e₁ o := by
      rw [polar_plane, planeQuadraticForm_apply]
      simp [e₁, e₂, positiveBasis]
    rw [hh, hv, map_neg]
  calc vec (e₂ o) * pseudoscalar o
      = vec (e₂ o) * vec (e₁ o) * vec (e₂ o) := by rw [pseudoscalar, mul_assoc]
    _ = -vec (e₁ o) := h
@[simp] theorem i_mul_e1 : pseudoscalar o * vec (e₁ o) = -vec (e₂ o) := by
  have polar_plane : ∀ a b : E,
      QuadraticMap.polar (planeQuadraticForm (E := E)) a b = 2 * ⟪a, b⟫ := by
    intro a b
    rw [planeQuadraticForm, LinearMap.BilinMap.polar_toQuadraticMap]
    simp [real_inner_comm a b, two_mul]
  have h : vec (e₁ o) * vec (e₂ o) * vec (e₁ o) = -vec (e₂ o) := by
    have hh := CliffordAlgebra.ι_mul_ι_mul_ι (Q := planeQuadraticForm (E := E)) (e₁ o) (e₂ o)
    simp only [vec] at hh ⊢
    have hv : QuadraticMap.polar (planeQuadraticForm (E := E)) (e₁ o) (e₂ o) • (e₁ o) -
        planeQuadraticForm (e₁ o) • (e₂ o) = -e₂ o := by
      rw [polar_plane, planeQuadraticForm_apply]
      simp [e₁, e₂, positiveBasis]
    rw [hh, hv, map_neg]
  show vec (e₁ o) * vec (e₂ o) * vec (e₁ o) = -vec (e₂ o)
  exact h
@[simp] theorem i_mul_e2 : pseudoscalar o * vec (e₂ o) = vec (e₁ o) := by
  rw [pseudoscalar, mul_assoc, e2_mul_e2, mul_one]

/-- Bit labels for Table 1, Middle and Right. -/
abbrev Bits := Fin 2 → Bool
/-- Bitwise XOR (`j+k` in the paper). -/
def bitAdd (j k : Bits) : Bits := fun n => j n ^^ k n
/-- The transposition counter of Table 1. -/
def transpositionCounter (j k : Bits) : ℕ := if j 1 && k 0 then 1 else 0
/-- Basis element indexed by two bits. -/
def bitBasis : Bits → G[E] := fun j =>
  (if j 0 then vec (e₁ o) else 1) * (if j 1 then vec (e₂ o) else 1)

/-- Equation (2), the bit presentation of the multiplication table. -/
theorem bitBasis_mul (j k : Bits) :
    bitBasis o j * bitBasis o k =
      ((-1 : ℝ) ^ transpositionCounter j k) • bitBasis o (bitAdd j k) := by
  -- a bit vector of length two is determined by its two bits
  obtain ⟨a, b, rfl⟩ : ∃ a b : Bool, j = ![a, b] :=
    ⟨j 0, j 1, by funext n; fin_cases n <;> rfl⟩
  obtain ⟨c, d, rfl⟩ : ∃ c d : Bool, k = ![c, d] :=
    ⟨k 0, k 1, by funext n; fin_cases n <;> rfl⟩
  -- the sixteen entries of Table 1
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [bitAdd, transpositionCounter, bitBasis]

theorem transpositionCounter_associativity_parity (j k l : Bits) :
    (transpositionCounter j k + transpositionCounter (bitAdd j k) l) % 2 =
    (transpositionCounter k l + transpositionCounter j (bitAdd k l)) % 2 := by
  revert j k l
  decide

/-! ### `⋄3` Geometric algebra and the even subalgebra -/

/-- Expansion of a plane vector in the chosen orthonormal basis. -/
private theorem aux_smul_e1_add_smul_e2 {o : Orientation ℝ E (Fin 2)} (v : E) :
    v = ⟪e₁ o, v⟫ • e₁ o + ⟪e₂ o, v⟫ • e₂ o := by
  have h := (positiveBasis o).sum_repr' v
  simpa [Fin.sum_univ_two, e₁, e₂] using h.symm

/-- The product of two even combinations `s + t i` and `α + β i`. -/
private theorem aux_grade_mul {o : Orientation ℝ E (Fin 2)} (s t α β : ℝ) :
    (s • (1 : G[E]) + t • pseudoscalar o) * (scalar α + β • pseudoscalar o)
      = scalar (s * α - t * β) + (s * β + t * α) • pseudoscalar o := by
  have hsc : ∀ r : ℝ, scalar (E := E) r = r • (1 : G[E]) := fun r => by
    rw [scalar, Algebra.algebraMap_eq_smul_one]
  have hωα : pseudoscalar o * scalar α = α • pseudoscalar o := by
    rw [scalar, Algebra.smul_def (R := ℝ) (A := G[E]), Algebra.commutes]
  calc (s • (1 : G[E]) + t • pseudoscalar o) * (scalar α + β • pseudoscalar o)
      = s • (scalar α + β • pseudoscalar o)
          + t • (pseudoscalar o * (scalar α + β • pseudoscalar o)) := by
        rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc]
    _ = s • (scalar α + β • pseudoscalar o)
          + t • (α • pseudoscalar o + β • (-(1 : G[E]))) := by
        rw [mul_add, hωα, mul_smul_comm, pseudoscalar_sq]
    _ = scalar (s * α - t * β) + (s * β + t * α) • pseudoscalar o := by
        rw [hsc (s * α - t * β), hsc α]
        module

/-- A product of two plane vectors lies in `ℝ·1 ⊕ ℝ·i`. -/
private theorem aux_pair_product {o : Orientation ℝ E (Fin 2)} (m₁ m₂ : E) :
    ∃ s t : ℝ, vec m₁ * vec m₂ = s • (1 : G[E]) + t • pseudoscalar o := by
  obtain ⟨a, b, h1⟩ : ∃ a b : ℝ, m₁ = a • e₁ o + b • e₂ o :=
    ⟨⟪e₁ o, m₁⟫, ⟪e₂ o, m₁⟫, aux_smul_e1_add_smul_e2 m₁⟩
  obtain ⟨c, d, h2⟩ : ∃ c d : ℝ, m₂ = c • e₁ o + d • e₂ o :=
    ⟨⟪e₁ o, m₂⟫, ⟪e₂ o, m₂⟫, aux_smul_e1_add_smul_e2 m₂⟩
  refine ⟨a * c + b * d, a * d - b * c, ?_⟩
  rw [h1, h2, aux_vec_mul_vec]

theorem evenWessel_representation (x : evenWessel (E := E)) :
    ∃ α β : ℝ, (x : G[E]) = scalar α + β • pseudoscalar o := by
  obtain ⟨y, hy⟩ := x
  have hy' : y ∈ CliffordAlgebra.evenOdd (planeQuadraticForm (E := E)) 0 := by
    rw [← CliffordAlgebra.even_toSubmodule]
    exact hy
  show ∃ α β : ℝ, y = scalar α + β • pseudoscalar o
  clear hy
  induction y, hy' using CliffordAlgebra.even_induction with
  | algebraMap r => exact ⟨r, 0, by simp [scalar]⟩
  | add a b ha hb iha ihb =>
      obtain ⟨α₁, β₁, h1⟩ := iha
      obtain ⟨α₂, β₂, h2⟩ := ihb
      refine ⟨α₁ + α₂, β₁ + β₂, ?_⟩
      rw [h1, h2, add_smul]
      simp only [scalar, map_add]
      abel
  | ι_mul_ι_mul m₁ m₂ y hy ih =>
      obtain ⟨α, β, hαβ⟩ := ih
      obtain ⟨s, t, hst⟩ := aux_pair_product (o := o) m₁ m₂
      refine ⟨s * α - t * β, s * β + t * α, ?_⟩
      show vec m₁ * vec m₂ * y = _
      rw [hαβ, hst, aux_grade_mul]


/- `G⁺` is the field of geometric complex numbers. -/

/-! ### Helpers for `evenWessel_equiv_complex` -/

theorem eec_toComplex_e1 (o : Orientation ℝ E (Fin 2)) : toComplex o (e₁ o) = 1 := by
  simp [toComplex, complexIsometryEquiv, e₁, OrthonormalBasis.equiv_apply_basis,
    Complex.coe_orthonormalBasisOneI]

theorem eec_toComplex_e2 (o : Orientation ℝ E (Fin 2)) : toComplex o (e₂ o) = Complex.I := by
  simp [toComplex, complexIsometryEquiv, e₂, OrthonormalBasis.equiv_apply_basis,
    Complex.coe_orthonormalBasisOneI]

theorem eec_expand (o : Orientation ℝ E (Fin 2)) (m : E) :
    m = ⟪e₁ o, m⟫ • e₁ o + ⟪e₂ o, m⟫ • e₂ o := by
  have h := (positiveBasis o).sum_repr' m
  simpa [Fin.sum_univ_two, e₁, e₂] using h.symm

theorem eec_area_diag (o : Orientation ℝ E (Fin 2)) : o.areaForm (e₁ o) (e₂ o) = 1 := by
  rw [Orientation.areaForm_to_volumeForm,
    Orientation.volumeForm_robust o (positiveBasis o) (by simp [positiveBasis])]
  have hfam : (![e₁ o, e₂ o] : Fin 2 → E) = fun i => positiveBasis o i := by
    funext i
    fin_cases i <;> rfl
  rw [hfam]
  simpa using (positiveBasis o).toBasis.det_self

theorem eec_inner_expand (o : Orientation ℝ E (Fin 2)) (m₁ m₂ : E) :
    ⟪m₁, m₂⟫ = ⟪e₁ o, m₁⟫ * ⟪e₁ o, m₂⟫ + ⟪e₂ o, m₁⟫ * ⟪e₂ o, m₂⟫ := by
  conv_lhs => rw [eec_expand o m₁, eec_expand o m₂]
  rw [aux_inner_eq]

theorem eec_area_expand (o : Orientation ℝ E (Fin 2)) (m₁ m₂ : E) :
    orientedArea o m₁ m₂ = ⟪e₁ o, m₁⟫ * ⟪e₂ o, m₂⟫ - ⟪e₂ o, m₁⟫ * ⟪e₁ o, m₂⟫ := by
  have hpos := eec_area_diag o
  have h11 : o.areaForm (e₁ o) (e₁ o) = 0 := Orientation.areaForm_apply_self o (e₁ o)
  have h22 : o.areaForm (e₂ o) (e₂ o) = 0 := Orientation.areaForm_apply_self o (e₂ o)
  have h21 : o.areaForm (e₂ o) (e₁ o) = -1 := by
    rw [Orientation.areaForm_swap, hpos]
  rw [orientedArea]
  conv_lhs => rw [eec_expand o m₁, eec_expand o m₂]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hpos, h11, h22, h21,
    smul_eq_mul, mul_neg, mul_one]
  ring

theorem eec_toComplex_expand (o : Orientation ℝ E (Fin 2)) (m : E) :
    toComplex o m = (⟪e₁ o, m⟫ : ℂ) + (⟪e₂ o, m⟫ : ℂ) * Complex.I := by
  conv_lhs => rw [eec_expand o m]
  rw [toComplex_add, toComplex_smul, toComplex_smul, eec_toComplex_e1, eec_toComplex_e2]
  simp

theorem eec_complex_mul (o : Orientation ℝ E (Fin 2)) (m₁ m₂ : E) :
    conj (toComplex o m₁) * toComplex o m₂ =
      (⟪m₁, m₂⟫ : ℂ) + (orientedArea o m₁ m₂ : ℂ) * Complex.I := by
  rw [eec_toComplex_expand o m₁, eec_toComplex_expand o m₂, eec_inner_expand o m₁ m₂,
    eec_area_expand o m₁ m₂]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
    ring

theorem eec_vec_mul_expand (o : Orientation ℝ E (Fin 2)) (m₁ m₂ : E) :
    vec m₁ * vec m₂ = scalar ⟪m₁, m₂⟫ + orientedArea o m₁ m₂ • pseudoscalar o := by
  conv_lhs => rw [eec_expand o m₁, eec_expand o m₂]
  rw [aux_vec_mul_vec, ← eec_inner_expand o m₁ m₂, ← eec_area_expand o m₁ m₂, scalar,
    Algebra.algebraMap_eq_smul_one]

/-! #### An orthonormal-frame-free orientation, the pseudoscalar as an even unit -/

theorem eec_orientation : Nonempty (Orientation ℝ E (Fin 2)) := by
  classical
  have h2 : Module.finrank ℝ E = 2 := Fact.out
  haveI : FiniteDimensional ℝ E :=
    FiniteDimensional.of_finrank_pos (by rw [h2]; norm_num)
  exact ⟨(Module.finBasisOfFinrankEq ℝ E h2).orientation⟩

theorem eec_u_mem (o : Orientation ℝ E (Fin 2)) : pseudoscalar o ∈ evenWessel (E := E) := by
  show pseudoscalar o ∈ (CliffordAlgebra.even (planeQuadraticForm (E := E))).toSubmodule
  rw [CliffordAlgebra.even_toSubmodule]
  exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (planeQuadraticForm (E := E)) (e₁ o) (e₂ o)

theorem eec_u_sq (o : Orientation ℝ E (Fin 2)) :
    (⟨pseudoscalar o, eec_u_mem o⟩ : evenWessel (E := E)) *
      (⟨pseudoscalar o, eec_u_mem o⟩ : evenWessel (E := E)) = -1 := by
  apply Subtype.ext
  show pseudoscalar o * pseudoscalar o = ((-1 : evenWessel (E := E)) : G[E])
  rw [pseudoscalar_sq]
  simp

theorem eec_evenι_pair (o : Orientation ℝ E (Fin 2)) (m₁ m₂ : E) :
    (CliffordAlgebra.even.ι (planeQuadraticForm (E := E))).bilin m₁ m₂ =
      (⟨vec m₁ * vec m₂, by
        show vec m₁ * vec m₂ ∈ (CliffordAlgebra.even (planeQuadraticForm (E := E))).toSubmodule
        rw [CliffordAlgebra.even_toSubmodule]
        exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero _ m₁ m₂⟩ : evenWessel (E := E)) := rfl

theorem eec_u_as_pair (o : Orientation ℝ E (Fin 2)) :
    (⟨pseudoscalar o, eec_u_mem o⟩ : evenWessel (E := E)) =
      (CliffordAlgebra.even.ι (planeQuadraticForm (E := E))).bilin (e₁ o) (e₂ o) := rfl

/-! #### The bilinear map `(m₁, m₂) ↦ conj z₁ * z₂` -/

def eec_bin (o : Orientation ℝ E (Fin 2)) : E →ₗ[ℝ] E →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (fun m₁ m₂ => conj (toComplex o m₁) * toComplex o m₂)
    (by intro m₁ m₂ n; simp [add_mul])
    (by intro c m n; rw [toComplex_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]; ring)
    (by intro m n₁ n₂; simp [mul_add])
    (by intro c m n; rw [toComplex_smul, Complex.real_smul]; ring)

theorem eec_bin_apply (o : Orientation ℝ E (Fin 2)) (m₁ m₂ : E) :
    eec_bin o m₁ m₂ = conj (toComplex o m₁) * toComplex o m₂ := rfl

theorem eec_bin_diag (o : Orientation ℝ E (Fin 2)) (m : E) :
    eec_bin o m m = (⟪m, m⟫ : ℂ) := by
  rw [eec_bin_apply, Complex.conj_mul', toComplex_norm, real_inner_self_eq_norm_sq,
    Complex.ofReal_pow]

theorem eec_bin_contract_mid (o : Orientation ℝ E (Fin 2)) (m₁ m₂ m₃ : E) :
    eec_bin o m₁ m₂ * eec_bin o m₂ m₃ = ⟪m₂, m₂⟫ • eec_bin o m₁ m₃ := by
  rw [eec_bin_apply, eec_bin_apply, eec_bin_apply, Complex.real_smul]
  have h₂ : toComplex o m₂ * conj (toComplex o m₂) = (⟪m₂, m₂⟫ : ℂ) := by
    rw [mul_comm, ← eec_bin_apply, eec_bin_diag]
  rw [← h₂]
  ring

/-! #### The two algebra homomorphisms and their inverse laws -/

def eec_evenHom (o : Orientation ℝ E (Fin 2)) :
    CliffordAlgebra.EvenHom (planeQuadraticForm (E := E)) ℂ where
  bilin := eec_bin o
  contract m := by
    show eec_bin o m m = algebraMap ℝ ℂ (planeQuadraticForm (E := E) m)
    rw [planeQuadraticForm_apply, eec_bin_diag, Complex.coe_algebraMap]
  contract_mid m₁ m₂ m₃ := eec_bin_contract_mid o m₁ m₂ m₃

def eec_Psi (o : Orientation ℝ E (Fin 2)) : evenWessel (E := E) →ₐ[ℝ] ℂ :=
  CliffordAlgebra.even.lift (planeQuadraticForm (E := E)) (eec_evenHom o)

theorem eec_Psi_pair (o : Orientation ℝ E (Fin 2)) (m₁ m₂ : E) :
    eec_Psi o ((CliffordAlgebra.even.ι (planeQuadraticForm (E := E))).bilin m₁ m₂) =
      conj (toComplex o m₁) * toComplex o m₂ :=
  CliffordAlgebra.even.lift_ι (planeQuadraticForm (E := E)) (eec_evenHom o) m₁ m₂

def eec_Phi (o : Orientation ℝ E (Fin 2)) : ℂ →ₐ[ℝ] evenWessel (E := E) :=
  Complex.liftAux ⟨pseudoscalar o, eec_u_mem o⟩ (eec_u_sq o)

theorem eec_Phi_apply (o : Orientation ℝ E (Fin 2)) (z : ℂ) :
    eec_Phi o z = algebraMap ℝ (evenWessel (E := E)) z.re +
      z.im • (⟨pseudoscalar o, eec_u_mem o⟩ : evenWessel (E := E)) :=
  Complex.liftAux_apply _ _ z

theorem eec_Phi_I (o : Orientation ℝ E (Fin 2)) :
    eec_Phi o Complex.I = ⟨pseudoscalar o, eec_u_mem o⟩ :=
  Complex.liftAux_apply_I _ _

theorem eec_Psi_comp_Phi (o : Orientation ℝ E (Fin 2)) :
    (eec_Psi o).comp (eec_Phi o) = AlgHom.id ℝ ℂ := by
  apply Complex.algHom_ext
  rw [AlgHom.comp_apply, eec_Phi_I, eec_u_as_pair, eec_Psi_pair, eec_toComplex_e1,
    eec_toComplex_e2]
  simp

theorem eec_Phi_apply_complex_mul (o : Orientation ℝ E (Fin 2)) (m₁ m₂ : E) :
    ((eec_Phi o (conj (toComplex o m₁) * toComplex o m₂) : evenWessel (E := E)) : G[E]) =
      vec m₁ * vec m₂ := by
  rw [eec_Phi_apply, eec_complex_mul]
  have hre : ((⟪m₁, m₂⟫ : ℂ) + (orientedArea o m₁ m₂ : ℂ) * Complex.I).re = ⟪m₁, m₂⟫ := by simp
  have him : ((⟪m₁, m₂⟫ : ℂ) + (orientedArea o m₁ m₂ : ℂ) * Complex.I).im = orientedArea o m₁ m₂ :=
    by simp
  rw [hre, him, eec_vec_mul_expand o m₁ m₂]
  simp [scalar]

theorem eec_Phi_comp_Psi (o : Orientation ℝ E (Fin 2)) :
    (eec_Phi o).comp (eec_Psi o) = AlgHom.id ℝ (evenWessel (E := E)) := by
  apply CliffordAlgebra.even.algHom_ext (Q := planeQuadraticForm (E := E))
  apply CliffordAlgebra.EvenHom.ext
  refine LinearMap.ext fun m₁ => LinearMap.ext fun m₂ => ?_
  simp only [CliffordAlgebra.EvenHom.compr₂_bilin, LinearMap.compr₂_apply,
    AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.id_apply]
  rw [eec_Psi_pair, eec_evenι_pair o m₁ m₂]
  apply Subtype.ext
  exact eec_Phi_apply_complex_mul o m₁ m₂

/-- `G⁺` is the field of geometric complex numbers. -/
theorem evenWessel_equiv_complex : Nonempty (evenWessel (E := E) ≃ₐ[ℝ] ℂ) := by
  classical
  obtain ⟨o⟩ := eec_orientation (E := E)
  exact ⟨AlgEquiv.ofAlgHom (eec_Psi o) (eec_Phi o) (eec_Psi_comp_Phi o) (eec_Phi_comp_Psi o)⟩


theorem wm_vec_add (v w : E) : vec (v + w) = vec v + vec w := by
  simp [vec]

theorem wm_vec_smul (r : ℝ) (v : E) : vec (r • v) = r • vec v := by
  simp [vec]

theorem wm_vec_sub (v w : E) : vec (v - w) = vec v - vec w := by
  simp [vec]

theorem wm_vec_neg (v : E) : vec (-v) = -vec v := by
  simp [vec]

theorem wm_eq_smul_e1_add_smul_e2 (v : E) :
    v = ⟪e₁ o, v⟫ • e₁ o + ⟪e₂ o, v⟫ • e₂ o := by
  have h := (positiveBasis o).sum_repr' v
  simpa [Fin.sum_univ_two, e₁, e₂] using h.symm

theorem wm_toComplex_e1 : toComplex o (e₁ o) = 1 := by
  simp [toComplex, complexIsometryEquiv, e₁, OrthonormalBasis.equiv_apply_basis,
    Complex.coe_orthonormalBasisOneI]

theorem wm_toComplex_e2 : toComplex o (e₂ o) = Complex.I := by
  simp [toComplex, complexIsometryEquiv, e₂, OrthonormalBasis.equiv_apply_basis,
    Complex.coe_orthonormalBasisOneI]

theorem wm_toComplex_perp (v : E) :
    toComplex o (perp o v) = toComplex o v * Complex.I := by
  rw [perp, toComplex_rotateVector]
  congr 1
  rw [Circle.coe_exp, Complex.exp_mul_I]
  norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem wm_perp_add (v w : E) :
    perp o (v + w) = perp o v + perp o w := by
  simp only [perp, rotateVector_add]

theorem wm_perp_smul (r : ℝ) (v : E) :
    perp o (r • v) = r • perp o v := by
  simp only [perp, rotateVector_smul]

theorem wm_perp_neg (v : E) : perp o (-v) = -perp o v := by
  rw [perp, perp, show -v = (-1 : ℝ) • v by simp, rotateVector_smul]
  simp

theorem wm_perp_e1 : perp o (e₁ o) = e₂ o := by
  apply toComplex_injective o
  rw [wm_toComplex_perp, wm_toComplex_e1, wm_toComplex_e2, one_mul]

theorem wm_perp_e2 : perp o (e₂ o) = -e₁ o := by
  apply toComplex_injective o
  rw [wm_toComplex_perp, wm_toComplex_e2, toComplex_neg, wm_toComplex_e1, Complex.I_mul_I]

theorem wm_scalar_mul_scalar (a b : ℝ) :
    scalar (E := E) a * scalar b = scalar (a * b) := by
  rw [scalar, scalar, scalar, map_mul]

theorem wm_scalar_mul_pseudo (a : ℝ) :
    scalar (E := E) a * pseudoscalar o = a • pseudoscalar o := by
  rw [scalar, ← Algebra.smul_def]

theorem wm_scalar_mul (a : ℝ) (x : G[E]) :
    scalar (E := E) a * x = a • x := by
  rw [scalar, ← Algebra.smul_def]

theorem wm_mul_scalar (x : G[E]) (a : ℝ) :
    x * scalar (E := E) a = a • x := by
  rw [scalar, ← Algebra.commutes, ← Algebra.smul_def]

theorem wm_pseudo_mul_scalar (a : ℝ) :
    pseudoscalar o * scalar (E := E) a = a • pseudoscalar o := wm_mul_scalar _ a

theorem wm_smul_pseudo_mul_smul (a b : ℝ) :
    (a • pseudoscalar o) * (b • pseudoscalar o) = -(scalar (E := E) (a * b)) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, pseudoscalar_sq, smul_neg, scalar,
    Algebra.algebraMap_eq_smul_one]

theorem wm_scalar_add (a b : ℝ) : scalar (E := E) (a + b) = scalar a + scalar b := by
  rw [scalar, scalar, scalar, map_add]

theorem wm_scalar_sub (a b : ℝ) : scalar (E := E) (a - b) = scalar a - scalar b := by
  rw [scalar, scalar, scalar, map_sub]

theorem wm_geometricComplex_add (z w : ℂ) :
    geometricComplex o (z + w) = geometricComplex o z + geometricComplex o w := by
  simp only [geometricComplex, Complex.add_re, Complex.add_im, add_smul]
  rw [wm_scalar_add]
  abel

theorem wm_geometricComplex_mul (z w : ℂ) :
    geometricComplex o (z * w) = geometricComplex o z * geometricComplex o w := by
  simp only [geometricComplex, Complex.mul_re, Complex.mul_im]
  rw [add_mul, mul_add, mul_add, wm_scalar_mul_scalar, mul_smul_comm, wm_scalar_mul_pseudo, smul_smul,
    smul_mul_assoc, wm_pseudo_mul_scalar, smul_smul, wm_smul_pseudo_mul_smul, wm_scalar_sub, add_smul]
  module

theorem wm_geometricComplex_one : geometricComplex o 1 = 1 := by
  simp only [geometricComplex, Complex.one_re, Complex.one_im, zero_smul, add_zero]
  exact map_one (algebraMap ℝ G[E])

theorem wm_cos_re (φ : ℝ) : (Complex.cos (φ : ℂ)).re = Real.cos φ := by
  rw [← Complex.ofReal_cos, Complex.ofReal_re]

theorem wm_sin_re (φ : ℝ) : (Complex.sin (φ : ℂ)).re = Real.sin φ := by
  rw [← Complex.ofReal_sin, Complex.ofReal_re]

theorem wm_cos_im (φ : ℝ) : (Complex.cos (φ : ℂ)).im = 0 := by
  rw [← Complex.ofReal_cos, Complex.ofReal_im]

theorem wm_sin_im (φ : ℝ) : (Complex.sin (φ : ℂ)).im = 0 := by
  rw [← Complex.ofReal_sin, Complex.ofReal_im]

theorem wm_expI_re (φ : ℝ) : (Complex.exp ((φ : ℂ) * Complex.I)).re = Real.cos φ := by
  rw [Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    wm_cos_re, wm_sin_re, wm_cos_im, wm_sin_im]
  ring

theorem wm_expI_im (φ : ℝ) : (Complex.exp ((φ : ℂ) * Complex.I)).im = Real.sin φ := by
  rw [Complex.exp_mul_I]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, wm_cos_re, wm_sin_re, wm_sin_im, wm_cos_im]
  ring

theorem wm_unit_eq (φ : ℝ) :
    unit o φ = scalar (E := E) (Real.cos φ) + Real.sin φ • pseudoscalar o := by
  rw [unit, geometricComplex, Circle.coe_exp, wm_expI_re, wm_expI_im]


/-! ## (3) [TARGETS] -/

theorem i_anticommutes_vectors (v : E) :
    pseudoscalar o * vec v = -(vec v * pseudoscalar o) := by
  have hv := wm_eq_smul_e1_add_smul_e2 o v
  have h1 : vec v = ⟪e₁ o, v⟫ • vec (e₁ o) + ⟪e₂ o, v⟫ • vec (e₂ o) := by
    conv_lhs => rw [hv]
    rw [wm_vec_add, wm_vec_smul, wm_vec_smul]
  have h2 : vec v * pseudoscalar o =
      ⟪e₁ o, v⟫ • vec (e₂ o) + ⟪e₂ o, v⟫ • (-vec (e₁ o)) := by
    conv_lhs => rw [h1]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, e1_mul_i, e2_mul_i]
  calc pseudoscalar o * vec v
      = ⟪e₁ o, v⟫ • (pseudoscalar o * vec (e₁ o)) +
          ⟪e₂ o, v⟫ • (pseudoscalar o * vec (e₂ o)) := by
        conv_lhs => rw [h1]
        rw [mul_add, mul_smul_comm, mul_smul_comm]
    _ = ⟪e₁ o, v⟫ • (-vec (e₂ o)) + ⟪e₂ o, v⟫ • vec (e₁ o) := by rw [i_mul_e1, i_mul_e2]
    _ = -(vec v * pseudoscalar o) := by
        rw [h2, smul_neg]
        simp only [smul_neg, neg_add, neg_neg]
theorem vector_mul_i_is_vector (v : E) :
    vec v * pseudoscalar o = vec (perp o v) := by
  have hv := wm_eq_smul_e1_add_smul_e2 o v
  have h1 : vec v = ⟪e₁ o, v⟫ • vec (e₁ o) + ⟪e₂ o, v⟫ • vec (e₂ o) := by
    conv_lhs => rw [hv]
    rw [wm_vec_add, wm_vec_smul, wm_vec_smul]
  have h2 : vec v * pseudoscalar o =
      ⟪e₁ o, v⟫ • vec (e₂ o) + ⟪e₂ o, v⟫ • (-vec (e₁ o)) := by
    conv_lhs => rw [h1]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, e1_mul_i, e2_mul_i]
  have hp : perp o v = ⟪e₁ o, v⟫ • e₂ o + ⟪e₂ o, v⟫ • (-e₁ o) := by
    conv_lhs => rw [hv]
    rw [wm_perp_add, wm_perp_smul, wm_perp_smul, wm_perp_e1, wm_perp_e2]
  rw [h2, hp, wm_vec_add, wm_vec_smul, wm_vec_smul, wm_vec_neg]
theorem unit_vector_pseudoscalar {u : E} (hu : ‖u‖ = 1) :
    vec u * vec (perp o u) = pseudoscalar o := by
  rw [← vector_mul_i_is_vector, ← mul_assoc, vector_square]
  have h : ⟪u, u⟫ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hu]
    norm_num
  rw [h, scalar]
  simp
theorem rotateVector_eq_complexMulVector (v : E) (φ : ℝ) :
    rotateVector o v φ = complexMulVector o (Circle.exp φ) v := rfl

theorem rotateVector_eq_cos_add_perp (v : E) (φ : ℝ) :
    rotateVector o v φ = Real.cos φ • v + Real.sin φ • perp o v := by
  apply toComplex_injective o
  rw [toComplex_rotateVector, toComplex_add, toComplex_smul, toComplex_smul, wm_toComplex_perp,
    Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring
theorem rotateVector_clifford (v : E) (φ : ℝ) :
    vec (rotateVector o v φ) = vec v * unit o φ := by
  rw [rotateVector_eq_cos_add_perp, wm_vec_add, wm_vec_smul, wm_vec_smul, ← vector_mul_i_is_vector,
    wm_unit_eq, mul_add, mul_smul_comm, wm_mul_scalar]
theorem rotateVector_left_clifford (v : E) (φ : ℝ) :
    vec (rotateVector o v φ) = unit o (-φ) * vec v := by
  rw [rotateVector_eq_cos_add_perp, wm_vec_add, wm_vec_smul, wm_vec_smul, ← vector_mul_i_is_vector,
    wm_unit_eq, show Real.cos (-φ) = Real.cos φ from Real.cos_neg φ,
    show Real.sin (-φ) = -Real.sin φ from Real.sin_neg φ, add_mul, wm_scalar_mul, smul_mul_assoc,
    i_anticommutes_vectors, smul_neg, neg_smul, neg_neg]
/-- Equation (4), the half-angle rotation formula. -/
theorem rotateVector_half_angle (v : E) (φ : ℝ) :
    vec (rotateVector o v φ) = unit o (-φ / 2) * vec v * unit o (φ / 2) := by
  have hφ : -φ / 2 = -(φ / 2) := by ring
  have hangle : rotateVector o v φ = rotateVector o (rotateVector o v (φ / 2)) (φ / 2) := by
    conv_lhs => rw [show φ = φ / 2 + φ / 2 by ring]
    rw [rotateVector_add_angle]
  rw [hφ, hangle, rotateVector_clifford, rotateVector_left_clifford]

/-! ### `⋄4` Points, translators and isometries -/

theorem translation_isIsometry (v : E) : Isometry (translation v) := by
  rw [isometry_iff_dist_eq]
  intro X Y
  simp [translation, dist_eq_norm]
theorem translation_injective (v : E) : Injective (translation v) :=
  (translation_isIsometry v).injective
theorem isometry_injective {f : E → E} (hf : Isometry f) : Injective f := hf.injective
theorem translation_sub (v : E) (X Y : E) :
    translation v X - translation v Y = X - Y := by
  simp [translation]

/-! ### `⋄5` Rotations and symmetries -/

theorem rotation_apply (P X : E) (φ : ℝ) :
    rotation o P φ X = P + rotateVector o (X - P) φ := rfl
theorem rotation_fixed_center (P : E) (φ : ℝ) : rotation o P φ P = P := by
  simp [rotation, rotateVector, toComplex]
theorem rotation_zero (P : E) : rotation o P 0 = id := by
  funext X
  simp [rotation]
theorem rotation_unique_fixed_point {P X : E} {φ : ℝ}
    (hφ : (Circle.exp φ : ℂ) ≠ 1) (hX : rotation o P φ X = X) : X = P := by
  have hd : rotateVector o (X - P) φ = X - P := by
    calc
      _ = P + rotateVector o (X - P) φ - P := by abel
      _ = rotation o P φ X - P := by rw [rotation]
      _ = X - P := by rw [hX]
  have hc := congrArg (toComplex o) hd
  rw [toComplex_rotateVector] at hc
  have hz : toComplex o (X - P) = 0 := by
    have hfactor : toComplex o (X - P) * ((Circle.exp φ : ℂ) - 1) = 0 := by
      calc
        _ = toComplex o (X - P) * Circle.exp φ - toComplex o (X - P) := by ring
        _ = 0 := by rw [hc, sub_self]
    exact (mul_eq_zero.mp hfactor).resolve_right (sub_ne_zero.mpr hφ)
  exact sub_eq_zero.mp ((toComplex_eq_zero o _).mp hz)
theorem rotation_isIsometry (P : E) (φ : ℝ) : Isometry (rotation o P φ) := by
  rw [isometry_iff_dist_eq]
  intro X Y
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖rotation o P φ X - rotation o P φ Y‖ =
        ‖rotateVector o (X - P) φ - rotateVector o (Y - P) φ‖ := by
      congr 1
      simp only [rotation]
      abel
    _ = ‖rotateVector o ((X - P) - (Y - P)) φ‖ :=
      (congrArg norm (rotateVector_sub o (X - P) (Y - P) φ)).symm
    _ = ‖rotateVector o (X - Y) φ‖ := by
      rw [show X - P - (Y - P) = X - Y by abel]
    _ = ‖X - Y‖ := rotateVector_norm o _ _
theorem rotation_sub (P : E) (φ : ℝ) (X Y : E) :
    rotation o P φ X - rotation o P φ Y = rotateVector o (X - Y) φ := by
  calc
    P + rotateVector o (X - P) φ - (P + rotateVector o (Y - P) φ) =
        rotateVector o (X - P) φ - rotateVector o (Y - P) φ := by abel
    _ = rotateVector o ((X - P) - (Y - P)) φ :=
      (rotateVector_sub o (X - P) (Y - P) φ).symm
    _ = rotateVector o (X - Y) φ := by
      rw [show X - P - (Y - P) = X - Y by abel]

/-- Equation (5): reflection is conjugation by a direction vector. -/
theorem symmetry_clifford (ℓ : Line E) (X : E) :
    Line.symmetry ℓ X = ℓ.base + ofComplex o (toComplex o
      (parallelComponent ℓ.direction (X - ℓ.base) - perpComponent ℓ.direction (X - ℓ.base))) := by
  rw [ofComplex_toComplex]
  rfl
theorem g3_vec_add (v w : E) : vec (v + w) = vec v + vec w := by
  simp [vec]

theorem g3_vec_sub (v w : E) : vec (v - w) = vec v - vec w := by
  simp [vec]

theorem g3_vec_smul (r : ℝ) (v : E) : vec (r • v) = r • vec v := by
  simp [vec]

theorem g3_scalar_mul_vec (r : ℝ) (v : E) : scalar r * vec v = r • vec v := by
  simp only [scalar]
  exact (Algebra.smul_def r (vec v)).symm

theorem g3_vec_mul_scalar (r : ℝ) (v : E) : vec v * scalar r = r • vec v := by
  simp only [scalar]
  rw [← Algebra.commutes r (vec v)]
  exact (Algebra.smul_def r (vec v)).symm

/-- The bilinear polar form of the plane form is twice the inner product. -/
theorem g3_polar_planeQuadraticForm (u v : E) :
    QuadraticMap.polar (planeQuadraticForm (E := E)) u v = 2 * ⟪u, v⟫ := by
  simp only [QuadraticMap.polar, planeQuadraticForm_apply, inner_add_left, inner_add_right,
    real_inner_comm v u]
  ring

/-! ### Helper lemmas: the parallel and perpendicular components -/

theorem g3_parallelComponent_of_smul {u : E} (hu : u ≠ 0) (r : ℝ) :
    parallelComponent u (r • u) = r • u := by
  have huu : (⟪u, u⟫ : ℝ) ≠ 0 := inner_self_ne_zero.mpr hu
  simp only [parallelComponent, inner_smul_left, starRingEnd_apply, star_trivial]
  rw [mul_div_cancel_right₀ r huu]

theorem g3_parallelComponent_self {u : E} (hu : u ≠ 0) : parallelComponent u u = u := by
  simpa using g3_parallelComponent_of_smul hu 1

theorem g3_perpComponent_of_smul {u : E} (hu : u ≠ 0) (r : ℝ) :
    perpComponent u (r • u) = 0 := by
  simp only [perpComponent, g3_parallelComponent_of_smul hu, sub_self]

theorem g3_parallelComponent_of_perp {u v : E} (h : ⟪v, u⟫ = 0) :
    parallelComponent u v = 0 := by
  simp only [parallelComponent, h, zero_div, zero_smul]

theorem g3_perpComponent_of_perp {u v : E} (h : ⟪v, u⟫ = 0) :
    perpComponent u v = v := by
  simp only [perpComponent, g3_parallelComponent_of_perp h, sub_zero]

/-! ### Helper lemmas: linearity and involutivity of `reflectVector` -/

theorem g3_reflectVector_sub (u v w : E) :
    Line.reflectVector u (v - w) = Line.reflectVector u v - Line.reflectVector u w := by
  simp only [Line.reflectVector, parallelComponent_sub, perpComponent_sub]
  abel

theorem g3_reflectVector_smul (u : E) (r : ℝ) (v : E) :
    Line.reflectVector u (r • v) = r • Line.reflectVector u v := by
  simp only [Line.reflectVector, parallelComponent_smul, perpComponent_smul, smul_sub]

theorem g3_reflectVector_self {u : E} (hu : u ≠ 0) : Line.reflectVector u u = u := by
  have hq : perpComponent u u = 0 := by simpa using g3_perpComponent_of_smul hu 1
  simp only [Line.reflectVector, g3_parallelComponent_self hu, hq, sub_zero]

theorem g3_reflectVector_involutive {u : E} (hu : u ≠ 0) (v : E) :
    Line.reflectVector u (Line.reflectVector u v) = v := by
  have hq : ⟪perpComponent u v, u⟫ = 0 := perpComponent_inner u v hu
  have hpq : parallelComponent u (perpComponent u v) = 0 := g3_parallelComponent_of_perp hq
  have hqq : perpComponent u (perpComponent u v) = perpComponent u v :=
    g3_perpComponent_of_perp hq
  have hpp : parallelComponent u (parallelComponent u v) = parallelComponent u v := by
    rw [parallelComponent]
    exact g3_parallelComponent_of_smul hu _
  have hqp : perpComponent u (parallelComponent u v) = 0 := g3_perpComponent_of_smul hu _
  simp only [Line.reflectVector, parallelComponent_sub, perpComponent_sub, hpp, hpq, hqp, hqq,
    sub_zero, zero_sub, sub_neg_eq_add]
  exact parallelComponent_add_perpComponent u v

theorem g3_reflectVector_smul_direction {d v : E} (hd : d ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    Line.reflectVector (r • d) v = Line.reflectVector d v := by
  have hdd : (⟪d, d⟫ : ℝ) ≠ 0 := inner_self_ne_zero.mpr hd
  have hp : parallelComponent (r • d) v = parallelComponent d v := by
    simp only [parallelComponent, inner_smul_right, inner_smul_left, starRingEnd_apply,
      star_trivial, smul_smul]
    congr 1
    field_simp
  have hq : perpComponent (r • d) v = perpComponent d v := by
    simp only [perpComponent, hp]
  simp only [Line.reflectVector, hp, hq]

/-! ### Helper lemma: `reflectVector` preserves norms -/

theorem g3_reflectVector_norm (u v : E) : ‖Line.reflectVector u v‖ = ‖v‖ := by
  rcases eq_or_ne u 0 with rfl | hu
  · have h : Line.reflectVector (0 : E) v = -v := by
      simp only [Line.reflectVector, parallelComponent, perpComponent, inner_zero_right,
        zero_div, zero_smul, sub_zero]
      abel
    rw [h, norm_neg]
  · have hq : ⟪perpComponent u v, u⟫ = 0 := perpComponent_inner u v hu
    have hpq : ⟪parallelComponent u v, perpComponent u v⟫ = 0 := by
      have h0 : ⟪u, perpComponent u v⟫ = 0 := by
        rw [real_inner_comm]
        exact hq
      simp only [parallelComponent, inner_smul_left, starRingEnd_apply, star_trivial, h0,
        mul_zero]
    have hsum : parallelComponent u v + perpComponent u v = v :=
      parallelComponent_add_perpComponent u v
    have h1 : ‖Line.reflectVector u v‖ ^ 2 =
        ‖parallelComponent u v‖ ^ 2 + ‖perpComponent u v‖ ^ 2 := by
      rw [Line.reflectVector, norm_sub_sq_real, hpq]
      ring
    have h2 : ‖v‖ ^ 2 = ‖parallelComponent u v‖ ^ 2 + ‖perpComponent u v‖ ^ 2 := by
      conv_lhs => rw [← hsum]
      rw [norm_add_sq_real, hpq]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [h1, h2])

/-! ### Equation (5) in the Clifford algebra -/

theorem g3_vec_reflectVector {u v : E} (hu : u ≠ 0) :
    vec (Line.reflectVector u v) = vec u * vec v * vectorInverse u := by
  have huu : (⟪u, u⟫ : ℝ) ≠ 0 := inner_self_ne_zero.mpr hu
  have hrefl : Line.reflectVector u v = (2 * (⟪v, u⟫ / ⟪u, u⟫)) • u - v := by
    simp only [Line.reflectVector, parallelComponent, perpComponent]
    module
  rw [hrefl]
  have h1 : vec u * vec v * vectorInverse u = (‖u‖ ^ 2)⁻¹ • (vec u * vec v * vec u) := by
    rw [vectorInverse, mul_smul_comm]
  rw [h1]
  have h2 : vec u * vec v * vec u =
      vec (QuadraticMap.polar (planeQuadraticForm (E := E)) u v • u -
        (planeQuadraticForm (E := E)) u • v) := by
    simpa only [vec] using
      (CliffordAlgebra.ι_mul_ι_mul_ι (Q := planeQuadraticForm (E := E)) u v)
  rw [h2, g3_polar_planeQuadraticForm u v]
  have hc1 : (‖u‖ ^ 2)⁻¹ * (2 * ⟪u, v⟫) = 2 * (⟪v, u⟫ / ⟪u, u⟫) := by
    rw [real_inner_self_eq_norm_sq u, real_inner_comm u v]
    field_simp
  have hc2 : (‖u‖ ^ 2)⁻¹ * ⟪u, u⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq u]
    field_simp
  simp only [vec, planeQuadraticForm_apply, map_smul, map_sub, smul_sub, smul_smul, hc1, hc2,
    one_smul]

theorem symmetry_clifford_product (ℓ : Line E) (X : E) :
    vec (Line.symmetry ℓ X - ℓ.base) =
      vec ℓ.direction * vec (X - ℓ.base) * vectorInverse ℓ.direction := by
  have hL : Line.symmetry ℓ X - ℓ.base = Line.reflectVector ℓ.direction (X - ℓ.base) := by
    simp only [Line.symmetry]
    abel
  rw [hL]
  exact g3_vec_reflectVector ℓ.direction_ne_zero
/-- Equation (6), decomposition into parallel and perpendicular components. -/
theorem symmetry_decomposition (ℓ : Line E) (X : E) :
    Line.symmetry ℓ X = X - 2 • perpComponent ℓ.direction (X - ℓ.base) := by
  simp only [Line.symmetry, Line.reflectVector, perpComponent]
  abel
theorem symmetry_independent_of_base {P : E} {ℓ : Line E} (hP : ℓ.mem P) (X : E) :
    P + Line.reflectVector ℓ.direction (X - P) = Line.symmetry ℓ X := by
  obtain ⟨t, rfl⟩ := hP
  simp only [Line.symmetry]
  have h1 : X - (ℓ.base + t • ℓ.direction) = (X - ℓ.base) - t • ℓ.direction := by abel
  rw [h1, g3_reflectVector_sub, g3_reflectVector_smul,
    g3_reflectVector_self ℓ.direction_ne_zero]
  abel
theorem symmetry_independent_of_direction {ℓ : Line E} {u : E}
    (hu : u ≠ 0) (h : Parallel ℓ.direction u) (X : E) :
    Line.symmetry ⟨ℓ.base, u, hu⟩ X = Line.symmetry ℓ X := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := by
    rintro rfl
    simp at hu
  simp only [Line.symmetry]
  rw [g3_reflectVector_smul_direction ℓ.direction_ne_zero hr]
theorem symmetry_isIsometry (ℓ : Line E) : Isometry (Line.symmetry ℓ) := by
  rw [isometry_iff_dist_eq]
  intro X Y
  have hsub : Line.symmetry ℓ X - Line.symmetry ℓ Y = Line.reflectVector ℓ.direction (X - Y) := by
    simp only [Line.symmetry, Line.reflectVector, parallelComponent_sub, perpComponent_sub]
    abel
  rw [dist_eq_norm, dist_eq_norm, hsub, g3_reflectVector_norm]
theorem symmetry_sub (ℓ : Line E) (X Y : E) :
    Line.symmetry ℓ X - Line.symmetry ℓ Y =
      Line.reflectVector ℓ.direction (X - Y) := by
  simp only [Line.symmetry, Line.reflectVector, parallelComponent_sub, perpComponent_sub]
  abel
theorem symmetry_fixed_iff (ℓ : Line E) (X : E) :
    Line.symmetry ℓ X = X ↔ ℓ.mem X := by
  rw [symmetry_decomposition]
  constructor
  · intro h
    have hp : perpComponent ℓ.direction (X - ℓ.base) = 0 := by
      have : (2 : ℕ) • perpComponent ℓ.direction (X - ℓ.base) = 0 := by
        rw [← neg_eq_zero]
        calc
          -((2 : ℕ) • perpComponent ℓ.direction (X - ℓ.base)) =
              X - (2 : ℕ) • perpComponent ℓ.direction (X - ℓ.base) - X := by abel
          _ = 0 := (congrArg (· - X) h).trans (sub_self X)
      have hr : (2 : ℝ) • perpComponent ℓ.direction (X - ℓ.base) = 0 := by
        rw [two_smul ℝ]
        simpa only [two_nsmul] using this
      exact (smul_eq_zero.mp hr).resolve_left (by norm_num)
    obtain ⟨r, hr⟩ := (perpComponent_eq_zero_iff ℓ.direction_ne_zero).mp hp
    exact ⟨r, by rw [← hr]; simp⟩
  · rintro ⟨r, rfl⟩
    have hp : perpComponent ℓ.direction (ℓ.base + r • ℓ.direction - ℓ.base) = 0 :=
      (perpComponent_eq_zero_iff ℓ.direction_ne_zero).mpr ⟨r, by abel⟩
    rw [hp, smul_zero, sub_zero]
theorem glide_isIsometry (ℓ : Line E) (w : E) : Isometry (Line.glide ℓ w) := by
  exact (translation_isIsometry w).comp (symmetry_isIsometry ℓ)
theorem glide_no_fixed_point {ℓ : Line E} {w : E}
    (hw : w ≠ 0) (hparallel : Parallel ℓ.direction w) (X : E) :
    Line.glide ℓ w X ≠ X := by
  obtain ⟨r, rfl⟩ := hparallel
  have hr : r ≠ 0 := by
    rintro rfl
    simp at hw
  intro h
  simp only [Line.glide] at h
  have hd : ℓ.direction ≠ 0 := ℓ.direction_ne_zero
  have hdd : (⟪ℓ.direction, ℓ.direction⟫ : ℝ) ≠ 0 := inner_self_ne_zero.mpr hd
  have hbase : Line.symmetry ℓ X = X - 2 • perpComponent ℓ.direction (X - ℓ.base) :=
    symmetry_decomposition ℓ X
  have hrepr : r • ℓ.direction = (2 : ℝ) • perpComponent ℓ.direction (X - ℓ.base) := by
    have h3 : (X - 2 • perpComponent ℓ.direction (X - ℓ.base)) + r • ℓ.direction = X := by
      rw [← hbase]
      exact h
    calc r • ℓ.direction
        = ((X - 2 • perpComponent ℓ.direction (X - ℓ.base)) + r • ℓ.direction) -
            (X - 2 • perpComponent ℓ.direction (X - ℓ.base)) := by abel
      _ = X - (X - 2 • perpComponent ℓ.direction (X - ℓ.base)) := by rw [h3]
      _ = (2 : ℝ) • perpComponent ℓ.direction (X - ℓ.base) := by
            rw [two_nsmul, two_smul]
            abel
  have hinner : ⟪r • ℓ.direction, ℓ.direction⟫ =
      ⟪(2 : ℝ) • perpComponent ℓ.direction (X - ℓ.base), ℓ.direction⟫ := by
    rw [hrepr]
  have h2 : ⟪(2 : ℝ) • perpComponent ℓ.direction (X - ℓ.base), ℓ.direction⟫ = 0 := by
    rw [inner_smul_left, starRingEnd_apply, star_trivial,
      perpComponent_inner ℓ.direction (X - ℓ.base) hd, mul_zero]
  rw [h2, inner_smul_left, starRingEnd_apply, star_trivial] at hinner
  exact hr ((mul_eq_zero.mp hinner).resolve_right hdd)

/-! ## 3. Composition of translations, rotations and symmetries -/

@[simp] theorem unit_neg (φ : ℝ) : unit o (-φ) = geometricComplex o (Circle.exp φ)⁻¹ := by
  rw [unit, Circle.exp_neg, Circle.coe_inv]
theorem unit_inverse (φ : ℝ) : unit o φ * unit o (-φ) = 1 := by
  have hinv : (Circle.exp φ : ℂ) * ((Circle.exp φ : Circle) : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (Circle.coe_ne_zero (Circle.exp φ))
  rw [unit_neg, unit]
  rw [← wm_geometricComplex_mul, hinv, wm_geometricComplex_one]
theorem unit_add (φ ψ : ℝ) : unit o φ * unit o ψ = unit o (φ + ψ) := by
  rw [unit, unit, unit, ← wm_geometricComplex_mul]
  congr 1
  simp only [Circle.coe_exp]
  rw [show ((φ + ψ : ℝ) : ℂ) * Complex.I = ↑φ * Complex.I + ↑ψ * Complex.I by
    push_cast; ring, Complex.exp_add]

/-! ### `⋄6` Translation–rotation compositions, Equations (7) and (8) -/

/-- The center in Equation (7), written exactly with `v'(1-uφ)⁻¹`. -/
def translationRotationCenter (P v' : E) (φ : ℝ) : E :=
  P + ofComplex o (toComplex o v' / (1 - Circle.exp φ : ℂ))

@[simp] theorem toComplex_translationRotationCenter (P v' : E) (φ : ℝ) :
    toComplex o (translationRotationCenter o P v' φ) =
      toComplex o P + toComplex o v' / (1 - Circle.exp φ : ℂ) := by
  simp [translationRotationCenter]

theorem translation_rotation_exact {P : E} {v' : E} {φ : ℝ}
    (hφ : (1 - Circle.exp φ : ℂ) ≠ 0) :
    translation v' ∘ rotation o P φ = rotation o (translationRotationCenter o P v' φ) φ := by
  funext X
  apply toComplex_injective o
  simp only [Function.comp_apply]
  rw [toComplex_translation, toComplex_rotation, toComplex_rotation, toComplex_translationRotationCenter]
  field_simp [hφ]
  ring

/-- The fixed point in the first part of `⋄6`. -/
theorem translation_rotation_fixedPoint {P X : E} {v' : E} {φ : ℝ}
    (hφ : (1 - Circle.exp φ : ℂ) ≠ 0) :
    translation v' (rotation o P φ X) = X ↔ X = translationRotationCenter o P v' φ := by
  have hexp : (Circle.exp φ : ℂ) ≠ 1 := by
    intro he
    apply hφ
    simp [he]
  constructor
  · intro hX
    apply rotation_unique_fixed_point o hexp
    rw [← congrFun (translation_rotation_exact o hφ) X]
    exact hX
  · rintro rfl
    exact (congrFun (translation_rotation_exact o hφ) _).trans (rotation_fixed_center o _ _)

/-- Equation (8). -/
def rotationTranslationCenter (P' v : E) (φ' : ℝ) : E :=
  P' + ofComplex o (toComplex o v * Circle.exp φ' / (1 - Circle.exp φ' : ℂ))

@[simp] theorem toComplex_rotationTranslationCenter (P' v : E) (φ' : ℝ) :
    toComplex o (rotationTranslationCenter o P' v φ') =
      toComplex o P' + toComplex o v * Circle.exp φ' / (1 - Circle.exp φ' : ℂ) := by
  simp [rotationTranslationCenter]

theorem rotation_translation {P' : E} {v : E} {φ' : ℝ}
    (hφ : (1 - Circle.exp φ' : ℂ) ≠ 0) :
    rotation o P' φ' ∘ translation v = rotation o (rotationTranslationCenter o P' v φ') φ' := by
  funext X
  apply toComplex_injective o
  simp only [Function.comp_apply]
  rw [toComplex_rotation, toComplex_rotation, toComplex_rotationTranslationCenter, toComplex_translation]
  field_simp [hφ]
  ring

theorem rotation_translation_fixedPoint {P' X : E} {v : E} {φ' : ℝ}
    (hφ : (1 - Circle.exp φ' : ℂ) ≠ 0) :
    rotation o P' φ' (translation v X) = X ↔ X = rotationTranslationCenter o P' v φ' := by
  have hexp : (Circle.exp φ' : ℂ) ≠ 1 := by
    intro he
    apply hφ
    simp [he]
  constructor
  · intro hX
    apply rotation_unique_fixed_point o hexp
    rw [← congrFun (rotation_translation o hφ) X]
    exact hX
  · rintro rfl
    exact (congrFun (rotation_translation o hφ) _).trans (rotation_fixed_center o _ _)

/-- Remark 1. -/
theorem one_sub_unit_eq (φ : ℝ) :
    (1 - Circle.exp φ : ℂ) =
      (2 * Real.sin (φ / 2) : ℂ) * Circle.exp (φ / 2 - Real.pi / 2) := by
  apply Complex.ext
  all_goals
    simp only [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    rw [show φ = φ / 2 + φ / 2 by ring]
    simp only [Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub]
    norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two] <;>
      nlinarith [Real.sin_sq_add_cos_sq (φ / 2)]

theorem one_sub_unit_inv (φ : ℝ) :
    (1 - Circle.exp φ : ℂ)⁻¹ =
      Circle.exp (Real.pi / 2 - φ / 2) / (2 * Real.sin (φ / 2) : ℂ) := by
  by_cases hs : Real.sin (φ / 2) = 0
  · rw [one_sub_unit_eq, hs]
    norm_num
  · symm
    apply eq_inv_of_mul_eq_one_right
    rw [one_sub_unit_eq]
    calc
      _ = (Circle.exp (φ / 2 - Real.pi / 2) : ℂ) *
          Circle.exp (Real.pi / 2 - φ / 2) := by
        field_simp [hs]
        ring_nf
        exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (by
          rw [show φ * (1 / 2) = φ / 2 by ring]
          exact hs))
      _ = 1 := by
        rw [← Circle.coe_mul, ← Circle.exp_add]
        ring_nf
        simp

/-- Remark 2. -/
theorem unit_mul_one_sub_unit_inv (φ : ℝ) :
    (Circle.exp φ : ℂ) * (1 - Circle.exp φ : ℂ)⁻¹ =
      Circle.exp (Real.pi / 2 + φ / 2) / (2 * Real.sin (φ / 2) : ℂ) := by
  by_cases hs : Real.sin (φ / 2) = 0
  · rw [one_sub_unit_eq, hs]
    norm_num
  · rw [one_sub_unit_inv]
    field_simp [hs]
    rw [← Circle.coe_mul, ← Circle.exp_add]
    congr 1 <;> ring_nf

@[simp] theorem toComplex_rotationFixedPoint (P Q : E) (φ ψ : ℝ) :
    toComplex o (rotationFixedPoint o P Q φ ψ) = toComplex o P + toComplex o (Q - P) *
      ((1 - Circle.exp ψ : ℂ) / (1 - (Circle.exp φ : ℂ) * Circle.exp ψ)) := by
  simp [rotationFixedPoint]

/-! ### `⋄7` Composition of two rotations -/

theorem rotation_rotation_formula (P P' X : E) (φ φ' : ℝ) :
    rotation o P' φ' (rotation o P φ X) =
      P + ofComplex o (toComplex o (P' - P) * (1 - Circle.exp φ')) +
        rotateVector o (X - P) (φ + φ') := by
  apply toComplex_injective o
  simp only [toComplex_add, toComplex_rotation, toComplex_ofComplex, toComplex_rotateVector,
    toComplex_sub, Circle.exp_add, Circle.coe_mul]
  ring

/-- The translation case of `⋄7`. -/
theorem rotation_rotation_translation {P P' : E} {φ φ' : ℝ}
    (h : (Circle.exp φ : ℂ) * Circle.exp φ' = 1) :
    rotation o P' φ' ∘ rotation o P φ =
      translation (ofComplex o (toComplex o (P' - P) * (1 - Circle.exp φ'))) := by
  funext X
  apply toComplex_injective o
  simp only [Function.comp_apply]
  rw [toComplex_rotation, toComplex_translation, toComplex_rotation, toComplex_ofComplex]
  generalize hu : (Circle.exp φ : ℂ) = u
  generalize hv : (Circle.exp φ' : ℂ) = v
  have h1 : u * (Circle.exp φ' : ℂ) = 1 := hu.symm ▸ h
  have huv : u * v = 1 := hv.symm ▸ h1
  ring_nf at huv ⊢
  rw [huv, toComplex_sub]
  ring

/-- The rotation case of `⋄7`; the full fixed-point theorem is restated below as
Theorem 3 in the notation of Section 4. -/
theorem rotation_rotation_rotation {P P' : E} {φ φ' : ℝ}
    (h : (1 - (Circle.exp φ : ℂ) * Circle.exp φ') ≠ 0) :
    rotation o P' φ' ∘ rotation o P φ =
      rotation o (rotationFixedPoint o P P' φ φ') (φ + φ') := by
  funext X
  apply toComplex_injective o
  simp only [Function.comp_apply]
  rw [toComplex_rotation, toComplex_rotation, toComplex_rotation, toComplex_rotationFixedPoint,
    toComplex_sub, Circle.exp_add, Circle.coe_mul]
  generalize hA : toComplex o P = a at *
  generalize hB : toComplex o P' = b at *
  generalize hX : toComplex o X = x at *
  generalize hu : (Circle.exp φ : ℂ) = u at *
  generalize hv : (Circle.exp φ' : ℂ) = v at *
  change b + (a + (x - a) * u - b) * v =
    a + (b - a) * ((1 - v) / (1 - u * v)) +
      (x - (a + (b - a) * ((1 - v) / (1 - u * v)))) * (u * v)
  field_simp [h]
  ring

theorem rotation_rotation_unique_fixedPoint {P P' X : E} {φ φ' : ℝ}
    (h : (1 - (Circle.exp φ : ℂ) * Circle.exp φ') ≠ 0) :
    rotation o P' φ' (rotation o P φ X) = X ↔
      X = rotationFixedPoint o P P' φ φ' := by
  have hexp : (Circle.exp (φ + φ') : ℂ) ≠ 1 := by
    intro he
    apply h
    change 1 - ((Circle.exp φ * Circle.exp φ' : Circle) : ℂ) = 0
    rw [← Circle.exp_add, he]
    simp
  have hcomp := congrFun (rotation_rotation_rotation (P := P) (P' := P') o h) X
  constructor
  · intro hX
    have hfixed : rotation o (rotationFixedPoint o P P' φ φ') (φ + φ') X = X :=
      hcomp.symm.trans hX
    exact rotation_unique_fixed_point o hexp hfixed
  · intro hX
    subst X
    exact hcomp.trans (rotation_fixed_center o _ _)


/-! ### `⋄8` Translation–symmetry compositions, Equations (9) and (10) -/

theorem m4_perp_idem {u : E} (hu : u ≠ 0) (w : E) :
    perpComponent u (perpComponent u w) = perpComponent u w := by
  have h : parallelComponent u (perpComponent u w) = 0 := by
    simp [parallelComponent, perpComponent_inner u w hu]
  rw [show perpComponent u (perpComponent u w) =
      perpComponent u w - parallelComponent u (perpComponent u w) from rfl, h, sub_zero]

omit [Fact (Module.finrank ℝ E = 2)] in
theorem m4_parallel_self {u : E} (hu : u ≠ 0) : parallelComponent u u = u := by
  simp only [parallelComponent]
  rw [div_self (by simpa [real_inner_self_eq_norm_sq, pow_two] using
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hu))), one_smul]

theorem m4_parallel_idem {u : E} (hu : u ≠ 0) (w : E) :
    parallelComponent u (parallelComponent u w) = parallelComponent u w := by
  rw [show parallelComponent u (parallelComponent u w)
      = parallelComponent u ((⟪w, u⟫ / ⟪u, u⟫) • u) from rfl,
    parallelComponent_smul, m4_parallel_self hu]
  rfl

omit [Fact (Module.finrank ℝ E = 2)] in
theorem m4_reflect_eq (u w : E) :
    Line.reflectVector u w = w - (2 : ℝ) • perpComponent u w := by
  simp only [Line.reflectVector, perpComponent, two_smul ℝ]
  abel

/-- On the `(-1)`-eigenspace of the reflection, translating the argument. -/
theorem m4_reflect_sub_eigen (u s w : E) (hs : perpComponent u s = s) :
    Line.reflectVector u (w - s) = Line.reflectVector u w + s := by
  rw [m4_reflect_eq, m4_reflect_eq, perpComponent_sub, hs]
  module

theorem m4_reflect_add_eigen (u s w : E) (hs : perpComponent u s = s) :
    Line.reflectVector u (w + s) = Line.reflectVector u w - s := by
  rw [m4_reflect_eq, m4_reflect_eq, perpComponent_add, hs]
  module

/-- On the `(+1)`-eigenspace of the reflection, translating the argument. -/
theorem m4_reflect_add_par (u p w : E) (hp : perpComponent u p = 0) :
    Line.reflectVector u (w + p) = Line.reflectVector u w + p := by
  rw [m4_reflect_eq, m4_reflect_eq, perpComponent_add, hp]
  module

omit [Fact (Module.finrank ℝ E = 2)] in
theorem m4_reflect_eq_symmetry (ℓ : Line E) (X : E) :
    Line.symmetry ℓ X = X - (2 : ℝ) • perpComponent ℓ.direction (X - ℓ.base) := by
  rw [Line.symmetry, m4_reflect_eq]
  abel

omit [Fact (Module.finrank ℝ E = 2)] in
theorem m4_reflect_self {u : E} (hu : u ≠ 0) : Line.reflectVector u u = u := by
  rw [show Line.reflectVector u u = parallelComponent u u - perpComponent u u from rfl,
    m4_parallel_self hu,
    show perpComponent u u = u - parallelComponent u u from rfl, m4_parallel_self hu, sub_self,
    sub_zero]

/-- Equation (9). -/
theorem translation_symmetry (ℓ : Line E) (v' : E) :
    let vℓ := parallelComponent ℓ.direction v'
    let vPerp := perpComponent ℓ.direction v'
    translation v' ∘ Line.symmetry ℓ =
      Line.glide (ℓ.translate ((1 / 2 : ℝ) • vPerp)) vℓ := by
  intro vℓ vPerp
  have hu : ℓ.direction ≠ 0 := ℓ.direction_ne_zero
  have hq : perpComponent ℓ.direction vPerp = vPerp := m4_perp_idem hu v'
  have hsplit : vℓ + vPerp = v' := parallelComponent_add_perpComponent _ _
  have hs : perpComponent ℓ.direction ((1 / 2 : ℝ) • vPerp) = (1 / 2 : ℝ) • vPerp := by
    rw [perpComponent_smul, hq]
  have h2 : (1 / 2 : ℝ) • vPerp + (1 / 2 : ℝ) • vPerp = vPerp := by
    rw [← add_smul]; norm_num
  funext X
  simp only [Function.comp_apply, Line.glide, Line.translate, Line.symmetry, translation]
  rw [show X - (ℓ.base + (1 / 2 : ℝ) • vPerp) = (X - ℓ.base) - (1 / 2 : ℝ) • vPerp by abel]
  rw [m4_reflect_sub_eigen ℓ.direction _ _ hs]
  rw [← hsplit]
  conv_lhs => rw [← h2]
  module

theorem translation_perp_symmetry (ℓ : Line E) {v : E}
    (hv : Orthogonal ℓ.direction v) :
    translation v ∘ Line.symmetry ℓ =
      Line.symmetry (ℓ.translate ((1 / 2 : ℝ) • v)) := by
  have hpar : parallelComponent ℓ.direction v = 0 := by
    simp only [Orthogonal] at hv
    simp only [parallelComponent]
    rw [real_inner_comm, hv]
    simp
  have hperp : perpComponent ℓ.direction v = v := by
    rw [show perpComponent ℓ.direction v = v - parallelComponent ℓ.direction v from rfl, hpar,
      sub_zero]
  have h := translation_symmetry ℓ v
  simp only [hpar, hperp] at h
  rw [h]
  funext X
  simp [Line.glide]

theorem translation_symmetry_is_reflection_iff (ℓ : Line E) (v' : E) :
    (∃ ℓ' : Line E, translation v' ∘ Line.symmetry ℓ = Line.symmetry ℓ') ↔
      Orthogonal ℓ.direction v' := by
  constructor
  · rintro ⟨ℓ', hℓ'⟩
    have hb' : Line.symmetry ℓ' ℓ'.base = ℓ'.base := by
      simp [Line.symmetry, Line.reflectVector, parallelComponent, perpComponent]
    have hX : Line.symmetry ℓ ℓ'.base + v' = ℓ'.base := by
      have h := congrFun hℓ' ℓ'.base
      simp only [Function.comp_apply, translation] at h
      rw [hb'] at h
      exact h
    have hv : v' - (2 : ℝ) • perpComponent ℓ.direction (ℓ'.base - ℓ.base) = 0 := by
      have h1 : Line.symmetry ℓ ℓ'.base + v' - ℓ'.base = 0 := by rw [hX, sub_self]
      rw [m4_reflect_eq_symmetry ℓ ℓ'.base] at h1
      rw [← h1]
      abel
    have hP : ⟪ℓ.direction, perpComponent ℓ.direction (ℓ'.base - ℓ.base)⟫ = 0 := by
      rw [real_inner_comm]
      exact perpComponent_inner _ _ ℓ.direction_ne_zero
    show ⟪ℓ.direction, v'⟫ = 0
    rw [sub_eq_zero.mp hv]
    simp only [real_inner_smul_right, hP, mul_zero]
  · intro hv
    exact ⟨_, translation_perp_symmetry ℓ hv⟩

/-- Equation (10). -/
theorem symmetry_translation (ℓ' : Line E) (v : E) :
    let vℓ := parallelComponent ℓ'.direction v
    let vPerp := perpComponent ℓ'.direction v
    Line.symmetry ℓ' ∘ translation v =
      Line.glide (ℓ'.translate (-(1 / 2 : ℝ) • vPerp)) vℓ := by
  intro vℓ vPerp
  have hu : ℓ'.direction ≠ 0 := ℓ'.direction_ne_zero
  have hq : perpComponent ℓ'.direction vPerp = vPerp := m4_perp_idem hu v
  have hp : perpComponent ℓ'.direction vℓ = 0 := by
    rw [show perpComponent ℓ'.direction vℓ
        = vℓ - parallelComponent ℓ'.direction vℓ from rfl]
    rw [show vℓ = parallelComponent ℓ'.direction v from rfl, m4_parallel_idem hu v, sub_self]
  have hsplit : vℓ + vPerp = v := parallelComponent_add_perpComponent _ _
  have hs : perpComponent ℓ'.direction ((1 / 2 : ℝ) • vPerp) = (1 / 2 : ℝ) • vPerp := by
    rw [perpComponent_smul, hq]
  have h2 : vPerp = (1 / 2 : ℝ) • vPerp + (1 / 2 : ℝ) • vPerp := by
    rw [← add_smul]; norm_num
  funext X
  simp only [Function.comp_apply, Line.glide, Line.translate, Line.symmetry, translation]
  rw [show X + v - ℓ'.base = (X - ℓ'.base) + v by abel]
  rw [show X - (ℓ'.base + -(1 / 2 : ℝ) • vPerp) = (X - ℓ'.base) + (1 / 2 : ℝ) • vPerp by
    rw [neg_smul]; abel]
  rw [m4_reflect_add_eigen ℓ'.direction _ _ hs]
  rw [show (X - ℓ'.base) + v = ((X - ℓ'.base) + vPerp) + vℓ by rw [← hsplit]; abel]
  rw [m4_reflect_add_par ℓ'.direction _ _ hp]
  rw [m4_reflect_add_eigen ℓ'.direction _ _ hq, h2]
  module

theorem symmetry_translation_is_reflection_iff (ℓ' : Line E) (v : E) :
    (∃ ℓ : Line E, Line.symmetry ℓ' ∘ translation v = Line.symmetry ℓ) ↔
      Orthogonal ℓ'.direction v := by
  constructor
  · rintro ⟨ℓ, hℓ⟩
    have hlin : ∀ w : E, Line.reflectVector ℓ'.direction w = Line.reflectVector ℓ.direction w := by
      intro w
      have h1 : Line.symmetry ℓ' (translation v w) - Line.symmetry ℓ' (translation v 0) =
          Line.symmetry ℓ w - Line.symmetry ℓ 0 := by
        have hw : Line.symmetry ℓ w = Line.symmetry ℓ' (translation v w) := (congrFun hℓ w).symm
        have h0 : Line.symmetry ℓ 0 = Line.symmetry ℓ' (translation v 0) := (congrFun hℓ 0).symm
        rw [hw, h0]
      rw [symmetry_sub, symmetry_sub] at h1
      simpa [translation_sub] using h1
    have hpar : Parallel ℓ.direction ℓ'.direction := by
      have h1 : Line.reflectVector ℓ.direction ℓ'.direction = ℓ'.direction := by
        rw [← hlin, m4_reflect_self ℓ'.direction_ne_zero]
      rw [m4_reflect_eq] at h1
      have h3 : (2 : ℝ) • perpComponent ℓ.direction ℓ'.direction = 0 :=
        sub_eq_self.mp h1
      exact (perpComponent_eq_zero_iff ℓ.direction_ne_zero).mp
        ((smul_eq_zero.mp h3).resolve_left (by norm_num))
    have hb' : Line.symmetry ℓ' ℓ'.base = ℓ'.base := by
      simp [Line.symmetry, Line.reflectVector, parallelComponent, perpComponent]
    have hX : Line.symmetry ℓ (ℓ'.base - v) = ℓ'.base := by
      have h := congrFun hℓ (ℓ'.base - v)
      simp only [Function.comp_apply, translation] at h
      rw [show ℓ'.base - v + v = ℓ'.base by abel, hb'] at h
      exact h.symm
    rw [m4_reflect_eq_symmetry ℓ (ℓ'.base - v)] at hX
    have hv : v + (2 : ℝ) • perpComponent ℓ.direction ((ℓ'.base - v) - ℓ.base) = 0 := by
      have h1 : ℓ'.base - ((ℓ'.base - v) - (2 : ℝ) •
          perpComponent ℓ.direction ((ℓ'.base - v) - ℓ.base)) = 0 := by
        rw [hX, sub_self]
      rw [← h1]
      abel
    have hP : ⟪ℓ.direction, perpComponent ℓ.direction ((ℓ'.base - v) - ℓ.base)⟫ = 0 := by
      rw [real_inner_comm]
      exact perpComponent_inner _ _ ℓ.direction_ne_zero
    have huv : ⟪ℓ.direction, v⟫ = 0 := by
      have hv' : v = -((2 : ℝ) • perpComponent ℓ.direction ((ℓ'.base - v) - ℓ.base)) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hv
      rw [hv']
      simp only [inner_neg_right, real_inner_smul_right, hP, mul_zero, neg_zero]
    obtain ⟨r, hr⟩ := hpar
    show ⟪ℓ'.direction, v⟫ = 0
    rw [hr]
    simp only [real_inner_smul_left, huv, mul_zero]
  · intro hv
    have hpar : parallelComponent ℓ'.direction v = 0 := by
      simp only [Orthogonal] at hv
      simp only [parallelComponent]
      rw [real_inner_comm, hv]
      simp
    have hperp : perpComponent ℓ'.direction v = v := by
      rw [show perpComponent ℓ'.direction v = v - parallelComponent ℓ'.direction v from rfl, hpar,
        sub_zero]
    refine ⟨ℓ'.translate (-(1 / 2 : ℝ) • v), ?_⟩
    have h := symmetry_translation ℓ' v
    simp only [hpar, hperp] at h
    rw [h]
    funext X
    simp [Line.glide]

/-- The orthogonal projection onto the line spanned by `u`, written in conjugate
complex coordinates. -/
theorem complex_parallelComponent_formula (u v : ℂ) (hu : u ≠ 0) :
    ((inner ℝ v u / inner ℝ u u : ℝ) : ℂ) * u = (v + conj v * (u / conj u)) / 2 := by
  have hu2 : u.re ^ 2 + u.im ^ 2 ≠ 0 := by
    have hp : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
    simp only [Complex.normSq_apply] at hp
    linarith
  rw [Complex.inner, Complex.inner]
  apply Complex.ext <;>
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im, Complex.conj_re,
      Complex.conj_im, Complex.normSq_apply] <;>
    norm_num <;>
    field_simp <;> ring

/-- Complex coordinates of the parallel component. -/
theorem toComplex_parallelComponent (u v : E) (hu : u ≠ 0) :
    toComplex o (parallelComponent u v) =
      (toComplex o v + conj (toComplex o v) *
        (toComplex o u / conj (toComplex o u))) / 2 := by
  have hin : inner ℝ (toComplex o v) (toComplex o u) = inner ℝ v u :=
    (complexIsometryEquiv o).inner_map_map v u
  have hin' : inner ℝ (toComplex o u) (toComplex o u) = inner ℝ u u :=
    (complexIsometryEquiv o).inner_map_map u u
  have hu' : toComplex o u ≠ 0 := by simpa using hu
  rw [parallelComponent, toComplex_smul, ← hin, ← hin']
  exact complex_parallelComponent_formula (toComplex o u) (toComplex o v) hu'

/-- Complex coordinates of a reflection. -/
theorem toComplex_symmetry (ℓ : Line E) (X : E) :
    toComplex o (Line.symmetry ℓ X) =
      toComplex o ℓ.base + conj (toComplex o X - toComplex o ℓ.base) *
        (toComplex o ℓ.direction / conj (toComplex o ℓ.direction)) := by
  have hpar : toComplex o (parallelComponent ℓ.direction (X - ℓ.base)) =
      (toComplex o (X - ℓ.base) + conj (toComplex o (X - ℓ.base)) *
        (toComplex o ℓ.direction / conj (toComplex o ℓ.direction))) / 2 :=
    toComplex_parallelComponent (o := o) ℓ.direction (X - ℓ.base) ℓ.direction_ne_zero
  simp only [Line.symmetry, Line.reflectVector, perpComponent, toComplex_add, toComplex_sub, hpar]
  ring

/-- The complex number of a circle element is a unit. -/
theorem circle_coe_mul_conj (θ : ℝ) :
    (Circle.exp θ : ℂ) * conj (Circle.exp θ : ℂ) = 1 := by
  rw [Complex.mul_conj, Circle.normSq_coe]
  norm_num

/-- Squaring of circle elements. -/
theorem circle_coe_sq_add (θ : ℝ) :
    (Circle.exp θ : ℂ) * (Circle.exp θ : ℂ) = (Circle.exp (θ + θ) : ℂ) := by
  rw [← Circle.coe_mul, ← Circle.exp_add]

/-- The square of a circle element times another is one when the angles sum to zero. -/
theorem circle_coe_sq_mul_eq_one {θ φ : ℝ} (h : θ + θ + φ = 0) :
    (Circle.exp θ : ℂ) * (Circle.exp θ : ℂ) * (Circle.exp φ : ℂ) = 1 := by
  rw [← Circle.coe_mul, ← Circle.coe_mul, ← Circle.exp_add, ← Circle.exp_add, h]
  simp

/-- Complex coordinates of the parallel and perpendicular components with respect
to a rotated direction. -/
theorem toComplex_parallel_rotate (ℓ : Line E) (ψ : ℝ) (v : E) :
    toComplex o (parallelComponent (rotateVector o ℓ.direction ψ) v) =
      (toComplex o v + conj (toComplex o v) *
        ((toComplex o ℓ.direction * (Circle.exp ψ : ℂ)) /
          conj (toComplex o ℓ.direction * (Circle.exp ψ : ℂ)))) / 2 := by
  rw [toComplex_parallelComponent (o := o) _ _ (rotateVector_ne_zero o ℓ.direction_ne_zero ψ),
    toComplex_rotateVector]

/-! ### `⋄9` Rotation–symmetry compositions -/

/-- The gliding-symmetry form of `R_{P',φ'} S_ℓ`. -/
theorem rotation_symmetry (ℓ : Line E) (P' : E) (φ' : ℝ) :
    let w := ofComplex o (toComplex o (P' - ℓ.base) * (1 - Circle.exp φ'))
    let uBar := rotateVector o ℓ.direction (φ' / 2)
    let wPar := parallelComponent uBar w
    let wPerp := perpComponent uBar w
    let ℓBar : Line E :=
      ⟨ℓ.base + (1 / 2 : ℝ) • wPerp, uBar, rotateVector_ne_zero o ℓ.direction_ne_zero _⟩
    rotation o P' φ' ∘ Line.symmetry ℓ = Line.glide ℓBar wPar := by
  dsimp only
  funext X
  apply toComplex_injective o
  set ψ : ℝ := φ' / 2 with hψ
  set b : ℂ := toComplex o ℓ.base with hb
  set s : ℂ := toComplex o ℓ.direction with hs
  set p : ℂ := toComplex o P' with hp
  set x : ℂ := toComplex o X with hx
  set c : ℂ := (Circle.exp φ' : ℂ) with hc
  set m : ℂ := (Circle.exp ψ : ℂ) with hm
  have hs0 : s ≠ 0 := by rw [hs]; simpa using ℓ.direction_ne_zero
  have hconjs : conj s ≠ 0 := by simpa using hs0
  have hm0 : m ≠ 0 := by
    intro h0
    have h1 := circle_coe_mul_conj ψ
    rw [← hm, h0] at h1
    simpa using h1
  have hcm : conj m = m⁻¹ := by
    rw [hm]
    exact eq_inv_of_mul_eq_one_right (circle_coe_mul_conj ψ)
  have hmm : m * m = c := by
    have h2 : ψ + ψ = φ' := by rw [hψ]; ring
    rw [hm, hc, ← h2]
    exact circle_coe_sq_add ψ
  have huU : toComplex o (rotateVector o ℓ.direction ψ) = s * m := by
    rw [toComplex_rotateVector, ← hs, ← hm]
  have hparU : ∀ v : E, toComplex o (parallelComponent (rotateVector o ℓ.direction ψ) v) =
      (toComplex o v + conj (toComplex o v) * ((s * m) / conj (s * m))) / 2 := by
    intro v
    rw [toComplex_parallel_rotate]
  have hperpU : ∀ v : E, toComplex o (perpComponent (rotateVector o ℓ.direction ψ) v) =
      toComplex o v - (toComplex o v + conj (toComplex o v) * ((s * m) / conj (s * m))) / 2 := by
    intro v
    rw [perpComponent, toComplex_sub, hparU v]
  simp only [Function.comp_apply, Line.glide, toComplex_add, toComplex_sub, toComplex_smul,
    Complex.real_smul, toComplex_symmetry (o := o), toComplex_rotation, toComplex_ofComplex,
    hparU, hperpU, huU, ← hb, ← hs, ← hp, ← hx, ← hc, ← hm]
  simp only [map_sub, map_add, map_mul, map_div₀, map_one, map_ofNat, map_pow, Complex.conj_conj,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [← hmm]
  simp only [map_mul, map_pow, map_add, map_sub, map_div₀, map_one, map_ofNat, map_inv₀,
    Complex.conj_conj]
  rw [hcm]
  field_simp
  ring

/-- The gliding-symmetry form of `S_ℓ' R_{P,φ}`. -/
theorem symmetry_rotation (ℓ' : Line E) (P : E) (φ : ℝ) :
    let Q := Line.symmetry ℓ' P
    let uBar := rotateVector o ℓ'.direction (-φ / 2)
    let v := Q - P
    let vPar := parallelComponent uBar v
    let vPerp := perpComponent uBar v
    let ℓBar : Line E :=
      ⟨Q - (1 / 2 : ℝ) • vPerp, uBar, rotateVector_ne_zero o ℓ'.direction_ne_zero _⟩
    Line.symmetry ℓ' ∘ rotation o P φ = Line.glide ℓBar vPar := by
  dsimp only
  funext X
  apply toComplex_injective o
  set ψ : ℝ := -φ / 2 with hψ
  set b : ℂ := toComplex o ℓ'.base with hb
  set s : ℂ := toComplex o ℓ'.direction with hs
  set p : ℂ := toComplex o P with hp
  set x : ℂ := toComplex o X with hx
  set c : ℂ := (Circle.exp φ : ℂ) with hc
  set m : ℂ := (Circle.exp ψ : ℂ) with hm
  have hs0 : s ≠ 0 := by rw [hs]; simpa using ℓ'.direction_ne_zero
  have hconjs : conj s ≠ 0 := by simpa using hs0
  have hm0 : m ≠ 0 := by
    intro h0
    have h1 := circle_coe_mul_conj ψ
    rw [← hm, h0] at h1
    simpa using h1
  have hcm : conj m = m⁻¹ := by
    rw [hm]
    exact eq_inv_of_mul_eq_one_right (circle_coe_mul_conj ψ)
  have hmmc : m * m * c = 1 := by
    have h2 : ψ + ψ + φ = 0 := by rw [hψ]; ring
    rw [hm, hc]
    exact circle_coe_sq_mul_eq_one h2
  have huU : toComplex o (rotateVector o ℓ'.direction ψ) = s * m := by
    rw [toComplex_rotateVector, ← hs, ← hm]
  have hparU : ∀ v : E, toComplex o (parallelComponent (rotateVector o ℓ'.direction ψ) v) =
      (toComplex o v + conj (toComplex o v) * ((s * m) / conj (s * m))) / 2 := by
    intro v
    rw [toComplex_parallel_rotate]
  have hperpU : ∀ v : E, toComplex o (perpComponent (rotateVector o ℓ'.direction ψ) v) =
      toComplex o v - (toComplex o v + conj (toComplex o v) * ((s * m) / conj (s * m))) / 2 := by
    intro v
    rw [perpComponent, toComplex_sub, hparU v]
  simp only [Function.comp_apply, Line.glide, toComplex_add, toComplex_sub, toComplex_smul,
    Complex.real_smul, toComplex_symmetry (o := o), toComplex_rotation, toComplex_ofComplex,
    hparU, hperpU, huU, ← hb, ← hs, ← hp, ← hx, ← hc, ← hm]
  simp only [map_sub, map_add, map_mul, map_div₀, map_one, map_ofNat, map_pow, Complex.conj_conj,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [show c = (m * m)⁻¹ from eq_inv_of_mul_eq_one_right hmmc]
  simp only [map_mul, map_pow, map_add, map_sub, map_div₀, map_one, map_ofNat, map_inv₀,
    Complex.conj_conj]
  rw [hcm]
  field_simp
  ring

/-! ### Helper lemmas (m5): complex coordinates of the plane -/

theorem toComplex_e₁ : toComplex o (e₁ o) = 1 := by
  simp only [e₁, toComplex, complexIsometryEquiv, positiveBasis,
    OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply,
    Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero]

theorem toComplex_e₂ : toComplex o (e₂ o) = Complex.I := by
  simp only [e₂, toComplex, complexIsometryEquiv, positiveBasis,
    OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply,
    Complex.coe_orthonormalBasisOneI, Matrix.cons_val_one, Matrix.cons_val_zero]

theorem ofComplex_eq_smul (z : ℂ) :
    ofComplex o z = z.re • e₁ o + z.im • e₂ o := by
  apply toComplex_injective o
  rw [toComplex_add, toComplex_smul, toComplex_smul, toComplex_e₁ o, toComplex_e₂ o,
    toComplex_ofComplex, mul_one]
  exact (Complex.re_add_im z).symm

theorem areaForm_e₁_e₂ : o.areaForm (e₁ o) (e₂ o) = 1 := by
  rw [o.areaForm_to_volumeForm,
    o.volumeForm_robust (positiveBasis o) (o.finOrthonormalBasis_orientation _ _)]
  have h : (![e₁ o, e₂ o] : Fin 2 → E) = (positiveBasis o : Fin 2 → E) := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  exact Module.Basis.det_self _

theorem areaForm_ofComplex (z w : ℂ) :
    o.areaForm (ofComplex o z) (ofComplex o w) = (conj z * w).im := by
  have h11 : o.areaForm (e₁ o) (e₁ o) = 0 := o.areaForm_apply_self _
  have h22 : o.areaForm (e₂ o) (e₂ o) = 0 := o.areaForm_apply_self _
  have h12 : o.areaForm (e₁ o) (e₂ o) = 1 := areaForm_e₁_e₂ o
  have h21 : o.areaForm (e₂ o) (e₁ o) = -1 := by
    rw [o.areaForm_swap, h12]
  rw [ofComplex_eq_smul, ofComplex_eq_smul]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    h11, h22, h12, h21]
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem inner_complex (v w : E) : ⟪v, w⟫ = (conj (toComplex o v) * toComplex o w).re := by
  have h := (complexIsometryEquiv o).inner_map_map v w
  rw [← h, Complex.inner, mul_comm]
  rfl

theorem areaForm_complex (v w : E) :
    (o.areaForm v) w = (conj (toComplex o v) * toComplex o w).im := by
  conv_lhs => rw [← ofComplex_toComplex o v, ← ofComplex_toComplex o w]
  exact areaForm_ofComplex o (toComplex o v) (toComplex o w)

theorem kahler_complex (v w : E) :
    o.kahler v w = conj (toComplex o v) * toComplex o w := by
  rw [o.kahler_apply_apply, inner_complex o, areaForm_complex o, Complex.real_smul]
  exact Complex.re_add_im _

theorem oangle_complex (v w : E) :
    o.oangle v w = Complex.arg (conj (toComplex o v) * toComplex o w) := by
  rw [Orientation.oangle, kahler_complex]

/-- Expansion of a complex number in the two non-parallel directions `u`, `u'`. -/
theorem complex_expansion {u u' z : ℂ} (h : (conj u * u').im ≠ 0) :
    z = ((conj z * u').im / (conj u * u').im) * u +
        ((conj u * z).im / (conj u * u').im) * u' := by
  have key : ((conj z * u').im) * u + ((conj u * z).im) * u'
      = z * ((conj u * u').im) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
      push_cast
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
      push_cast
      ring
  have hc : ((conj u * u').im : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact h
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hc]
  exact key.symm

/-- A complex number whose `conj u *`-product is real is a real multiple of `u`. -/
theorem complex_parallel_of_im_zero {u u' : ℂ} (hu : u ≠ 0)
    (h : (conj u * u').im = 0) : ∃ r : ℝ, u' = (r : ℂ) * u := by
  set r : ℝ := (conj u * u').re with hr
  refine ⟨r / ‖u‖ ^ 2, ?_⟩
  have hcu : conj u ≠ 0 := by simpa using hu
  have hreal : conj u * u' = ((r : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hr]
    · simpa [hr] using h
  have huun : conj u * u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hnorm : (‖u‖ : ℝ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (by simpa using norm_ne_zero_iff.mpr hu)
  have hrhs : conj u * ((↑(r / ‖u‖ ^ 2) : ℂ) * u) = ((r : ℝ) : ℂ) := by
    rw [← mul_assoc, mul_comm (conj u) (↑(r / ‖u‖ ^ 2) : ℂ), mul_assoc, huun]
    have hc2 : ((‖u‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact hnorm
    have hu0 : ((‖u‖ : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact norm_ne_zero_iff.mpr hu
    push_cast
    field_simp
  refine mul_left_cancel₀ hcu ?_
  rw [hreal, hrhs]

/-- The two-line intersection identity in complex coordinates. -/
theorem complex_intersection_mem {p u q u' : ℂ} (h : (conj u * u').im ≠ 0) :
    p + ((((conj (q - p) * u').im / (conj u * u').im : ℝ)) : ℂ) * u =
      q + ((-(((conj u * (q - p)).im / (conj u * u').im)) : ℝ) : ℂ) * u' := by
  have h1 : ((((conj (q - p) * u').im / (conj u * u').im : ℝ)) : ℂ) =
      ((conj (q - p) * u').im : ℂ) / ((conj u * u').im : ℂ) := by
    push_cast; ring
  have h2 : (((-(((conj u * (q - p)).im / (conj u * u').im)) : ℝ)) : ℂ) =
      -(((conj u * (q - p)).im : ℂ) / ((conj u * u').im : ℂ)) := by
    push_cast; ring
  rw [h1, h2]
  have hexp := complex_expansion (u := u) (u' := u') (z := q - p) h
  linear_combination -hexp

theorem Parallel_of_areaForm_eq_zero {v w : E} (hv : v ≠ 0)
    (h : (o.areaForm v) w = 0) : Parallel v w := by
  have h0 : (conj (toComplex o v) * toComplex o w).im = 0 := by
    rw [← areaForm_complex o v w]; exact h
  have htv : toComplex o v ≠ 0 := by
    intro hc
    exact hv ((toComplex_eq_zero o v).mp hc)
  obtain ⟨r, hr⟩ := complex_parallel_of_im_zero htv h0
  refine ⟨r, ?_⟩
  apply toComplex_injective o
  rw [toComplex_smul, hr]

theorem parallel_directions (ℓ ℓ' : Line E) (h : Line.parallel o ℓ ℓ') :
    ∃ r : ℝ, r ≠ 0 ∧ ℓ'.direction = r • ℓ.direction := by
  have h0 : (o.areaForm ℓ.direction) ℓ'.direction = 0 := h
  obtain ⟨r, hr⟩ := Parallel_of_areaForm_eq_zero o ℓ.direction_ne_zero h0
  refine ⟨r, ?_, hr⟩
  intro hr0
  exact ℓ'.direction_ne_zero (by rw [hr, hr0, zero_smul])

theorem perpComponent_smul_left {u : E} (hu : u ≠ 0) {r : ℝ} (hr : r ≠ 0) (v : E) :
    perpComponent (r • u) v = perpComponent u v := by
  have huu : ⟪u, u⟫ ≠ 0 := inner_self_ne_zero.mpr hu
  simp only [perpComponent, parallelComponent, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial, smul_smul]
  rw [show r * ⟪v, u⟫ / (r * (r * ⟪u, u⟫)) * r = ⟪v, u⟫ / ⟪u, u⟫ by
    field_simp]

theorem nsmul_eq_smul_natCast (n : ℕ) (v : E) : n • v = (n : ℝ) • v :=
  (Nat.cast_smul_eq_nsmul ℝ n v).symm

theorem perpComponent_eq_self {u w : E} (hw : ⟪w, u⟫ = 0) :
    perpComponent u w = w := by
  simp [perpComponent, parallelComponent, hw]

theorem perpComponent_idem {u : E} (hu : u ≠ 0) (v : E) :
    perpComponent u (perpComponent u v) = perpComponent u v :=
  perpComponent_eq_self (perpComponent_inner u v hu)

theorem areaForm_sub_base (ℓ ℓ' : Line E) :
    (o.areaForm (ℓ'.base - ℓ.base)) ℓ'.direction =
      (conj (toComplex o ℓ'.base - toComplex o ℓ.base) * toComplex o ℓ'.direction).im := by
  rw [areaForm_complex, toComplex_sub]

theorem areaForm_directions (ℓ ℓ' : Line E) :
    (o.areaForm ℓ.direction) ℓ'.direction =
      (conj (toComplex o ℓ.direction) * toComplex o ℓ'.direction).im :=
  areaForm_complex o ℓ.direction ℓ'.direction

theorem reflectVector_complex {u v : E} (hu : u ≠ 0) :
    toComplex o (Line.reflectVector u v) =
      (toComplex o u / conj (toComplex o u)) * conj (toComplex o v) := by
  set U := toComplex o u with hUdef
  set Z := toComplex o v with hZdef
  have hU0 : U ≠ 0 := by
    rw [hUdef]
    intro hc
    exact hu ((toComplex_eq_zero o u).mp hc)
  have hcU0 : conj U ≠ 0 := by simpa using hU0
  have hrev : Line.reflectVector u v = (2 : ℝ) • parallelComponent u v - v := by
    simp only [Line.reflectVector, perpComponent]
    rw [two_smul ℝ]
    abel
  rw [hrev, toComplex_sub, toComplex_smul]
  have hpc : toComplex o (parallelComponent u v) = ((⟪v, u⟫ / ⟪u, u⟫ : ℝ) : ℂ) * U := by
    rw [parallelComponent, toComplex_smul]
  rw [hpc]
  set A : ℝ := (conj Z * U).re with hAdef
  set B : ℝ := (conj U * U).re with hBdef
  have hA : (⟪v, u⟫ : ℝ) = A := by
    rw [hAdef, hZdef, hUdef, inner_complex]
  have hB : (⟪u, u⟫ : ℝ) = B := by
    rw [hBdef, hUdef, inner_complex]
  rw [hA, hB]
  have hB0 : B ≠ 0 := by
    rw [← hB]
    exact inner_self_ne_zero.mpr hu
  have hBc : ((B : ℝ) : ℂ) = U * conj U := by
    have h1 : ((B : ℝ) : ℂ) = ((Complex.normSq U : ℝ) : ℂ) := by
      rw [hBdef]
      congr 1
      exact (congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := U))).symm
    rw [h1, ← Complex.mul_conj U]
  have hkey : (2 : ℂ) * ((A : ℝ) : ℂ) = conj Z * U + Z * conj U := by
    have h2 := (Complex.add_conj (conj Z * U)).symm
    rw [map_mul, Complex.conj_conj] at h2
    rw [← h2, hAdef]
    push_cast
    ring
  have hcast : ((A / B : ℝ) : ℂ) = ((A : ℝ) : ℂ) / ((B : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, hBc, ← mul_right_inj' hcU0]
  field_simp
  rw [← hZdef]
  have htwo : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  rw [htwo]
  linear_combination hkey

theorem exp_two_lineAngle (ℓ ℓ' : Line E) (h : ¬Line.parallel o ℓ ℓ') :
    ((Circle.exp (2 * Line.angle o ℓ ℓ') : Circle) : ℂ) =
      (toComplex o ℓ'.direction * conj (toComplex o ℓ.direction)) /
        (conj (toComplex o ℓ'.direction) * toComplex o ℓ.direction) := by
  set u := toComplex o ℓ.direction with hudef
  set u' := toComplex o ℓ'.direction with hu'def
  set w := conj u * u' with hwdef
  have hu0 : u ≠ 0 := by
    rw [hudef]
    intro hc
    exact ℓ.direction_ne_zero ((toComplex_eq_zero o ℓ.direction).mp hc)
  have hu0' : u' ≠ 0 := by
    rw [hu'def]
    intro hc
    exact ℓ'.direction_ne_zero ((toComplex_eq_zero o ℓ'.direction).mp hc)
  have hw0 : w ≠ 0 := by
    rw [hwdef]
    exact mul_ne_zero (by simpa using hu0) hu0'
  have harg : (o.oangle ℓ.direction ℓ'.direction).toReal = w.arg := by
    rw [oangle_complex]
    exact Real.Angle.toReal_coe_eq_self_iff.mpr ⟨Complex.neg_pi_lt_arg w, Complex.arg_le_pi w⟩
  have hmain : ((Circle.exp (2 * w.arg) : Circle) : ℂ) = w / conj w := by
    have h1 : ((Circle.exp w.arg : Circle) : ℂ) = w / ‖w‖ := by
      rw [Circle.coe_exp]
      have hnorm := Complex.norm_mul_exp_arg_mul_I w
      have hw' : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact norm_ne_zero_iff.mpr hw0
      field_simp
      rw [mul_comm]
      exact hnorm
    have h2 : (((Circle.exp (2 * w.arg) : Circle)) : ℂ) =
        ((Circle.exp w.arg : Circle) : ℂ) ^ 2 := by
      rw [Circle.coe_exp, Circle.coe_exp,
        show ((2 * w.arg : ℝ) : ℂ) * Complex.I = w.arg * Complex.I + w.arg * Complex.I by
          push_cast; ring, Complex.exp_add]
      ring
    have hsq : (((‖w‖ : ℝ)) : ℂ) ^ 2 = w * conj w := by
      rw [Complex.mul_conj w, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [h2, h1]
    have hw' : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact norm_ne_zero_iff.mpr hw0
    have hcw : conj w ≠ 0 := by simpa using hw0
    field_simp
    rw [hsq]
  have hkey : ((Circle.exp (2 * Line.angle o ℓ ℓ') : Circle) : ℂ) =
      ((Circle.exp (2 * w.arg) : Circle) : ℂ) := by
    rw [Line.angle]
    simp only [harg]
    split_ifs with hpos
    · rfl
    · rw [show (2 : ℝ) * (w.arg + Real.pi) = 2 * w.arg + 2 * Real.pi by ring,
        Circle.exp_add, Circle.exp_two_pi, mul_one]
  rw [hkey, hmain]
  rw [hwdef, map_mul, Complex.conj_conj]
  ring

theorem symmetry_complex (ℓ : Line E) (X : E) :
    toComplex o (Line.symmetry ℓ X) =
      toComplex o ℓ.base + (toComplex o ℓ.direction / conj (toComplex o ℓ.direction)) *
        conj (toComplex o X - toComplex o ℓ.base) := by
  simp only [Line.symmetry, toComplex_add, toComplex_sub,
    reflectVector_complex o ℓ.direction_ne_zero]

theorem reflectVector_reflectVector (ℓ ℓ' : Line E) (h : ¬Line.parallel o ℓ ℓ') (v : E) :
    Line.reflectVector ℓ'.direction (Line.reflectVector ℓ.direction v) =
      rotateVector o v (2 * Line.angle o ℓ ℓ') := by
  apply toComplex_injective o
  rw [reflectVector_complex o ℓ'.direction_ne_zero, reflectVector_complex o ℓ.direction_ne_zero,
    toComplex_rotateVector, exp_two_lineAngle o ℓ ℓ' h]
  rw [map_mul, Complex.conj_conj]
  have hU : toComplex o ℓ.direction ≠ 0 := fun hc =>
    ℓ.direction_ne_zero ((toComplex_eq_zero o _).mp hc)
  have hU' : toComplex o ℓ'.direction ≠ 0 := fun hc =>
    ℓ'.direction_ne_zero ((toComplex_eq_zero o _).mp hc)
  have hcU : conj (toComplex o ℓ.direction) ≠ 0 := by simpa using hU
  have hcU' : conj (toComplex o ℓ'.direction) ≠ 0 := by simpa using hU'
  simp only [map_div₀, Complex.conj_conj]
  field_simp

theorem orientedArea_complex (v w : E) :
    orientedArea o v w = (conj (toComplex o v) * toComplex o w).im :=
  areaForm_complex o v w

theorem orientedArea_sub_base (ℓ ℓ' : Line E) :
    orientedArea o (ℓ'.base - ℓ.base) ℓ'.direction =
      (conj (toComplex o ℓ'.base - toComplex o ℓ.base) * toComplex o ℓ'.direction).im := by
  rw [orientedArea_complex, toComplex_sub]

theorem orientedArea_directions (ℓ ℓ' : Line E) :
    orientedArea o ℓ.direction ℓ'.direction =
      (conj (toComplex o ℓ.direction) * toComplex o ℓ'.direction).im :=
  orientedArea_complex o ℓ.direction ℓ'.direction


/-
  ================= C. THE FIVE REPLACEMENT THEOREMS =================
-/

/-! ### `⋄10` Composition of two symmetries, Equation (11) -/

theorem intersection_mem_left (ℓ ℓ' : Line E) (h : ¬Line.parallel o ℓ ℓ') :
    ℓ.mem (Line.intersection o ℓ ℓ') :=
  ⟨_, rfl⟩

theorem intersection_mem_right (ℓ ℓ' : Line E) (h : ¬Line.parallel o ℓ ℓ') :
    ℓ'.mem (Line.intersection o ℓ ℓ') := by
  have ht0 : (conj (toComplex o ℓ.direction) * toComplex o ℓ'.direction).im ≠ 0 := by
    intro h0
    refine h ?_
    show (o.areaForm ℓ.direction) ℓ'.direction = 0
    rw [areaForm_complex]
    exact h0
  refine ⟨-(((conj (toComplex o ℓ.direction) *
    (toComplex o ℓ'.base - toComplex o ℓ.base)).im /
      (conj (toComplex o ℓ.direction) * toComplex o ℓ'.direction).im)), ?_⟩
  apply toComplex_injective o
  rw [Line.intersection, toComplex_add, toComplex_smul, orientedArea_sub_base o ℓ ℓ',
    orientedArea_directions o ℓ ℓ', toComplex_add, toComplex_smul]
  exact complex_intersection_mem ht0

theorem intersection_unique (ℓ ℓ' : Line E) (h : ¬Line.parallel o ℓ ℓ') {X : E}
    (hX : ℓ.mem X) (hX' : ℓ'.mem X) : X = Line.intersection o ℓ ℓ' := by
  obtain ⟨s, hs⟩ := hX
  obtain ⟨t, ht⟩ := hX'
  have ht0 : (o.areaForm ℓ.direction) ℓ'.direction ≠ 0 := h
  have h1 : (o.areaForm (X - ℓ'.base)) ℓ'.direction = 0 := by
    have hXq : X - ℓ'.base = t • ℓ'.direction := by rw [ht]; abel
    rw [hXq, map_smul, LinearMap.smul_apply, smul_eq_mul, o.areaForm_apply_self, mul_zero]
  have h2 : (o.areaForm (X - ℓ'.base)) ℓ'.direction =
      (o.areaForm (ℓ.base - ℓ'.base)) ℓ'.direction +
        s * ((o.areaForm ℓ.direction) ℓ'.direction) := by
    have hXq : X - ℓ'.base = (ℓ.base - ℓ'.base) + s • ℓ.direction := by rw [hs]; abel
    rw [hXq, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hsval : s = (o.areaForm (ℓ'.base - ℓ.base)) ℓ'.direction /
      ((o.areaForm ℓ.direction) ℓ'.direction) := by
    have hA : (o.areaForm (ℓ'.base - ℓ.base)) ℓ'.direction =
        -((o.areaForm (ℓ.base - ℓ'.base)) ℓ'.direction) := by
      rw [show ℓ'.base - ℓ.base = -(ℓ.base - ℓ'.base) by abel, map_neg, LinearMap.neg_apply]
    have hzero : (o.areaForm (ℓ.base - ℓ'.base)) ℓ'.direction +
        s * ((o.areaForm ℓ.direction) ℓ'.direction) = 0 := h2.symm.trans h1
    rw [hA]
    field_simp
    linarith
  rw [hs, hsval, Line.intersection]
  rfl

/-- Equation (11): two reflections in intersecting lines give a rotation through
twice the oriented line angle. -/
theorem symmetry_symmetry_nonparallel (ℓ ℓ' : Line E)
    (h : ¬Line.parallel o ℓ ℓ') :
    Line.symmetry ℓ' ∘ Line.symmetry ℓ =
      rotation o (Line.intersection o ℓ ℓ') (2 * Line.angle o ℓ ℓ') := by
  funext X
  set P := Line.intersection o ℓ ℓ' with hP
  have hPleft : Line.symmetry ℓ P = P :=
    (symmetry_fixed_iff ℓ P).mpr (intersection_mem_left o ℓ ℓ' h)
  have hPright : Line.symmetry ℓ' P = P :=
    (symmetry_fixed_iff ℓ' P).mpr (intersection_mem_right o ℓ ℓ' h)
  have hPfix : Line.symmetry ℓ' (Line.symmetry ℓ P) = P := by
    rw [hPleft, hPright]
  have hstep : Line.symmetry ℓ' (Line.symmetry ℓ X) - Line.symmetry ℓ' (Line.symmetry ℓ P) =
      rotateVector o (X - P) (2 * Line.angle o ℓ ℓ') := by
    rw [symmetry_sub, symmetry_sub]
    exact reflectVector_reflectVector o ℓ ℓ' h (X - P)
  rw [Function.comp_apply, rotation, ← hstep, hPfix]
  abel

/-- Two reflections in parallel lines give the translation by `2v''`. -/
theorem symmetry_symmetry_parallel (ℓ ℓ' : Line E)
    (h : Line.parallel o ℓ ℓ') :
    Line.symmetry ℓ' ∘ Line.symmetry ℓ =
      translation (2 • perpComponent ℓ.direction (ℓ'.base - ℓ.base)) := by
  obtain ⟨r, hr0, hr⟩ := parallel_directions o ℓ ℓ' h
  have hperp : ∀ v, perpComponent ℓ'.direction v = perpComponent ℓ.direction v := by
    intro v
    rw [hr]
    exact perpComponent_smul_left ℓ.direction_ne_zero hr0 v
  funext X
  simp only [Function.comp_apply, translation]
  rw [symmetry_decomposition ℓ X, symmetry_decomposition ℓ', hperp]
  simp only [nsmul_eq_smul_natCast]
  simp only [perpComponent_sub, perpComponent_smul, perpComponent_idem ℓ.direction_ne_zero]
  module

theorem line_angle_add_reverse (ℓ ℓ' : Line E) (h : ¬Line.parallel o ℓ ℓ') :
    Line.angle o ℓ ℓ' + Line.angle o ℓ' ℓ = Real.pi := by
  have harea : o.areaForm ℓ.direction ℓ'.direction ≠ 0 := h
  have hzero : o.oangle ℓ.direction ℓ'.direction ≠ 0 := by
    intro h0
    apply harea
    exact ((o.nonneg_inner_and_areaForm_eq_zero_iff_sameRay _ _).mpr
      (o.oangle_eq_zero_iff_sameRay.mp h0)).2
  have hpi : o.oangle ℓ.direction ℓ'.direction ≠ (Real.pi : Real.Angle) := by
    intro h0
    apply harea
    obtain ⟨-, -, hsr⟩ := o.oangle_eq_pi_iff_sameRay_neg.mp h0
    have h1 : (o.areaForm ℓ.direction) (-ℓ'.direction) = 0 :=
      ((o.nonneg_inner_and_areaForm_eq_zero_iff_sameRay _ _).mpr hsr).2
    simpa using h1
  set α : Real.Angle := o.oangle ℓ.direction ℓ'.direction with hα
  have hθ0 : α.toReal ≠ 0 := by simpa using hzero
  have hθπ : α.toReal ≠ Real.pi := by simpa using hpi
  have hrev : o.oangle ℓ'.direction ℓ.direction = -α := by
    have h1 := o.oangle_rev (x := ℓ'.direction) (y := ℓ.direction)
    rw [hα]
    rw [h1, neg_neg]
  have hneg : (-α).toReal = -α.toReal := Real.Angle.toReal_neg_eq_neg_toReal_iff.mpr hpi
  simp only [Line.angle, hrev, hneg]
  rcases lt_or_gt_of_ne hθ0 with hlt | hgt
  · rw [if_neg (not_lt.mpr hlt.le), if_pos (by linarith)]
    ring
  · rw [if_pos hgt, if_neg (by linarith)]
    ring

@[simp] theorem symmetry_sq (ℓ : Line E) :
    Line.symmetry ℓ ∘ Line.symmetry ℓ = id := by
  funext X
  show Line.symmetry ℓ (Line.symmetry ℓ X) = X
  have h1 : Line.symmetry ℓ X - ℓ.base = Line.reflectVector ℓ.direction (X - ℓ.base) := by
    simp only [Line.symmetry]
    abel
  have h2 : Line.symmetry ℓ (Line.symmetry ℓ X) =
      ℓ.base + Line.reflectVector ℓ.direction (Line.reflectVector ℓ.direction (X - ℓ.base)) := by
    rw [Line.symmetry, h1]
  rw [h2, g3_reflectVector_involutive ℓ.direction_ne_zero]
  abel

/-! ### `⋄11` Groups of isometries -/

/-- The semidirect product `P = E ⋉ U`, with `(v,u)(v',u')=(v+v'u,uu')`. -/
structure ProperMotion (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2)) where
  displacement : E
  turn : Circle

namespace ProperMotion

@[ext] theorem ext {p q : ProperMotion E o} (hdisplacement : p.displacement = q.displacement)
    (hturn : p.turn = q.turn) : p = q := by
  cases p
  cases q
  simp_all

variable (o : Orientation ℝ E (Fin 2))

instance : One (ProperMotion E o) where one := ⟨0, 1⟩
instance : Mul (ProperMotion E o) where
  mul p q := ⟨p.displacement + ofComplex o (toComplex o q.displacement * p.turn),
    p.turn * q.turn⟩
instance : Inv (ProperMotion E o) where
  inv p := ⟨ofComplex o (toComplex o (-p.displacement) * (p.turn : ℂ)⁻¹), p.turn⁻¹⟩

@[simp] theorem one_displacement : (1 : ProperMotion E o).displacement = 0 := rfl
@[simp] theorem one_turn : (1 : ProperMotion E o).turn = 1 := rfl
@[simp] theorem mul_displacement (p q : ProperMotion E o) : (p * q).displacement =
    p.displacement + ofComplex o (toComplex o q.displacement * p.turn) := rfl
@[simp] theorem mul_turn (p q : ProperMotion E o) : (p * q).turn = p.turn * q.turn := rfl
@[simp] theorem inv_displacement (p : ProperMotion E o) : p⁻¹.displacement =
    ofComplex o (toComplex o (-p.displacement) * (p.turn : ℂ)⁻¹) := rfl
@[simp] theorem inv_turn (p : ProperMotion E o) : p⁻¹.turn = p.turn⁻¹ := rfl

instance : Group (ProperMotion E o) where
  mul_assoc := by
    intro p q r
    apply ProperMotion.ext o
    · simp only [mul_displacement, mul_turn]
      simp only [toComplex_ofComplex, Circle.coe_mul]
      simp only [toComplex_add]
      simp only [add_assoc]
      rw [add_left_cancel_iff, ← ofComplex_add]
      congr 1
      rw [toComplex_ofComplex]
      ring
    · simp only [mul_turn, mul_assoc]
  one_mul := by
    intro p
    apply ProperMotion.ext o
    · change 0 + ofComplex o (toComplex o p.displacement * (1 : ℂ)) = p.displacement
      simp
    · simp
  mul_one := by
    intro p
    apply ProperMotion.ext o
    · change p.displacement + ofComplex o (toComplex o 0 * (p.turn : ℂ)) = p.displacement
      simp
    · simp
  inv_mul_cancel := by
    intro p
    apply ProperMotion.ext o
    · change ofComplex o (toComplex o (-p.displacement) * (p.turn : ℂ)⁻¹) +
        ofComplex o (toComplex o p.displacement * (p.turn : ℂ)⁻¹) = 0
      rw [← ofComplex_add]
      simp [toComplex]
    · simp

/-- Rotate a vector by an element of `U` rather than by a real angle. -/
def rotateByUnit (u : Circle) (v : E) : E := ofComplex o (toComplex o v * u)

/-- The affine action `(v,u) : X ↦ v+(X-O)u`. -/
def action (O : E) (p : ProperMotion E o) : E → E :=
  fun X => O + p.displacement + rotateByUnit o p.turn (X - O)

/-- The action of translations. -/
def translationMotion (v : E) : ProperMotion E o := ⟨v, 1⟩

/-- The action of rotations about the chosen origin. -/
def originRotation (φ : ℝ) : ProperMotion E o := ⟨0, Circle.exp φ⟩

/-- The matrix associated with `(v,u)` in Equation (12). -/
def matrix (p : ProperMotion E o) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![1, 0], ![toComplex o p.displacement, p.turn]]

/-- The slightly modified matrix product in Equation (12). -/
def matrixMul (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![1, 0], ![A 1 0 + B 1 0 * A 1 1, A 1 1 * B 1 1]]

/-- The two-vector used to represent the point `X` relative to `O`. -/
def pointVector (O X : E) : Fin 2 → ℂ := ![1, toComplex o (X - O)]

/-- The surjective angular homomorphism `δ`. -/
def delta : ProperMotion E o →* Circle where
  toFun := ProperMotion.turn
  map_one' := rfl
  map_mul' := fun _ _ => rfl

end ProperMotion

/-- The property of being a translation–rotation (a proper plane isometry). -/
def IsProperIsometry (o : Orientation ℝ E (Fin 2)) (O : E) (f : E → E) : Prop :=
  ∃ p : ProperMotion E o, f = ProperMotion.action o O p

/-- The property of being a gliding symmetry (an improper plane isometry). -/
def IsImproperIsometry (f : E → E) : Prop :=
  ∃ (ℓ : Line E) (w : E), Parallel ℓ.direction w ∧ f = Line.glide ℓ w

/-- The translation formulas in `T`. -/
theorem translation_comp (v v' : E) :
    translation v' ∘ translation v = translation (v + v') := by
  funext X
  simp only [translation, Function.comp_apply]
  abel
theorem translation_eq_id_iff (v : E) : translation v = id ↔ v = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    simpa [translation] using h0
  · rintro rfl
    funext X
    simp [translation]

/-- Every rotation occurs in the translation–rotation group. -/
theorem rotation_as_proper (O P : E) (φ : ℝ) :
    ∃ v : E, rotation o P φ = ProperMotion.action o O
      (ProperMotion.mk v (Circle.exp φ)) := by
  refine ⟨P - O - rotateVector o (P - O) φ, ?_⟩
  funext X
  simp only [rotation, ProperMotion.action, ProperMotion.rotateByUnit, toComplex_rotateVector]
  change P + rotateVector o (X - P) φ =
    O + (P - O - rotateVector o (P - O) φ) + rotateVector o (X - O) φ
  have hdiff : X - O - (P - O) = X - P := by abel
  rw [← hdiff, rotateVector_sub]
  abel

/-- The map `E × U → G` is injective, and its range is exactly `G`. -/
theorem properMotion_action_injective (O : E) :
    Injective (fun p : ProperMotion E o => ProperMotion.action o O p) := by
  intro p q hpq
  have hd : p.displacement = q.displacement := by
    have h := congrFun hpq O
    dsimp [ProperMotion.action, ProperMotion.rotateByUnit] at h
    simpa only [sub_self, toComplex_zero, zero_mul, ofComplex_zero, add_zero, add_left_cancel_iff] using h
  apply ProperMotion.ext o hd
  apply Circle.ext
  have h := congrFun hpq (O + ofComplex o 1)
  dsimp [ProperMotion.action, ProperMotion.rotateByUnit] at h
  have h0 : O + ofComplex o 1 - O = ofComplex o 1 := by abel
  rw [hd, h0] at h
  have h1 : toComplex o (ofComplex o (1 : ℂ)) = 1 := toComplex_ofComplex o 1
  rw [h1, one_mul, one_mul] at h
  have ht := congrArg (toComplex o) h
  simpa only [toComplex_add, toComplex_sub, toComplex_ofComplex, add_left_cancel_iff] using ht

theorem proper_isometry_iff (O : E) (f : E → E) :
    IsProperIsometry o O f ↔ ∃ p : ProperMotion E o, ProperMotion.action o O p = f := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, rfl⟩

/-- Composition is the semidirect-product multiplication. -/
theorem properMotion_action_mul (O : E) (p q : ProperMotion E o) :
    ProperMotion.action o O (p * q) =
      ProperMotion.action o O p ∘ ProperMotion.action o O q := by
  funext X
  dsimp [ProperMotion.action, ProperMotion.rotateByUnit]
  have hbase : toComplex o (O + q.displacement + ofComplex o (toComplex o (X - O) * q.turn) - O) =
      toComplex o q.displacement + (toComplex o X - toComplex o O) * q.turn := by
    simp only [toComplex_sub, toComplex_add, toComplex_ofComplex]
    ring_nf
  rw [hbase]
  simp only [add_assoc, add_left_cancel_iff]
  rw [← ofComplex_add]
  congr 1
  rw [toComplex_sub]
  ring

theorem properMotion_action_one (O : E) : ProperMotion.action o O 1 = id := by
  funext X
  change ProperMotion.action o O 1 X = X
  simp only [ProperMotion.action, ProperMotion.rotateByUnit, ProperMotion.one_displacement,
    ProperMotion.one_turn, Circle.coe_one, mul_one, zero_add]
  rw [ofComplex_toComplex]
  abel
theorem translationMotion_mul (v w : E) :
    ProperMotion.translationMotion o v * ProperMotion.translationMotion o w =
      ProperMotion.translationMotion o (v + w) := by
  apply ProperMotion.ext o
  · change v + ofComplex o (toComplex o w * 1) = v + w
    simp
  · change (1 : Circle) * 1 = 1
    exact mul_one (1 : Circle)
theorem originRotation_mul (φ ψ : ℝ) :
    ProperMotion.originRotation o φ * ProperMotion.originRotation o ψ =
      ProperMotion.originRotation o (φ + ψ) := by
  apply ProperMotion.ext o
  · change 0 + ofComplex o (toComplex o 0 * Circle.exp φ) = 0
    simp [toComplex]
  · change Circle.exp φ * Circle.exp ψ = Circle.exp (φ + ψ)
    exact (Circle.exp_add φ ψ).symm
theorem originRotation_inv (φ : ℝ) :
    (ProperMotion.originRotation o φ)⁻¹ = ProperMotion.originRotation o (-φ) := by
  apply ProperMotion.ext o
  · change ofComplex o (toComplex o (-0) * (Circle.exp φ : ℂ)⁻¹) = 0
    simp [toComplex]
  · change (Circle.exp φ)⁻¹ = Circle.exp (-φ)
    exact (Circle.exp_neg φ).symm
theorem properMotion_action_inv (O : E) (p : ProperMotion E o) :
    ProperMotion.action o O p⁻¹ ∘ ProperMotion.action o O p = id := by
  rw [← properMotion_action_mul, inv_mul_cancel, properMotion_action_one]
private theorem rotateByUnit_isometry (u : Circle) : Isometry (ProperMotion.rotateByUnit o u) := by
  rw [isometry_iff_dist_eq]
  intro X Y
  dsimp [ProperMotion.rotateByUnit]
  rw [dist_eq_norm, dist_eq_norm]
  rw [← ofComplex_sub, ofComplex_norm, ← sub_mul, norm_mul, Circle.norm_coe, mul_one]
  simp only [← toComplex_sub, toComplex_norm]

theorem properMotion_action_isIsometry (O : E) (p : ProperMotion E o) :
    Isometry (ProperMotion.action o O p) := by
  rw [isometry_iff_dist_eq]
  intro X Y
  calc
    dist (ProperMotion.action o O p X) (ProperMotion.action o O p Y) =
        dist (ProperMotion.rotateByUnit o p.turn (X - O))
          (ProperMotion.rotateByUnit o p.turn (Y - O)) := by
      dsimp [ProperMotion.action]
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    _ = dist X Y := by
      simpa [dist_eq_norm] using
        (rotateByUnit_isometry o p.turn).dist_eq (X - O) (Y - O)

/-- Equation (12), in terms of the underlying matrices. -/
theorem properMotion_matrix_mul (p q : ProperMotion E o) :
    ProperMotion.matrix o (p * q) =
      ProperMotion.matrixMul (ProperMotion.matrix o p) (ProperMotion.matrix o q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ProperMotion.matrix, ProperMotion.matrixMul, ProperMotion.mul_displacement,
      ProperMotion.mul_turn, toComplex_add, toComplex_ofComplex] <;> ring

theorem properMotion_matrix_one :
    ProperMotion.matrix o (1 : ProperMotion E o) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ProperMotion.matrix]
theorem properMotion_matrix_inv (p : ProperMotion E o) :
    ProperMotion.matrix o p⁻¹ =
      ![![1, 0], ![-toComplex o p.displacement * (p.turn : ℂ)⁻¹, (p.turn : ℂ)⁻¹]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ProperMotion.matrix]
theorem properMotion_matrix_det (p : ProperMotion E o) :
    (ProperMotion.matrix o p).det = p.turn := by
  rw [Matrix.det_fin_two]
  simp [ProperMotion.matrix]

/-- Matrix multiplication gives the affine action on represented points. -/
theorem properMotion_matrix_action (O X : E) (p : ProperMotion E o) :
    (ProperMotion.matrix o p).mulVec (ProperMotion.pointVector o O X) =
      ProperMotion.pointVector o O (ProperMotion.action o O p X) := by
  ext i
  fin_cases i <;>
    simp [ProperMotion.matrix, ProperMotion.pointVector, ProperMotion.action,
      ProperMotion.rotateByUnit, Matrix.mulVec] <;> ring

/-- `ker δ = T`. -/
theorem delta_eq_one_iff (p : ProperMotion E o) :
    ProperMotion.delta o p = 1 ↔ p = ProperMotion.translationMotion o p.displacement := by
  constructor
  · intro h
    cases p with | mk d t =>
      exact ProperMotion.ext o rfl h
  · intro h
    exact congrArg ProperMotion.turn h

/-- Translations form a normal subgroup, stated extensionally in `P`. -/
theorem translations_normal (p : ProperMotion E o) (v : E) :
    ∃ w : E, p * ProperMotion.translationMotion o v * p⁻¹ =
      ProperMotion.translationMotion o w := by
  refine ⟨ofComplex o (toComplex o v * p.turn), ?_⟩
  apply ProperMotion.ext o
  · simp only [ProperMotion.mul_displacement, ProperMotion.inv_displacement,
      ProperMotion.mul_turn, ProperMotion.inv_turn, ProperMotion.translationMotion,
      toComplex_add, toComplex_neg, toComplex_ofComplex, Circle.coe_inv,
      add_zero]
    simp
  · simp [ProperMotion.mul_turn, ProperMotion.inv_turn, ProperMotion.translationMotion]

/-! ### Remark 3: all plane isometries -/

theorem proper_isometry_closure_id (O : E) : IsProperIsometry o O id := by
  exact ⟨1, (properMotion_action_one o O).symm⟩

/-! ### Group 7 helpers for Remark 3 -/

section Group7Helpers

variable (o : Orientation ℝ E (Fin 2))

theorem g7_inner_toComplex_re (v w : E) :
    ⟪v, w⟫ = (toComplex o v * conj (toComplex o w)).re := by
  have h := inner_map_complex (complexIsometryEquiv o) w v
  rw [real_inner_comm] at h
  simpa only [toComplex] using h

theorem g7_inner_toComplex_self (v : E) : ⟪v, v⟫ = Complex.normSq (toComplex o v) := by
  rw [g7_inner_toComplex_re, Complex.mul_conj, Complex.ofReal_re]

theorem g7_toComplex_parallelComponent (u v : E) :
    toComplex o (parallelComponent u v) =
      ((⟪v, u⟫ / ⟪u, u⟫ : ℝ) : ℂ) * toComplex o u := by
  rw [parallelComponent, toComplex_smul]

theorem g7_normSq_toComplex_ne_zero {u : E} (hu : u ≠ 0) :
    (Complex.normSq (toComplex o u) : ℝ) ≠ 0 := by
  intro h
  apply hu
  apply toComplex_injective o
  rw [toComplex_zero]
  exact Complex.normSq_eq_zero.mp h

theorem g7_toComplex_reflectVector_mul {u v : E} (hu : u ≠ 0) :
    toComplex o (Line.reflectVector u v) * (Complex.normSq (toComplex o u) : ℂ) =
      conj (toComplex o v) * (toComplex o u) ^ 2 := by
  have hdu : toComplex o u ≠ 0 := fun h => hu ((toComplex_eq_zero o u).mp h)
  have hnR := g7_normSq_toComplex_ne_zero o hu
  have hnc : (Complex.normSq (toComplex o u) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnR
  have hd : (Complex.normSq (toComplex o u) : ℂ) = toComplex o u * conj (toComplex o u) :=
    (Complex.mul_conj _).symm
  have h2 : (⟪u, u⟫ : ℝ) = Complex.normSq (toComplex o u) := g7_inner_toComplex_self o u
  have h3 : (⟪v, u⟫ : ℝ) = (toComplex o v * conj (toComplex o u)).re := g7_inner_toComplex_re o v u
  have hparn : toComplex o (parallelComponent u v) * (Complex.normSq (toComplex o u) : ℂ) =
      ((toComplex o v * conj (toComplex o u)).re : ℂ) * toComplex o u := by
    rw [g7_toComplex_parallelComponent o u v, h3, h2]
    push_cast
    rw [mul_assoc, mul_comm (toComplex o u), ← mul_assoc, div_mul_cancel₀ _ hnc]
  have hrw : Line.reflectVector u v = parallelComponent u v + parallelComponent u v - v := by
    simp only [Line.reflectVector, perpComponent]
    abel
  have hconj : conj (toComplex o v * conj (toComplex o u)) =
      conj (toComplex o v) * toComplex o u := by simp
  rw [hrw, toComplex_sub, toComplex_add]
  calc
    (toComplex o (parallelComponent u v) + toComplex o (parallelComponent u v) -
        toComplex o v) * (Complex.normSq (toComplex o u) : ℂ)
        = ((toComplex o v * conj (toComplex o u)).re : ℂ) * toComplex o u +
            ((toComplex o v * conj (toComplex o u)).re : ℂ) * toComplex o u -
            toComplex o v * (Complex.normSq (toComplex o u) : ℂ) := by
          rw [sub_mul, add_mul, hparn]
    _ = conj (toComplex o v) * (toComplex o u) ^ 2 := by
          rw [hd, Complex.re_eq_add_conj, hconj]
          ring

theorem g7_circle_exp_pi_div_two : (Circle.exp (Real.pi / 2) : ℂ) = Complex.I := by
  rw [Circle.coe_exp, Complex.exp_mul_I]
  norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem g7_toComplex_perp (v : E) : toComplex o (perp o v) = toComplex o v * Complex.I := by
  simp [perp, rotateVector, g7_circle_exp_pi_div_two]

theorem g7_perp_injective : Injective (perp o) := by
  intro a b h
  have := congrArg (fun v => toComplex o v) h
  simp only [g7_toComplex_perp] at this
  have h2 : toComplex o a = toComplex o b := mul_right_cancel₀ Complex.I_ne_zero this
  exact toComplex_injective o h2

@[simp] theorem g7_perp_zero : perp o (0 : E) = 0 := by simp [perp, rotateVector]

theorem g7_perp_ne_zero {v : E} (hv : v ≠ 0) : perp o v ≠ 0 := fun h =>
  hv (g7_perp_injective o (h.trans (g7_perp_zero o).symm))

theorem g7_rotateByUnit_add (u : Circle) (a b : E) :
    ProperMotion.rotateByUnit o u (a + b) =
      ProperMotion.rotateByUnit o u a + ProperMotion.rotateByUnit o u b := by
  simp only [ProperMotion.rotateByUnit, toComplex_add]
  rw [add_mul, ofComplex_add]

theorem g7_rotateByUnit_sub (u : Circle) (a b : E) :
    ProperMotion.rotateByUnit o u (a - b) =
      ProperMotion.rotateByUnit o u a - ProperMotion.rotateByUnit o u b := by
  simp only [ProperMotion.rotateByUnit, toComplex_sub]
  rw [sub_mul, ofComplex_sub]

theorem g7_rotateByUnit_neg (u : Circle) (a : E) :
    ProperMotion.rotateByUnit o u (-a) = -ProperMotion.rotateByUnit o u a := by
  simp [ProperMotion.rotateByUnit]

theorem g7_rotateByUnit_injective (u : Circle) : Injective (ProperMotion.rotateByUnit o u) := by
  intro a b h
  have := congrArg (ProperMotion.rotateByUnit o u⁻¹) h
  simpa [ProperMotion.rotateByUnit, mul_assoc] using this

theorem g7_perp_rotateByUnit (u : Circle) (v : E) :
    perp o (ProperMotion.rotateByUnit o u v) = ProperMotion.rotateByUnit o u (perp o v) := by
  apply toComplex_injective o
  simp only [g7_toComplex_perp, ProperMotion.rotateByUnit, toComplex_ofComplex]
  ring

theorem g7_toComplex_reflectVector {u v : E} (hu : u ≠ 0) :
    toComplex o (Line.reflectVector u v) =
      conj (toComplex o v) * (toComplex o u) ^ 2 / (Complex.normSq (toComplex o u) : ℂ) := by
  rw [eq_div_iff (Complex.ofReal_ne_zero.mpr (g7_normSq_toComplex_ne_zero o hu))]
  exact g7_toComplex_reflectVector_mul o hu

theorem g7_perp_reflectVector {u v : E} (hu : u ≠ 0) :
    perp o (Line.reflectVector u v) = -Line.reflectVector u (perp o v) := by
  apply toComplex_injective o
  rw [g7_toComplex_perp, g7_toComplex_reflectVector o hu, toComplex_neg,
    g7_toComplex_reflectVector o hu, g7_toComplex_perp, map_mul, Complex.conj_I]
  ring

theorem g7_action_sub (O : E) (p : ProperMotion E o) (X Y : E) :
    ProperMotion.action o O p X - ProperMotion.action o O p Y =
      ProperMotion.rotateByUnit o p.turn (X - Y) := by
  have h : ProperMotion.action o O p X - ProperMotion.action o O p Y =
      ProperMotion.rotateByUnit o p.turn (X - O) -
        ProperMotion.rotateByUnit o p.turn (Y - O) := by
    simp only [ProperMotion.action]
    abel
  rw [h, ← g7_rotateByUnit_sub, show X - O - (Y - O) = X - Y by abel]

theorem proper_isometry_closure_comp (O : E) {f g : E → E}
    (hf : IsProperIsometry o O f) (hg : IsProperIsometry o O g) :
    IsProperIsometry o O (f ∘ g) := by
  obtain ⟨p, rfl⟩ := hf
  obtain ⟨q, rfl⟩ := hg
  exact ⟨p * q, (properMotion_action_mul o O p q).symm⟩

theorem proper_isometry_closure_inverse (O : E) {f : E → E}
    (hf : IsProperIsometry o O f) :
    ∃ g, IsProperIsometry o O g ∧ g ∘ f = id ∧ f ∘ g = id := by
  obtain ⟨p, rfl⟩ := hf
  exact ⟨ProperMotion.action o O p⁻¹, ⟨p⁻¹, rfl⟩, properMotion_action_inv o O p,
    by simpa using properMotion_action_inv o O p⁻¹⟩

theorem g7_proper_action_toComplex (O X : E) (p : ProperMotion E o) :
    toComplex o (ProperMotion.action o O p X) =
      toComplex o O + toComplex o p.displacement + (toComplex o X - toComplex o O) * p.turn := by
  simp [ProperMotion.action, ProperMotion.rotateByUnit]

theorem g7_rotateVector_eq_rotateByUnit (v : E) (φ : ℝ) :
    rotateVector o v φ = ProperMotion.rotateByUnit o (Circle.exp φ) v := rfl

theorem g7_isProper_of_toComplex_form (O : E) {f : E → E} {u : ℂ} (hu : ‖u‖ = 1) {d : ℂ}
    (h : ∀ X, toComplex o (f X) = d + toComplex o X * u) : IsProperIsometry o O f := by
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    exact zero_ne_one hu
  refine ⟨⟨ofComplex o (d + (u - 1) * toComplex o O), ⟨u, ?_⟩⟩, ?_⟩
  · show u ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    simpa using hu
  funext X
  apply toComplex_injective o
  rw [g7_proper_action_toComplex]
  simp only [toComplex_ofComplex]
  rw [h X]
  ring

theorem not_proper_and_improper (O : E) (f : E → E) :
    ¬(IsProperIsometry o O f ∧ IsImproperIsometry f) := by
  rintro ⟨⟨p, hf⟩, ⟨ℓ, w, hw, hg⟩⟩
  have hAG : ProperMotion.action o O p = Line.glide ℓ w := hf.symm.trans hg
  have hlin : ∀ v : E, ProperMotion.rotateByUnit o p.turn v = Line.reflectVector ℓ.direction v := by
    intro v
    have h1 : ProperMotion.action o O p (O + v) - ProperMotion.action o O p O =
        ProperMotion.rotateByUnit o p.turn v := by
      rw [g7_action_sub, show O + v - O = v by abel]
    have h2 : Line.glide ℓ w (O + v) - Line.glide ℓ w O = Line.reflectVector ℓ.direction v := by
      have hsym : Line.symmetry ℓ (O + v) - Line.symmetry ℓ O =
          Line.reflectVector ℓ.direction v := by
        rw [symmetry_sub, show O + v - O = v by abel]
      simp only [Line.glide]
      rw [show Line.symmetry ℓ (O + v) + w - (Line.symmetry ℓ O + w) =
        Line.symmetry ℓ (O + v) - Line.symmetry ℓ O by abel, hsym]
    rw [← h1, ← h2, hAG]
  have hzero : ∀ v : E, ProperMotion.rotateByUnit o p.turn (perp o v) = 0 := by
    intro v
    have h3 : ProperMotion.rotateByUnit o p.turn (perp o v) =
        -Line.reflectVector ℓ.direction (perp o v) := by
      have h := congrArg (perp o) (hlin v)
      rw [g7_perp_rotateByUnit, g7_perp_reflectVector o ℓ.direction_ne_zero] at h
      exact h
    rw [hlin (perp o v)] at h3
    have h4 : Line.reflectVector ℓ.direction (perp o v) = 0 := by
      have h6 : Line.reflectVector ℓ.direction (perp o v) +
          Line.reflectVector ℓ.direction (perp o v) = 0 := by
        nth_rw 1 [h3]
        exact neg_add_cancel _
      rw [← two_smul ℝ, smul_eq_zero] at h6
      exact h6.resolve_left (by norm_num)
    rw [hlin (perp o v), h4]
  have hv : perp o (ofComplex o 1) ≠ 0 := by
    apply g7_perp_ne_zero o
    intro h
    have := congrArg (toComplex o) h
    rw [toComplex_ofComplex, toComplex_zero] at this
    exact one_ne_zero this
  refine hv (g7_rotateByUnit_injective o p.turn ?_)
  rw [hzero]
  simp [ProperMotion.rotateByUnit]

/-- The factor `s = d²/|d|²` attached to a line: reflection in the line has coordinate form
`z ↦ s * conj z + β`. -/
def g7_reflFactor (ℓ : Line E) : ℂ :=
  (toComplex o ℓ.direction) ^ 2 / (Complex.normSq (toComplex o ℓ.direction) : ℂ)

theorem g7_toComplex_symmetry (ℓ : Line E) (X : E) :
    toComplex o (Line.symmetry ℓ X) = g7_reflFactor o ℓ * conj (toComplex o X) +
      (toComplex o ℓ.base - g7_reflFactor o ℓ * conj (toComplex o ℓ.base)) := by
  have hX : Line.symmetry ℓ X = ℓ.base + Line.reflectVector ℓ.direction (X - ℓ.base) := rfl
  rw [hX, toComplex_add,
    g7_toComplex_reflectVector (o := o) (u := ℓ.direction) (v := X - ℓ.base) ℓ.direction_ne_zero,
    toComplex_sub, map_sub]
  simp only [g7_reflFactor]
  ring

theorem g7_toComplex_glide (ℓ : Line E) (w X : E) :
    toComplex o (Line.glide ℓ w X) = g7_reflFactor o ℓ * conj (toComplex o X) +
      (toComplex o ℓ.base - g7_reflFactor o ℓ * conj (toComplex o ℓ.base)) + toComplex o w := by
  rw [Line.glide, toComplex_add, g7_toComplex_symmetry]

theorem g7_norm_reflFactor (ℓ : Line E) : ‖g7_reflFactor o ℓ‖ = 1 := by
  have hd : toComplex o ℓ.direction ≠ 0 := fun h =>
    ℓ.direction_ne_zero ((toComplex_eq_zero o ℓ.direction).mp h)
  have hns : Complex.normSq (toComplex o ℓ.direction) ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
  have h1 : Complex.normSq (g7_reflFactor o ℓ) = 1 := by
    simp only [g7_reflFactor, Complex.normSq_div, map_pow, Complex.normSq_ofReal]
    field_simp
  have h2 : ‖g7_reflFactor o ℓ‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq, h1]
  nlinarith [norm_nonneg (g7_reflFactor o ℓ)]

theorem g7_exists_form_of_isImproper {f : E → E} (hf : IsImproperIsometry f) :
    ∃ (s β : ℂ), ‖s‖ = 1 ∧ ∀ X, toComplex o (f X) = s * conj (toComplex o X) + β := by
  obtain ⟨ℓ, w, hw, rfl⟩ := hf
  refine ⟨g7_reflFactor o ℓ, toComplex o ℓ.base - g7_reflFactor o ℓ * conj (toComplex o ℓ.base) +
    toComplex o w, g7_norm_reflFactor o ℓ, fun X => ?_⟩
  rw [g7_toComplex_glide]
  ring

theorem g7_isImproper_of_form {f : E → E} {s β : ℂ} (hs : ‖s‖ = 1)
    (hf : ∀ X, toComplex o (f X) = s * conj (toComplex o X) + β) : IsImproperIsometry f := by
  set u : Circle := ⟨s, by
    show s ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    simpa using hs⟩ with hu
  have hθ : (Circle.exp (Complex.arg u) : ℂ) = s := by
    have h2 : (Circle.exp (Complex.arg u) : ℂ) = (u : ℂ) :=
      congrArg (fun z : Circle => (z : ℂ)) (Circle.exp_arg u)
    simpa [hu] using h2
  set δ : ℂ := (Circle.exp (Complex.arg u / 2) : ℂ) with hδdef
  have hδ2 : δ ^ 2 = s := by
    have h1 : δ = Complex.exp ((Complex.arg u / 2) * Complex.I) := by
      rw [hδdef, Circle.coe_exp]
      push_cast
      ring_nf
    rw [h1, pow_two, ← Complex.exp_add]
    rw [show (Complex.arg u / 2) * Complex.I + (Complex.arg u / 2) * Complex.I =
      (Complex.arg u) * Complex.I by ring]
    rw [← Circle.coe_exp]
    exact hθ
  have hδnorm : ‖δ‖ = 1 := by
    rw [hδdef]
    simpa using Circle.norm_coe (Circle.exp (Complex.arg u / 2))
  have hδne : δ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hδnorm
    exact zero_ne_one hδnorm
  have hnsδ : (Complex.normSq δ : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hδnorm]
    norm_num
  have hδconj : δ * conj δ = 1 := by
    rw [Complex.mul_conj, hnsδ]
  have hδne' : ofComplex o δ ≠ 0 := by
    intro h
    have h2 := congrArg (toComplex o) h
    rw [toComplex_ofComplex, toComplex_zero] at h2
    exact hδne h2
  set ζ : ℂ := conj δ * β with hζdef
  have hβ : β = δ * ((ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I) := by
    rw [hζdef, Complex.re_add_im]
    rw [← mul_assoc, hδconj, one_mul]
  set η : ℝ := ζ.im with hηdef
  set α : ℝ := ζ.re with hαdef
  have hβ' : β = δ * ((α : ℂ) + (η : ℂ) * Complex.I) := by
    rw [hβ, hαdef, hηdef]
  have hδinv : conj δ = δ⁻¹ := (inv_eq_of_mul_eq_one_right hδconj).symm
  set b : ℂ := ((η : ℂ) / 2) * Complex.I * δ with hbdef
  have hconjb : conj b = -(((η : ℂ) / 2) * Complex.I * δ⁻¹) := by
    simp only [hbdef, map_mul, map_div₀, map_ofNat, Complex.conj_I, Complex.conj_ofReal, hδinv]
    ring
  have hkey : b - s * conj b + (α : ℂ) * δ = β := by
    rw [hβ', ← hδ2, hconjb, hbdef]
    field_simp
    ring
  refine ⟨⟨ofComplex o b, ofComplex o δ, hδne'⟩, ofComplex o ((α : ℂ) * δ), ⟨α, ?_⟩, ?_⟩
  · apply toComplex_injective o
    simp only [toComplex_smul, toComplex_ofComplex]
  · funext X
    apply toComplex_injective o
    rw [hf X, g7_toComplex_glide]
    have hrefl : g7_reflFactor o ⟨ofComplex o b, ofComplex o δ, hδne'⟩ = s := by
      simp only [g7_reflFactor, toComplex_ofComplex, hδ2, hnsδ, div_one]
    rw [hrefl]
    simp only [toComplex_ofComplex]
    rw [← hkey]
    ring

theorem g7_proper_form (O : E) {f : E → E} (hf : IsProperIsometry o O f) :
    ∃ (u d : ℂ), ‖u‖ = 1 ∧ ∀ X, toComplex o (f X) = d + toComplex o X * u := by
  obtain ⟨p, rfl⟩ := hf
  refine ⟨p.turn, toComplex o O + toComplex o p.displacement - toComplex o O * p.turn,
    Circle.norm_coe p.turn, fun X => ?_⟩
  rw [g7_proper_action_toComplex]
  ring

theorem g7_improper_comp_proper {O : E} {f g : E → E}
    (hf : IsProperIsometry o O f) (hg : IsImproperIsometry g) : IsImproperIsometry (f ∘ g) := by
  obtain ⟨u, d, hu, hf'⟩ := g7_proper_form o O hf
  obtain ⟨s, β, hs, hg'⟩ := g7_exists_form_of_isImproper o hg
  refine g7_isImproper_of_form o (s := s * u) (β := d + β * u) ?_ ?_
  · rw [norm_mul, hs, hu, one_mul]
  · intro X
    simp only [Function.comp_apply]
    rw [hf' (g X), hg' X]
    ring

theorem g7_improper_comp_of_proper {O : E} {f g : E → E}
    (hf : IsImproperIsometry f) (hg : IsProperIsometry o O g) : IsImproperIsometry (f ∘ g) := by
  obtain ⟨s, β, hs, hf'⟩ := g7_exists_form_of_isImproper o hf
  obtain ⟨u, d, hu, hg'⟩ := g7_proper_form o O hg
  refine g7_isImproper_of_form o (s := s * conj u) (β := s * conj d + β) ?_ ?_
  · rw [norm_mul, hs, RCLike.norm_conj, hu, one_mul]
  · intro X
    simp only [Function.comp_apply]
    rw [hf' (g X), hg' X, map_add, map_mul]
    ring

theorem g7_proper_comp_improper {O : E} {f g : E → E}
    (hf : IsImproperIsometry f) (hg : IsImproperIsometry g) : IsProperIsometry o O (f ∘ g) := by
  obtain ⟨s₁, β₁, hs₁, hf'⟩ := g7_exists_form_of_isImproper o hf
  obtain ⟨s₂, β₂, hs₂, hg'⟩ := g7_exists_form_of_isImproper o hg
  refine g7_isProper_of_toComplex_form (o := o) (O := O) (f := f ∘ g)
    (u := s₁ * conj s₂) (d := s₁ * conj β₂ + β₁) ?_ ?_
  · rw [norm_mul, hs₁, RCLike.norm_conj, hs₂, one_mul]
  · intro X
    simp only [Function.comp_apply]
    rw [hf' (g X), hg' X, map_add, map_mul, Complex.conj_conj]
    ring

theorem improper_isometry_closure (O : E) {f g : E → E}
    (hf : IsProperIsometry o O f) (hg : IsImproperIsometry g) :
    IsImproperIsometry (f ∘ g) ∧ IsImproperIsometry (g ∘ f) :=
  ⟨g7_improper_comp_proper o hf hg, g7_improper_comp_of_proper o hg hf⟩

theorem all_isometries_closed (O : E) {f g : E → E}
    (hf : IsProperIsometry o O f ∨ IsImproperIsometry f)
    (hg : IsProperIsometry o O g ∨ IsImproperIsometry g) :
    IsProperIsometry o O (f ∘ g) ∨ IsImproperIsometry (f ∘ g) := by
  rcases hf with hf | hf <;> rcases hg with hg | hg
  · exact Or.inl (proper_isometry_closure_comp o O hf hg)
  · exact Or.inr (g7_improper_comp_proper o hf hg)
  · exact Or.inr (g7_improper_comp_of_proper o hf hg)
  · exact Or.inl (g7_proper_comp_improper o hf hg)

/-! ### Classification of plane isometries -/

open scoped InnerProductSpace

theorem g7_isometry_inner_map {f : E → E} (hf : Isometry f) (h0 : f 0 = 0) (X Y : E) :
    ⟪f X, f Y⟫ = ⟪X, Y⟫ := by
  have hXY : ‖f X - f Y‖ = ‖X - Y‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm]
    exact hf.dist_eq X Y
  have hX : ‖f X‖ = ‖X‖ := by
    simpa [h0, dist_eq_norm] using hf.dist_eq X 0
  have hY : ‖f Y‖ = ‖Y‖ := by
    simpa [h0, dist_eq_norm] using hf.dist_eq Y 0
  have e1 := norm_sub_sq_real (f X) (f Y)
  have e2 := norm_sub_sq_real X Y
  rw [hXY, hX, hY] at e1
  linarith

theorem g7_isometry_add {f : E → E} (hf : Isometry f) (h0 : f 0 = 0) (X Y : E) :
    f (X + Y) = f X + f Y := by
  have hkey : ∀ Z : E, ⟪f (X + Y) - f X - f Y, f Z⟫ = 0 := by
    intro Z
    rw [inner_sub_left, inner_sub_left, g7_isometry_inner_map hf h0, g7_isometry_inner_map hf h0,
      g7_isometry_inner_map hf h0, inner_add_left]
    ring
  have hnorm : ‖f (X + Y) - f X - f Y‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_right, inner_sub_right, hkey, hkey, hkey]
    ring
  have hzero : f (X + Y) - f X - f Y = 0 := by
    have h1 : ‖f (X + Y) - f X - f Y‖ = 0 := by
      nlinarith [norm_nonneg (f (X + Y) - f X - f Y)]
    exact norm_eq_zero.mp h1
  calc f (X + Y) = f (X + Y) - f X - f Y + f X + f Y := by abel
    _ = f X + f Y := by rw [hzero]; abel

theorem g7_isometry_smul {f : E → E} (hf : Isometry f) (h0 : f 0 = 0) (r : ℝ) (X : E) :
    f (r • X) = r • f X := by
  have hkey : ∀ Z : E, ⟪f (r • X) - r • f X, f Z⟫ = 0 := by
    intro Z
    rw [inner_sub_left, g7_isometry_inner_map hf h0, real_inner_smul_left, real_inner_smul_left,
      ← g7_isometry_inner_map hf h0 X Z]
    ring
  have hnorm : ‖f (r • X) - r • f X‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_right, inner_smul_right, hkey, hkey]
    ring
  have hzero : f (r • X) - r • f X = 0 := by
    have h1 : ‖f (r • X) - r • f X‖ = 0 := by
      nlinarith [norm_nonneg (f (r • X) - r • f X)]
    exact norm_eq_zero.mp h1
  calc f (r • X) = f (r • X) - r • f X + r • f X := by abel
    _ = r • f X := by rw [hzero]; abel

theorem g7_complex_inner_re (x y : ℂ) : ⟪x, y⟫_ℝ = (x * conj y).re := by
  rw [real_inner_comm, Complex.inner]

theorem g7_complex_conj_eq_re_sub_im (z : ℂ) :
    conj z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
  rw [Complex.ext_iff]
  exact ⟨by simp, by simp⟩

theorem g7_complex_eq_or_eq_of_orthonormal {u w : ℂ} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (horth : ⟪w, u⟫_ℝ = 0) : w = Complex.I * u ∨ w = -Complex.I * u := by
  set t := u * conj w with ht
  have ht_re : t.re = 0 := by
    rw [g7_complex_inner_re] at horth
    have hce : conj (u * conj w) = w * conj u := by simp [mul_comm]
    rw [ht, ← horth, ← hce, Complex.conj_re]
  have ht_norm : ‖t‖ = 1 := by
    rw [ht, norm_mul, RCLike.norm_conj, hw, hu, one_mul]
  have hwconj : w * conj w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
    norm_num
  have ht_im : t.im = 1 ∨ t.im = -1 := by
    have hns : Complex.normSq t = 1 := by
      rw [Complex.normSq_eq_norm_sq, ht_norm]
      norm_num
    rw [Complex.normSq_apply, ht_re] at hns
    have : t.im * t.im = 1 := by linarith
    exact mul_self_eq_one_iff.mp this
  have hu_eq : u = t * w := by
    rw [ht, mul_assoc, mul_comm (conj w) w, hwconj, mul_one]
  have ht_eq : t = Complex.I ∨ t = -Complex.I := by
    rcases ht_im with him | him
    · left
      rw [Complex.ext_iff]
      exact ⟨by simp [ht_re], by simp [him]⟩
    · right
      rw [Complex.ext_iff]
      exact ⟨by simp [ht_re], by simp [him]⟩
  rcases ht_eq with htI | htI
  · right
    have h2 : u = Complex.I * w := by rw [hu_eq, htI]
    rw [h2]
    have h3 : Complex.I * (Complex.I * w) = -w := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    rw [neg_mul, h3, neg_neg]
  · left
    have h2 : u = -Complex.I * w := by rw [hu_eq, htI]
    rw [h2]
    have h3 : Complex.I * (-Complex.I * w) = w := by
      rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
    rw [h3]

theorem isometry_classification (O : E) (f : E → E) :
    Isometry f → (IsProperIsometry o O f ∨ IsImproperIsometry f) := by
  intro hf
  set g : E → E := fun X => f X - f 0 with hgdef
  have hg0 : g 0 = 0 := by simp [hgdef]
  have hg_iso : Isometry g := by
    rw [isometry_iff_dist_eq]
    intro X Y
    rw [dist_eq_norm, dist_eq_norm]
    have e : g X - g Y = f X - f Y := by simp only [hgdef]; abel
    rw [e, ← dist_eq_norm, ← dist_eq_norm]
    exact hf.dist_eq X Y
  have hadd := g7_isometry_add hg_iso hg0
  have hsmul := g7_isometry_smul hg_iso hg0
  have hinner := g7_isometry_inner_map hg_iso hg0
  have hfX : ∀ X : E, f X = f 0 + g X := by
    intro X; simp only [hgdef]; abel
  set h : ℂ → ℂ := fun z => toComplex o (g (ofComplex o z)) with hhdef
  have h_add : ∀ z w : ℂ, h (z + w) = h z + h w := by
    intro z w
    simp only [hhdef, ofComplex_add, hadd, toComplex_add]
  have h_smul : ∀ (r : ℝ) (z : ℂ), h (r • z) = r • h z := by
    intro r z
    simp only [hhdef, ofComplex_smul, hsmul, toComplex_smul]
    rw [Complex.real_smul]
  have h_inner : ∀ z w : ℂ, ⟪h z, h w⟫_ℝ = ⟪z, w⟫_ℝ := by
    intro z w
    rw [g7_complex_inner_re, g7_complex_inner_re]
    have h1 : ⟪g (ofComplex o z), g (ofComplex o w)⟫ = (h z * conj (h w)).re :=
      g7_inner_toComplex_re o _ _
    rw [hinner] at h1
    have h2 : ⟪ofComplex o z, ofComplex o w⟫ = (z * conj w).re := by
      rw [g7_inner_toComplex_re o (ofComplex o z) (ofComplex o w), toComplex_ofComplex,
        toComplex_ofComplex]
    rw [h2] at h1
    exact h1.symm
  set u : ℂ := h 1 with hudef
  set w₀ : ℂ := h Complex.I with hw₀def
  have hu_norm : ‖u‖ = 1 := by
    have h1 := h_inner 1 1
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
    have h2 : ‖(1 : ℂ)‖ = 1 := by norm_num
    rw [h2] at h1
    nlinarith [norm_nonneg u]
  have hw_norm : ‖w₀‖ = 1 := by
    have h1 := h_inner Complex.I Complex.I
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
    have h2 : ‖(Complex.I : ℂ)‖ = 1 := by norm_num
    rw [h2] at h1
    nlinarith [norm_nonneg w₀]
  have hu_orth : ⟪w₀, u⟫_ℝ = 0 := by
    show ⟪h Complex.I, h 1⟫_ℝ = 0
    have h1 := h_inner Complex.I 1
    rw [h1, g7_complex_inner_re]
    simp
  have hz_split : ∀ z : ℂ, h z = z.re • u + z.im • w₀ := by
    intro z
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one]
      exact (Complex.re_add_im z).symm
    rw [hz, h_add, h_smul, h_smul]
    simp [hudef, hw₀def]
  rcases g7_complex_eq_or_eq_of_orthonormal hu_norm hw_norm hu_orth with hwI | hwI
  · left
    refine g7_isProper_of_toComplex_form (o := o) (O := O) (f := f) (u := u) (d := toComplex o (f 0))
      hu_norm ?_
    intro X
    rw [hfX X, toComplex_add, add_left_cancel_iff]
    have h1 := hz_split (toComplex o X)
    simp only [hhdef] at h1
    rw [ofComplex_toComplex] at h1
    rw [h1, hwI, Complex.real_smul, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im (toComplex o X)]
    ring
  · right
    refine g7_isImproper_of_form (o := o) (f := f) (s := u) (β := toComplex o (f 0)) hu_norm ?_
    intro X
    rw [hfX X, toComplex_add, add_comm (u * conj (toComplex o X)), add_left_cancel_iff]
    have h1 := hz_split (toComplex o X)
    simp only [hhdef] at h1
    rw [ofComplex_toComplex] at h1
    rw [h1, hwI, Complex.real_smul, Complex.real_smul, g7_complex_conj_eq_re_sub_im]
    ring

end Group7Helpers

/-! ## 4. Symmetry insights about Morley's construction -/

/-- Unnamespaced alias for the triangle equilaterality predicate. -/
abbrev Equilateral (P Q R : E) : Prop := OrientedTriangle.Equilateral P Q R

namespace OrientedTriangle

variable {o : Orientation ℝ E (Fin 2)}

/-- The three side lines. -/
def AB (T : OrientedTriangle E o) : Line E where
  base := T.A
  direction := T.B - T.A
  direction_ne_zero := sub_ne_zero.mpr T.A_ne_B.symm
def BC (T : OrientedTriangle E o) : Line E where
  base := T.B
  direction := T.C - T.B
  direction_ne_zero := sub_ne_zero.mpr T.B_ne_C.symm
def CA (T : OrientedTriangle E o) : Line E where
  base := T.C
  direction := T.A - T.C
  direction_ne_zero := sub_ne_zero.mpr T.A_ne_C

/-- Equation (13). -/
def RA (T : OrientedTriangle E o) : E → E := rotation o T.A (2 * T.alpha)
def RB (T : OrientedTriangle E o) : E → E := rotation o T.B (2 * T.beta)
def RC (T : OrientedTriangle E o) : E → E := rotation o T.C (2 * T.gamma)

/-- Reversed side lines used in Theorem 2. -/
def BA (T : OrientedTriangle E o) : Line E where
  base := T.B
  direction := T.A - T.B
  direction_ne_zero := sub_ne_zero.mpr T.A_ne_B
def CB (T : OrientedTriangle E o) : Line E where
  base := T.C
  direction := T.B - T.C
  direction_ne_zero := sub_ne_zero.mpr T.B_ne_C

end OrientedTriangle


/-! ### Pure complex algebra -/

theorem conj_circle_exp (θ : ℝ) :
    conj ((Circle.exp θ : Circle) : ℂ) = ((Circle.exp θ : Circle)⁻¹ : Circle) := by
  rw [Circle.coe_inv_eq_conj]

theorem dirSq_mul_exp {a : ℂ} (ha : a ≠ 0) (θ : ℝ) :
    (a * (Circle.exp θ : Circle)) / conj (a * (Circle.exp θ : Circle))
      = a / conj a * ((Circle.exp (2 * θ) : Circle) : ℂ) := by
  rw [map_mul, conj_circle_exp, Circle.coe_inv]
  rw [show (2:ℝ) * θ = θ + θ by ring, Circle.exp_add, Circle.coe_mul]
  have he : ((Circle.exp θ : Circle) : ℂ) ≠ 0 := by simp
  field_simp

theorem dirSq_smul (a : ℂ) {r : ℝ} (hr : r ≠ 0) :
    ((r : ℂ) * a) / conj ((r : ℂ) * a) = a / conj a := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [map_mul, Complex.conj_ofReal]
  field_simp

theorem dirSq_neg (a : ℂ) : -a / conj (-a) = a / conj a := by
  simp

theorem complex_reflect_identity_aux {a b : ℂ} (ha : a ≠ 0) :
    ((2 * (a * conj b).re / (a * conj a).re : ℝ) : ℂ) * a - b = a / conj a * conj b := by
  have hca : conj a ≠ 0 := by simpa using ha
  have hreal : (a * conj a).im = 0 := by rw [Complex.mul_conj]; simp
  have hy : ((a * conj a).re : ℂ) = a * conj a := by
    conv_rhs => rw [← Complex.re_add_im (a * conj a)]
    rw [hreal, Complex.ofReal_zero, zero_mul, add_zero]
  have hy0 : (a * conj a).re ≠ 0 := by
    have h : (a * conj a).re = Complex.normSq a := by
      rw [Complex.mul_conj]; simp
    rw [h]
    exact (Complex.normSq_pos.mpr ha).ne'
  have hx : ((2 * (a * conj b).re : ℝ) : ℂ) = a * conj b + conj a * b := by
    rw [← Complex.add_conj]
    simp
  have hcomm : conj a * a = ((a * conj a).re : ℂ) := (mul_comm (conj a) a).trans hy.symm
  have step1 : conj a * (((2 * (a * conj b).re / (a * conj a).re : ℝ) : ℂ) * a)
      = ((2 * (a * conj b).re : ℝ) : ℂ) := by
    calc conj a * (((2 * (a * conj b).re / (a * conj a).re : ℝ) : ℂ) * a)
        = ((2 * (a * conj b).re / (a * conj a).re : ℝ) : ℂ) * (conj a * a) := by ring
      _ = ((2 * (a * conj b).re / (a * conj a).re : ℝ) : ℂ) * ((a * conj a).re : ℂ) := by
            rw [hcomm]
      _ = ((2 * (a * conj b).re : ℝ) : ℂ) := by
            rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hy0]
  have k1 : conj a * (((2 * (a * conj b).re / (a * conj a).re : ℝ) : ℂ) * a) - conj a * b
      = a * conj b := by rw [step1, hx]; ring
  have hdiv : conj a * (a / conj a) = a := by field_simp
  have k2 : conj a * (a / conj a * conj b) = a * conj b := by
    rw [← mul_assoc, hdiv]
  have hmain : conj a * (((2 * (a * conj b).re / (a * conj a).re : ℝ) : ℂ) * a - b)
      = conj a * (a / conj a * conj b) := by
    rw [mul_sub, k1, k2]
  exact mul_left_cancel₀ hca hmain
theorem complex_reflect_identity {a b : ℂ} (ha : a ≠ 0) :
    (2 : ℂ) * ((((a * conj b).re / (a * conj a).re : ℝ) : ℂ) * a) - b
      = a / conj a * conj b := by
  have h2 : (2 : ℂ) * ((((a * conj b).re / (a * conj a).re : ℝ)) : ℂ)
      = (((2 * (a * conj b).re / (a * conj a).re : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [← mul_assoc, h2]
  exact complex_reflect_identity_aux ha

/-! ### Complex coordinates of the plane -/

theorem m12_toComplex_e₁ (o : Orientation ℝ E (Fin 2)) : toComplex o (e₁ o) = 1 := by
  simp [toComplex, complexIsometryEquiv, e₁]

theorem m12_toComplex_e₂ (o : Orientation ℝ E (Fin 2)) : toComplex o (e₂ o) = Complex.I := by
  simp [toComplex, complexIsometryEquiv, e₂]

theorem toComplex_eq_re_add_im (o : Orientation ℝ E (Fin 2)) (v : E) :
    toComplex o v = ⟪e₁ o, v⟫ + ⟪e₂ o, v⟫ * Complex.I := by
  have h := OrthonormalBasis.equiv_apply (positiveBasis o) Complex.orthonormalBasisOneI
    (Equiv.refl (Fin 2)) v
  rw [toComplex, complexIsometryEquiv, h]
  simp [Fin.sum_univ_two, OrthonormalBasis.repr_apply_apply, e₁, e₂, real_inner_comm]

theorem complexIsometryEquiv_orientation (o : Orientation ℝ E (Fin 2)) :
    Orientation.map (Fin 2) (complexIsometryEquiv o).toLinearEquiv o = Complex.orientation := by
  have hmap := Module.Basis.orientation_map (positiveBasis o).toBasis
    (complexIsometryEquiv o).toLinearEquiv
  have hb : (positiveBasis o).toBasis.orientation = o :=
    o.finOrthonormalBasis_orientation (by norm_num) Fact.out
  rw [hb] at hmap
  rw [← hmap]
  have hbas : (positiveBasis o).toBasis.map (complexIsometryEquiv o).toLinearEquiv
      = Complex.basisOneI := by
    ext i
    fin_cases i <;>
      simp [e₁, e₂, toComplex, complexIsometryEquiv]
  rw [hbas]
  rfl

theorem orientedArea_eq_complex (o : Orientation ℝ E (Fin 2)) (v w : E) :
    orientedArea o v w =
      (toComplex o v).re * (toComplex o w).im - (toComplex o v).im * (toComplex o w).re := by
  have h := Orientation.areaForm_map_complex o (complexIsometryEquiv o)
    (complexIsometryEquiv_orientation o) v w
  change o.areaForm v w = _
  rw [h]
  simp [Complex.mul_im, Complex.conj_re, Complex.conj_im, toComplex]
  ring

/-! ### Reflection in complex coordinates -/

theorem m12_toComplex_parallelComponent (o : Orientation ℝ E (Fin 2)) {u : E} (hu : u ≠ 0) (v : E) :
    toComplex o (parallelComponent u v) =
      ((⟪v, u⟫ / ⟪u, u⟫ : ℝ) : ℂ) * toComplex o u := by
  rw [parallelComponent, toComplex_smul]

theorem toComplex_reflectVector (o : Orientation ℝ E (Fin 2)) {u : E} (hu : u ≠ 0) (v : E) :
    toComplex o (Line.reflectVector u v) =
      toComplex o u / conj (toComplex o u) * conj (toComplex o v) := by
  have ha : toComplex o u ≠ 0 := by simpa using hu
  have hinner1 : ⟪v, u⟫ = (toComplex o u * conj (toComplex o v)).re := by
    rw [← Complex.inner]
    exact ((complexIsometryEquiv o).inner_map_map v u).symm
  have hinner2 : ⟪u, u⟫ = (toComplex o u * conj (toComplex o u)).re := by
    rw [← Complex.inner]
    exact ((complexIsometryEquiv o).inner_map_map u u).symm
  have href : Line.reflectVector u v = (2 : ℝ) • parallelComponent u v - v := by
    simp only [Line.reflectVector, perpComponent]
    module
  rw [href, toComplex_sub, toComplex_smul, m12_toComplex_parallelComponent o hu v, hinner1, hinner2]
  exact complex_reflect_identity ha

/-! ### Base independence and composition of two reflections -/

theorem conj_conj' (z : ℂ) : conj (conj z) = z := by simp

theorem dirSq_mul_conj {a : ℂ} (ha : a ≠ 0) :
    (a / conj a) * conj (a / conj a) = 1 := by
  have hca : conj a ≠ 0 := by simpa using ha
  have h1 : conj (a / conj a) = conj a / a := by simp
  rw [h1]
  field_simp


theorem reflectVector_self {u : E} : Line.reflectVector u u = u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [Line.reflectVector, parallelComponent, perpComponent]
  · have h : (‖u‖ ^ 2 / ‖u‖ ^ 2 : ℝ) = 1 := div_self (by positivity)
    simp [Line.reflectVector, parallelComponent, perpComponent, h]

theorem reflectVector_smul (u : E) (r : ℝ) (v : E) :
    Line.reflectVector u (r • v) = r • Line.reflectVector u v := by
  simp only [Line.reflectVector, perpComponent, parallelComponent_smul, smul_sub]

theorem reflectVector_add (u v w : E) :
    Line.reflectVector u (v + w) = Line.reflectVector u v + Line.reflectVector u w := by
  simp only [Line.reflectVector, perpComponent_add, parallelComponent_add]
  module

theorem reflectVector_sub (u v w : E) :
    Line.reflectVector u (v - w) = Line.reflectVector u v - Line.reflectVector u w := by
  simp only [Line.reflectVector, perpComponent_sub, parallelComponent_sub]
  module

theorem reflectVector_involutive (o : Orientation ℝ E (Fin 2)) {u : E} (hu : u ≠ 0) (v : E) :
    Line.reflectVector u (Line.reflectVector u v) = v := by
  apply toComplex_injective o
  have ha : toComplex o u ≠ 0 := by simpa using hu
  rw [toComplex_reflectVector o hu, toComplex_reflectVector o hu, map_mul, conj_conj']
  rw [show toComplex o u / conj (toComplex o u)
        * (conj (toComplex o u / conj (toComplex o u)) * toComplex o v)
      = (toComplex o u / conj (toComplex o u))
        * conj (toComplex o u / conj (toComplex o u)) * toComplex o v by ring,
    dirSq_mul_conj ha, one_mul]

theorem symmetry_eq_base {ℓ : Line E} {P : E} (hP : ℓ.mem P) (X : E) :
    Line.symmetry ℓ X = P + Line.reflectVector ℓ.direction (X - P) := by
  obtain ⟨t, rfl⟩ := hP
  have hX : X - (ℓ.base + t • ℓ.direction) = (X - ℓ.base) - t • ℓ.direction := by abel
  simp only [Line.symmetry, hX, reflectVector_sub, reflectVector_smul, reflectVector_self]
  abel

theorem symmetry_comp_eq_rotation {ℓ ℓ' : Line E} {P : E}
    (hP : ℓ.mem P) (hP' : ℓ'.mem P) {φ : ℝ}
    (hm : toComplex o ℓ'.direction / conj (toComplex o ℓ'.direction) =
      toComplex o ℓ.direction / conj (toComplex o ℓ.direction) * (Circle.exp (2 * φ) : ℂ)) :
    Line.symmetry ℓ' ∘ Line.symmetry ℓ = rotation o P (2 * φ) := by
  funext X
  apply toComplex_injective o
  simp only [Function.comp_apply, toComplex_rotation]
  rw [symmetry_eq_base hP', symmetry_eq_base hP]
  have hsub : P + Line.reflectVector ℓ.direction (X - P) - P
      = Line.reflectVector ℓ.direction (X - P) := by abel
  rw [hsub, toComplex_add, toComplex_reflectVector o ℓ'.direction_ne_zero,
    toComplex_reflectVector o ℓ.direction_ne_zero, toComplex_sub, map_mul, conj_conj']
  have hkey : toComplex o ℓ'.direction / conj (toComplex o ℓ'.direction)
        * conj (toComplex o ℓ.direction / conj (toComplex o ℓ.direction))
      = (Circle.exp (2 * φ) : ℂ) := by
    rw [hm]
    have h := dirSq_mul_conj (a := toComplex o ℓ.direction) (by simpa using ℓ.direction_ne_zero)
    rw [show toComplex o ℓ.direction / conj (toComplex o ℓ.direction)
          * (Circle.exp (2 * φ) : ℂ)
          * conj (toComplex o ℓ.direction / conj (toComplex o ℓ.direction))
        = (Circle.exp (2 * φ) : ℂ)
          * (toComplex o ℓ.direction / conj (toComplex o ℓ.direction)
            * conj (toComplex o ℓ.direction / conj (toComplex o ℓ.direction))) by ring,
      h, mul_one]
  calc toComplex o P + toComplex o ℓ'.direction / conj (toComplex o ℓ'.direction)
        * (conj (toComplex o ℓ.direction / conj (toComplex o ℓ.direction))
          * (toComplex o X - toComplex o P))
      = toComplex o P + (toComplex o ℓ'.direction / conj (toComplex o ℓ'.direction)
          * conj (toComplex o ℓ.direction / conj (toComplex o ℓ.direction)))
          * (toComplex o X - toComplex o P) := by ring
    _ = toComplex o P + (toComplex o X - toComplex o P) * (Circle.exp (2 * φ) : ℂ) := by
          rw [hkey]; ring

/-! ### Direction squares of rotated vectors -/

theorem dirSq_rotateVector (o : Orientation ℝ E (Fin 2)) {u : E} (hu : u ≠ 0) (θ : ℝ) :
    toComplex o (rotateVector o u θ) / conj (toComplex o (rotateVector o u θ))
      = toComplex o u / conj (toComplex o u) * (Circle.exp (2 * θ) : ℂ) := by
  rw [toComplex_rotateVector]
  exact dirSq_mul_exp (by simpa using hu) θ

namespace OrientedTriangle

variable {o : Orientation ℝ E (Fin 2)}

/-- The point `A` lies on the line `AB`. -/
theorem A_mem_AB (T : OrientedTriangle E o) : T.AB.mem T.A := ⟨0, by simp [AB]⟩
theorem A_mem_AZ (T : OrientedTriangle E o) : T.AZ.mem T.A := ⟨0, by simp [AZ]⟩
theorem A_mem_AY (T : OrientedTriangle E o) : T.AY.mem T.A := ⟨0, by simp [AY]⟩
theorem A_mem_CA (T : OrientedTriangle E o) : T.CA.mem T.A := by
  refine ⟨1, ?_⟩
  simp [CA]
theorem B_mem_BC (T : OrientedTriangle E o) : T.BC.mem T.B := ⟨0, by simp [BC]⟩
theorem B_mem_BX (T : OrientedTriangle E o) : T.BX.mem T.B := ⟨0, by simp [BX]⟩
theorem B_mem_BZ (T : OrientedTriangle E o) : T.BZ.mem T.B := ⟨0, by simp [BZ]⟩
theorem B_mem_BA (T : OrientedTriangle E o) : T.BA.mem T.B := ⟨0, by simp [BA]⟩
theorem C_mem_CA (T : OrientedTriangle E o) : T.CA.mem T.C := ⟨0, by simp [CA]⟩
theorem C_mem_CY (T : OrientedTriangle E o) : T.CY.mem T.C := ⟨0, by simp [CY]⟩
theorem C_mem_CX (T : OrientedTriangle E o) : T.CX.mem T.C := ⟨0, by simp [CX]⟩
theorem C_mem_CB (T : OrientedTriangle E o) : T.CB.mem T.C := ⟨0, by simp [CB]⟩

/-- (AZ.direction)²-ratio relative to AB. -/
theorem dirSq_AZ (T : OrientedTriangle E o) :
    toComplex o T.AZ.direction / conj (toComplex o T.AZ.direction)
      = toComplex o T.AB.direction / conj (toComplex o T.AB.direction)
        * (Circle.exp (2 * T.alpha) : ℂ) := by
  have := dirSq_rotateVector o (T.AB.direction_ne_zero) T.alpha
  simpa [AZ, AB] using this

theorem dirSq_BX (T : OrientedTriangle E o) :
    toComplex o T.BX.direction / conj (toComplex o T.BX.direction)
      = toComplex o T.BC.direction / conj (toComplex o T.BC.direction)
        * (Circle.exp (2 * T.beta) : ℂ) := by
  have := dirSq_rotateVector o (T.BC.direction_ne_zero) T.beta
  simpa [BX, BC] using this

theorem dirSq_CY (T : OrientedTriangle E o) :
    toComplex o T.CY.direction / conj (toComplex o T.CY.direction)
      = toComplex o T.CA.direction / conj (toComplex o T.CA.direction)
        * (Circle.exp (2 * T.gamma) : ℂ) := by
  have := dirSq_rotateVector o (T.CA.direction_ne_zero) T.gamma
  simpa [CY, CA] using this

/-- Theorem 2 (1). -/
theorem RA_eq_AZ_AB (T : OrientedTriangle E o) :
    T.RA = Line.symmetry T.AZ ∘ Line.symmetry T.AB := by
  rw [show Line.symmetry T.AZ ∘ Line.symmetry T.AB = rotation o T.A (2 * T.alpha) from
    symmetry_comp_eq_rotation o (T.A_mem_AB) (T.A_mem_AZ) (dirSq_AZ T)]
  rfl

theorem RB_eq_BX_BC (T : OrientedTriangle E o) :
    T.RB = Line.symmetry T.BX ∘ Line.symmetry T.BC := by
  rw [show Line.symmetry T.BX ∘ Line.symmetry T.BC = rotation o T.B (2 * T.beta) from
    symmetry_comp_eq_rotation o (T.B_mem_BC) (T.B_mem_BX) (dirSq_BX T)]
  rfl

theorem RC_eq_CY_CA (T : OrientedTriangle E o) :
    T.RC = Line.symmetry T.CY ∘ Line.symmetry T.CA := by
  rw [show Line.symmetry T.CY ∘ Line.symmetry T.CA = rotation o T.C (2 * T.gamma) from
    symmetry_comp_eq_rotation o (T.C_mem_CA) (T.C_mem_CY) (dirSq_CY T)]
  rfl

end OrientedTriangle


/-! ### Polar form: the direction square of a triangle side -/

theorem circle_exp_arg {z : ℂ} (hz : z ≠ 0) :
    ((Circle.exp (Complex.arg z) : Circle) : ℂ) = z / ‖z‖ := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  rw [Circle.coe_exp, eq_div_iff (by exact_mod_cast norm_ne_zero_iff.mpr hz), mul_comm]
  exact h

theorem inner_eq_re_conj_mul (o : Orientation ℝ E (Fin 2)) (u w : E) :
    ⟪u, w⟫ = (conj (toComplex o u) * toComplex o w).re := by
  rw [← (complexIsometryEquiv o).inner_map_map u w, Complex.inner, mul_comm]
  rfl

theorem arg_conj_mul_eq_angle (o : Orientation ℝ E (Fin 2)) {u w : E}
    (hu : u ≠ 0) (hw : w ≠ 0) (h : 0 < orientedArea o u w) :
    Complex.arg (conj (toComplex o u) * toComplex o w) = InnerProductGeometry.angle u w := by
  have ha : toComplex o u ≠ 0 := by simpa using hu
  have hb : toComplex o w ≠ 0 := by simpa using hw
  have him : 0 < (conj (toComplex o u) * toComplex o w).im := by
    have hA := orientedArea_eq_complex o u w
    rw [hA] at h
    simpa [Complex.mul_im, Complex.conj_re, Complex.conj_im, sub_eq_add_neg] using h
  have hz : conj (toComplex o u) * toComplex o w ≠ 0 := by
    intro h0
    rw [h0] at him
    exact lt_irrefl 0 him
  have h1 : InnerProductGeometry.angle u w ∈ Set.Icc 0 Real.pi :=
    ⟨InnerProductGeometry.angle_nonneg u w, InnerProductGeometry.angle_le_pi u w⟩
  have harg0 : 0 ≤ Complex.arg (conj (toComplex o u) * toComplex o w) :=
    Complex.arg_nonneg_iff.mpr him.le
  have hargpi : Complex.arg (conj (toComplex o u) * toComplex o w) < Real.pi := by
    rw [Complex.arg_lt_pi_iff]
    exact Or.inr (fun h0 => absurd h0 him.ne')
  have hcos : Real.cos (InnerProductGeometry.angle u w)
      = Real.cos (Complex.arg (conj (toComplex o u) * toComplex o w)) := by
    rw [InnerProductGeometry.cos_angle, Complex.cos_arg hz, inner_eq_re_conj_mul o u w]
    have hnorm : ‖conj (toComplex o u) * toComplex o w‖ = ‖u‖ * ‖w‖ := by
      rw [norm_mul, Complex.norm_conj, toComplex_norm, toComplex_norm]
    rw [hnorm]
  exact (Real.injOn_cos h1 ⟨harg0, hargpi.le⟩ hcos).symm

theorem toComplex_eq_smul_mul_circle_exp (o : Orientation ℝ E (Fin 2)) {u w : E}
    (hu : u ≠ 0) (hw : w ≠ 0) (h : 0 < orientedArea o u w) :
    toComplex o w = (‖w‖ / ‖u‖ : ℝ)
      * (toComplex o u * (Circle.exp (Complex.arg (conj (toComplex o u) * toComplex o w)) : ℂ)) := by
  have ha : toComplex o u ≠ 0 := by simpa using hu
  have hb : toComplex o w ≠ 0 := by simpa using hw
  have him : 0 < (conj (toComplex o u) * toComplex o w).im := by
    have hA := orientedArea_eq_complex o u w
    rw [hA] at h
    simpa [Complex.mul_im, Complex.conj_re, Complex.conj_im, sub_eq_add_neg] using h
  have hz : conj (toComplex o u) * toComplex o w ≠ 0 := by
    intro h0
    rw [h0] at him
    exact lt_irrefl 0 him
  have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hnorm : ‖conj (toComplex o u) * toComplex o w‖ = ‖u‖ * ‖w‖ := by
    rw [norm_mul, Complex.norm_conj, toComplex_norm, toComplex_norm]
  have hconj : toComplex o u * conj (toComplex o u) = ((‖u‖ : ℂ)) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, toComplex_norm]
    push_cast
    ring
  have huc : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast hun
  have hwc : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hwn
  rw [circle_exp_arg hz, hnorm]
  rw [show (‖w‖ / ‖u‖ : ℝ) * (toComplex o u * (conj (toComplex o u) * toComplex o w / ((‖u‖ * ‖w‖ : ℝ) : ℂ)))
      = ((‖w‖ / ‖u‖ : ℝ) : ℂ) * (toComplex o u * conj (toComplex o u)) * toComplex o w
        / ((‖u‖ * ‖w‖ : ℝ) : ℂ) by ring]
  rw [hconj]
  push_cast
  field_simp

theorem dirSq_eq_dirSq_mul_exp_of_pos (o : Orientation ℝ E (Fin 2)) {u w : E}
    (hu : u ≠ 0) (hw : w ≠ 0) (h : 0 < orientedArea o u w) :
    toComplex o w / conj (toComplex o w)
      = toComplex o u / conj (toComplex o u)
        * (Circle.exp (2 * InnerProductGeometry.angle u w) : ℂ) := by
  have ha : toComplex o u ≠ 0 := by simpa using hu
  have hpolar := toComplex_eq_smul_mul_circle_exp o hu hw h
  have harg := arg_conj_mul_eq_angle o hu hw h
  conv_lhs => rw [hpolar]
  rw [dirSq_smul _ (by positivity : (‖w‖ / ‖u‖ : ℝ) ≠ 0)]
  rw [dirSq_mul_exp ha]
  rw [harg]

/-! ### Oriented areas of cyclic permutations -/

theorem areaForm_add_self (o : Orientation ℝ E (Fin 2)) (x y : E) :
    orientedArea o x (y + x) = orientedArea o x y := by
  show o.areaForm x (y + x) = o.areaForm x y
  rw [map_add, Orientation.areaForm_apply_self, add_zero]

theorem orientedArea_cyclic (o : Orientation ℝ E (Fin 2)) (a b c : E) :
    orientedArea o (b - a) (c - a) = orientedArea o (c - b) (a - b) := by
  have h1 : c - a = (c - b) + (b - a) := by abel
  have h2 : a - b = -(b - a) := by abel
  show o.areaForm (b - a) (c - a) = o.areaForm (c - b) (a - b)
  rw [h1, h2, map_add, Orientation.areaForm_apply_self, add_zero,
    LinearMap.map_neg (o.areaForm (c - b)) (b - a), Orientation.areaForm_swap o (c - b) (b - a),
    neg_neg]

theorem orientedArea_cyclic' (o : Orientation ℝ E (Fin 2)) (a b c : E) :
    orientedArea o (b - a) (c - a) = orientedArea o (a - c) (b - c) := by
  rw [orientedArea_cyclic o a b c, orientedArea_cyclic o b c a]

namespace OrientedTriangle

variable {o : Orientation ℝ E (Fin 2)}

theorem angle_BAC_eq (T : OrientedTriangle E o) :
    InnerProductGeometry.angle (T.B - T.A) (T.C - T.A) = 3 * T.alpha := by
  have hα : 3 * T.alpha = EuclideanGeometry.angle T.B T.A T.C := by
    rw [alpha]; field_simp
  rw [hα]
  rfl

theorem angle_CBA_eq (T : OrientedTriangle E o) :
    InnerProductGeometry.angle (T.C - T.B) (T.A - T.B) = 3 * T.beta := by
  have hβ : 3 * T.beta = EuclideanGeometry.angle T.C T.B T.A := by
    rw [beta]; field_simp
  rw [hβ]
  rfl

theorem angle_ACB_eq (T : OrientedTriangle E o) :
    InnerProductGeometry.angle (T.A - T.C) (T.B - T.C) = 3 * T.gamma := by
  have hγ : 3 * T.gamma = EuclideanGeometry.angle T.A T.C T.B := by
    rw [gamma]; field_simp
  rw [hγ]
  rfl

theorem orientedArea_BC_BA_pos (T : OrientedTriangle E o) :
    0 < orientedArea o (T.C - T.B) (T.A - T.B) := by
  rw [← orientedArea_cyclic o T.A T.B T.C]
  exact T.positive

theorem orientedArea_AC_BC_pos (T : OrientedTriangle E o) :
    0 < orientedArea o (T.A - T.C) (T.B - T.C) := by
  rw [← orientedArea_cyclic' o T.A T.B T.C]
  exact T.positive

end OrientedTriangle

namespace OrientedTriangle

variable {o : Orientation ℝ E (Fin 2)}

theorem sub_ne_zero_A_B (T : OrientedTriangle E o) : T.B - T.A ≠ 0 :=
  sub_ne_zero.mpr T.A_ne_B.symm
theorem sub_ne_zero_B_C (T : OrientedTriangle E o) : T.C - T.B ≠ 0 :=
  sub_ne_zero.mpr T.B_ne_C.symm
theorem sub_ne_zero_A_C (T : OrientedTriangle E o) : T.C - T.A ≠ 0 :=
  sub_ne_zero.mpr T.A_ne_C.symm

theorem dirSq_toComplex_neg (o : Orientation ℝ E (Fin 2)) (v : E) :
    toComplex o (-v) / conj (toComplex o (-v)) = toComplex o v / conj (toComplex o v) := by
  rw [toComplex_neg]
  exact dirSq_neg _

theorem dirSq_CA_AB (T : OrientedTriangle E o) :
    toComplex o T.CA.direction / conj (toComplex o T.CA.direction)
      = toComplex o T.AB.direction / conj (toComplex o T.AB.direction)
        * (Circle.exp (2 * (3 * T.alpha)) : ℂ) := by
  have hgeo := dirSq_eq_dirSq_mul_exp_of_pos o (u := T.B - T.A) (w := T.C - T.A)
    (T.sub_ne_zero_A_B) (T.sub_ne_zero_A_C) T.positive
  rw [angle_BAC_eq T] at hgeo
  have hCA : toComplex o T.CA.direction / conj (toComplex o T.CA.direction)
      = toComplex o (T.C - T.A) / conj (toComplex o (T.C - T.A)) := by
    have h : T.A - T.C = -(T.C - T.A) := by abel
    simp only [CA, h]
    exact dirSq_toComplex_neg o (T.C - T.A)
  rw [hCA, hgeo, AB]

theorem dirSq_CB_CA (T : OrientedTriangle E o) :
    toComplex o T.CB.direction / conj (toComplex o T.CB.direction)
      = toComplex o T.CA.direction / conj (toComplex o T.CA.direction)
        * (Circle.exp (2 * (3 * T.gamma)) : ℂ) := by
  have hgeo := dirSq_eq_dirSq_mul_exp_of_pos o (u := T.A - T.C) (w := T.B - T.C)
    (sub_ne_zero.mpr T.A_ne_C) (sub_ne_zero.mpr T.B_ne_C) (orientedArea_AC_BC_pos T)
  rw [angle_ACB_eq T] at hgeo
  simp only [CB, CA]
  rw [hgeo]

theorem dirSq_BA_AB (T : OrientedTriangle E o) :
    toComplex o T.BA.direction / conj (toComplex o T.BA.direction)
      = toComplex o T.AB.direction / conj (toComplex o T.AB.direction) := by
  have h : T.A - T.B = -(T.B - T.A) := by abel
  simp only [BA, AB, h]
  exact dirSq_toComplex_neg o (T.B - T.A)

end OrientedTriangle

namespace OrientedTriangle

variable {o : Orientation ℝ E (Fin 2)}

theorem B_mem_AB (T : OrientedTriangle E o) : T.AB.mem T.B := by
  refine ⟨1, ?_⟩
  simp [AB]
theorem C_mem_BC (T : OrientedTriangle E o) : T.BC.mem T.C := by
  refine ⟨1, ?_⟩
  simp [BC]

theorem dirSq_BA_BC (T : OrientedTriangle E o) :
    toComplex o T.BA.direction / conj (toComplex o T.BA.direction)
      = toComplex o T.BC.direction / conj (toComplex o T.BC.direction)
        * (Circle.exp (2 * (3 * T.beta)) : ℂ) := by
  have hgeo := dirSq_eq_dirSq_mul_exp_of_pos o (u := T.C - T.B) (w := T.A - T.B)
    (T.sub_ne_zero_B_C) (sub_ne_zero.mpr T.A_ne_B) (orientedArea_BC_BA_pos T)
  rw [angle_CBA_eq T] at hgeo
  simp only [BA, BC]
  exact hgeo

theorem dirSq_BA_BZ (T : OrientedTriangle E o) :
    toComplex o T.BA.direction / conj (toComplex o T.BA.direction)
      = toComplex o T.BZ.direction / conj (toComplex o T.BZ.direction)
        * (Circle.exp (2 * T.beta) : ℂ) := by
  have hgeo := T.dirSq_BA_BC
  have hBZ : toComplex o T.BZ.direction / conj (toComplex o T.BZ.direction)
      = toComplex o (T.C - T.B) / conj (toComplex o (T.C - T.B))
        * (Circle.exp (2 * (2 * T.beta)) : ℂ) := by
    have h := dirSq_rotateVector o (T.BC.direction_ne_zero) (2 * T.beta)
    simpa [BZ, BC] using h
  have hBC : toComplex o T.BC.direction / conj (toComplex o T.BC.direction)
      = toComplex o (T.C - T.B) / conj (toComplex o (T.C - T.B)) := by
    simp only [BC]
  rw [hgeo, hBC, hBZ]
  rw [show (2:ℝ) * (3 * T.beta) = 2 * (2 * T.beta) + 2 * T.beta by ring, Circle.exp_add,
    Circle.coe_mul]
  ring

/-- Theorem 2 (1), second form. -/
theorem RA_eq_CA_AY (T : OrientedTriangle E o) :
    T.RA = Line.symmetry T.CA ∘ Line.symmetry T.AY := by
  rw [show Line.symmetry T.CA ∘ Line.symmetry T.AY = rotation o T.A (2 * T.alpha) from
    symmetry_comp_eq_rotation o (T.A_mem_AY) (T.A_mem_CA)
      (by
        have h := dirSq_CA_AB T
        have hAY : toComplex o T.AY.direction / conj (toComplex o T.AY.direction)
            = toComplex o T.AB.direction / conj (toComplex o T.AB.direction)
              * (Circle.exp (2 * (2 * T.alpha)) : ℂ) := by
          have h2 := dirSq_rotateVector o (T.AB.direction_ne_zero) (2 * T.alpha)
          simpa [AY, AB] using h2
        rw [h, hAY]
        rw [show (2:ℝ) * (3 * T.alpha) = 2 * (2 * T.alpha) + 2 * T.alpha by ring,
          Circle.exp_add, Circle.coe_mul]
        ring)]
  rfl

theorem RB_eq_BA_BZ (T : OrientedTriangle E o) :
    T.RB = Line.symmetry T.BA ∘ Line.symmetry T.BZ := by
  rw [show Line.symmetry T.BA ∘ Line.symmetry T.BZ = rotation o T.B (2 * T.beta) from
    symmetry_comp_eq_rotation o (T.B_mem_BZ) (T.B_mem_BA) (dirSq_BA_BZ T)]
  rfl

theorem RC_eq_CB_CX (T : OrientedTriangle E o) :
    T.RC = Line.symmetry T.CB ∘ Line.symmetry T.CX := by
  rw [show Line.symmetry T.CB ∘ Line.symmetry T.CX = rotation o T.C (2 * T.gamma) from
    symmetry_comp_eq_rotation o (T.C_mem_CX) (T.C_mem_CB)
      (by
        have h := dirSq_CB_CA T
        have hCX : toComplex o T.CX.direction / conj (toComplex o T.CX.direction)
            = toComplex o T.CA.direction / conj (toComplex o T.CA.direction)
              * (Circle.exp (2 * (2 * T.gamma)) : ℂ) := by
          have h2 := dirSq_rotateVector o (T.CA.direction_ne_zero) (2 * T.gamma)
          simpa [CX, CA] using h2
        rw [h, hCX]
        rw [show (2:ℝ) * (3 * T.gamma) = 2 * (2 * T.gamma) + 2 * T.gamma by ring,
          Circle.exp_add, Circle.coe_mul]
        ring)]
  rfl

end OrientedTriangle

theorem reflectVector_neg (o : Orientation ℝ E (Fin 2)) {u : E} (hu : u ≠ 0) (v : E) :
    Line.reflectVector (-u) v = Line.reflectVector u v := by
  apply toComplex_injective o
  have hu' : -u ≠ 0 := neg_ne_zero.mpr hu
  rw [toComplex_reflectVector o hu', toComplex_reflectVector o hu, toComplex_neg, map_neg,
    neg_div_neg_eq]

theorem symmetry_sq_aux (o : Orientation ℝ E (Fin 2)) (ℓ : Line E) :
    Line.symmetry ℓ ∘ Line.symmetry ℓ = id := by
  funext X
  rw [Function.comp_apply, symmetry_eq_base (ℓ := ℓ) (P := ℓ.base) ⟨0, by simp⟩ X]
  rw [symmetry_eq_base (ℓ := ℓ) (P := ℓ.base) ⟨0, by simp⟩
    (ℓ.base + Line.reflectVector ℓ.direction (X - ℓ.base))]
  have h : ℓ.base + Line.reflectVector ℓ.direction (X - ℓ.base) - ℓ.base
      = Line.reflectVector ℓ.direction (X - ℓ.base) := by abel
  rw [h, reflectVector_involutive o ℓ.direction_ne_zero, id]
  abel

theorem rotation_comp_rotation (o : Orientation ℝ E (Fin 2)) (P : E) (φ ψ : ℝ) :
    rotation o P φ ∘ rotation o P ψ = rotation o P (φ + ψ) := by
  funext X
  apply toComplex_injective o
  simp only [Function.comp_apply, toComplex_rotation, Circle.exp_add, Circle.coe_mul]
  ring

theorem rotation_iterate_three (o : Orientation ℝ E (Fin 2)) (P : E) (φ : ℝ) :
    (rotation o P φ)^[3] = rotation o P (3 * φ) := by
  have h : (rotation o P φ)^[3] = rotation o P φ ∘ rotation o P φ ∘ rotation o P φ := by
    funext X
    simp [Function.iterate_succ, Function.iterate_zero, Function.comp_apply]
  rw [h, show rotation o P φ ∘ rotation o P φ = rotation o P (φ + φ) from
      rotation_comp_rotation o P φ φ,
    show rotation o P φ ∘ rotation o P (φ + φ) = rotation o P (φ + (φ + φ)) from
      rotation_comp_rotation o P φ (φ + φ),
    show φ + (φ + φ) = 3 * φ by ring]

namespace OrientedTriangle

variable {o : Orientation ℝ E (Fin 2)}

theorem symmetry_BA_eq (T : OrientedTriangle E o) :
    Line.symmetry T.BA = Line.symmetry T.AB := by
  funext X
  rw [symmetry_eq_base (ℓ := T.BA) (T.B_mem_BA) X,
    symmetry_eq_base (ℓ := T.AB) (T.B_mem_AB) X]
  have h : T.BA.direction = -T.AB.direction := by
    simp only [BA, AB]; abel
  rw [h]
  exact congrArg (fun Y => T.B + Y) (reflectVector_neg o T.AB.direction_ne_zero (X - T.B))

theorem symmetry_CB_eq (T : OrientedTriangle E o) :
    Line.symmetry T.CB = Line.symmetry T.BC := by
  funext X
  rw [symmetry_eq_base (ℓ := T.CB) (T.C_mem_CB) X,
    symmetry_eq_base (ℓ := T.BC) (T.C_mem_BC) X]
  have h : T.CB.direction = -T.BC.direction := by
    simp only [CB, BC]; abel
  rw [h]
  exact congrArg (fun Y => T.C + Y) (reflectVector_neg o T.BC.direction_ne_zero (X - T.C))

/-- Theorem 2 (3). -/
theorem RA_cubed (T : OrientedTriangle E o) :
    T.RA^[3] = Line.symmetry T.CA ∘ Line.symmetry T.AB := by
  have hRA : (T.RA^[3]) = rotation o T.A (3 * (2 * T.alpha)) := by
    show (rotation o T.A (2 * T.alpha))^[3] = rotation o T.A (3 * (2 * T.alpha))
    rw [rotation_iterate_three]
  rw [hRA]
  rw [show Line.symmetry T.CA ∘ Line.symmetry T.AB = rotation o T.A (2 * (3 * T.alpha)) from
    symmetry_comp_eq_rotation o (T.A_mem_AB) (T.A_mem_CA) (dirSq_CA_AB T)]
  congr 1
  ring

theorem RB_cubed (T : OrientedTriangle E o) :
    T.RB^[3] = Line.symmetry T.BA ∘ Line.symmetry T.BC := by
  have hRB : (T.RB^[3]) = rotation o T.B (3 * (2 * T.beta)) := by
    show (rotation o T.B (2 * T.beta))^[3] = rotation o T.B (3 * (2 * T.beta))
    rw [rotation_iterate_three]
  rw [hRB]
  rw [show Line.symmetry T.BA ∘ Line.symmetry T.BC = rotation o T.B (2 * (3 * T.beta)) from
    symmetry_comp_eq_rotation o (T.B_mem_BC) (T.B_mem_BA) (dirSq_BA_BC T)]
  congr 1
  ring

theorem RC_cubed (T : OrientedTriangle E o) :
    T.RC^[3] = Line.symmetry T.CB ∘ Line.symmetry T.CA := by
  have hRC : (T.RC^[3]) = rotation o T.C (3 * (2 * T.gamma)) := by
    show (rotation o T.C (2 * T.gamma))^[3] = rotation o T.C (3 * (2 * T.gamma))
    rw [rotation_iterate_three]
  rw [hRC]
  rw [show Line.symmetry T.CB ∘ Line.symmetry T.CA = rotation o T.C (2 * (3 * T.gamma)) from
    symmetry_comp_eq_rotation o (T.C_mem_CA) (T.C_mem_CB) (dirSq_CB_CA T)]
  congr 1
  ring

/-- Theorem 2 (4). -/
theorem rotation_cubes_identity (T : OrientedTriangle E o) :
    T.RA^[3] ∘ T.RB^[3] ∘ T.RC^[3] = id := by
  rw [RA_cubed, RB_cubed, RC_cubed, symmetry_BA_eq, symmetry_CB_eq]
  funext X
  simp only [Function.comp_apply]
  rw [show Line.symmetry T.BC (Line.symmetry T.BC (Line.symmetry T.CA X))
        = Line.symmetry T.CA X from congrFun (symmetry_sq_aux o T.BC) _,
    show Line.symmetry T.AB (Line.symmetry T.AB (Line.symmetry T.CA X))
        = Line.symmetry T.CA X from congrFun (symmetry_sq_aux o T.AB) _,
    show Line.symmetry T.CA (Line.symmetry T.CA X) = X from congrFun (symmetry_sq_aux o T.CA) X]
  rfl

end OrientedTriangle

namespace OrientedTriangle

variable {o : Orientation ℝ E (Fin 2)}

/-- `exp (iθ) ≠ 1` for `0 < θ < π`. -/
theorem circle_exp_ne_one_of_pos_of_lt_pi {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    (Circle.exp θ : ℂ) ≠ 1 := by
  intro h
  have h1 : Circle.exp θ = 1 := Subtype.ext (by simpa using h)
  rw [Circle.exp_eq_one] at h1
  obtain ⟨n, hn⟩ := h1
  have hpos : (0:ℝ) < (n:ℝ) := by
    rcases lt_trichotomy (n:ℝ) 0 with hneg | hzero | hpos
    · nlinarith [Real.pi_pos]
    · exfalso
      rw [hzero] at hn
      simp at hn
      linarith
    · exact hpos
  have hpos' : (0:ℤ) < n := by exact_mod_cast hpos
  have hn1 : (1:ℤ) ≤ n := by omega
  have h2 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hθ : 2 * Real.pi ≤ θ := by
    rw [hn]
    nlinarith [Real.pi_pos]
  linarith [Real.pi_pos]

theorem alpha_nonneg (T : OrientedTriangle E o) : 0 ≤ T.alpha := by
  rw [alpha]
  exact div_nonneg (EuclideanGeometry.angle_nonneg _ _ _) (by norm_num)

theorem beta_pos (T : OrientedTriangle E o) : 0 < T.beta := by
  rw [beta]
  exact div_pos (EuclideanGeometry.angle_pos_of_not_collinear
    (by
      rw [show ({T.C, T.B, T.A} : Set E) = {T.A, T.B, T.C} from by ext w; simp; tauto]
      exact T.noncollinear)) (by norm_num)

theorem gamma_pos (T : OrientedTriangle E o) : 0 < T.gamma := by
  rw [gamma]
  exact div_pos (EuclideanGeometry.angle_pos_of_not_collinear
    (by
      rw [show ({T.A, T.C, T.B} : Set E) = {T.A, T.B, T.C} from by ext w; simp; tauto]
      exact T.noncollinear)) (by norm_num)

theorem alpha_lt (T : OrientedTriangle E o) : T.alpha < Real.pi / 3 := by
  rw [alpha, show Real.pi / 3 = Real.pi / (3:ℝ) by norm_num]
  exact div_lt_div_of_pos_right (EuclideanGeometry.angle_lt_pi_of_not_collinear
    (by
      rw [show ({T.B, T.A, T.C} : Set E) = {T.A, T.B, T.C} from by ext w; simp; tauto]
      exact T.noncollinear)) (by norm_num)

theorem beta_lt (T : OrientedTriangle E o) : T.beta < Real.pi / 3 := by
  rw [beta, show Real.pi / 3 = Real.pi / (3:ℝ) by norm_num]
  exact div_lt_div_of_pos_right (EuclideanGeometry.angle_lt_pi_of_not_collinear
    (by
      rw [show ({T.C, T.B, T.A} : Set E) = {T.A, T.B, T.C} from by ext w; simp; tauto]
      exact T.noncollinear)) (by norm_num)

theorem gamma_lt (T : OrientedTriangle E o) : T.gamma < Real.pi / 3 := by
  rw [gamma, show Real.pi / 3 = Real.pi / (3:ℝ) by norm_num]
  exact div_lt_div_of_pos_right (EuclideanGeometry.angle_lt_pi_of_not_collinear
    (by
      rw [show ({T.A, T.C, T.B} : Set E) = {T.A, T.B, T.C} from by ext x; simp; tauto]
      exact T.noncollinear)) (by norm_num)

theorem beta_gamma_bounds (T : OrientedTriangle E o) :
    0 < 2 * (T.beta + T.gamma) ∧ 2 * (T.beta + T.gamma) < Real.pi := by
  have hsum := T.angle_sum
  have hb := T.beta_pos
  have hg := T.gamma_pos
  have ha := T.alpha_nonneg
  have halt := T.alpha_lt
  constructor <;> linarith

theorem alpha_gamma_bounds (T : OrientedTriangle E o) :
    0 < 2 * (T.alpha + T.gamma) ∧ 2 * (T.alpha + T.gamma) < Real.pi := by
  have hsum := T.angle_sum
  have ha := T.alpha_nonneg
  have hb := T.beta_pos
  have hblt := T.beta_lt
  constructor <;> linarith

theorem alpha_beta_bounds (T : OrientedTriangle E o) :
    0 < 2 * (T.alpha + T.beta) ∧ 2 * (T.alpha + T.beta) < Real.pi := by
  have hsum := T.angle_sum
  have ha := T.alpha_nonneg
  have hg := T.gamma_pos
  have hglt := T.gamma_lt
  constructor <;> linarith

/-- A general nonzero denominator. -/
theorem one_sub_exp_mul_ne_zero_of {φ ψ : ℝ} (h0 : 0 < φ + ψ) (hπ : φ + ψ < Real.pi) :
    (1 - (Circle.exp φ : ℂ) * Circle.exp ψ) ≠ 0 := by
  have hne : (Circle.exp φ : ℂ) * Circle.exp ψ ≠ 1 := by
    rw [← Circle.coe_mul, ← Circle.exp_add]
    exact circle_exp_ne_one_of_pos_of_lt_pi h0 hπ
  intro h
  exact hne (by rw [eq_comm, ← sub_eq_zero]; exact h)

/-- The denominator appearing in `Theorem 3` is nonzero. -/
theorem one_sub_exp_mul_ne_zero (T : OrientedTriangle E o) :
    (1 - (Circle.exp (2 * T.beta) : ℂ) * Circle.exp (2 * T.gamma)) ≠ 0 := by
  obtain ⟨h0, hπ⟩ := T.beta_gamma_bounds
  exact one_sub_exp_mul_ne_zero_of (φ := 2 * T.beta) (ψ := 2 * T.gamma)
    (by linarith) (by linarith)

end OrientedTriangle



namespace OrientedTriangle

variable {o : Orientation ℝ E (Fin 2)}

/-- Corrected `X`: the Morley vertex is the fixed point of `RB ∘ RC`, i.e.
`rotationFixedPoint o C B (2γ) (2β)`, not `rotationFixedPoint o B C (2β) (2γ)`. -/
def Xc (T : OrientedTriangle E o) : E := rotationFixedPoint o T.C T.B (2 * T.gamma) (2 * T.beta)
def Yc (T : OrientedTriangle E o) : E := rotationFixedPoint o T.A T.C (2 * T.alpha) (2 * T.gamma)
def Zc (T : OrientedTriangle E o) : E := rotationFixedPoint o T.B T.A (2 * T.beta) (2 * T.alpha)

/-- Theorem 2 (2), corrected form: with the fixed point of `RB ∘ RC`. -/
theorem RB_RC_corrected (T : OrientedTriangle E o) :
    T.RB ∘ T.RC = rotation o T.Xc (2 * (Real.pi / 3 - T.alpha)) := by
  have h := rotation_rotation_rotation o (P := T.C) (P' := T.B) (φ := 2 * T.gamma)
    (φ' := 2 * T.beta) (by rw [mul_comm]; exact one_sub_exp_mul_ne_zero T)
  have h' : T.RB ∘ T.RC = rotation o T.B (2 * T.beta) ∘ rotation o T.C (2 * T.gamma) := rfl
  rw [h', h, show 2 * T.gamma + 2 * T.beta = 2 * (Real.pi / 3 - T.alpha) by
    have := T.angle_sum; linarith]
  rfl

theorem RC_RA_corrected (T : OrientedTriangle E o) :
    T.RC ∘ T.RA = rotation o T.Yc (2 * (Real.pi / 3 - T.beta)) := by
  obtain ⟨hb0, hbπ⟩ := T.alpha_gamma_bounds
  have h := rotation_rotation_rotation o (P := T.A) (P' := T.C) (φ := 2 * T.alpha)
    (φ' := 2 * T.gamma) (one_sub_exp_mul_ne_zero_of (φ := 2 * T.alpha) (ψ := 2 * T.gamma)
      (by linarith) (by linarith))
  have h' : T.RC ∘ T.RA = rotation o T.C (2 * T.gamma) ∘ rotation o T.A (2 * T.alpha) := rfl
  rw [h', h, show 2 * T.alpha + 2 * T.gamma = 2 * (Real.pi / 3 - T.beta) by
    have := T.angle_sum; linarith]
  rfl

theorem RA_RB_corrected (T : OrientedTriangle E o) :
    T.RA ∘ T.RB = rotation o T.Zc (2 * (Real.pi / 3 - T.gamma)) := by
  obtain ⟨hc0, hcπ⟩ := T.alpha_beta_bounds
  have h := rotation_rotation_rotation o (P := T.B) (P' := T.A) (φ := 2 * T.beta)
    (φ' := 2 * T.alpha) (by rw [mul_comm]; exact
      one_sub_exp_mul_ne_zero_of (φ := 2 * T.alpha) (ψ := 2 * T.beta) (by linarith) (by linarith))
  have h' : T.RA ∘ T.RB = rotation o T.A (2 * T.alpha) ∘ rotation o T.B (2 * T.beta) := rfl
  rw [h', h, show 2 * T.beta + 2 * T.alpha = 2 * (Real.pi / 3 - T.gamma) by
    have := T.angle_sum; linarith]
  rfl

/-- Theorem 2 (2). -/
theorem RB_RC (T : OrientedTriangle E o) :
    T.RB ∘ T.RC = rotation o T.X (2 * (Real.pi / 3 - T.alpha)) := by
  exact RB_RC_corrected T

theorem RC_RA (T : OrientedTriangle E o) :
    T.RC ∘ T.RA = rotation o T.Y (2 * (Real.pi / 3 - T.beta)) := by
  exact RC_RA_corrected T

theorem RA_RB (T : OrientedTriangle E o) :
    T.RA ∘ T.RB = rotation o T.Z (2 * (Real.pi / 3 - T.gamma)) := by
  exact RA_RB_corrected T

/-- The three unit multipliers of Corollary 1. -/
def uA (T : OrientedTriangle E o) : Circle := Circle.exp (2 * T.alpha)
def uB (T : OrientedTriangle E o) : Circle := Circle.exp (2 * T.beta)
def uC (T : OrientedTriangle E o) : Circle := Circle.exp (2 * T.gamma)

/-! ### Morley coordinates: Corollary 1 of Xambó-Descamps, *Wessel's Algebra and Morley's
Theorem*, with complete proofs (no `sorry`, no new axioms). -/

/-! ### m3: elementary complex helpers -/

theorem m3_coe_exp_eq (θ : ℝ) :
    (Circle.exp θ : ℂ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I]

theorem m3_exp_mul_exp (x y : ℝ) :
    (Circle.exp x : ℂ) * Circle.exp y = Circle.exp (x + y) := by
  rw [← Circle.coe_mul, Circle.exp_add]

theorem m3_exp_two_add (θ ψ : ℝ) :
    (Circle.exp (2 * θ) : ℂ) * Circle.exp (2 * ψ) = Circle.exp (2 * (θ + ψ)) := by
  rw [m3_exp_mul_exp, show 2 * θ + 2 * ψ = 2 * (θ + ψ) from by ring]

theorem m3_exp_split (θ ψ : ℝ) :
    (Circle.exp (θ + ψ) : ℂ) = Circle.exp θ * Circle.exp ψ :=
  (m3_exp_mul_exp θ ψ).symm

theorem m3_exp_neg_mul (ψ : ℝ) : (Circle.exp (-ψ) : ℂ) * Circle.exp ψ = 1 := by
  rw [m3_exp_mul_exp, show -ψ + ψ = 0 from by ring, Circle.exp_zero, Circle.coe_one]

theorem m3_exp_inv (ψ : ℝ) : (Circle.exp (-ψ) : ℂ) = (Circle.exp ψ : ℂ)⁻¹ := by
  rw [Circle.exp_neg, Circle.coe_inv]

theorem m3_exp_double_sub (θ : ℝ) :
    (Circle.exp (2 * θ) : ℂ) * (Circle.exp θ : ℂ)⁻¹ = Circle.exp θ := by
  rw [← m3_exp_inv θ, m3_exp_mul_exp, show 2 * θ + -θ = θ from by ring]

theorem m3_one_sub_exp_two (θ : ℝ) :
    (1 - (Circle.exp (2 * θ) : ℂ)) = (-2 * Complex.I * (Real.sin θ : ℂ)) * Circle.exp θ := by
  rw [Circle.coe_exp, Circle.coe_exp, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re,
      Complex.neg_im, mul_zero, sub_zero, zero_add, add_zero, zero_sub, neg_zero]
  · rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  · rw [Real.sin_two_mul]
    ring

theorem m3_one_sub_exp_two_ne (θ : ℝ) (h : Real.sin θ ≠ 0) :
    (1 - (Circle.exp (2 * θ) : ℂ)) ≠ 0 := by
  rw [m3_one_sub_exp_two]
  intro hh
  rcases mul_eq_zero.mp hh with h1 | h2
  · rcases mul_eq_zero.mp h1 with h3 | h3
    · norm_num at h3
    · exact h (Complex.ofReal_eq_zero.mp h3)
  · exact Circle.coe_ne_zero _ h2

theorem m3_sin_complex_ne (θ ψ : ℝ) (h : Real.sin (θ + ψ) ≠ 0) :
    Complex.sin ((θ : ℂ) + (ψ : ℂ)) ≠ 0 := by
  rw [← Complex.ofReal_add, ← Complex.ofReal_sin, ne_eq, Complex.ofReal_eq_zero]
  exact h

/-- `(1 - e^{2iθ})/(1 - e^{2iθ}e^{2iψ}) = (sin θ / sin (θ+ψ)) e^{-iψ}`. -/
theorem m3_ratio_eq (θ ψ : ℝ) (h : Real.sin (θ + ψ) ≠ 0) :
    ((1 - (Circle.exp (2 * θ) : ℂ)) / (1 - (Circle.exp (2 * θ) : ℂ) * Circle.exp (2 * ψ)))
      = ((Real.sin θ / Real.sin (θ + ψ) : ℝ) : ℂ) * Circle.exp (-ψ) := by
  have hden : (1 - (Circle.exp (2 * θ) : ℂ) * Circle.exp (2 * ψ))
      = (-2 * Complex.I * (Real.sin (θ + ψ) : ℂ)) *
        ((Circle.exp θ : ℂ) * Circle.exp ψ) := by
    rw [m3_exp_two_add, m3_one_sub_exp_two, m3_exp_split]
  have hsinC : (-2 * Complex.I * (Real.sin (θ + ψ) : ℂ)) ≠ 0 := by
    intro hh
    rcases mul_eq_zero.mp hh with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h3
      · norm_num at h3
      · exact Complex.I_ne_zero h3
    · exact h (Complex.ofReal_eq_zero.mp h2)
  have hden0 : (1 - (Circle.exp (2 * θ) : ℂ) * Circle.exp (2 * ψ)) ≠ 0 := by
    rw [hden]
    exact mul_ne_zero hsinC (mul_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _))
  rw [m3_one_sub_exp_two, m3_exp_inv, div_eq_iff hden0, hden]
  push_cast
  field_simp [m3_sin_complex_ne θ ψ h]

/-- `(1 - e^{2iθ})/(1 - e^{2iθ}e^{2iψ}) - 1 = -(sin ψ / sin (θ+ψ)) e^{iθ}`. -/
theorem m3_ratio_sub (θ ψ : ℝ) (h : Real.sin (θ + ψ) ≠ 0) :
    (1 - (Circle.exp (2 * θ) : ℂ)) / (1 - (Circle.exp (2 * θ) : ℂ) * Circle.exp (2 * ψ)) - 1
      = -(((Real.sin ψ / Real.sin (θ + ψ) : ℝ) : ℂ) * Circle.exp θ) := by
  have hden : (1 - (Circle.exp (2 * θ) : ℂ) * Circle.exp (2 * ψ))
      = (-2 * Complex.I * (Real.sin (θ + ψ) : ℂ)) *
        ((Circle.exp θ : ℂ) * Circle.exp ψ) := by
    rw [m3_exp_two_add, m3_one_sub_exp_two, m3_exp_split]
  have hden0 : (1 - (Circle.exp (2 * θ) : ℂ) * Circle.exp (2 * ψ)) ≠ 0 := by
    rw [hden]
    refine mul_ne_zero ?_ (mul_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _))
    intro hh
    rcases mul_eq_zero.mp hh with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h3
      · norm_num at h3
      · exact Complex.I_ne_zero h3
    · exact h (Complex.ofReal_eq_zero.mp h2)
  have h' : Real.sin (ψ + θ) ≠ 0 := by rw [add_comm]; exact h
  have hs : Real.sin (ψ + θ) = Real.sin (θ + ψ) := by rw [add_comm]
  have hrw : (1 - (Circle.exp (2 * θ) : ℂ)) /
        (1 - (Circle.exp (2 * θ) : ℂ) * Circle.exp (2 * ψ))
      = 1 - (Circle.exp (2 * θ) : ℂ) *
        ((1 - (Circle.exp (2 * ψ) : ℂ)) /
          (1 - (Circle.exp (2 * ψ) : ℂ) * Circle.exp (2 * θ))) := by
    field_simp
    ring
  rw [hrw, m3_ratio_eq ψ θ h', hs, m3_exp_inv θ]
  linear_combination (-(↑(Real.sin ψ / Real.sin (θ + ψ)) : ℂ)) * m3_exp_double_sub θ

/-! ### m3: positivity of the trisected angles -/

theorem m3_not_collinear_perm {T : OrientedTriangle E o} {S : Set E}
    (hS : S = ({T.A, T.B, T.C} : Set E)) : ¬Collinear ℝ S := hS ▸ T.noncollinear

theorem m3_alpha_pos (T : OrientedTriangle E o) : 0 < T.alpha := by
  have hs : ({T.B, T.A, T.C} : Set E) = {T.A, T.B, T.C} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have h := EuclideanGeometry.angle_pos_of_not_collinear (m3_not_collinear_perm hs)
  simp only [alpha]
  linarith

theorem m3_beta_pos (T : OrientedTriangle E o) : 0 < T.beta := by
  have hs : ({T.C, T.B, T.A} : Set E) = {T.A, T.B, T.C} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have h := EuclideanGeometry.angle_pos_of_not_collinear (m3_not_collinear_perm hs)
  simp only [beta]
  linarith

theorem m3_gamma_pos (T : OrientedTriangle E o) : 0 < T.gamma := by
  have hs : ({T.A, T.C, T.B} : Set E) = {T.A, T.B, T.C} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have h := EuclideanGeometry.angle_pos_of_not_collinear (m3_not_collinear_perm hs)
  simp only [gamma]
  linarith

theorem m3_beta_add_gamma_lt_pi (T : OrientedTriangle E o) : T.beta + T.gamma < Real.pi := by
  have h := T.angle_sum
  have ha := m3_alpha_pos T
  have hp := Real.pi_pos
  linarith

theorem m3_gamma_add_alpha_lt_pi (T : OrientedTriangle E o) : T.gamma + T.alpha < Real.pi := by
  have h := T.angle_sum
  have hb := m3_beta_pos T
  have hp := Real.pi_pos
  linarith

theorem m3_alpha_add_beta_lt_pi (T : OrientedTriangle E o) : T.alpha + T.beta < Real.pi := by
  have h := T.angle_sum
  have hg := m3_gamma_pos T
  have hp := Real.pi_pos
  linarith

theorem m3_beta_add_gamma_pos (T : OrientedTriangle E o) : 0 < T.beta + T.gamma := by
  have h1 := m3_beta_pos T
  have h2 := m3_gamma_pos T
  linarith

theorem m3_gamma_add_alpha_pos (T : OrientedTriangle E o) : 0 < T.gamma + T.alpha := by
  have h1 := m3_gamma_pos T
  have h2 := m3_alpha_pos T
  linarith

theorem m3_alpha_add_beta_pos (T : OrientedTriangle E o) : 0 < T.alpha + T.beta := by
  have h1 := m3_alpha_pos T
  have h2 := m3_beta_pos T
  linarith

theorem m3_sin_beta_add_gamma_pos (T : OrientedTriangle E o) :
    0 < Real.sin (T.beta + T.gamma) :=
  Real.sin_pos_of_pos_of_lt_pi (m3_beta_add_gamma_pos T) (m3_beta_add_gamma_lt_pi T)

theorem m3_sin_gamma_add_alpha_pos (T : OrientedTriangle E o) :
    0 < Real.sin (T.gamma + T.alpha) :=
  Real.sin_pos_of_pos_of_lt_pi (m3_gamma_add_alpha_pos T) (m3_gamma_add_alpha_lt_pi T)

theorem m3_sin_alpha_add_beta_pos (T : OrientedTriangle E o) :
    0 < Real.sin (T.alpha + T.beta) :=
  Real.sin_pos_of_pos_of_lt_pi (m3_alpha_add_beta_pos T) (m3_alpha_add_beta_lt_pi T)

/-! ### m3: Corollary 1, the three coordinates of `X` -/

/-- The first expression for `X` in Corollary 1. -/
theorem X_first (T : OrientedTriangle E o) :
    T.X = T.C + ofComplex o (toComplex o (T.B - T.C) *
      ((1 - T.uB : ℂ) / (1 - (T.uB : ℂ) * T.uC))) := by
  simp [X, rotationFixedPoint, uB, uC, mul_comm]

/-- The auxiliary exponential calculation in Corollary 1. -/
theorem one_sub_uB (T : OrientedTriangle E o) :
    (1 - T.uB : ℂ) = (-2 * Complex.I * Real.sin T.beta) * Circle.exp T.beta := by
  simp only [uB]
  exact m3_one_sub_exp_two T.beta

/-- The second expression for `X` in Corollary 1. -/
theorem X_second (T : OrientedTriangle E o) :
    T.X = T.C + (Real.sin T.beta / Real.sin (T.beta + T.gamma)) •
      rotateVector o (T.B - T.C) (-T.gamma) := by
  have hsin : Real.sin (T.beta + T.gamma) ≠ 0 := ne_of_gt (m3_sin_beta_add_gamma_pos T)
  apply toComplex_injective o
  rw [X_first]
  simp only [toComplex_add, toComplex_ofComplex, toComplex_smul, toComplex_rotateVector, uB, uC]
  rw [← Complex.real_smul, m3_ratio_eq T.beta T.gamma hsin, Complex.real_smul]
  ring

/-- The third expression for `X` in Corollary 1. -/
theorem X_third (T : OrientedTriangle E o) :
    T.X = T.B + (Real.sin T.gamma / Real.sin (T.beta + T.gamma)) •
      rotateVector o (T.C - T.B) T.beta := by
  have hsin : Real.sin (T.beta + T.gamma) ≠ 0 := ne_of_gt (m3_sin_beta_add_gamma_pos T)
  apply toComplex_injective o
  rw [X_first]
  simp only [toComplex_add, toComplex_ofComplex, toComplex_smul, toComplex_rotateVector,
    toComplex_sub, uB, uC]
  rw [← Complex.real_smul]
  have key : (toComplex o T.B - toComplex o T.C) *
      ((1 - (Circle.exp (2 * T.beta) : ℂ)) /
        (1 - (Circle.exp (2 * T.beta) : ℂ) * Circle.exp (2 * T.gamma)))
      = (toComplex o T.B - toComplex o T.C) +
        (toComplex o T.B - toComplex o T.C) *
          ((1 - (Circle.exp (2 * T.beta) : ℂ)) /
            (1 - (Circle.exp (2 * T.beta) : ℂ) * Circle.exp (2 * T.gamma)) - 1) := by
    ring
  rw [key, m3_ratio_sub T.beta T.gamma hsin, Complex.real_smul]
  ring


/-! ### m3: Corollary 1, the three coordinates of `Y` and `Z` -/

theorem Y_first (T : OrientedTriangle E o) :
    T.Y = T.A + ofComplex o (toComplex o (T.C - T.A) *
      ((1 - T.uC : ℂ) / (1 - (T.uC : ℂ) * T.uA))) := by
  simp [Y, rotationFixedPoint, uA, uC, mul_comm]

theorem Y_second (T : OrientedTriangle E o) :
    T.Y = T.A + (Real.sin T.gamma / Real.sin (T.gamma + T.alpha)) •
      rotateVector o (T.C - T.A) (-T.alpha) := by
  have hsin : Real.sin (T.gamma + T.alpha) ≠ 0 := ne_of_gt (m3_sin_gamma_add_alpha_pos T)
  apply toComplex_injective o
  rw [Y_first]
  simp only [toComplex_add, toComplex_ofComplex, toComplex_smul, toComplex_rotateVector, uA, uC]
  rw [← Complex.real_smul, m3_ratio_eq T.gamma T.alpha hsin, Complex.real_smul]
  ring

theorem Y_third (T : OrientedTriangle E o) :
    T.Y = T.C + (Real.sin T.alpha / Real.sin (T.gamma + T.alpha)) •
      rotateVector o (T.A - T.C) T.gamma := by
  have hsin : Real.sin (T.gamma + T.alpha) ≠ 0 := ne_of_gt (m3_sin_gamma_add_alpha_pos T)
  apply toComplex_injective o
  rw [Y_first]
  simp only [toComplex_add, toComplex_ofComplex, toComplex_smul, toComplex_rotateVector,
    toComplex_sub, uA, uC]
  rw [← Complex.real_smul]
  have key : (toComplex o T.C - toComplex o T.A) *
      ((1 - (Circle.exp (2 * T.gamma) : ℂ)) /
        (1 - (Circle.exp (2 * T.gamma) : ℂ) * Circle.exp (2 * T.alpha)))
      = (toComplex o T.C - toComplex o T.A) +
        (toComplex o T.C - toComplex o T.A) *
          ((1 - (Circle.exp (2 * T.gamma) : ℂ)) /
            (1 - (Circle.exp (2 * T.gamma) : ℂ) * Circle.exp (2 * T.alpha)) - 1) := by
    ring
  rw [key, m3_ratio_sub T.gamma T.alpha hsin, Complex.real_smul]
  ring

theorem Z_first (T : OrientedTriangle E o) :
    T.Z = T.B + ofComplex o (toComplex o (T.A - T.B) *
      ((1 - T.uA : ℂ) / (1 - (T.uA : ℂ) * T.uB))) := by
  simp [Z, rotationFixedPoint, uA, uB, mul_comm]

theorem Z_second (T : OrientedTriangle E o) :
    T.Z = T.B + (Real.sin T.alpha / Real.sin (T.alpha + T.beta)) •
      rotateVector o (T.A - T.B) (-T.beta) := by
  have hsin : Real.sin (T.alpha + T.beta) ≠ 0 := ne_of_gt (m3_sin_alpha_add_beta_pos T)
  apply toComplex_injective o
  rw [Z_first]
  simp only [toComplex_add, toComplex_ofComplex, toComplex_smul, toComplex_rotateVector, uA, uB]
  rw [← Complex.real_smul, m3_ratio_eq T.alpha T.beta hsin, Complex.real_smul]
  ring

theorem Z_third (T : OrientedTriangle E o) :
    T.Z = T.A + (Real.sin T.beta / Real.sin (T.alpha + T.beta)) •
      rotateVector o (T.B - T.A) T.alpha := by
  have hsin : Real.sin (T.alpha + T.beta) ≠ 0 := ne_of_gt (m3_sin_alpha_add_beta_pos T)
  apply toComplex_injective o
  rw [Z_first]
  simp only [toComplex_add, toComplex_ofComplex, toComplex_smul, toComplex_rotateVector,
    toComplex_sub, uA, uB]
  rw [← Complex.real_smul]
  have key : (toComplex o T.A - toComplex o T.B) *
      ((1 - (Circle.exp (2 * T.alpha) : ℂ)) /
        (1 - (Circle.exp (2 * T.alpha) : ℂ) * Circle.exp (2 * T.beta)))
      = (toComplex o T.A - toComplex o T.B) +
        (toComplex o T.A - toComplex o T.B) *
          ((1 - (Circle.exp (2 * T.alpha) : ℂ)) /
            (1 - (Circle.exp (2 * T.alpha) : ℂ) * Circle.exp (2 * T.beta)) - 1) := by
    ring
  rw [key, m3_ratio_sub T.alpha T.beta hsin, Complex.real_smul]
  ring

theorem m3_toComplex_eq_coord (v : E) :
    toComplex o v = (⟪e₁ o, v⟫ : ℂ) + (⟪e₂ o, v⟫ : ℂ) * Complex.I := by
  conv_lhs => rw [wm_eq_smul_e1_add_smul_e2 (o := o) v]
  rw [toComplex_add, toComplex_smul, toComplex_smul, wm_toComplex_e1, wm_toComplex_e2]
  ring

theorem m3_area_e1_e2 : o.areaForm (e₁ o) (e₂ o) = 1 := by
  rw [Orientation.areaForm_to_volumeForm,
    Orientation.volumeForm_robust o (positiveBasis o) (by simp [positiveBasis])]
  have hfam : (![e₁ o, e₂ o] : Fin 2 → E) = fun i => positiveBasis o i := by
    funext i
    fin_cases i <;> rfl
  rw [hfam]
  simpa using (positiveBasis o).toBasis.det_self

theorem m3_areaForm_eq_im (v w : E) :
    orientedArea o v w = (conj (toComplex o v) * toComplex o w).im := by
  have hpos : o.areaForm (e₁ o) (e₂ o) = 1 := m3_area_e1_e2 (o := o)
  have he2e1 : o.areaForm (e₂ o) (e₁ o) = -1 := by
    rw [Orientation.areaForm_swap, hpos]
  have he1e1 : o.areaForm (e₁ o) (e₁ o) = 0 := Orientation.areaForm_apply_self o (e₁ o)
  have he2e2 : o.areaForm (e₂ o) (e₂ o) = 0 := Orientation.areaForm_apply_self o (e₂ o)
  have hL : orientedArea o v w =
      ⟪e₁ o, v⟫ * ⟪e₂ o, w⟫ - ⟪e₂ o, v⟫ * ⟪e₁ o, w⟫ := by
    conv_lhs => rw [wm_eq_smul_e1_add_smul_e2 (o := o) v, wm_eq_smul_e1_add_smul_e2 (o := o) w]
    simp only [orientedArea, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hpos,
      he2e1, he1e1, he2e2, smul_eq_mul]
    ring
  have hcv : conj (toComplex o v) =
      (⟪e₁ o, v⟫ : ℂ) - (⟪e₂ o, v⟫ : ℂ) * Complex.I := by
    rw [m3_toComplex_eq_coord (o := o) v]
    apply Complex.ext <;> simp
  have hR : (conj (toComplex o v) * toComplex o w).im =
      ⟪e₁ o, v⟫ * ⟪e₂ o, w⟫ - ⟪e₂ o, v⟫ * ⟪e₁ o, w⟫ := by
    rw [hcv, m3_toComplex_eq_coord (o := o) w]
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, zero_add, zero_sub, mul_one, add_zero]
    ring
  rw [hL, hR]

theorem m3_toComplex_inner (v w : E) :
    ⟪v, w⟫ = (conj (toComplex o v) * toComplex o w).re := by
  rw [g7_inner_toComplex_re o v w]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem m3_angle_gamma (T : OrientedTriangle E o) :
    InnerProductGeometry.angle (T.A - T.C) (T.B - T.C) = 3 * T.gamma := by
  have h1 : 3 * T.gamma = InnerProductGeometry.angle (T.A - T.C) (T.B - T.C) := by
    simp only [gamma, EuclideanGeometry.angle, vsub_eq_sub]
    ring
  exact h1.symm

theorem m3_angle_alpha (T : OrientedTriangle E o) :
    InnerProductGeometry.angle (T.B - T.A) (T.C - T.A) = 3 * T.alpha := by
  have h1 : 3 * T.alpha = InnerProductGeometry.angle (T.B - T.A) (T.C - T.A) := by
    simp only [alpha, EuclideanGeometry.angle, vsub_eq_sub]
    ring
  exact h1.symm

theorem m3_angle_beta (T : OrientedTriangle E o) :
    InnerProductGeometry.angle (T.C - T.B) (T.A - T.B) = 3 * T.beta := by
  have h1 : 3 * T.beta = InnerProductGeometry.angle (T.C - T.B) (T.A - T.B) := by
    simp only [beta, EuclideanGeometry.angle, vsub_eq_sub]
    ring
  exact h1.symm

theorem m3_three_gamma_lt_pi (T : OrientedTriangle E o) : 3 * T.gamma < Real.pi := by
  have h := T.angle_sum
  have h1 := m3_alpha_pos T
  have h2 := m3_beta_pos T
  linarith

theorem m3_sin_three_gamma_pos (T : OrientedTriangle E o) : 0 < Real.sin (3 * T.gamma) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [m3_gamma_pos T]) (m3_three_gamma_lt_pi T)

/-- The oriented area of the side pair at `C` is negative. -/
theorem m3_area_BC_AC_neg (T : OrientedTriangle E o) :
    orientedArea o (T.B - T.C) (T.A - T.C) < 0 := by
  have h := T.positive
  have e1 : T.B - T.A = (T.B - T.C) - (T.A - T.C) := by abel
  have e2 : T.C - T.A = -(T.A - T.C) := by abel
  rw [e1, e2] at h
  have hsw : o.areaForm (T.A) (T.C) = -(o.areaForm (T.C)) (T.A) :=
    Orientation.areaForm_swap o T.A T.C
  have hx : orientedArea o ((T.B - T.C) - (T.A - T.C)) (-(T.A - T.C))
      = -orientedArea o (T.B - T.C) (T.A - T.C) := by
    simp only [orientedArea, map_sub, map_neg, LinearMap.sub_apply,
      Orientation.areaForm_apply_self, hsw]
    ring
  rw [hx] at h
  linarith

/-! ### m3: real/vs complex extraction of exponential factors -/

theorem m3_real_mul_exp_re (r t : ℝ) :
    (((r : ℂ) * (Circle.exp t : ℂ))).re = r * Real.cos t := by
  rw [m3_coe_exp_eq t]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    zero_mul, sub_zero, add_zero, zero_add]

theorem m3_real_mul_exp_im (r t : ℝ) :
    (((r : ℂ) * (Circle.exp t : ℂ))).im = r * Real.sin t := by
  rw [m3_coe_exp_eq t]
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    zero_mul, sub_zero, add_zero, zero_add]

theorem m3_conj_exp (φ : ℝ) :
    conj (Circle.exp φ : ℂ) = (Circle.exp (-φ) : ℂ) := by
  rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, ← m3_exp_inv]

theorem m3_exp_three (a b c : ℝ) :
    ((Circle.exp a : ℂ) * Circle.exp b) * Circle.exp c = Circle.exp (a + b + c) := by
  rw [m3_exp_mul_exp, m3_exp_mul_exp]

theorem m3_exp_mix (a b c : ℝ) (R : ℝ) :
    (Circle.exp a : ℂ) * (((Circle.exp b : ℂ) * (R : ℂ)) * Circle.exp c)
      = (R : ℂ) * (Circle.exp (a + b + c) : ℂ) := by
  rw [show (Circle.exp a : ℂ) * (((Circle.exp b : ℂ) * (R : ℂ)) * Circle.exp c)
      = ((Circle.exp a : ℂ) * Circle.exp b * Circle.exp c) * (R : ℂ) by ring]
  rw [m3_exp_three]
  ring

/-- The area of two rotated vectors, given the key product identity for `x` and `y`. -/
theorem m3_area_rot_general (x y : E) (θ R : ℝ)
    (hkey : conj (toComplex o x) * toComplex o y
      = (Circle.exp (-θ) : ℂ) * ((R : ℝ) : ℂ))
    (r : ℝ) (φ ψ : ℝ) :
    orientedArea o (r • rotateVector o x φ) (rotateVector o y ψ)
      = r * (R * Real.sin (ψ - φ - θ)) := by
  have h1 : toComplex o (r • rotateVector o x φ)
      = (r : ℂ) * (toComplex o x * Circle.exp φ) := by
    rw [toComplex_smul, toComplex_rotateVector]
  have h2 : toComplex o (rotateVector o y ψ) = toComplex o y * Circle.exp ψ :=
    toComplex_rotateVector o y ψ
  have hprod : conj (toComplex o (r • rotateVector o x φ)) * toComplex o (rotateVector o y ψ)
      = (((r * R) : ℝ) : ℂ) * (Circle.exp (ψ - φ - θ) : ℂ) := by
    calc conj (toComplex o (r • rotateVector o x φ)) * toComplex o (rotateVector o y ψ)
        = (r : ℂ) * (conj (toComplex o x) * Circle.exp (-φ)) *
            (toComplex o y * Circle.exp ψ) := by
          rw [h1, h2, map_mul, map_mul, Complex.conj_ofReal, m3_conj_exp]
      _ = (r : ℂ) * ((Circle.exp (-φ) : ℂ) *
            ((conj (toComplex o x) * toComplex o y) * Circle.exp ψ)) := by
          ring
      _ = (r : ℂ) * ((Circle.exp (-φ) : ℂ) *
            (((Circle.exp (-θ) : ℂ) * ((R : ℝ) : ℂ)) * Circle.exp ψ)) := by
          rw [hkey]
      _ = (r : ℂ) * ((R : ℂ) * (Circle.exp (-φ + -θ + ψ) : ℂ)) := by
          rw [m3_exp_mix (-φ) (-θ) ψ R]
      _ = (((r * R) : ℝ) : ℂ) * (Circle.exp (ψ - φ - θ) : ℂ) := by
          rw [show -φ + -θ + ψ = ψ - φ - θ from by ring]
          push_cast
          ring
  rw [m3_areaForm_eq_im, hprod, m3_real_mul_exp_im]
  ring

/-! ### m3: the key complex identity at a vertex -/

/-- At a vertex, the conjugate product of the two side vectors is `e^{-iθ}` times the
product of their lengths, `θ` being the (full) angle at the vertex. -/
theorem m3_key (x y : E) (θ R : ℝ) (hangle : InnerProductGeometry.angle y x = θ)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (hRpos : 0 < R) (hRval : R = ‖x‖ * ‖y‖)
    (hneg : orientedArea o x y < 0) :
    conj (toComplex o x) * toComplex o y = (Circle.exp (-θ) : ℂ) * ((R : ℝ) : ℂ) := by
  have hangle' : InnerProductGeometry.angle x y = θ := by
    rw [InnerProductGeometry.angle_comm]
    exact hangle
  have hinner : ⟪x, y⟫ = Real.cos θ * R := by
    rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm (x := x) (y := y), ← hRval, hangle']
  have hre : (conj (toComplex o x) * toComplex o y).re = Real.cos θ * R := by
    rw [← m3_toComplex_inner (o := o) x y]
    exact hinner
  have harea : orientedArea o x y = -(Real.sin θ * R) := by
    have hlag := Orientation.inner_sq_add_areaForm_sq o x y
    rw [hinner] at hlag
    have hnorm : ‖x‖ ^ 2 * ‖y‖ ^ 2 = R ^ 2 := by
      rw [hRval]; ring
    rw [hnorm] at hlag
    have hlag' : (Real.cos θ * R) ^ 2 + orientedArea o x y ^ 2 = R ^ 2 := hlag
    have hsq : orientedArea o x y ^ 2 = (Real.sin θ * R) ^ 2 := by
      linear_combination hlag' - R ^ 2 * Real.sin_sq_add_cos_sq θ
    have hsinpos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
    have hspos : 0 < Real.sin θ * R := mul_pos hsinpos hRpos
    have hfac : (orientedArea o x y + Real.sin θ * R) * (orientedArea o x y - Real.sin θ * R)
        = 0 := by nlinarith
    have h1 : orientedArea o x y - Real.sin θ * R < 0 := by linarith
    have h2 : orientedArea o x y + Real.sin θ * R = 0 := by
      rcases mul_eq_zero.mp hfac with hh | hh
      · exact hh
      · linarith
    linarith
  have him : (conj (toComplex o x) * toComplex o y).im = -(Real.sin θ * R) := by
    rw [← m3_areaForm_eq_im (o := o) x y]
    exact harea
  have hRre : ((Circle.exp (-θ) : ℂ) * ((R : ℝ) : ℂ)).re = Real.cos θ * R := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero, Real.cos_neg]
  have hRim : ((Circle.exp (-θ) : ℂ) * ((R : ℝ) : ℂ)).im = -(Real.sin θ * R) := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      add_zero, Real.sin_neg]
    ring
  apply Complex.ext
  · rw [hre, hRre]
  · rw [him, hRim]

theorem m3_three_alpha_lt_pi (T : OrientedTriangle E o) : 3 * T.alpha < Real.pi := by
  have h := T.angle_sum
  have h1 := m3_beta_pos T
  have h2 := m3_gamma_pos T
  have hp := Real.pi_pos
  linarith

theorem m3_three_beta_lt_pi (T : OrientedTriangle E o) : 3 * T.beta < Real.pi := by
  have h := T.angle_sum
  have h1 := m3_gamma_pos T
  have h2 := m3_alpha_pos T
  have hp := Real.pi_pos
  linarith

theorem m3_sin_three_alpha_pos (T : OrientedTriangle E o) : 0 < Real.sin (3 * T.alpha) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [m3_alpha_pos T]) (m3_three_alpha_lt_pi T)

theorem m3_sin_three_beta_pos (T : OrientedTriangle E o) : 0 < Real.sin (3 * T.beta) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [m3_beta_pos T]) (m3_three_beta_lt_pi T)

/-- At `A` the oriented area of the side pair is negative. -/
theorem m3_area_CA_BA_neg (T : OrientedTriangle E o) :
    orientedArea o (T.C - T.A) (T.B - T.A) < 0 := by
  have h := T.positive
  have hsw : orientedArea o (T.B - T.A) (T.C - T.A)
      = -orientedArea o (T.C - T.A) (T.B - T.A) :=
    Orientation.areaForm_swap o (T.B - T.A) (T.C - T.A)
  rw [hsw] at h
  linarith

/-- At `B` the oriented area of the side pair is negative. -/
theorem m3_area_AB_CB_neg (T : OrientedTriangle E o) :
    orientedArea o (T.A - T.B) (T.C - T.B) < 0 := by
  have h := T.positive
  have heq : orientedArea o (T.B - T.A) (T.C - T.A)
      = -orientedArea o (T.A - T.B) (T.C - T.B) := by
    have e1 : T.B - T.A = -(T.A - T.B) := by abel
    have e2 : T.C - T.A = (T.C - T.B) - (T.A - T.B) := by abel
    rw [e1, e2]
    simp only [orientedArea, map_neg, LinearMap.neg_apply, map_sub, LinearMap.sub_apply,
      Orientation.areaForm_apply_self, sub_zero]
    have hsw2 : (o.areaForm (T.B)) (T.A) = -(o.areaForm (T.A)) (T.B) :=
      Orientation.areaForm_swap o T.B T.A
    rw [hsw2]
    ring
  linarith

/-- Key identity at `C`. -/
theorem m3_key_C (T : OrientedTriangle E o) :
    conj (toComplex o (T.B - T.C)) * toComplex o (T.A - T.C)
      = (Circle.exp (-(3 * T.gamma)) : ℂ) * ((‖T.B - T.C‖ * ‖T.A - T.C‖ : ℝ) : ℂ) :=
  m3_key (o := o) (T.B - T.C) (T.A - T.C) (3 * T.gamma) (‖T.B - T.C‖ * ‖T.A - T.C‖)
    (m3_angle_gamma T)
    (by linarith [m3_gamma_pos T]) (m3_three_gamma_lt_pi T)
    (mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr T.B_ne_C))
      (norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_C))) rfl (m3_area_BC_AC_neg T)

/-- Key identity at `A`. -/
theorem m3_key_A (T : OrientedTriangle E o) :
    conj (toComplex o (T.C - T.A)) * toComplex o (T.B - T.A)
      = (Circle.exp (-(3 * T.alpha)) : ℂ) * ((‖T.C - T.A‖ * ‖T.B - T.A‖ : ℝ) : ℂ) :=
  m3_key (o := o) (T.C - T.A) (T.B - T.A) (3 * T.alpha) (‖T.C - T.A‖ * ‖T.B - T.A‖)
    (m3_angle_alpha T)
    (by linarith [m3_alpha_pos T]) (m3_three_alpha_lt_pi T)
    (mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_C.symm))
      (norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_B.symm))) rfl (m3_area_CA_BA_neg T)

/-- Key identity at `B`. -/
theorem m3_key_B (T : OrientedTriangle E o) :
    conj (toComplex o (T.A - T.B)) * toComplex o (T.C - T.B)
      = (Circle.exp (-(3 * T.beta)) : ℂ) * ((‖T.A - T.B‖ * ‖T.C - T.B‖ : ℝ) : ℂ) :=
  m3_key (o := o) (T.A - T.B) (T.C - T.B) (3 * T.beta) (‖T.A - T.B‖ * ‖T.C - T.B‖)
    (m3_angle_beta T)
    (by linarith [m3_beta_pos T]) (m3_three_beta_lt_pi T)
    (mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_B))
      (norm_pos_iff.mpr (sub_ne_zero.mpr T.B_ne_C.symm))) rfl (m3_area_AB_CB_neg T)

/-! ### m3: the affine parameter of the intersection at `C` -/

theorem m3_area_X_num (T : OrientedTriangle E o) :
    orientedArea o (T.C - T.B) (rotateVector o (T.A - T.C) (2 * T.gamma))
      = (‖T.B - T.C‖ * ‖T.A - T.C‖) * Real.sin T.gamma := by
  have hrw : (-1 : ℝ) • rotateVector o (T.B - T.C) 0 = T.C - T.B := by
    rw [rotateVector_zero_angle, neg_one_smul]
    abel
  rw [← hrw, m3_area_rot_general (o := o) (T.B - T.C) (T.A - T.C) (3 * T.gamma)
    (‖T.B - T.C‖ * ‖T.A - T.C‖) (m3_key_C T) (-1) 0 (2 * T.gamma)]
  rw [show 2 * T.gamma - 0 - 3 * T.gamma = -T.gamma from by ring, Real.sin_neg]
  ring

theorem m3_area_X_den (T : OrientedTriangle E o) :
    orientedArea o (rotateVector o (T.C - T.B) T.beta)
        (rotateVector o (T.A - T.C) (2 * T.gamma))
      = (‖T.B - T.C‖ * ‖T.A - T.C‖) * Real.sin (T.beta + T.gamma) := by
  have hrw : rotateVector o (T.C - T.B) T.beta
      = (-1 : ℝ) • rotateVector o (T.B - T.C) T.beta := by
    rw [show T.C - T.B = (-1 : ℝ) • (T.B - T.C) from by rw [neg_one_smul]; abel, rotateVector_smul]
  rw [hrw, m3_area_rot_general (o := o) (T.B - T.C) (T.A - T.C) (3 * T.gamma)
    (‖T.B - T.C‖ * ‖T.A - T.C‖) (m3_key_C T) (-1) T.beta (2 * T.gamma)]
  rw [show 2 * T.gamma - T.beta - 3 * T.gamma = -(T.beta + T.gamma) from by ring, Real.sin_neg]
  ring

theorem X_eq_intersection (T : OrientedTriangle E o) :
    T.X = Line.intersection o T.BX T.CX := by
  have hRpos : 0 < ‖T.B - T.C‖ * ‖T.A - T.C‖ :=
    mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr T.B_ne_C))
      (norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_C))
  rw [X_third, Line.intersection]
  simp only [BX, CX]
  rw [m3_area_X_num T, m3_area_X_den T,
    mul_div_mul_left (Real.sin T.gamma) (Real.sin (T.beta + T.gamma)) (ne_of_gt hRpos)]

/-! ### m3: the affine parameter of the intersection at `A` -/

theorem m3_area_Y_num (T : OrientedTriangle E o) :
    orientedArea o (T.A - T.C) (rotateVector o (T.B - T.A) (2 * T.alpha))
      = (‖T.C - T.A‖ * ‖T.B - T.A‖) * Real.sin T.alpha := by
  have hrw : (-1 : ℝ) • rotateVector o (T.C - T.A) 0 = T.A - T.C := by
    rw [rotateVector_zero_angle, neg_one_smul]
    abel
  rw [← hrw, m3_area_rot_general (o := o) (T.C - T.A) (T.B - T.A) (3 * T.alpha)
    (‖T.C - T.A‖ * ‖T.B - T.A‖) (m3_key_A T) (-1) 0 (2 * T.alpha)]
  rw [show 2 * T.alpha - 0 - 3 * T.alpha = -T.alpha from by ring, Real.sin_neg]
  ring

theorem m3_area_Y_den (T : OrientedTriangle E o) :
    orientedArea o (rotateVector o (T.A - T.C) T.gamma)
        (rotateVector o (T.B - T.A) (2 * T.alpha))
      = (‖T.C - T.A‖ * ‖T.B - T.A‖) * Real.sin (T.alpha + T.gamma) := by
  have hrw : rotateVector o (T.A - T.C) T.gamma
      = (-1 : ℝ) • rotateVector o (T.C - T.A) T.gamma := by
    rw [show T.A - T.C = (-1 : ℝ) • (T.C - T.A) from by rw [neg_one_smul]; abel, rotateVector_smul]
  rw [hrw, m3_area_rot_general (o := o) (T.C - T.A) (T.B - T.A) (3 * T.alpha)
    (‖T.C - T.A‖ * ‖T.B - T.A‖) (m3_key_A T) (-1) T.gamma (2 * T.alpha)]
  rw [show 2 * T.alpha - T.gamma - 3 * T.alpha = -(T.alpha + T.gamma) from by ring, Real.sin_neg]
  ring

theorem Y_eq_intersection (T : OrientedTriangle E o) :
    T.Y = Line.intersection o T.CY T.AY := by
  have hRpos : 0 < ‖T.C - T.A‖ * ‖T.B - T.A‖ :=
    mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_C.symm))
      (norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_B.symm))
  rw [Y_third, show T.gamma + T.alpha = T.alpha + T.gamma from add_comm _ _, Line.intersection]
  simp only [CY, AY]
  rw [m3_area_Y_num T, m3_area_Y_den T,
    mul_div_mul_left (Real.sin T.alpha) (Real.sin (T.alpha + T.gamma)) (ne_of_gt hRpos)]

/-! ### m3: the affine parameter of the intersection at `B` -/

theorem m3_area_Z_num (T : OrientedTriangle E o) :
    orientedArea o (T.B - T.A) (rotateVector o (T.C - T.B) (2 * T.beta))
      = (‖T.A - T.B‖ * ‖T.C - T.B‖) * Real.sin T.beta := by
  have hrw : (-1 : ℝ) • rotateVector o (T.A - T.B) 0 = T.B - T.A := by
    rw [rotateVector_zero_angle, neg_one_smul]
    abel
  rw [← hrw, m3_area_rot_general (o := o) (T.A - T.B) (T.C - T.B) (3 * T.beta)
    (‖T.A - T.B‖ * ‖T.C - T.B‖) (m3_key_B T) (-1) 0 (2 * T.beta)]
  rw [show 2 * T.beta - 0 - 3 * T.beta = -T.beta from by ring, Real.sin_neg]
  ring

theorem m3_area_Z_den (T : OrientedTriangle E o) :
    orientedArea o (rotateVector o (T.B - T.A) T.alpha)
        (rotateVector o (T.C - T.B) (2 * T.beta))
      = (‖T.A - T.B‖ * ‖T.C - T.B‖) * Real.sin (T.alpha + T.beta) := by
  have hrw : rotateVector o (T.B - T.A) T.alpha
      = (-1 : ℝ) • rotateVector o (T.A - T.B) T.alpha := by
    rw [show T.B - T.A = (-1 : ℝ) • (T.A - T.B) from by rw [neg_one_smul]; abel, rotateVector_smul]
  rw [hrw, m3_area_rot_general (o := o) (T.A - T.B) (T.C - T.B) (3 * T.beta)
    (‖T.A - T.B‖ * ‖T.C - T.B‖) (m3_key_B T) (-1) T.alpha (2 * T.beta)]
  rw [show 2 * T.beta - T.alpha - 3 * T.beta = -(T.alpha + T.beta) from by ring, Real.sin_neg]
  ring

theorem Z_eq_intersection (T : OrientedTriangle E o) :
    T.Z = Line.intersection o T.AZ T.BZ := by
  have hRpos : 0 < ‖T.A - T.B‖ * ‖T.C - T.B‖ :=
    mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_B))
      (norm_pos_iff.mpr (sub_ne_zero.mpr T.B_ne_C.symm))
  rw [Z_third, Line.intersection]
  simp only [AZ, BZ]
  rw [m3_area_Z_num T, m3_area_Z_den T,
    mul_div_mul_left (Real.sin T.beta) (Real.sin (T.alpha + T.beta)) (ne_of_gt hRpos)]


end OrientedTriangle

/-- **Theorem 3**, fixed point of the composition of two rotations. -/
theorem fixed_point_composition_two_rotations {P Q : E} {φ ψ : ℝ}
    (h : (Circle.exp φ : ℂ) * Circle.exp ψ ≠ 1) :
    (∃! F : E, rotation o Q ψ (rotation o P φ F) = F) ∧
      rotation o Q ψ ∘ rotation o P φ =
        rotation o (rotationFixedPoint o P Q φ ψ) (φ + ψ) := by
  have hd : (1 - (Circle.exp φ : ℂ) * Circle.exp ψ) ≠ 0 := sub_ne_zero.mpr h.symm
  refine ⟨⟨rotationFixedPoint o P Q φ ψ,
    (rotation_rotation_unique_fixedPoint o hd).mpr rfl, ?_⟩,
    rotation_rotation_rotation o hd⟩
  intro F hF
  exact (rotation_rotation_unique_fixedPoint o hd).mp hF

theorem fixed_point_composition_two_rotations_translation {P Q : E} {φ ψ : ℝ}
    (h : (Circle.exp φ : ℂ) * Circle.exp ψ = 1) :
    rotation o Q ψ ∘ rotation o P φ =
      translation (complexMulVector o (1 - Circle.exp ψ) (Q - P)) := by
  exact rotation_rotation_translation o h

/-! ### `⋄12` Criteria for a triangle to be equilateral -/

/-- The weighted expression (15). -/
def weightedTriangleExpression (O A B C : E) (ω₀ ω₁ ω₂ : ℂ) : E :=
  complexMulVector o ω₀ (A - O) + complexMulVector o ω₁ (B - O) +
    complexMulVector o ω₂ (C - O)

/-! ### Direction m9: weighted equilateral criteria (`⋄12`) -/

/-- Complex coordinates of a right multiplication. -/
theorem w9_toComplex_complexMulVector (z : ℂ) (v : E) :
    toComplex o (complexMulVector o z v) = toComplex o v * z := by
  simp [complexMulVector]

/-- Complex coordinates of the weighted expression. -/
theorem w9_weighted_toComplex (O A B C : E) (ω₀ ω₁ ω₂ : ℂ) :
    toComplex o (weightedTriangleExpression o O A B C ω₀ ω₁ ω₂) =
      toComplex o A * ω₀ + toComplex o B * ω₁ + toComplex o C * ω₂ -
        toComplex o O * (ω₀ + ω₁ + ω₂) := by
  simp only [weightedTriangleExpression, toComplex_add, toComplex_sub,
    w9_toComplex_complexMulVector]
  ring

/-- Independence from the origin iff the weights sum to zero. -/
theorem weighted_expression_origin_independent (A B C : E) (ω₀ ω₁ ω₂ : ℂ) :
    (∀ O O' : E, weightedTriangleExpression o O A B C ω₀ ω₁ ω₂ =
      weightedTriangleExpression o O' A B C ω₀ ω₁ ω₂) ↔ ω₀ + ω₁ + ω₂ = 0 := by
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by rw [(Fact.out : Module.finrank ℝ E = 2)]; norm_num)
  obtain ⟨w, hw⟩ := exists_ne (0 : E)
  have hw' : toComplex o w ≠ 0 := by simpa [toComplex_eq_zero] using hw
  constructor
  · intro h
    have h0 := congrArg (toComplex o) (h 0 w)
    rw [w9_weighted_toComplex, w9_weighted_toComplex, toComplex_zero, zero_mul, sub_zero] at h0
    have hS : toComplex o w * (ω₀ + ω₁ + ω₂) = 0 := by linear_combination h0
    exact (mul_eq_zero.mp hS).resolve_left hw'
  · intro hsum O O'
    have hsub : toComplex o (weightedTriangleExpression o O A B C ω₀ ω₁ ω₂) -
        toComplex o (weightedTriangleExpression o O' A B C ω₀ ω₁ ω₂) = 0 := by
      rw [w9_weighted_toComplex, w9_weighted_toComplex, hsum, mul_zero]
      ring
    have := sub_eq_zero.mp hsub
    exact toComplex_injective o this

/-- The barycenter used in `⋄12`. -/
def barycenter (A B C : E) : E := (1 / 3 : ℝ) • (A + B + C)

/-- The primitive cube root of unity `ω`. -/
def omega : Circle := Circle.exp (2 * Real.pi / 3)

theorem w9_omega_coe : (omega : ℂ) = Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I) :=
  Circle.coe_exp _

theorem w9_omega_re : (omega : ℂ).re = -(1 / 2) := by
  rw [w9_omega_coe, Complex.exp_ofReal_mul_I_re]
  have h2 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h2, Real.cos_pi_sub, Real.cos_pi_div_three]

theorem w9_omega_im_pos : 0 < (omega : ℂ).im := by
  rw [w9_omega_coe, Complex.exp_ofReal_mul_I_im]
  have h2 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h2, Real.sin_pi_sub, Real.sin_pi_div_three]
  positivity

theorem w9_omega_im_sq : (omega : ℂ).im ^ 2 = 3 / 4 := by
  have h : Complex.normSq (omega : ℂ) = 1 := Circle.normSq_coe _
  rw [Complex.normSq_apply, w9_omega_re] at h
  linear_combination h

theorem w9_omega_ne_one : (omega : ℂ) ≠ 1 := by
  intro h
  have h2 : (omega : ℂ).im = 0 := by rw [h]; rfl
  linarith [w9_omega_im_pos]

theorem omega_cubed : (omega : ℂ) ^ 3 = 1 := by
  have h1 : (omega : ℂ) ^ 3 = (((omega : Circle) ^ 3 : Circle) : ℂ) :=
    (Circle.coe_pow omega 3).symm
  have h2 : (omega : Circle) ^ 3 = Circle.exp (3 * (2 * Real.pi / 3)) := by
    rw [omega, ← Circle.exp_natCast_mul]
    norm_num
  rw [h1, h2, show 3 * (2 * Real.pi / 3) = 2 * Real.pi from by ring, Circle.coe_exp]
  rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I from by
    push_cast; ring]
  exact Complex.exp_two_pi_mul_I

theorem omega_sum : (1 : ℂ) + omega + (omega : ℂ) ^ 2 = 0 := by
  have hfac : ((omega : ℂ) - 1) * (1 + (omega : ℂ) + (omega : ℂ) ^ 2) = 0 := by
    linear_combination omega_cubed
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) w9_omega_ne_one
  · exact h

theorem weighted_expression_barycenter (A B C O : E) :
    weightedTriangleExpression o O A B C 1 omega ((omega : ℂ) ^ 2) =
      weightedTriangleExpression o (barycenter A B C) A B C 1 omega ((omega : ℂ) ^ 2) :=
  (weighted_expression_origin_independent o A B C 1 omega ((omega : ℂ) ^ 2)).mpr omega_sum
    O (barycenter A B C)

/-- The area form in geometric complex coordinates. -/
theorem w9_areaForm_eq_im (v w : E) :
    orientedArea o v w = (conj (toComplex o v) * toComplex o w).im := by
  have hb : (positiveBasis o).toBasis.orientation = o :=
    Orientation.finOrthonormalBasis_orientation (by norm_num)
      (Fact.out : Module.finrank ℝ E = 2) o
  have h3 : (⇑Complex.orthonormalBasisOneI : Fin 2 → ℂ) = ⇑Complex.basisOneI := by
    rw [← Complex.toBasis_orthonormalBasisOneI, OrthonormalBasis.coe_toBasis]
  have hmap : (positiveBasis o).toBasis.map (complexIsometryEquiv o).toLinearEquiv =
      Complex.basisOneI := by
    ext i
    rw [Module.Basis.map_apply]
    simp only [LinearIsometryEquiv.coe_toLinearEquiv]
    have h1 : (positiveBasis o).toBasis i = positiveBasis o i :=
      congrFun (OrthonormalBasis.coe_toBasis (positiveBasis o)) i
    rw [h1]
    have h2 : (complexIsometryEquiv o) (positiveBasis o i) = Complex.orthonormalBasisOneI i := by
      rw [complexIsometryEquiv, OrthonormalBasis.equiv_apply_basis]
      rfl
    rw [h2]
    exact congrFun h3 i
  have hf : Orientation.map (Fin 2) (complexIsometryEquiv o).toLinearEquiv o =
      Complex.orientation := by
    calc Orientation.map (Fin 2) (complexIsometryEquiv o).toLinearEquiv o
        = Orientation.map (Fin 2) (complexIsometryEquiv o).toLinearEquiv
            (positiveBasis o).toBasis.orientation := by rw [hb]
      _ = ((positiveBasis o).toBasis.map (complexIsometryEquiv o).toLinearEquiv).orientation :=
            (Module.Basis.orientation_map _ _).symm
      _ = Complex.orientation := by rw [hmap]; rfl
  exact Orientation.areaForm_map_complex o (complexIsometryEquiv o) hf v w

/-- The branch of the cube root selected by a positive orientation. -/
theorem w9_branch {u v : ℂ} (hu : u ≠ 0) (h1 : ‖v‖ = ‖u‖) (h2 : ‖u + v‖ = ‖u‖)
    (h3 : 0 < (conj u * v).im) : v = (omega : ℂ) * u := by
  have hA : (0 : ℝ) < Complex.normSq u := by
    rw [← Complex.sq_norm]; exact pow_pos (norm_pos_iff.mpr hu) 2
  have hv : Complex.normSq v = Complex.normSq u := by
    rw [← Complex.sq_norm, ← Complex.sq_norm, h1]
  have hsq : Complex.normSq (u + v) = Complex.normSq u := by
    rw [← Complex.sq_norm, ← Complex.sq_norm, h2]
  have hre : (conj u * v).re = -Complex.normSq u / 2 := by
    have hsq' : Complex.normSq (v + u) = Complex.normSq u := by rw [add_comm, hsq]
    rw [Complex.normSq_add, hv] at hsq'
    have h' : (v * conj u).re = -Complex.normSq u / 2 := by
      linear_combination (1 / 2) * hsq'
    rwa [mul_comm v (conj u)] at h'
  have hnorm : Complex.normSq (conj u * v) = Complex.normSq u * Complex.normSq u := by
    rw [Complex.normSq_mul, Complex.normSq_conj, hv]
  have hsq_im : (conj u * v).im ^ 2 = ((omega : ℂ).im * Complex.normSq u) ^ 2 := by
    have h := hnorm
    rw [Complex.normSq_apply, hre] at h
    have h2' : (conj u * v).im ^ 2 = 3 / 4 * Complex.normSq u ^ 2 := by
      linear_combination h
    rw [h2', mul_pow, w9_omega_im_sq]
  have hcombre : ((omega : ℂ) * ((Complex.normSq u : ℝ) : ℂ)).re =
      -Complex.normSq u / 2 := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, w9_omega_re]
    ring
  have hcombim : ((omega : ℂ) * ((Complex.normSq u : ℝ) : ℂ)).im =
      (omega : ℂ).im * Complex.normSq u := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  have hs_eq : conj u * v = (omega : ℂ) * (Complex.normSq u : ℂ) := by
    apply Complex.ext
    · rw [hcombre, hre]
    · rw [hcombim]
      have habs : |(conj u * v).im| = |(omega : ℂ).im * Complex.normSq u| := by
        rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs, hsq_im]
      rwa [abs_of_pos h3, abs_of_pos (mul_pos w9_omega_im_pos hA)] at habs
  have hmul : ((Complex.normSq u : ℝ) : ℂ) * v =
      ((Complex.normSq u : ℝ) : ℂ) * ((omega : ℂ) * u) := by
    have h1' : (u : ℂ) * (conj u * v) = u * ((omega : ℂ) * (Complex.normSq u : ℂ)) := by
      rw [hs_eq]
    rw [← mul_assoc, Complex.mul_conj] at h1'
    rw [h1']
    ring
  refine mul_left_cancel₀ (by simpa using hA.ne' : ((Complex.normSq u : ℝ) : ℂ) ≠ 0) ?_
  rw [hmul]

/-- A positively oriented equilateral triangle satisfies the weighted relation. -/
theorem w9_complex_equilateral (p q r : ℂ) (hpos : 0 < (conj (q - p) * (r - p)).im) :
    (‖q - p‖ = ‖r - q‖ ∧ ‖r - q‖ = ‖p - r‖) ↔
      p + (omega : ℂ) * q + (omega : ℂ) ^ 2 * r = 0 := by
  have hω1 : ‖(omega : ℂ)‖ = 1 := Circle.norm_coe omega
  have hω2n : ‖(omega : ℂ) ^ 2‖ = 1 := by rw [← Circle.coe_pow, Circle.norm_coe]
  have hωsq : (omega : ℂ) ^ 2 = -1 - (omega : ℂ) := by linear_combination omega_sum
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hu : q - p = 0
    · have hqp : q = p := sub_eq_zero.mp hu
      have hrq : r - q = 0 := by
        have hz : ‖r - q‖ = 0 := by rw [← h1, hu, norm_zero]
        exact norm_eq_zero.mp hz
      have hrp : r = p := by rw [sub_eq_zero.mp hrq, hqp]
      rw [hqp, hrp]
      linear_combination p * omega_sum
    · have h2' : ‖r - q‖ = ‖(q - p) + (r - q)‖ := by
        have hpr : p - r = -((q - p) + (r - q)) := by ring
        have h3 := h2
        rw [hpr, norm_neg] at h3
        exact h3
      have h3' : 0 < (conj (q - p) * (r - q)).im := by
        have hsplit : r - p = (q - p) + (r - q) := by ring
        rw [hsplit, mul_add, Complex.add_im] at hpos
        have hzero : (conj (q - p) * (q - p)).im = 0 := by
          rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_im]
        rwa [hzero, zero_add] at hpos
      have hbr : r - q = (omega : ℂ) * (q - p) := w9_branch hu h1.symm (h2'.symm.trans h1.symm) h3'
      have hq : q = p + (q - p) := by ring
      have hr : r = q + (r - q) := by ring
      rw [hr, hbr, hq]
      linear_combination p * omega_sum + (q - p) * omega_sum + (q - p) * omega_cubed
  · intro h
    have hω2 : (omega : ℂ) ^ 2 * r = -(p + (omega : ℂ) * q) := by linear_combination h
    have hr : r = -((omega : ℂ) * p) - (omega : ℂ) ^ 2 * q := by
      have hmul : (omega : ℂ) * ((omega : ℂ) ^ 2 * r) =
          (omega : ℂ) * (-(p + (omega : ℂ) * q)) := by rw [hω2]
      have h3 : (omega : ℂ) * ((omega : ℂ) ^ 2 * r) = r := by
        rw [← mul_assoc, show (omega : ℂ) * (omega : ℂ) ^ 2 = (omega : ℂ) ^ 3 by ring,
          omega_cubed, one_mul]
      rw [h3] at hmul
      rw [hmul]; ring
    have h1 : r - q = (omega : ℂ) * (q - p) := by rw [hr, hωsq]; ring
    have h2 : p - r = (omega : ℂ) ^ 2 * (q - p) := by rw [hr, hωsq]; ring
    constructor
    · rw [h1, norm_mul, hω1, one_mul]
    · rw [h1, h2, norm_mul, norm_mul, hω1, hω2n, one_mul]

/-- The equilateral criterion at an arbitrary origin, with the positive ordering
used in the paper. -/
theorem equilateral_iff_weighted (T : OrientedTriangle E o) (O : E) :
    Equilateral T.A T.B T.C ↔
      weightedTriangleExpression o O T.A T.B T.C 1 omega ((omega : ℂ) ^ 2) = 0 := by
  have hpos : 0 < (conj (toComplex o T.B - toComplex o T.A) *
      (toComplex o T.C - toComplex o T.A)).im := by
    have hp := T.positive
    rw [w9_areaForm_eq_im] at hp
    rw [toComplex_sub, toComplex_sub] at hp
    have hsplit : toComplex o T.C - toComplex o T.A =
        (toComplex o T.B - toComplex o T.A) + (toComplex o T.C - toComplex o T.B) := by ring
    have hzero : (conj (toComplex o T.B - toComplex o T.A) *
        (toComplex o T.B - toComplex o T.A)).im = 0 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_im]
    rw [hsplit, mul_add, Complex.add_im, hzero, zero_add] at hp ⊢
    exact hp
  have hd : ∀ P Q : E, dist P Q = ‖toComplex o Q - toComplex o P‖ := by
    intro P Q
    rw [dist_eq_norm, ← toComplex_norm o (P - Q), toComplex_sub, norm_sub_rev]
  have hdist : Equilateral T.A T.B T.C ↔
      (‖toComplex o T.B - toComplex o T.A‖ = ‖toComplex o T.C - toComplex o T.B‖ ∧
        ‖toComplex o T.C - toComplex o T.B‖ = ‖toComplex o T.A - toComplex o T.C‖) := by
    simp only [Equilateral, OrientedTriangle.Equilateral, hd]
  have hW : weightedTriangleExpression o O T.A T.B T.C 1 omega ((omega : ℂ) ^ 2) = 0 ↔
      toComplex o T.A + (omega : ℂ) * toComplex o T.B +
        (omega : ℂ) ^ 2 * toComplex o T.C = 0 := by
    have hkey := w9_weighted_toComplex o O T.A T.B T.C 1 omega ((omega : ℂ) ^ 2)
    rw [omega_sum, mul_zero, sub_zero] at hkey
    constructor
    · intro h
      have h0 : toComplex o
          (weightedTriangleExpression o O T.A T.B T.C 1 omega ((omega : ℂ) ^ 2)) = 0 := by
        rw [h, toComplex_zero]
      rw [hkey] at h0
      rw [← h0]; ring
    · intro h
      apply toComplex_injective o
      rw [hkey, toComplex_zero]
      rw [← h]; ring
  rw [hdist, hW]
  exact w9_complex_equilateral _ _ _ hpos

/-- Equation (16), the special case `O=A`. -/
theorem equilateral_iff_at_A (T : OrientedTriangle E o) :
    Equilateral T.A T.B T.C ↔
      complexMulVector o omega (T.B - T.A) +
        complexMulVector o ((omega : ℂ) ^ 2) (T.C - T.A) = 0 := by
  rw [equilateral_iff_weighted o T T.A]
  simp only [weightedTriangleExpression, complexMulVector, sub_self, toComplex_zero, zero_mul,
    ofComplex_zero, zero_add]

theorem equilateral_iff_mul_omega (T : OrientedTriangle E o) :
    Equilateral T.A T.B T.C ↔ T.B - T.A = complexMulVector o omega (T.A - T.C) := by
  rw [equilateral_iff_at_A o T]
  have hAC : toComplex o (T.C - T.A) = -toComplex o (T.A - T.C) := by
    have h1 : toComplex o (-(T.A - T.C)) = -toComplex o (T.A - T.C) :=
      toComplex_neg o (T.A - T.C)
    have h2 : T.C - T.A = -(T.A - T.C) := by abel
    rw [h2]; exact h1
  have hω : (omega : ℂ) ≠ 0 := Circle.coe_ne_zero omega
  constructor
  · intro h
    have h0 : toComplex o (complexMulVector o omega (T.B - T.A)) +
        toComplex o (complexMulVector o ((omega : ℂ) ^ 2) (T.C - T.A)) = 0 := by
      have hh := congrArg (toComplex o) h
      simpa [toComplex_add] using hh
    rw [w9_toComplex_complexMulVector, w9_toComplex_complexMulVector] at h0
    apply toComplex_injective o
    rw [w9_toComplex_complexMulVector]
    have h1 : toComplex o (T.B - T.A) * (omega : ℂ) =
        toComplex o (T.A - T.C) * (omega : ℂ) ^ 2 := by
      rw [hAC] at h0
      linear_combination h0
    refine mul_right_cancel₀ hω ?_
    rw [h1]; ring
  · intro h
    have hx : toComplex o (T.B - T.A) = toComplex o (T.A - T.C) * (omega : ℂ) := by
      have hh := congrArg (toComplex o) h
      simpa [w9_toComplex_complexMulVector] using hh
    apply toComplex_injective o
    simp only [toComplex_add, w9_toComplex_complexMulVector, toComplex_zero]
    rw [hx, hAC]
    ring
/-! ## 5. Proof of Theorem 1 with Wessel's algebra -/

namespace OrientedTriangle

variable {o : Orientation ℝ E (Fin 2)}

/-! ### `⋄13` Notations and conventions -/

def a (T : OrientedTriangle E o) : E := T.C - T.B
def b (T : OrientedTriangle E o) : E := T.A - T.C
def c (T : OrientedTriangle E o) : E := T.B - T.A
def aLength (T : OrientedTriangle E o) : ℝ := ‖T.a‖
def bLength (T : OrientedTriangle E o) : ℝ := ‖T.b‖
def cLength (T : OrientedTriangle E o) : ℝ := ‖T.c‖
def aStar (T : OrientedTriangle E o) : E := T.aLength⁻¹ • T.a
def bStar (T : OrientedTriangle E o) : E := T.bLength⁻¹ • T.b
def cStar (T : OrientedTriangle E o) : E := T.cLength⁻¹ • T.c

theorem a_eq (T : OrientedTriangle E o) : T.a = T.aLength • T.aStar := by
  rw [aStar, aLength, smul_smul]
  have ha : ‖T.a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr T.B_ne_C.symm)
  rw [mul_inv_cancel₀ ha, one_smul]
theorem b_eq (T : OrientedTriangle E o) : T.b = T.bLength • T.bStar := by
  rw [bStar, bLength, smul_smul]
  have hb : ‖T.b‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr T.A_ne_C)
  rw [mul_inv_cancel₀ hb, one_smul]
theorem c_eq (T : OrientedTriangle E o) : T.c = T.cLength • T.cStar := by
  rw [cStar, cLength, smul_smul]
  have hc : ‖T.c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr T.A_ne_B.symm)
  rw [mul_inv_cancel₀ hc, one_smul]

/- Equation (17): proved below with the sine-law identities. -/
end OrientedTriangle

/-- The four angle transforms in Table 3. -/
def thetaPrime (θ : ℝ) : ℝ := Real.pi / 3 + θ
def thetaSecond (θ : ℝ) : ℝ := 2 * Real.pi / 3 + θ
def thetaStar (θ : ℝ) : ℝ := Real.pi / 3 - θ
def thetaStarStar (θ : ℝ) : ℝ := 2 * Real.pi / 3 - θ

theorem theta_conditions (θ : ℝ) :
    thetaPrime θ + thetaStarStar θ = Real.pi ∧
      thetaSecond θ + thetaStar θ = Real.pi := by
  constructor <;> dsimp [thetaPrime, thetaSecond, thetaStar, thetaStarStar] <;> ring
theorem sin_thetaStarStar (θ : ℝ) : Real.sin (thetaStarStar θ) = Real.sin (thetaPrime θ) := by
  dsimp [thetaStarStar, thetaPrime]
  rw [show 2 * Real.pi / 3 - θ = Real.pi - (Real.pi / 3 + θ) by ring, Real.sin_pi_sub]
theorem cos_thetaStarStar (θ : ℝ) : Real.cos (thetaStarStar θ) = -Real.cos (thetaPrime θ) := by
  dsimp [thetaStarStar, thetaPrime]
  rw [show 2 * Real.pi / 3 - θ = Real.pi - (Real.pi / 3 + θ) by ring, Real.cos_pi_sub]
theorem sin_thetaStar (θ : ℝ) : Real.sin (thetaStar θ) = Real.sin (thetaSecond θ) := by
  dsimp [thetaStar, thetaSecond]
  rw [show Real.pi / 3 - θ = Real.pi - (2 * Real.pi / 3 + θ) by ring, Real.sin_pi_sub]
theorem cos_thetaStar (θ : ℝ) : Real.cos (thetaStar θ) = -Real.cos (thetaSecond θ) := by
  dsimp [thetaStar, thetaSecond]
  rw [show Real.pi / 3 - θ = Real.pi - (2 * Real.pi / 3 + θ) by ring, Real.cos_pi_sub]
theorem sin_beta_add_gamma (T : OrientedTriangle E o) :
    Real.sin (T.beta + T.gamma) = Real.sin (thetaStar T.alpha) := by
  have h := T.angle_sum
  dsimp [thetaStar]
  congr 1 <;> linarith
theorem sin_gamma_add_alpha (T : OrientedTriangle E o) :
    Real.sin (T.gamma + T.alpha) = Real.sin (thetaStar T.beta) := by
  have h := T.angle_sum
  dsimp [thetaStar]
  congr 1 <;> linarith
theorem sin_alpha_add_beta (T : OrientedTriangle E o) :
    Real.sin (T.alpha + T.beta) = Real.sin (thetaStar T.gamma) := by
  have h := T.angle_sum
  dsimp [thetaStar]
  congr 1 <;> linarith

namespace OrientedTriangle

variable {o : Orientation ℝ E (Fin 2)}

/-- The common value in the sine law; it is identified with the circumdiameter
in Appendix A. -/
def delta (T : OrientedTriangle E o) : ℝ := T.aLength / Real.sin (3 * T.alpha)

/-- The expression for `Z-Y` preceding Equation (18), exactly as in `⋄14`. -/
theorem betaStarStar_eq (T : OrientedTriangle E o) :
    thetaStarStar T.beta = thetaPrime T.gamma + T.alpha := by
  have h := T.angle_sum
  dsimp [thetaStarStar, thetaPrime]
  linarith

theorem gammaPrime_sub_alpha (T : OrientedTriangle E o) :
    thetaPrime T.gamma - T.alpha = T.beta + 2 * T.gamma := by
  have h := T.angle_sum
  dsimp [thetaPrime]
  linarith

end OrientedTriangle

/-! ## Appendix A. Notes -/

/-! ### `⋄17` The algebraic model of the Euclidean plane -/

/-- The length function of `⋄17`, agreeing with the norm. -/
def vectorLength {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (v : V) : ℝ := ‖v‖

theorem vectorLength_eq_sqrt {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : V) : vectorLength v = √⟪v, v⟫ := by
  rw [vectorLength, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem cauchy_schwarz_bounds {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v w : V) : -‖v‖ * ‖w‖ ≤ ⟪v, w⟫ ∧ ⟪v, w⟫ ≤ ‖v‖ * ‖w‖ := by
  have habs := abs_real_inner_le_norm v w
  exact ⟨by simpa [neg_mul] using neg_le_of_abs_le habs, le_of_abs_le habs⟩

theorem unique_unoriented_angle {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃! θ ∈ Set.Icc 0 Real.pi, Real.cos θ = ⟪v, w⟫ / (‖v‖ * ‖w‖) := by
  let θ := InnerProductGeometry.angle v w
  have hmem : θ ∈ Set.Icc 0 Real.pi :=
    ⟨InnerProductGeometry.angle_nonneg v w, InnerProductGeometry.angle_le_pi v w⟩
  refine ⟨θ, ⟨hmem, InnerProductGeometry.cos_angle v w⟩, ?_⟩
  intro θ' hθ'
  exact Real.strictAntiOn_cos.injOn hθ'.1 hmem (hθ'.2.trans (InnerProductGeometry.cos_angle v w).symm)

/-! ### `⋄18` The Argand plane -/

def complexLength (z : ℂ) : ℝ := ‖z‖
def complexDot (z w : ℂ) : ℝ := (conj z * w).re
def complexArea (z w : ℂ) : ℝ := (conj z * w).im

theorem complexLength_sq (z : ℂ) : complexLength z ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [complexLength, Complex.sq_norm, Complex.normSq_apply]
  ring
theorem complexLength_normSq (z : ℂ) : (complexLength z : ℂ) ^ 2 = z * conj z := by
  rw [complexLength, ← Complex.mul_conj' z]
theorem complexDot_coordinates (z w : ℂ) : complexDot z w = z.re * w.re + z.im * w.im := by
  rw [complexDot, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring
theorem complexArea_coordinates (z w : ℂ) : complexArea z w = z.re * w.im - z.im * w.re := by
  rw [complexArea, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem complex_polar_dot (z w : ℂ) :
    complexDot z w = ‖z‖ * ‖w‖ * Real.cos (Complex.arg (conj z * w)) := by
  rw [complexDot, ← Complex.norm_mul_cos_arg (conj z * w), Complex.norm_mul, Complex.norm_conj]
theorem complex_polar_area (z w : ℂ) :
    complexArea z w = ‖z‖ * ‖w‖ * Real.sin (Complex.arg (conj z * w)) := by
  rw [complexArea, ← Complex.norm_mul_sin_arg (conj z * w), Complex.norm_mul, Complex.norm_conj]
theorem complex_oriented_angle {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    ∃ ε ∈ ({-1, 1} : Set ℝ),
      Complex.arg (conj z * w) = ε * Real.arccos (complexDot z w / (‖z‖ * ‖w‖)) := by
  set u := conj z * w with hu
  have hz' : conj z ≠ 0 := by simpa using hz
  have hu0 : u ≠ 0 := mul_ne_zero hz' hw
  have hnorm : u.re / ‖u‖ = complexDot z w / (‖z‖ * ‖w‖) := by
    rw [hu, complexDot, Complex.norm_mul, Complex.norm_conj]
  by_cases h : 0 ≤ u.im
  · refine ⟨1, by norm_num, ?_⟩
    rw [Complex.arg_of_im_nonneg_of_ne_zero h hu0, one_mul, ← hnorm]
  · rw [not_le] at h
    refine ⟨-1, by norm_num, ?_⟩
    rw [Complex.arg_of_im_neg h, neg_one_mul, ← hnorm]

theorem complex_conj_mul_polar (z w : ℂ) :
    conj z * w = (‖z‖ * ‖w‖ : ℂ) * Circle.exp (Complex.arg (conj z * w)) := by
  have h := Complex.norm_mul_exp_arg_mul_I (conj z * w)
  rw [Complex.norm_mul, Complex.norm_conj] at h
  conv_lhs => rw [← h]
  rw [Circle.coe_exp]
  push_cast
  ring

theorem complexIsometryEquiv_positiveBasis (o : Orientation ℝ E (Fin 2)) (i : Fin 2) :
    complexIsometryEquiv o (positiveBasis o i) = Complex.orthonormalBasisOneI i := by
  simp [complexIsometryEquiv, OrthonormalBasis.equiv]

theorem toComplex_positiveBasis (o : Orientation ℝ E (Fin 2)) (i : Fin 2) :
    toComplex o (positiveBasis o i) = Complex.orthonormalBasisOneI i :=
  complexIsometryEquiv_positiveBasis o i

theorem toComplex_eq_coord (o : Orientation ℝ E (Fin 2)) (v : E) :
    toComplex o v =
      ((positiveBasis o).repr v 0 : ℝ) + ((positiveBasis o).repr v 1 : ℝ) * Complex.I := by
  have hsum := (positiveBasis o).sum_repr v
  conv_lhs => rw [← hsum]
  simp [toComplex_positiveBasis, Fin.sum_univ_two]

/-- The oriented area form is the imaginary part of the complex product. -/
theorem areaForm_toComplex (o : Orientation ℝ E (Fin 2)) (v w : E) :
    orientedArea o v w = (conj (toComplex o v) * toComplex o w).im := by
  have hb : (positiveBasis o).toBasis.orientation = o :=
    o.finOrthonormalBasis_orientation (by norm_num) Fact.out
  have hvol : o.volumeForm = (positiveBasis o).toBasis.det :=
    o.volumeForm_robust (positiveBasis o) hb
  rw [orientedArea, Orientation.areaForm_to_volumeForm, hvol, Module.Basis.det_apply,
    toComplex_eq_coord o v, toComplex_eq_coord o w]
  simp [Module.Basis.toMatrix_apply, Matrix.det_fin_two, Complex.mul_im, Complex.mul_re]
  ring

/-- The real inner product is the real part of the complex product. -/
theorem toComplex_inner (o : Orientation ℝ E (Fin 2)) (v w : E) :
    ⟪v, w⟫ = (conj (toComplex o v) * toComplex o w).re := by
  rw [show (⟪v, w⟫ : ℝ) = ⟪toComplex o v, toComplex o w⟫ from
    (LinearIsometryEquiv.inner_map_map (complexIsometryEquiv o) v w).symm]
  rw [Complex.inner]
  simp [toComplex, mul_comm]

/-- Lagrange's identity in the plane: the two-dimensional Gram determinant. -/
theorem lagrange_area (o : Orientation ℝ E (Fin 2)) (v w : E) :
    ⟪v, v⟫ * ⟪w, w⟫ - ⟪v, w⟫ * ⟪v, w⟫ = orientedArea o v w ^ 2 := by
  have hv : ⟪v, v⟫ = Complex.normSq (toComplex o v) := by
    rw [real_inner_self_eq_norm_sq,
      show ‖v‖ = ‖toComplex o v‖ from (toComplex_norm o v).symm, Complex.sq_norm]
  have hw : ⟪w, w⟫ = Complex.normSq (toComplex o w) := by
    rw [real_inner_self_eq_norm_sq,
      show ‖w‖ = ‖toComplex o w‖ from (toComplex_norm o w).symm, Complex.sq_norm]
  have hvw : ⟪v, w⟫ = (conj (toComplex o v) * toComplex o w).re := toComplex_inner o v w
  rw [hv, hw, hvw, areaForm_toComplex]
  have hmul : Complex.normSq (toComplex o v) * Complex.normSq (toComplex o w) =
      Complex.normSq (conj (toComplex o v) * toComplex o w) := by
    rw [Complex.normSq_mul, Complex.normSq_conj]
  rw [hmul, Complex.normSq_apply]
  ring

/-- The sine of the angle between two nonzero vectors, with the area form. -/
theorem sin_angle_eq_area (o : Orientation ℝ E (Fin 2)) {v w : E} (hv : v ≠ 0)
    (hw : w ≠ 0) :
    Real.sin (InnerProductGeometry.angle v w) = |orientedArea o v w| / (‖v‖ * ‖w‖) := by
  rw [InnerProductGeometry.sin_angle hv hw, lagrange_area o v w, Real.sqrt_sq_eq_abs]

/-- The signed form of the previous lemma, when the orientation is positive. -/
theorem sin_angle_mul_norm_mul_norm (o : Orientation ℝ E (Fin 2)) {v w : E} (hv : v ≠ 0)
    (hw : w ≠ 0) (hpos : 0 < orientedArea o v w) :
    ‖v‖ * ‖w‖ * Real.sin (InnerProductGeometry.angle v w) = orientedArea o v w := by
  rw [sin_angle_eq_area o hv hw, abs_of_pos hpos]
  field_simp

theorem gram_identity_complex (q u v : ℂ) :
    (conj u * v).im ^ 2 * ‖q‖ ^ 2 =
      ‖v‖ ^ 2 * (conj q * u).re ^ 2
        - 2 * (conj u * v).re * (conj q * u).re * (conj q * v).re
        + ‖u‖ ^ 2 * (conj q * v).re ^ 2 := by
  simp only [Complex.sq_norm, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply]
  ring

/-- The Gram-determinant identity for three vectors of the plane. -/
theorem gram_identity (o : Orientation ℝ E (Fin 2)) (q u v : E) :
    orientedArea o u v ^ 2 * ‖q‖ ^ 2 =
      ‖v‖ ^ 2 * ⟪q, u⟫ ^ 2 - 2 * ⟪u, v⟫ * ⟪q, u⟫ * ⟪q, v⟫ + ‖u‖ ^ 2 * ⟪q, v⟫ ^ 2 := by
  have h := gram_identity_complex (toComplex o q) (toComplex o u) (toComplex o v)
  rw [← areaForm_toComplex o u v, ← toComplex_inner o q u, ← toComplex_inner o q v,
    ← toComplex_inner o u v, toComplex_norm, toComplex_norm, toComplex_norm] at h
  exact h

/-! ### `⋄19` The law of sines, Equations (A1) and (A2) -/

namespace OrientedTriangle

variable {o : Orientation ℝ E (Fin 2)}

/-- The triangle as a Mathlib simplex, giving access to its circumcircle. -/
def toSimplex (T : OrientedTriangle E o) : Affine.Simplex ℝ E 2 where
  points := ![T.A, T.B, T.C]
  independent := affineIndependent_iff_not_collinear_set.mpr T.noncollinear

/-- The oriented area `S` of `ABC`. -/
def area (T : OrientedTriangle E o) : ℝ := orientedArea o (T.B - T.A) (T.C - T.A) / 2

/-- Diameter of the circumcircle. -/
def circumdiameter (T : OrientedTriangle E o) : ℝ := 2 * T.toSimplex.circumradius

theorem a_add_b_add_c (T : OrientedTriangle E o) : T.a + T.b + T.c = 0 := by
  simp [OrientedTriangle.a, OrientedTriangle.b, OrientedTriangle.c]

theorem orientedArea_a_b_pos (T : OrientedTriangle E o) : 0 < orientedArea o T.a T.b := by
  have h := T.positive
  rw [show T.B - T.A = T.c from rfl,
    show T.C - T.A = -T.b from by simp [OrientedTriangle.b]] at h
  have hcb : T.c = -(T.a + T.b) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact T.a_add_b_add_c
  rw [hcb] at h
  simpa [orientedArea] using h

theorem two_area (T : OrientedTriangle E o) : 2 * T.area = orientedArea o T.a T.b := by
  have hBA : T.B - T.A = T.c := rfl
  have hCA : T.C - T.A = -T.b := by simp [OrientedTriangle.b]
  have hcb : T.c = -(T.a + T.b) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact T.a_add_b_add_c
  rw [OrientedTriangle.area, hBA, hCA, hcb]
  simp [orientedArea]
  ring

theorem area_pos (T : OrientedTriangle E o) : 0 < T.area := by
  have h := T.two_area
  nlinarith [T.orientedArea_a_b_pos]

theorem a_ne_zero (T : OrientedTriangle E o) : T.a ≠ 0 := sub_ne_zero.mpr T.B_ne_C.symm
theorem b_ne_zero (T : OrientedTriangle E o) : T.b ≠ 0 := sub_ne_zero.mpr T.A_ne_C
theorem c_ne_zero (T : OrientedTriangle E o) : T.c ≠ 0 := sub_ne_zero.mpr T.A_ne_B.symm

theorem aLength_pos (T : OrientedTriangle E o) : 0 < T.aLength := by
  simpa [OrientedTriangle.aLength] using norm_pos_iff.mpr T.a_ne_zero
theorem bLength_pos (T : OrientedTriangle E o) : 0 < T.bLength := by
  simpa [OrientedTriangle.bLength] using norm_pos_iff.mpr T.b_ne_zero
theorem cLength_pos (T : OrientedTriangle E o) : 0 < T.cLength := by
  simpa [OrientedTriangle.cLength] using norm_pos_iff.mpr T.c_ne_zero

theorem sin_three_gamma_mul (T : OrientedTriangle E o) :
    T.aLength * T.bLength * Real.sin (3 * T.gamma) = orientedArea o T.a T.b := by
  have ha : T.a ≠ 0 := T.a_ne_zero
  have hb : T.b ≠ 0 := T.b_ne_zero
  have hsign : orientedArea o T.b (-T.a) = orientedArea o T.a T.b := by
    show (o.areaForm T.b) (-T.a) = (o.areaForm T.a) T.b
    rw [map_neg, Orientation.areaForm_swap o T.b T.a, neg_neg]
  have hang : 3 * T.gamma = InnerProductGeometry.angle T.b (-T.a) := by
    have h1 : 3 * T.gamma = InnerProductGeometry.angle (T.A - T.C) (T.B - T.C) := by
      simp only [OrientedTriangle.gamma, EuclideanGeometry.angle, vsub_eq_sub]
      ring
    rw [h1, show T.A - T.C = T.b from rfl, show T.B - T.C = -T.a from by simp [OrientedTriangle.a]]
  have hp : 0 < orientedArea o T.b (-T.a) := by rw [hsign]; exact T.orientedArea_a_b_pos
  have h := sin_angle_mul_norm_mul_norm o (v := T.b) (w := -T.a) hb (neg_ne_zero.mpr ha) hp
  rw [← hang, hsign] at h
  have h2 : ‖T.b‖ * ‖-T.a‖ = T.aLength * T.bLength := by
    rw [show ‖T.b‖ = T.bLength from rfl,
      show ‖-T.a‖ = T.aLength from by simp [OrientedTriangle.aLength], mul_comm]
  rwa [h2] at h

theorem sin_three_alpha_mul (T : OrientedTriangle E o) :
    T.bLength * T.cLength * Real.sin (3 * T.alpha) = orientedArea o T.a T.b := by
  have hb : T.b ≠ 0 := T.b_ne_zero
  have hc : T.c ≠ 0 := T.c_ne_zero
  have habc := T.a_add_b_add_c
  have hsign : orientedArea o T.c (-T.b) = orientedArea o T.a T.b := by
    have hcb : T.c = -(T.a + T.b) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact habc
    rw [hcb]
    simp [orientedArea]
  have hang : 3 * T.alpha = InnerProductGeometry.angle T.c (-T.b) := by
    have h1 : 3 * T.alpha = InnerProductGeometry.angle (T.B - T.A) (T.C - T.A) := by
      simp only [OrientedTriangle.alpha, EuclideanGeometry.angle, vsub_eq_sub]
      ring
    rw [h1, show T.B - T.A = T.c from rfl, show T.C - T.A = -T.b from by simp [OrientedTriangle.b]]
  have hp : 0 < orientedArea o T.c (-T.b) := by rw [hsign]; exact T.orientedArea_a_b_pos
  have h := sin_angle_mul_norm_mul_norm o (v := T.c) (w := -T.b) hc (neg_ne_zero.mpr hb) hp
  rw [← hang, hsign] at h
  have h2 : ‖T.c‖ * ‖-T.b‖ = T.bLength * T.cLength := by
    rw [show ‖T.c‖ = T.cLength from rfl,
      show ‖-T.b‖ = T.bLength from by simp [OrientedTriangle.bLength], mul_comm]
  rwa [h2] at h

theorem sin_three_beta_mul (T : OrientedTriangle E o) :
    T.cLength * T.aLength * Real.sin (3 * T.beta) = orientedArea o T.a T.b := by
  have ha : T.a ≠ 0 := T.a_ne_zero
  have hc : T.c ≠ 0 := T.c_ne_zero
  have hsign : orientedArea o T.a (-T.c) = orientedArea o T.a T.b := by
    have h := congrArg (fun x => (o.areaForm T.a) x) T.a_add_b_add_c
    simp only [map_add, map_zero] at h
    have haa : (o.areaForm T.a) T.a = 0 := Orientation.areaForm_apply_self o T.a
    show (o.areaForm T.a) (-T.c) = (o.areaForm T.a) T.b
    rw [map_neg]
    linarith
  have hang : 3 * T.beta = InnerProductGeometry.angle T.a (-T.c) := by
    have h1 : 3 * T.beta = InnerProductGeometry.angle (T.C - T.B) (T.A - T.B) := by
      simp only [OrientedTriangle.beta, EuclideanGeometry.angle, vsub_eq_sub]
      ring
    rw [h1, show T.C - T.B = T.a from rfl, show T.A - T.B = -T.c from by simp [OrientedTriangle.c]]
  have hp : 0 < orientedArea o T.a (-T.c) := by rw [hsign]; exact T.orientedArea_a_b_pos
  have h := sin_angle_mul_norm_mul_norm o (v := T.a) (w := -T.c) ha (neg_ne_zero.mpr hc) hp
  rw [← hang, hsign] at h
  have h2 : ‖T.a‖ * ‖-T.c‖ = T.cLength * T.aLength := by
    rw [show ‖T.a‖ = T.aLength from rfl,
      show ‖-T.c‖ = T.cLength from by simp [OrientedTriangle.cLength], mul_comm]
  rwa [h2] at h

theorem sin_three_gamma_pos (T : OrientedTriangle E o) : 0 < Real.sin (3 * T.gamma) := by
  have h := T.sin_three_gamma_mul
  rw [← T.two_area] at h
  have hab : 0 < T.aLength * T.bLength := mul_pos T.aLength_pos T.bLength_pos
  have hS : 0 < T.aLength * T.bLength * Real.sin (3 * T.gamma) := by rw [h]; linarith [T.area_pos]
  exact (pos_iff_pos_of_mul_pos hS).mp hab

theorem sin_three_alpha_pos (T : OrientedTriangle E o) : 0 < Real.sin (3 * T.alpha) := by
  have h := T.sin_three_alpha_mul
  rw [← T.two_area] at h
  have hbc : 0 < T.bLength * T.cLength := mul_pos T.bLength_pos T.cLength_pos
  have hS : 0 < T.bLength * T.cLength * Real.sin (3 * T.alpha) := by rw [h]; linarith [T.area_pos]
  exact (pos_iff_pos_of_mul_pos hS).mp hbc

theorem sin_three_beta_pos (T : OrientedTriangle E o) : 0 < Real.sin (3 * T.beta) := by
  have h := T.sin_three_beta_mul
  rw [← T.two_area] at h
  have hca : 0 < T.cLength * T.aLength := mul_pos T.cLength_pos T.aLength_pos
  have hS : 0 < T.cLength * T.aLength * Real.sin (3 * T.beta) := by rw [h]; linarith [T.area_pos]
  exact (pos_iff_pos_of_mul_pos hS).mp hca

theorem aLength_div_sin_alpha (T : OrientedTriangle E o) :
    T.aLength / Real.sin (3 * T.alpha) =
      T.aLength * T.bLength * T.cLength / (2 * T.area) := by
  have hmul : T.bLength * T.cLength * Real.sin (3 * T.alpha) = 2 * T.area := by
    rw [T.sin_three_alpha_mul, T.two_area]
  have hs : Real.sin (3 * T.alpha) ≠ 0 := ne_of_gt T.sin_three_alpha_pos
  have hS : 2 * T.area ≠ 0 := ne_of_gt (by linarith [T.area_pos])
  rw [div_eq_div_iff hs hS, ← hmul]
  ring

theorem bLength_div_sin_beta (T : OrientedTriangle E o) :
    T.bLength / Real.sin (3 * T.beta) =
      T.aLength * T.bLength * T.cLength / (2 * T.area) := by
  have hmul : T.cLength * T.aLength * Real.sin (3 * T.beta) = 2 * T.area := by
    rw [T.sin_three_beta_mul, T.two_area]
  have hs : Real.sin (3 * T.beta) ≠ 0 := ne_of_gt T.sin_three_beta_pos
  have hS : 2 * T.area ≠ 0 := ne_of_gt (by linarith [T.area_pos])
  rw [div_eq_div_iff hs hS, ← hmul]
  ring

theorem cLength_div_sin_gamma (T : OrientedTriangle E o) :
    T.cLength / Real.sin (3 * T.gamma) =
      T.aLength * T.bLength * T.cLength / (2 * T.area) := by
  have hmul : T.aLength * T.bLength * Real.sin (3 * T.gamma) = 2 * T.area := by
    rw [T.sin_three_gamma_mul, T.two_area]
  have hs : Real.sin (3 * T.gamma) ≠ 0 := ne_of_gt T.sin_three_gamma_pos
  have hS : 2 * T.area ≠ 0 := ne_of_gt (by linarith [T.area_pos])
  rw [div_eq_div_iff hs hS, ← hmul]
  ring

theorem side_wedge_area (T : OrientedTriangle E o) :
    orientedArea o T.a T.b = T.aLength * T.bLength * Real.sin (3 * T.gamma) := by
  rw [← T.sin_three_gamma_mul]

theorem side_area_a_b (T : OrientedTriangle E o) :
    T.aLength * T.bLength * Real.sin (3 * T.gamma) = 2 * T.area := by
  rw [T.sin_three_gamma_mul, T.two_area]

theorem side_area_b_c (T : OrientedTriangle E o) :
    T.bLength * T.cLength * Real.sin (3 * T.alpha) = 2 * T.area := by
  rw [T.sin_three_alpha_mul, T.two_area]

theorem side_area_c_a (T : OrientedTriangle E o) :
    T.cLength * T.aLength * Real.sin (3 * T.beta) = 2 * T.area := by
  rw [T.sin_three_beta_mul, T.two_area]




variable {o : Orientation ℝ E (Fin 2)}

theorem areaForm_ab_bc (T : OrientedTriangle E o) :
    o.areaForm T.a T.b = o.areaForm T.b T.c := by
  have hsum : T.a + T.b + T.c = 0 := by
    simp only [OrientedTriangle.a, OrientedTriangle.b, OrientedTriangle.c]
    abel
  have h2 : T.a + T.b = -T.c := by
    rw [eq_neg_iff_add_eq_zero]
    exact hsum
  have h1 : o.areaForm (T.a + T.b) T.b = o.areaForm T.a T.b := by
    rw [map_add]
    simp
  rw [h2, map_neg, LinearMap.neg_apply, o.areaForm_swap T.c T.b] at h1
  linarith only [h1]

theorem areaForm_bc_ca (T : OrientedTriangle E o) :
    o.areaForm T.b T.c = o.areaForm T.c T.a := by
  have hsum : T.a + T.b + T.c = 0 := by
    simp only [OrientedTriangle.a, OrientedTriangle.b, OrientedTriangle.c]
    abel
  have h2 : T.b + T.c = -T.a := by
    rw [eq_neg_iff_add_eq_zero]
    calc T.b + T.c + T.a = T.a + T.b + T.c := by abel
      _ = 0 := hsum
  have h1 : o.areaForm (T.b + T.c) T.c = o.areaForm T.b T.c := by
    rw [map_add]
    simp
  rw [h2, map_neg, LinearMap.neg_apply, o.areaForm_swap T.a T.c] at h1
  linarith only [h1]

theorem areaForm_eq_two_area (T : OrientedTriangle E o) :
    o.areaForm T.a T.b = 2 * T.area := by
  simp only [OrientedTriangle.a, OrientedTriangle.b, OrientedTriangle.area, orientedArea,
    map_sub, LinearMap.sub_apply, o.areaForm_apply_self, sub_zero]
  rw [o.areaForm_swap T.C T.A]
  ring

theorem side_wedge_area' (T : OrientedTriangle E o) :
    o.areaForm T.a T.b = T.aLength * T.bLength * Real.sin (3 * T.gamma) := by
  have h := side_wedge_area T
  simpa [orientedArea] using h

theorem side_area_b_c' (T : OrientedTriangle E o) :
    o.areaForm T.b T.c = T.bLength * T.cLength * Real.sin (3 * T.alpha) := by
  have h := side_area_b_c T
  have h2 : o.areaForm T.b T.c = 2 * T.area := by
    rw [← areaForm_ab_bc]; exact areaForm_eq_two_area T
  rw [h2, ← h]

theorem side_area_c_a' (T : OrientedTriangle E o) :
    o.areaForm T.c T.a = T.cLength * T.aLength * Real.sin (3 * T.beta) := by
  have h := side_area_c_a T
  have h2 : o.areaForm T.c T.a = 2 * T.area := by
    rw [← areaForm_bc_ca, ← areaForm_ab_bc]; exact areaForm_eq_two_area T
  rw [h2, ← h]


theorem bStar_relation (T : OrientedTriangle E o) :
    T.bStar = -rotateVector o T.aStar (-3 * T.gamma) := by
  have hbridge : ∀ u v : E, o.areaForm u v = (conj (toComplex o u) * toComplex o v).im := by
    intro u v
    have h1 : (positiveBasis o).toBasis.orientation = o := o.finOrthonormalBasis_orientation _ _
    have h3 : (positiveBasis o).toBasis.map (complexIsometryEquiv o).toLinearEquiv = Complex.basisOneI := by
      ext i
      simp [positiveBasis, complexIsometryEquiv]
    have h2 : Orientation.map (Fin 2) (complexIsometryEquiv o).toLinearEquiv o = Complex.orientation := by
      calc Orientation.map (Fin 2) (complexIsometryEquiv o).toLinearEquiv o
          = Orientation.map (Fin 2) (complexIsometryEquiv o).toLinearEquiv
              ((positiveBasis o).toBasis.orientation) := by rw [h1]
        _ = ((positiveBasis o).toBasis.map (complexIsometryEquiv o).toLinearEquiv).orientation :=
              (Module.Basis.orientation_map _ _).symm
        _ = Complex.orientation := by rw [h3]; rfl
    exact Orientation.areaForm_map_complex o (complexIsometryEquiv o) h2 u v
  have hinner : ∀ u v : E, ⟪u, v⟫ = (conj (toComplex o u) * toComplex o v).re := by
    intro u v
    rw [← (complexIsometryEquiv o).inner_map_map u v]
    rw [Complex.inner, mul_comm]
    rfl
  have hbpos : 0 < T.bLength := by
    rw [OrientedTriangle.bLength]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_C)
  have hapos : 0 < T.aLength := by
    rw [OrientedTriangle.aLength]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm T.B_ne_C))
  have hca : InnerProductGeometry.angle T.b (-T.a) = 3 * T.gamma := by
    have h : EuclideanGeometry.angle T.A T.C T.B = 3 * T.gamma := by
      simp only [OrientedTriangle.gamma]
      ring
    simpa [EuclideanGeometry.angle, OrientedTriangle.b, OrientedTriangle.a] using h
  have hcos : (conj (toComplex o T.b) * toComplex o (-T.a)).re =
      T.bLength * T.aLength * Real.cos (3 * T.gamma) := by
    have h1 : (conj (toComplex o T.b) * toComplex o (-T.a)).re = ⟪T.b, -T.a⟫ := by
      rw [hinner T.b (-T.a)]
    rw [h1]
    have h3 := InnerProductGeometry.cos_angle_mul_norm_mul_norm T.b (-T.a)
    rw [hca] at h3
    simp only [norm_neg, OrientedTriangle.aLength, OrientedTriangle.bLength] at h3
    rw [← h3]
    simp only [OrientedTriangle.bLength, OrientedTriangle.aLength]
    ring
  have hsin : (conj (toComplex o T.b) * toComplex o (-T.a)).im =
      T.bLength * T.aLength * Real.sin (3 * T.gamma) := by
    have h1 : (conj (toComplex o T.b) * toComplex o (-T.a)).im = o.areaForm T.b (-T.a) := by
      rw [hbridge T.b (-T.a)]
    rw [h1]
    have h2 : o.areaForm T.b (-T.a) = o.areaForm T.a T.b := by
      rw [map_neg, o.areaForm_swap]
      ring
    rw [h2]
    have h3 := side_wedge_area' T
    change o.areaForm T.a T.b = T.aLength * T.bLength * Real.sin (3 * T.gamma) at h3
    rw [h3]
    ring
  have hkey : conj (toComplex o T.b) * toComplex o (-T.a) =
      ((T.bLength * T.aLength : ℝ) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ) := by
    have hexp : ((Circle.exp (3 * T.gamma) : Circle) : ℂ) =
        Real.cos (3 * T.gamma) + Real.sin (3 * T.gamma) * Complex.I := by
      rw [Circle.coe_exp, Complex.exp_ofReal_mul_I]
    have hre : (((T.bLength * T.aLength : ℝ) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ)).re =
        T.bLength * T.aLength * Real.cos (3 * T.gamma) := by
      rw [hexp]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero,
        add_zero]
      ring
    have him : (((T.bLength * T.aLength : ℝ) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ)).im =
        T.bLength * T.aLength * Real.sin (3 * T.gamma) := by
      rw [hexp]
      simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero,
        add_zero]
      ring
    apply Complex.ext
    · rw [hre]; exact hcos
    · rw [him]; exact hsin
  have h4 : conj (toComplex o T.b) * toComplex o T.a =
      -(((T.bLength * T.aLength : ℝ) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ)) := by
    have h5 := hkey
    rw [toComplex_neg] at h5
    linear_combination -h5
  have hbne : ((T.bLength : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hbpos
  have hane : ((T.aLength : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hapos
  have hstar : conj (toComplex o T.bStar) * toComplex o (-T.aStar) = (Circle.exp (3 * T.gamma) : ℂ) := by
    have hb : toComplex o T.bStar = ((T.bLength : ℝ) : ℂ)⁻¹ * toComplex o T.b := by
      simp [OrientedTriangle.bStar, toComplex_smul]
    have ha : toComplex o (-T.aStar) = -(((T.aLength : ℝ) : ℂ)⁻¹ * toComplex o T.a) := by
      rw [toComplex_neg]
      simp [OrientedTriangle.aStar, toComplex_smul]
    rw [hb, ha]
    simp only [map_mul, map_neg, map_inv₀, Complex.conj_ofReal]
    have hcoef : ((T.bLength : ℂ))⁻¹ * ((T.aLength : ℂ))⁻¹ * ((T.bLength * T.aLength : ℝ) : ℂ) = 1 := by
      push_cast
      field_simp
    calc ((T.bLength : ℂ))⁻¹ * conj (toComplex o T.b) * -(((T.aLength : ℂ))⁻¹ * toComplex o T.a)
        = -((((T.bLength : ℂ))⁻¹ * ((T.aLength : ℂ))⁻¹) *
            (conj (toComplex o T.b) * toComplex o T.a)) := by ring
      _ = -((((T.bLength : ℂ))⁻¹ * ((T.aLength : ℂ))⁻¹) *
            (-(((T.bLength * T.aLength : ℝ) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ)))) := by rw [h4]
      _ = (Circle.exp (3 * T.gamma) : ℂ) := by
          rw [show -((((T.bLength : ℂ))⁻¹ * ((T.aLength : ℂ))⁻¹) *
            (-(((T.bLength * T.aLength : ℝ) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ))))
            = ((((T.bLength : ℂ))⁻¹ * ((T.aLength : ℂ))⁻¹) * ((T.bLength * T.aLength : ℝ) : ℂ)) *
              (Circle.exp (3 * T.gamma) : ℂ) from by ring]
          rw [hcoef, one_mul]
  have hbS : ‖toComplex o T.bStar‖ = 1 := by
    rw [toComplex_norm, OrientedTriangle.bStar, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hbpos, OrientedTriangle.bLength]
    exact inv_mul_cancel₀ (ne_of_gt hbpos)
  have hzb : toComplex o T.bStar = -(toComplex o T.aStar) * (Circle.exp (3 * T.gamma) : ℂ)⁻¹ := by
    have hunit : toComplex o T.bStar * conj (toComplex o T.bStar) = 1 := by
      rw [Complex.mul_conj, ← Complex.sq_norm, hbS]
      norm_num
    have hE : (Circle.exp (3 * T.gamma) : ℂ) ≠ 0 := by
      rw [Circle.coe_exp]
      exact Complex.exp_ne_zero _
    have h1 : (toComplex o T.bStar * conj (toComplex o T.bStar)) * toComplex o (-T.aStar) =
        (Circle.exp (3 * T.gamma) : ℂ) * toComplex o T.bStar := by
      calc toComplex o T.bStar * conj (toComplex o T.bStar) * toComplex o (-T.aStar)
          = toComplex o T.bStar * (conj (toComplex o T.bStar) * toComplex o (-T.aStar)) := by ring
        _ = toComplex o T.bStar * (Circle.exp (3 * T.gamma) : ℂ) := by rw [hstar]
        _ = (Circle.exp (3 * T.gamma) : ℂ) * toComplex o T.bStar := by ring
    rw [hunit, one_mul] at h1
    have h3 : -toComplex o T.aStar = (Circle.exp (3 * T.gamma) : ℂ) * toComplex o T.bStar := by
      rw [← h1, toComplex_neg]
    calc toComplex o T.bStar
        = (Circle.exp (3 * T.gamma) : ℂ) * toComplex o T.bStar * (Circle.exp (3 * T.gamma) : ℂ)⁻¹ := by
          rw [mul_comm ((Circle.exp (3 * T.gamma) : ℂ)) (toComplex o T.bStar), mul_assoc,
            mul_inv_cancel₀ hE, mul_one]
      _ = (-toComplex o T.aStar) * (Circle.exp (3 * T.gamma) : ℂ)⁻¹ := by rw [h3]
  apply toComplex_injective o
  rw [toComplex_neg, toComplex_rotateVector, hzb]
  have hneg : ((Circle.exp (-3 * T.gamma) : ℂ)) = ((Circle.exp (3 * T.gamma) : ℂ))⁻¹ := by
    rw [Circle.coe_exp, Circle.coe_exp]
    have harg : ((-3 * T.gamma : ℝ) : ℂ) * Complex.I = -(((3 * T.gamma : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_neg]
  rw [hneg]
  ring


theorem cStar_relation (T : OrientedTriangle E o) :
    T.cStar = -rotateVector o T.bStar (-3 * T.alpha) := by
  have hbridge : ∀ u v : E, o.areaForm u v = (conj (toComplex o u) * toComplex o v).im := by
    intro u v
    have h1 : (positiveBasis o).toBasis.orientation = o := o.finOrthonormalBasis_orientation _ _
    have h3 : (positiveBasis o).toBasis.map (complexIsometryEquiv o).toLinearEquiv = Complex.basisOneI := by
      ext i
      simp [positiveBasis, complexIsometryEquiv]
    have h2 : Orientation.map (Fin 2) (complexIsometryEquiv o).toLinearEquiv o = Complex.orientation := by
      calc Orientation.map (Fin 2) (complexIsometryEquiv o).toLinearEquiv o
          = Orientation.map (Fin 2) (complexIsometryEquiv o).toLinearEquiv
              ((positiveBasis o).toBasis.orientation) := by rw [h1]
        _ = ((positiveBasis o).toBasis.map (complexIsometryEquiv o).toLinearEquiv).orientation :=
              (Module.Basis.orientation_map _ _).symm
        _ = Complex.orientation := by rw [h3]; rfl
    exact Orientation.areaForm_map_complex o (complexIsometryEquiv o) h2 u v
  have hinner : ∀ u v : E, ⟪u, v⟫ = (conj (toComplex o u) * toComplex o v).re := by
    intro u v
    rw [← (complexIsometryEquiv o).inner_map_map u v]
    rw [Complex.inner, mul_comm]
    rfl
  have hbpos : 0 < T.cLength := by
    rw [OrientedTriangle.cLength]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm T.A_ne_B))
  have hapos : 0 < T.bLength := by
    rw [OrientedTriangle.bLength]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_C)
  have hca : InnerProductGeometry.angle T.c (-T.b) = 3 * T.alpha := by
    have h : EuclideanGeometry.angle T.B T.A T.C = 3 * T.alpha := by
      simp only [OrientedTriangle.alpha]
      ring
    simpa [EuclideanGeometry.angle, OrientedTriangle.c, OrientedTriangle.b] using h
  have hcos : (conj (toComplex o T.c) * toComplex o (-T.b)).re =
      T.cLength * T.bLength * Real.cos (3 * T.alpha) := by
    have h1 : (conj (toComplex o T.c) * toComplex o (-T.b)).re = ⟪T.c, -T.b⟫ := by
      rw [hinner T.c (-T.b)]
    rw [h1]
    have h3 := InnerProductGeometry.cos_angle_mul_norm_mul_norm T.c (-T.b)
    rw [hca] at h3
    simp only [norm_neg, OrientedTriangle.bLength, OrientedTriangle.cLength] at h3
    rw [← h3]
    simp only [OrientedTriangle.cLength, OrientedTriangle.bLength]
    ring
  have hsin : (conj (toComplex o T.c) * toComplex o (-T.b)).im =
      T.cLength * T.bLength * Real.sin (3 * T.alpha) := by
    have h1 : (conj (toComplex o T.c) * toComplex o (-T.b)).im = o.areaForm T.c (-T.b) := by
      rw [hbridge T.c (-T.b)]
    rw [h1]
    have h2 : o.areaForm T.c (-T.b) = o.areaForm T.b T.c := by
      rw [map_neg, o.areaForm_swap]
      ring
    rw [h2]
    have h3 := side_area_b_c' T
    change o.areaForm T.b T.c = T.bLength * T.cLength * Real.sin (3 * T.alpha) at h3
    rw [h3]
    ring
  have hkey : conj (toComplex o T.c) * toComplex o (-T.b) =
      ((T.cLength * T.bLength : ℝ) : ℂ) * (Circle.exp (3 * T.alpha) : ℂ) := by
    have hexp : ((Circle.exp (3 * T.alpha) : Circle) : ℂ) =
        Real.cos (3 * T.alpha) + Real.sin (3 * T.alpha) * Complex.I := by
      rw [Circle.coe_exp, Complex.exp_ofReal_mul_I]
    have hre : (((T.cLength * T.bLength : ℝ) : ℂ) * (Circle.exp (3 * T.alpha) : ℂ)).re =
        T.cLength * T.bLength * Real.cos (3 * T.alpha) := by
      rw [hexp]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero,
        add_zero]
      ring
    have him : (((T.cLength * T.bLength : ℝ) : ℂ) * (Circle.exp (3 * T.alpha) : ℂ)).im =
        T.cLength * T.bLength * Real.sin (3 * T.alpha) := by
      rw [hexp]
      simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero,
        add_zero]
      ring
    apply Complex.ext
    · rw [hre]; exact hcos
    · rw [him]; exact hsin
  have h4 : conj (toComplex o T.c) * toComplex o T.b =
      -(((T.cLength * T.bLength : ℝ) : ℂ) * (Circle.exp (3 * T.alpha) : ℂ)) := by
    have h5 := hkey
    rw [toComplex_neg] at h5
    linear_combination -h5
  have hbne : ((T.cLength : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hbpos
  have hane : ((T.bLength : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hapos
  have hstar : conj (toComplex o T.cStar) * toComplex o (-T.bStar) = (Circle.exp (3 * T.alpha) : ℂ) := by
    have hb : toComplex o T.cStar = ((T.cLength : ℝ) : ℂ)⁻¹ * toComplex o T.c := by
      simp [OrientedTriangle.cStar, toComplex_smul]
    have ha : toComplex o (-T.bStar) = -(((T.bLength : ℝ) : ℂ)⁻¹ * toComplex o T.b) := by
      rw [toComplex_neg]
      simp [OrientedTriangle.bStar, toComplex_smul]
    rw [hb, ha]
    simp only [map_mul, map_neg, map_inv₀, Complex.conj_ofReal]
    have hcoef : ((T.cLength : ℂ))⁻¹ * ((T.bLength : ℂ))⁻¹ * ((T.cLength * T.bLength : ℝ) : ℂ) = 1 := by
      push_cast
      field_simp
    calc ((T.cLength : ℂ))⁻¹ * conj (toComplex o T.c) * -(((T.bLength : ℂ))⁻¹ * toComplex o T.b)
        = -((((T.cLength : ℂ))⁻¹ * ((T.bLength : ℂ))⁻¹) *
            (conj (toComplex o T.c) * toComplex o T.b)) := by ring
      _ = -((((T.cLength : ℂ))⁻¹ * ((T.bLength : ℂ))⁻¹) *
            (-(((T.cLength * T.bLength : ℝ) : ℂ) * (Circle.exp (3 * T.alpha) : ℂ)))) := by rw [h4]
      _ = (Circle.exp (3 * T.alpha) : ℂ) := by
          rw [show -((((T.cLength : ℂ))⁻¹ * ((T.bLength : ℂ))⁻¹) *
            (-(((T.cLength * T.bLength : ℝ) : ℂ) * (Circle.exp (3 * T.alpha) : ℂ))))
            = ((((T.cLength : ℂ))⁻¹ * ((T.bLength : ℂ))⁻¹) * ((T.cLength * T.bLength : ℝ) : ℂ)) *
              (Circle.exp (3 * T.alpha) : ℂ) from by ring]
          rw [hcoef, one_mul]
  have hbS : ‖toComplex o T.cStar‖ = 1 := by
    rw [toComplex_norm, OrientedTriangle.cStar, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hbpos, OrientedTriangle.cLength]
    exact inv_mul_cancel₀ (ne_of_gt hbpos)
  have hzb : toComplex o T.cStar = -(toComplex o T.bStar) * (Circle.exp (3 * T.alpha) : ℂ)⁻¹ := by
    have hunit : toComplex o T.cStar * conj (toComplex o T.cStar) = 1 := by
      rw [Complex.mul_conj, ← Complex.sq_norm, hbS]
      norm_num
    have hE : (Circle.exp (3 * T.alpha) : ℂ) ≠ 0 := by
      rw [Circle.coe_exp]
      exact Complex.exp_ne_zero _
    have h1 : (toComplex o T.cStar * conj (toComplex o T.cStar)) * toComplex o (-T.bStar) =
        (Circle.exp (3 * T.alpha) : ℂ) * toComplex o T.cStar := by
      calc toComplex o T.cStar * conj (toComplex o T.cStar) * toComplex o (-T.bStar)
          = toComplex o T.cStar * (conj (toComplex o T.cStar) * toComplex o (-T.bStar)) := by ring
        _ = toComplex o T.cStar * (Circle.exp (3 * T.alpha) : ℂ) := by rw [hstar]
        _ = (Circle.exp (3 * T.alpha) : ℂ) * toComplex o T.cStar := by ring
    rw [hunit, one_mul] at h1
    have h3 : -toComplex o T.bStar = (Circle.exp (3 * T.alpha) : ℂ) * toComplex o T.cStar := by
      rw [← h1, toComplex_neg]
    calc toComplex o T.cStar
        = (Circle.exp (3 * T.alpha) : ℂ) * toComplex o T.cStar * (Circle.exp (3 * T.alpha) : ℂ)⁻¹ := by
          rw [mul_comm ((Circle.exp (3 * T.alpha) : ℂ)) (toComplex o T.cStar), mul_assoc,
            mul_inv_cancel₀ hE, mul_one]
      _ = (-toComplex o T.bStar) * (Circle.exp (3 * T.alpha) : ℂ)⁻¹ := by rw [h3]
  apply toComplex_injective o
  rw [toComplex_neg, toComplex_rotateVector, hzb]
  have hneg : ((Circle.exp (-3 * T.alpha) : ℂ)) = ((Circle.exp (3 * T.alpha) : ℂ))⁻¹ := by
    rw [Circle.coe_exp, Circle.coe_exp]
    have harg : ((-3 * T.alpha : ℝ) : ℂ) * Complex.I = -(((3 * T.alpha : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_neg]
  rw [hneg]
  ring



theorem aStar_relation (T : OrientedTriangle E o) :
    T.aStar = -rotateVector o T.cStar (-3 * T.beta) := by
  have hbridge : ∀ u v : E, o.areaForm u v = (conj (toComplex o u) * toComplex o v).im := by
    intro u v
    have h1 : (positiveBasis o).toBasis.orientation = o := o.finOrthonormalBasis_orientation _ _
    have h3 : (positiveBasis o).toBasis.map (complexIsometryEquiv o).toLinearEquiv = Complex.basisOneI := by
      ext i
      simp [positiveBasis, complexIsometryEquiv]
    have h2 : Orientation.map (Fin 2) (complexIsometryEquiv o).toLinearEquiv o = Complex.orientation := by
      calc Orientation.map (Fin 2) (complexIsometryEquiv o).toLinearEquiv o
          = Orientation.map (Fin 2) (complexIsometryEquiv o).toLinearEquiv
              ((positiveBasis o).toBasis.orientation) := by rw [h1]
        _ = ((positiveBasis o).toBasis.map (complexIsometryEquiv o).toLinearEquiv).orientation :=
              (Module.Basis.orientation_map _ _).symm
        _ = Complex.orientation := by rw [h3]; rfl
    exact Orientation.areaForm_map_complex o (complexIsometryEquiv o) h2 u v
  have hinner : ∀ u v : E, ⟪u, v⟫ = (conj (toComplex o u) * toComplex o v).re := by
    intro u v
    rw [← (complexIsometryEquiv o).inner_map_map u v]
    rw [Complex.inner, mul_comm]
    rfl
  have hbpos : 0 < T.aLength := by
    rw [OrientedTriangle.aLength]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm T.B_ne_C))
  have hapos : 0 < T.cLength := by
    rw [OrientedTriangle.cLength]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm T.A_ne_B))
  have hca : InnerProductGeometry.angle T.a (-T.c) = 3 * T.beta := by
    have h : EuclideanGeometry.angle T.C T.B T.A = 3 * T.beta := by
      simp only [OrientedTriangle.beta]
      ring
    simpa [EuclideanGeometry.angle, OrientedTriangle.a, OrientedTriangle.c] using h
  have hcos : (conj (toComplex o T.a) * toComplex o (-T.c)).re =
      T.aLength * T.cLength * Real.cos (3 * T.beta) := by
    have h1 : (conj (toComplex o T.a) * toComplex o (-T.c)).re = ⟪T.a, -T.c⟫ := by
      rw [hinner T.a (-T.c)]
    rw [h1]
    have h3 := InnerProductGeometry.cos_angle_mul_norm_mul_norm T.a (-T.c)
    rw [hca] at h3
    simp only [norm_neg, OrientedTriangle.cLength, OrientedTriangle.aLength] at h3
    rw [← h3]
    simp only [OrientedTriangle.aLength, OrientedTriangle.cLength]
    ring
  have hsin : (conj (toComplex o T.a) * toComplex o (-T.c)).im =
      T.aLength * T.cLength * Real.sin (3 * T.beta) := by
    have h1 : (conj (toComplex o T.a) * toComplex o (-T.c)).im = o.areaForm T.a (-T.c) := by
      rw [hbridge T.a (-T.c)]
    rw [h1]
    have h2 : o.areaForm T.a (-T.c) = o.areaForm T.c T.a := by
      rw [map_neg, o.areaForm_swap]
      ring
    rw [h2]
    have h3 := side_area_c_a' T
    change o.areaForm T.c T.a = T.cLength * T.aLength * Real.sin (3 * T.beta) at h3
    rw [h3]
    ring
  have hkey : conj (toComplex o T.a) * toComplex o (-T.c) =
      ((T.aLength * T.cLength : ℝ) : ℂ) * (Circle.exp (3 * T.beta) : ℂ) := by
    have hexp : ((Circle.exp (3 * T.beta) : Circle) : ℂ) =
        Real.cos (3 * T.beta) + Real.sin (3 * T.beta) * Complex.I := by
      rw [Circle.coe_exp, Complex.exp_ofReal_mul_I]
    have hre : (((T.aLength * T.cLength : ℝ) : ℂ) * (Circle.exp (3 * T.beta) : ℂ)).re =
        T.aLength * T.cLength * Real.cos (3 * T.beta) := by
      rw [hexp]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero,
        add_zero]
      ring
    have him : (((T.aLength * T.cLength : ℝ) : ℂ) * (Circle.exp (3 * T.beta) : ℂ)).im =
        T.aLength * T.cLength * Real.sin (3 * T.beta) := by
      rw [hexp]
      simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero,
        add_zero]
      ring
    apply Complex.ext
    · rw [hre]; exact hcos
    · rw [him]; exact hsin
  have h4 : conj (toComplex o T.a) * toComplex o T.c =
      -(((T.aLength * T.cLength : ℝ) : ℂ) * (Circle.exp (3 * T.beta) : ℂ)) := by
    have h5 := hkey
    rw [toComplex_neg] at h5
    linear_combination -h5
  have hbne : ((T.aLength : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hbpos
  have hane : ((T.cLength : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hapos
  have hstar : conj (toComplex o T.aStar) * toComplex o (-T.cStar) = (Circle.exp (3 * T.beta) : ℂ) := by
    have hb : toComplex o T.aStar = ((T.aLength : ℝ) : ℂ)⁻¹ * toComplex o T.a := by
      simp [OrientedTriangle.aStar, toComplex_smul]
    have ha : toComplex o (-T.cStar) = -(((T.cLength : ℝ) : ℂ)⁻¹ * toComplex o T.c) := by
      rw [toComplex_neg]
      simp [OrientedTriangle.cStar, toComplex_smul]
    rw [hb, ha]
    simp only [map_mul, map_neg, map_inv₀, Complex.conj_ofReal]
    have hcoef : ((T.aLength : ℂ))⁻¹ * ((T.cLength : ℂ))⁻¹ * ((T.aLength * T.cLength : ℝ) : ℂ) = 1 := by
      push_cast
      field_simp
    calc ((T.aLength : ℂ))⁻¹ * conj (toComplex o T.a) * -(((T.cLength : ℂ))⁻¹ * toComplex o T.c)
        = -((((T.aLength : ℂ))⁻¹ * ((T.cLength : ℂ))⁻¹) *
            (conj (toComplex o T.a) * toComplex o T.c)) := by ring
      _ = -((((T.aLength : ℂ))⁻¹ * ((T.cLength : ℂ))⁻¹) *
            (-(((T.aLength * T.cLength : ℝ) : ℂ) * (Circle.exp (3 * T.beta) : ℂ)))) := by rw [h4]
      _ = (Circle.exp (3 * T.beta) : ℂ) := by
          rw [show -((((T.aLength : ℂ))⁻¹ * ((T.cLength : ℂ))⁻¹) *
            (-(((T.aLength * T.cLength : ℝ) : ℂ) * (Circle.exp (3 * T.beta) : ℂ))))
            = ((((T.aLength : ℂ))⁻¹ * ((T.cLength : ℂ))⁻¹) * ((T.aLength * T.cLength : ℝ) : ℂ)) *
              (Circle.exp (3 * T.beta) : ℂ) from by ring]
          rw [hcoef, one_mul]
  have hbS : ‖toComplex o T.aStar‖ = 1 := by
    rw [toComplex_norm, OrientedTriangle.aStar, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hbpos, OrientedTriangle.aLength]
    exact inv_mul_cancel₀ (ne_of_gt hbpos)
  have hzb : toComplex o T.aStar = -(toComplex o T.cStar) * (Circle.exp (3 * T.beta) : ℂ)⁻¹ := by
    have hunit : toComplex o T.aStar * conj (toComplex o T.aStar) = 1 := by
      rw [Complex.mul_conj, ← Complex.sq_norm, hbS]
      norm_num
    have hE : (Circle.exp (3 * T.beta) : ℂ) ≠ 0 := by
      rw [Circle.coe_exp]
      exact Complex.exp_ne_zero _
    have h1 : (toComplex o T.aStar * conj (toComplex o T.aStar)) * toComplex o (-T.cStar) =
        (Circle.exp (3 * T.beta) : ℂ) * toComplex o T.aStar := by
      calc toComplex o T.aStar * conj (toComplex o T.aStar) * toComplex o (-T.cStar)
          = toComplex o T.aStar * (conj (toComplex o T.aStar) * toComplex o (-T.cStar)) := by ring
        _ = toComplex o T.aStar * (Circle.exp (3 * T.beta) : ℂ) := by rw [hstar]
        _ = (Circle.exp (3 * T.beta) : ℂ) * toComplex o T.aStar := by ring
    rw [hunit, one_mul] at h1
    have h3 : -toComplex o T.cStar = (Circle.exp (3 * T.beta) : ℂ) * toComplex o T.aStar := by
      rw [← h1, toComplex_neg]
    calc toComplex o T.aStar
        = (Circle.exp (3 * T.beta) : ℂ) * toComplex o T.aStar * (Circle.exp (3 * T.beta) : ℂ)⁻¹ := by
          rw [mul_comm ((Circle.exp (3 * T.beta) : ℂ)) (toComplex o T.aStar), mul_assoc,
            mul_inv_cancel₀ hE, mul_one]
      _ = (-toComplex o T.cStar) * (Circle.exp (3 * T.beta) : ℂ)⁻¹ := by rw [h3]
  apply toComplex_injective o
  rw [toComplex_neg, toComplex_rotateVector, hzb]
  have hneg : ((Circle.exp (-3 * T.beta) : ℂ)) = ((Circle.exp (3 * T.beta) : ℂ))⁻¹ := by
    rw [Circle.coe_exp, Circle.coe_exp]
    have harg : ((-3 * T.beta : ℝ) : ℂ) * Complex.I = -(((3 * T.beta : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_neg]
  rw [hneg]
  ring


theorem sin_star_difference (T : OrientedTriangle E o) :
    (Real.sin (thetaStarStar T.beta) : ℂ) -
        Real.sin (thetaStarStar T.gamma) * Circle.exp (-T.alpha) =
      Real.sin T.alpha * Circle.exp (thetaPrime T.gamma) := by
  have hsum := T.angle_sum
  have h1 : thetaStarStar T.beta = thetaPrime T.gamma + T.alpha := by
    simp only [thetaStarStar, thetaPrime]
    linarith
  have h2 : thetaStarStar T.gamma = Real.pi - thetaPrime T.gamma := by
    simp only [thetaStarStar, thetaPrime]
    ring
  have e1 : ((Circle.exp (-T.alpha) : ℂ)) =
      Real.cos T.alpha - Real.sin T.alpha * Complex.I := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have e2 : ((Circle.exp (thetaPrime T.gamma) : ℂ)) =
      Real.cos (thetaPrime T.gamma) + Real.sin (thetaPrime T.gamma) * Complex.I := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I]
  rw [h1, h2, Real.sin_pi_sub, e1, e2, Real.sin_add]
  push_cast
  ring



theorem law_of_sines (T : OrientedTriangle E o) :
    T.aLength / Real.sin (3 * T.alpha) = T.bLength / Real.sin (3 * T.beta) ∧
    T.bLength / Real.sin (3 * T.beta) = T.cLength / Real.sin (3 * T.gamma) ∧
    T.cLength / Real.sin (3 * T.gamma) = T.delta := by
  refine ⟨?_, ?_, ?_⟩
  · rw [T.aLength_div_sin_alpha, T.bLength_div_sin_beta]
  · rw [T.bLength_div_sin_beta, T.cLength_div_sin_gamma]
  · rw [T.cLength_div_sin_gamma, OrientedTriangle.delta, T.aLength_div_sin_alpha]

theorem delta_eq_product_div_area (T : OrientedTriangle E o) :
    T.delta = T.aLength * T.bLength * T.cLength / (2 * T.area) := by
  rw [OrientedTriangle.delta]
  exact T.aLength_div_sin_alpha

theorem side_lengths_sine (T : OrientedTriangle E o) :
    T.aLength = T.delta * Real.sin (3 * T.alpha) ∧
    T.bLength = T.delta * Real.sin (3 * T.beta) ∧
    T.cLength = T.delta * Real.sin (3 * T.gamma) := by
  have hsl := T.law_of_sines
  refine ⟨?_, ?_, ?_⟩
  · rw [OrientedTriangle.delta, div_mul_cancel₀ _ (ne_of_gt T.sin_three_alpha_pos)]
  · have h : T.delta = T.bLength / Real.sin (3 * T.beta) := (hsl.2.1.trans hsl.2.2).symm
    rw [h, div_mul_cancel₀ _ (ne_of_gt T.sin_three_beta_pos)]
  · have h : T.delta = T.cLength / Real.sin (3 * T.gamma) := hsl.2.2.symm
    rw [h, div_mul_cancel₀ _ (ne_of_gt T.sin_three_gamma_pos)]

theorem delta_eq_circumdiameter (T : OrientedTriangle E o) :
    T.delta = T.circumdiameter := by
  set R := T.toSimplex.circumradius with hR
  have hdist : ∀ i : Fin 3, dist (T.toSimplex.points i) T.toSimplex.circumcenter = R := by
    intro i
    rw [hR]
    exact Affine.Simplex.dist_circumcenter_eq_circumradius T.toSimplex i
  have hA : dist T.A T.toSimplex.circumcenter = R := by
    have := hdist 0; simpa [toSimplex] using this
  have hB : dist T.B T.toSimplex.circumcenter = R := by
    have := hdist 1; simpa [toSimplex] using this
  have hC : dist T.C T.toSimplex.circumcenter = R := by
    have := hdist 2; simpa [toSimplex] using this
  have hqA : ‖T.toSimplex.circumcenter - T.A‖ = R := by
    rw [← dist_eq_norm, dist_comm]; exact hA
  have hqB : ‖T.toSimplex.circumcenter - T.B‖ = R := by
    rw [← dist_eq_norm, dist_comm]; exact hB
  have hqC : ‖T.toSimplex.circumcenter - T.C‖ = R := by
    rw [← dist_eq_norm, dist_comm]; exact hC
  have h1 : 2 * ⟪T.toSimplex.circumcenter - T.A, T.B - T.A⟫ = ‖T.B - T.A‖ ^ 2 := by
    have hsq : ‖T.toSimplex.circumcenter - T.A‖ ^ 2 =
        ‖T.toSimplex.circumcenter - T.B‖ ^ 2 := by rw [hqA, hqB]
    have hsub : T.toSimplex.circumcenter - T.B =
        (T.toSimplex.circumcenter - T.A) - (T.B - T.A) := by abel
    have hsplit : ‖(T.toSimplex.circumcenter - T.A) - (T.B - T.A)‖ ^ 2 =
        ‖T.toSimplex.circumcenter - T.A‖ ^ 2
          - 2 * ⟪T.toSimplex.circumcenter - T.A, T.B - T.A⟫ + ‖T.B - T.A‖ ^ 2 :=
      norm_sub_sq_real _ _
    rw [hsub, hsplit] at hsq
    linarith
  have h2 : 2 * ⟪T.toSimplex.circumcenter - T.A, T.C - T.A⟫ = ‖T.C - T.A‖ ^ 2 := by
    have hsq : ‖T.toSimplex.circumcenter - T.A‖ ^ 2 =
        ‖T.toSimplex.circumcenter - T.C‖ ^ 2 := by rw [hqA, hqC]
    have hsub : T.toSimplex.circumcenter - T.C =
        (T.toSimplex.circumcenter - T.A) - (T.C - T.A) := by abel
    have hsplit : ‖(T.toSimplex.circumcenter - T.A) - (T.C - T.A)‖ ^ 2 =
        ‖T.toSimplex.circumcenter - T.A‖ ^ 2
          - 2 * ⟪T.toSimplex.circumcenter - T.A, T.C - T.A⟫ + ‖T.C - T.A‖ ^ 2 :=
      norm_sub_sq_real _ _
    rw [hsub, hsplit] at hsq
    linarith
  have hkey := gram_identity o (T.toSimplex.circumcenter - T.A) (T.B - T.A) (T.C - T.A)
  have hX1 : ⟪T.toSimplex.circumcenter - T.A, T.B - T.A⟫ = ‖T.B - T.A‖ ^ 2 / 2 := by
    linarith [h1]
  have hX2 : ⟪T.toSimplex.circumcenter - T.A, T.C - T.A⟫ = ‖T.C - T.A‖ ^ 2 / 2 := by
    linarith [h2]
  have hQ : ‖T.toSimplex.circumcenter - T.A‖ ^ 2 = R ^ 2 := by rw [hqA]
  rw [hX1, hX2, hQ] at hkey
  have hP : ‖(T.B - T.A) - (T.C - T.A)‖ ^ 2 =
      ‖T.B - T.A‖ ^ 2 + ‖T.C - T.A‖ ^ 2 - 2 * ⟪T.B - T.A, T.C - T.A⟫ := by
    rw [norm_sub_sq_real]
    ring
  have hmain1 : 4 * orientedArea o (T.B - T.A) (T.C - T.A) ^ 2 * R ^ 2 =
      ‖T.B - T.A‖ ^ 2 * ‖T.C - T.A‖ ^ 2 * ‖(T.B - T.A) - (T.C - T.A)‖ ^ 2 := by
    rw [hP]
    linear_combination 4 * hkey
  have hsq : (2 * orientedArea o (T.B - T.A) (T.C - T.A) * R) ^ 2 =
      (‖T.B - T.A‖ * ‖T.C - T.A‖ * ‖(T.B - T.A) - (T.C - T.A)‖) ^ 2 := by
    calc (2 * orientedArea o (T.B - T.A) (T.C - T.A) * R) ^ 2
        = 4 * orientedArea o (T.B - T.A) (T.C - T.A) ^ 2 * R ^ 2 := by ring
      _ = ‖T.B - T.A‖ ^ 2 * ‖T.C - T.A‖ ^ 2 * ‖(T.B - T.A) - (T.C - T.A)‖ ^ 2 := hmain1
      _ = (‖T.B - T.A‖ * ‖T.C - T.A‖ * ‖(T.B - T.A) - (T.C - T.A)‖) ^ 2 := by ring
  have hA0eq : orientedArea o (T.B - T.A) (T.C - T.A) = 2 * T.area := by
    rw [OrientedTriangle.area]; ring
  have hA0pos : 0 < orientedArea o (T.B - T.A) (T.C - T.A) := by
    rw [hA0eq]; linarith [T.area_pos]
  have hR0 : 0 ≤ R := by
    rw [hR]; exact Affine.Simplex.circumradius_nonneg _
  have hnn1 : 0 ≤ 2 * orientedArea o (T.B - T.A) (T.C - T.A) * R :=
    mul_nonneg (by linarith [hA0pos]) hR0
  have hnn2 : 0 ≤ ‖T.B - T.A‖ * ‖T.C - T.A‖ * ‖(T.B - T.A) - (T.C - T.A)‖ :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have h2AR : 2 * orientedArea o (T.B - T.A) (T.C - T.A) * R =
      ‖T.B - T.A‖ * ‖T.C - T.A‖ * ‖(T.B - T.A) - (T.C - T.A)‖ :=
    (sq_eq_sq₀ hnn1 hnn2).mp hsq
  have hnu : ‖T.B - T.A‖ = T.cLength := rfl
  have hnv : ‖T.C - T.A‖ = T.bLength := by
    rw [show T.C - T.A = -T.b from by simp [OrientedTriangle.b]]
    simp [OrientedTriangle.bLength]
  have hnuv : ‖(T.B - T.A) - (T.C - T.A)‖ = T.aLength := by
    rw [show (T.B - T.A) - (T.C - T.A) = -T.a from by
      simp only [OrientedTriangle.a]; abel]
    simp [OrientedTriangle.aLength]
  have hmain : 4 * T.area * R = T.aLength * T.bLength * T.cLength := by
    have h := h2AR
    rw [hnu, hnv, hnuv, hA0eq] at h
    linear_combination h
  have h2R : 2 * R = T.aLength * T.bLength * T.cLength / (2 * T.area) := by
    rw [eq_div_iff (ne_of_gt (by linarith [T.area_pos] : (0:ℝ) < 2 * T.area))]
    linear_combination hmain
  calc T.delta = T.aLength * T.bLength * T.cLength / (2 * T.area) := T.delta_eq_product_div_area
    _ = 2 * R := h2R.symm
    _ = T.circumdiameter := by rw [OrientedTriangle.circumdiameter, ← hR]

end OrientedTriangle

/-! ### `⋄20` A trigonometric identity, Equations (A3) and (A4) -/

theorem sin_three_mul_eq (θ : ℝ) :
    Real.sin (3 * θ) = Real.sin θ * (4 * Real.cos θ ^ 2 - 1) := by
  rw [Real.sin_three_mul]
  have h := Real.sin_sq_add_cos_sq θ
  calc
    3 * Real.sin θ - 4 * Real.sin θ ^ 3 = Real.sin θ * (3 - 4 * Real.sin θ ^ 2) := by ring
    _ = Real.sin θ * (4 * Real.cos θ ^ 2 - 1) := by
      rw [show Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 by linarith]
      ring

/-- Equation (A4), valid for every real `θ`. -/
theorem trigonometric_identity_A4 (θ : ℝ) :
    Real.sin (3 * θ) = 4 * Real.sin θ * Real.sin (thetaStar θ) * Real.sin (thetaStarStar θ) := by
  rw [sin_thetaStarStar, sin_three_mul_eq]
  have hA : Real.sin (thetaStar θ) =
      Real.sin (Real.pi / 3) * Real.cos θ - Real.cos (Real.pi / 3) * Real.sin θ := by
    rw [thetaStar, Real.sin_sub]
  have hB : Real.sin (thetaPrime θ) =
      Real.sin (Real.pi / 3) * Real.cos θ + Real.cos (Real.pi / 3) * Real.sin θ := by
    rw [thetaPrime, Real.sin_add]
  have hAB : Real.sin (thetaStar θ) * Real.sin (thetaPrime θ) =
      3 / 4 * Real.cos θ ^ 2 - 1 / 4 * Real.sin θ ^ 2 := by
    rw [hA, hB, Real.sin_pi_div_three, Real.cos_pi_div_three]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    linear_combination (Real.cos θ ^ 2 / 4) * h3
  have h4 : 4 * Real.sin θ * Real.sin (thetaStar θ) * Real.sin (thetaPrime θ) =
      4 * Real.sin θ * (Real.sin (thetaStar θ) * Real.sin (thetaPrime θ)) := by ring
  rw [h4, hAB]
  have h := Real.sin_sq_add_cos_sq θ
  linear_combination Real.sin θ * h



/-- Equation (A3), with the nonzero denominator made explicit. -/
theorem trigonometric_identity_A3 {θ : ℝ} (h : Real.sin θ ≠ 0) :
    Real.sin (3 * θ) / Real.sin θ =
      4 * Real.sin (thetaStar θ) * Real.sin (thetaStarStar θ) := by
  rw [trigonometric_identity_A4]
  field_simp

/-! ## Appendix B. Angle trisectors and Morley's constellation -/

/-- The colors assigned to sides `BC`, `CA`, `AB`, respectively. -/
inductive TrisectorColor where
  | red | green | blue
  deriving DecidableEq

instance : Fintype TrisectorColor where
  elems := {TrisectorColor.red, TrisectorColor.green, TrisectorColor.blue}
  complete := by
    intro c
    cases c <;> simp

/-- A trisector label `0`, `1`, or `2`, with addition modulo three. -/
abbrev TrisectorLabel := ZMod 3

/-- Real angle corresponding to a label, in units of `2π/3`. -/
def labelAngle (i : TrisectorLabel) : ℝ := (i.val : ℝ) * (2 * Real.pi / 3)

namespace OrientedTriangle

variable {o : Orientation ℝ E (Fin 2)}

/-- Red trisectors at `B`, rotated positively from `BX`. -/
def redB (T : OrientedTriangle E o) (i : TrisectorLabel) : Line E where
  base := T.B
  direction := rotateVector o T.BX.direction (labelAngle i)
  direction_ne_zero := rotateVector_ne_zero o T.BX.direction_ne_zero _
/-- Red trisectors at `C`, rotated negatively from `CX`. -/
def redC (T : OrientedTriangle E o) (j : TrisectorLabel) : Line E where
  base := T.C
  direction := rotateVector o T.CX.direction (-labelAngle j)
  direction_ne_zero := rotateVector_ne_zero o T.CX.direction_ne_zero _
/-- Green trisectors at `C`, rotated positively from `CY`. -/
def greenC (T : OrientedTriangle E o) (i : TrisectorLabel) : Line E where
  base := T.C
  direction := rotateVector o T.CY.direction (labelAngle i)
  direction_ne_zero := rotateVector_ne_zero o T.CY.direction_ne_zero _
/-- Green trisectors at `A`, rotated negatively from `AY`. -/
def greenA (T : OrientedTriangle E o) (j : TrisectorLabel) : Line E where
  base := T.A
  direction := rotateVector o T.AY.direction (-labelAngle j)
  direction_ne_zero := rotateVector_ne_zero o T.AY.direction_ne_zero _
/-- Blue trisectors at `A`, rotated positively from `AZ`. -/
def blueA (T : OrientedTriangle E o) (i : TrisectorLabel) : Line E where
  base := T.A
  direction := rotateVector o T.AZ.direction (labelAngle i)
  direction_ne_zero := rotateVector_ne_zero o T.AZ.direction_ne_zero _
/-- Blue trisectors at `B`, rotated negatively from `BZ`. -/
def blueB (T : OrientedTriangle E o) (j : TrisectorLabel) : Line E where
  base := T.B
  direction := rotateVector o T.BZ.direction (-labelAngle j)
  direction_ne_zero := rotateVector_ne_zero o T.BZ.direction_ne_zero _

@[simp] theorem redB_zero (T : OrientedTriangle E o) : T.redB 0 = T.BX := by
  apply Line.ext <;> simp [redB, BX, labelAngle]
@[simp] theorem redC_zero (T : OrientedTriangle E o) : T.redC 0 = T.CX := by
  apply Line.ext <;> simp [redC, CX, labelAngle]
@[simp] theorem greenC_zero (T : OrientedTriangle E o) : T.greenC 0 = T.CY := by
  apply Line.ext <;> simp [greenC, CY, labelAngle]
@[simp] theorem greenA_zero (T : OrientedTriangle E o) : T.greenA 0 = T.AY := by
  apply Line.ext <;> simp [greenA, AY, labelAngle]
@[simp] theorem blueA_zero (T : OrientedTriangle E o) : T.blueA 0 = T.AZ := by
  apply Line.ext <;> simp [blueA, AZ, labelAngle]
@[simp] theorem blueB_zero (T : OrientedTriangle E o) : T.blueB 0 = T.BZ := by
  apply Line.ext <;> simp [blueB, BZ, labelAngle]

/-- An index for one of the 27 constellation points. -/
structure ConstellationIndex where
  color : TrisectorColor
  first : TrisectorLabel
  second : TrisectorLabel
  deriving DecidableEq, Fintype

/-- Generalization of the fixed-point formula in Corollary 1 to all trisectors. -/
def constellationPoint (T : OrientedTriangle E o) (q : ConstellationIndex) : E :=
  match q.color with
  | .red => rotationFixedPoint o T.C T.B
      (2 * T.gamma - labelAngle q.second) (2 * T.beta - labelAngle q.first)
  | .green => rotationFixedPoint o T.A T.C
      (2 * T.alpha - labelAngle q.second) (2 * T.gamma - labelAngle q.first)
  | .blue => rotationFixedPoint o T.B T.A
      (2 * T.beta - labelAngle q.second) (2 * T.alpha - labelAngle q.first)

/-- Morley's constellation `MC`. -/
def constellation (T : OrientedTriangle E o) : Set E := Set.range T.constellationPoint

/-- The intersection of the two trisectors named by a constellation index. -/
def trisectorPair (T : OrientedTriangle E o) (q : ConstellationIndex) : Line E × Line E :=
  match q.color with
  | .red => (T.redB q.first, T.redC q.second)
  | .green => (T.greenC q.first, T.greenA q.second)
  | .blue => (T.blueA q.first, T.blueB q.second)

theorem m1_area_redC_num (T : OrientedTriangle E o) (j : TrisectorLabel) :
    orientedArea o (T.C - T.B) (rotateVector o (T.A - T.C) (2 * T.gamma - labelAngle j))
      = (‖T.B - T.C‖ * ‖T.A - T.C‖) * Real.sin (T.gamma + labelAngle j) := by
  have hrw : T.C - T.B = (-1 : ℝ) • rotateVector o (T.B - T.C) 0 := by
    rw [rotateVector_zero_angle, neg_one_smul]
    abel
  rw [hrw, m3_area_rot_general (o := o) (T.B - T.C) (T.A - T.C) (3 * T.gamma)
    (‖T.B - T.C‖ * ‖T.A - T.C‖) (m3_key_C T) (-1) 0 (2 * T.gamma - labelAngle j)]
  rw [show 2 * T.gamma - labelAngle j - 0 - 3 * T.gamma = -(T.gamma + labelAngle j) by ring,
    Real.sin_neg]
  ring

/-- The denominator of the intersection parameter of `redB i` and `redC j`. -/
theorem m1_area_redC_den (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    orientedArea o (rotateVector o (T.C - T.B) (T.beta + labelAngle i))
        (rotateVector o (T.A - T.C) (2 * T.gamma - labelAngle j))
      = (‖T.B - T.C‖ * ‖T.A - T.C‖) *
        Real.sin (T.beta + T.gamma + labelAngle i + labelAngle j) := by
  have hrw : rotateVector o (T.C - T.B) (T.beta + labelAngle i)
      = (-1 : ℝ) • rotateVector o (T.B - T.C) (T.beta + labelAngle i) := by
    rw [show T.C - T.B = (-1 : ℝ) • (T.B - T.C) from by rw [neg_one_smul]; abel,
      rotateVector_smul]
  rw [hrw, m3_area_rot_general (o := o) (T.B - T.C) (T.A - T.C) (3 * T.gamma)
    (‖T.B - T.C‖ * ‖T.A - T.C‖) (m3_key_C T) (-1) (T.beta + labelAngle i)
    (2 * T.gamma - labelAngle j)]
  rw [show 2 * T.gamma - labelAngle j - (T.beta + labelAngle i) - 3 * T.gamma
      = -(T.beta + T.gamma + labelAngle i + labelAngle j) by ring, Real.sin_neg]
  ring

/-- Rotation by `π` is negation. -/
theorem m1_rotateVector_pi (v : E) : rotateVector o v Real.pi = -v := by
  apply toComplex_injective o
  rw [toComplex_rotateVector, toComplex_neg]
  have h : ((Circle.exp Real.pi : Circle) : ℂ) = -1 := by
    rw [Circle.coe_exp]
    exact Complex.exp_pi_mul_I
  rw [h, mul_neg, mul_one]

/-- Rotation by an integral multiple of `π`. -/
theorem m1_rotateVector_nat_mul_pi (v : E) (n : ℕ) :
    rotateVector o v (n * Real.pi) = ((-1 : ℝ) ^ n) • v := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [show (↑(k + 1) : ℝ) * Real.pi = Real.pi + k * Real.pi by push_cast; ring,
      rotateVector_add_angle, ih, rotateVector_smul, m1_rotateVector_pi, smul_neg, pow_succ]
    simp [smul_neg, mul_comm]

/-- Rotation by a negative integral multiple of `π`. -/
theorem m1_rotateVector_neg_nat_mul_pi (v : E) (n : ℕ) :
    rotateVector o v (-(n * Real.pi)) = ((-1 : ℝ) ^ n) • v := by
  have h := m1_rotateVector_nat_mul_pi (o := o) v n
  have h2 : rotateVector o (rotateVector o v (n * Real.pi)) (-(n * Real.pi)) = v := by
    rw [← rotateVector_add_angle, show -(n * Real.pi) + n * Real.pi = 0 by ring,
      rotateVector_zero_angle]
  rw [h, rotateVector_smul] at h2
  have hsq : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← mul_pow]
    norm_num
  calc rotateVector o v (-(n * Real.pi))
      = (((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n)) • rotateVector o v (-(n * Real.pi)) := by
        rw [hsq, one_smul]
    _ = ((-1 : ℝ) ^ n) • (((-1 : ℝ) ^ n) • rotateVector o v (-(n * Real.pi))) := by
        rw [mul_smul]
    _ = ((-1 : ℝ) ^ n) • v := by rw [h2]

/-- `sin (β + γ - k π/3) ≠ 0`: no shift of `β+γ` by a multiple of `π/3` is a multiple of `π`. -/
theorem m1_sin_shift_ne (T : OrientedTriangle E o) (k : ℕ) :
    Real.sin (T.beta + T.gamma - k * Real.pi / 3) ≠ 0 := by
  have hsum := T.angle_sum
  have ha := m3_alpha_pos T
  have hbp := m3_beta_pos T
  have hgp := m3_gamma_pos T
  have hb : 0 < T.beta + T.gamma := by linarith
  have hlt : 3 * (T.beta + T.gamma) < Real.pi := by linarith
  intro hs
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
  have hkey : Real.pi * (3 * (n : ℝ) + (k : ℝ)) = 3 * (T.beta + T.gamma) := by
    have h : T.beta + T.gamma = (n : ℝ) * Real.pi + k * Real.pi / 3 := by linarith
    rw [h]; ring
  have hpi := Real.pi_pos
  have h1 : (0 : ℝ) < 3 * (n : ℝ) + (k : ℝ) := by
    apply pos_of_mul_pos_right _ (le_of_lt hpi)
    rw [hkey]; linarith
  have h2 : 3 * (n : ℝ) + (k : ℝ) < 1 := by
    apply lt_of_mul_lt_mul_left _ (le_of_lt hpi)
    rw [hkey, mul_one]; linarith
  have h3 : (0 : ℤ) < 3 * n + (k : ℤ) := by exact_mod_cast h1
  have h4 : 3 * n + (k : ℤ) < 1 := by exact_mod_cast h2
  omega

/-
  EXACT CONSTELLATION FORMULAS (member m6, swarm smwf9bxwn)

  Discharges the remaining constellation target of Appendix B

      theorem constellationPoint_eq_intersection

  together with the exact incidence formulas for all 27 constellation points
  (m6_constellation_mem_redB / _redC / _greenC / _greenA / _blueA / _blueB)
  and their sine-scaled coordinates (m6_constellation_eq_first / _eq_second).

  HOW TO APPLY (checked against the root snapshot md5
  1655abfd842cdc79017f333688134e45, 8010 lines):

  Insert this whole block immediately BEFORE the declaration

      theorem constellationPoint_eq_intersection (T : OrientedTriangle E o)
          (q : ConstellationIndex) : ... := by sorry

  of Appendix B (`namespace OrientedTriangle`, after `trisectorPair`) and DELETE
  that declaration (the block ends with the proved version, with the statement
  byte-identical to the root's).  Everything else stays unchanged; all new names
  are `m6_`-prefixed and none duplicates an existing name.

  The complete assembled file is MorleyC.lean in this directory; `lean MorleyC.lean`
  reports NO errors, and `#print axioms` gives only
  [propext, Classical.choice, Quot.sound] for every declaration below
  (see CheckC.lean / README_C.md).
-/

/-! ### The exact constellation formulas (new, member m6): support lemmas and targets -/

/-! ## Support: complex exponential calculus and the closed form of `rotationFixedPoint` -/

theorem m6_circle_exp_eq (θ : ℝ) :
    (Circle.exp θ : ℂ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  rw [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem m6_conj_circle_exp (θ : ℝ) :
    (starRingEnd ℂ) (Circle.exp θ : ℂ) = (Circle.exp (-θ) : ℂ) := by
  rw [← Circle.coe_inv_eq_conj (Circle.exp θ), ← Circle.exp_neg]

theorem m6_circle_exp_mul (a b : ℝ) :
    (Circle.exp a : ℂ) * (Circle.exp b : ℂ) = (Circle.exp (a + b) : ℂ) := by
  rw [← Circle.coe_mul, Circle.exp_add]

theorem m6_exp_neg_pi_div_two : (Circle.exp (-(Real.pi / 2)) : ℂ) = -Complex.I := by
  rw [m6_circle_exp_eq]
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem m6_one_sub_exp (θ : ℝ) :
    (1 - Circle.exp θ : ℂ) =
      (-2 * Complex.I * (Real.sin (θ / 2) : ℂ)) * (Circle.exp (θ / 2) : ℂ) := by
  rw [one_sub_unit_eq θ]
  have hπ : (Circle.exp (θ / 2 - Real.pi / 2) : ℂ) =
      (Circle.exp (θ / 2) : ℂ) * (-Complex.I) := by
    rw [show θ / 2 - Real.pi / 2 = θ / 2 + -(Real.pi / 2) by ring, Circle.exp_add, Circle.coe_mul,
      m6_exp_neg_pi_div_two]
  rw [hπ]
  ring

theorem m6_circle_ratio (φ ψ : ℝ) (h : Real.sin ((φ + ψ) / 2) ≠ 0) :
    ((1 - Circle.exp ψ : ℂ) / (1 - (Circle.exp φ : ℂ) * Circle.exp ψ)) =
      ((Real.sin (ψ / 2) / Real.sin ((φ + ψ) / 2) : ℝ) : ℂ) * (Circle.exp (-(φ / 2)) : ℂ) := by
  have hA : (φ + ψ) / 2 = ψ / 2 + φ / 2 := by ring
  have hφψ : Real.sin (ψ / 2 + φ / 2) ≠ 0 := by rw [← hA]; exact h
  rw [m6_circle_exp_mul φ ψ, m6_one_sub_exp ψ, m6_one_sub_exp (φ + ψ), hA]
  have hsin : Real.sin (ψ / 2 + φ / 2) ≠ 0 := hφψ
  field_simp
  rw [show (-(φ / 2) : ℝ) = ψ / 2 - (ψ / 2 + φ / 2) by ring, Circle.exp_sub]
  push_cast
  field_simp

theorem m6_rotationFixedPoint_smul_rotate (P Q : E) (φ ψ : ℝ)
    (h : Real.sin ((φ + ψ) / 2) ≠ 0) :
    rotationFixedPoint o P Q φ ψ =
      P + (Real.sin (ψ / 2) / Real.sin ((φ + ψ) / 2)) • rotateVector o (Q - P) (-(φ / 2)) := by
  apply toComplex_injective o
  rw [toComplex_rotationFixedPoint, toComplex_add, toComplex_smul, toComplex_rotateVector,
    m6_circle_ratio φ ψ h]
  ring

theorem m6_sine_identity (B C : ℝ) :
    (Real.sin B : ℂ) * (Circle.exp (-C) : ℂ) + (Real.sin C : ℂ) * (Circle.exp B : ℂ) =
      (Real.sin (B + C) : ℂ) := by
  rw [m6_circle_exp_eq (-C), m6_circle_exp_eq B, Real.sin_add]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Real.sin_neg, Real.cos_neg] <;> ring

theorem m6_rotationFixedPoint_sub_smul (P Q : E) (φ ψ : ℝ)
    (h : Real.sin ((φ + ψ) / 2) ≠ 0) :
    rotationFixedPoint o P Q φ ψ =
      Q - (Real.sin (φ / 2) / Real.sin ((φ + ψ) / 2)) • rotateVector o (Q - P) (ψ / 2) := by
  rw [m6_rotationFixedPoint_smul_rotate P Q φ ψ h]
  have hA : (φ + ψ) / 2 = ψ / 2 + φ / 2 := by ring
  have hS : Real.sin ((φ + ψ) / 2) ≠ 0 := h
  have hid := m6_sine_identity (ψ / 2) (φ / 2)
  rw [show (ψ / 2 + φ / 2) = (φ + ψ) / 2 from by ring] at hid
  have hsin : ((Real.sin (ψ / 2) / Real.sin ((φ + ψ) / 2) : ℝ) : ℂ) * (Circle.exp (-(φ / 2)) : ℂ) +
      ((Real.sin (φ / 2) / Real.sin ((φ + ψ) / 2) : ℝ) : ℂ) * (Circle.exp (ψ / 2) : ℂ) = 1 := by
    have hcast : ((Real.sin ((φ + ψ) / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS
    rw [Complex.ofReal_div, Complex.ofReal_div]
    field_simp
    exact hid
  rw [show Q = P + (Q - P) by abel]
  simp only [add_sub_cancel_left]
  apply toComplex_injective o
  rw [toComplex_add, toComplex_sub, toComplex_add, toComplex_smul, toComplex_smul,
    toComplex_rotateVector, toComplex_rotateVector]
  linear_combination (toComplex o (Q - P)) * hsin


theorem m6_rotateVector_neg (v : E) (θ : ℝ) :
    rotateVector o (-v) θ = -rotateVector o v θ := by
  apply toComplex_injective o
  simp [toComplex_neg]

theorem m6_rfp_double_P (P Q : E) (φ ψ : ℝ) (h : Real.sin (φ + ψ) ≠ 0) :
    rotationFixedPoint o P Q (2 * φ) (2 * ψ) =
      P + (Real.sin ψ / Real.sin (φ + ψ)) • rotateVector o (Q - P) (-φ) := by
  rw [m6_rotationFixedPoint_smul_rotate P Q (2 * φ) (2 * ψ) (by
    rwa [show (2 * φ + 2 * ψ) / 2 = φ + ψ by ring])]
  rw [show (2 * ψ) / 2 = ψ by ring, show (2 * φ + 2 * ψ) / 2 = φ + ψ by ring,
    show -((2 * φ) / 2) = -φ by ring]

theorem m6_rfp_double_Q (P Q : E) (φ ψ : ℝ) (h : Real.sin (φ + ψ) ≠ 0) :
    rotationFixedPoint o P Q (2 * φ) (2 * ψ) =
      Q - (Real.sin φ / Real.sin (φ + ψ)) • rotateVector o (Q - P) ψ := by
  rw [m6_rotationFixedPoint_sub_smul P Q (2 * φ) (2 * ψ) (by
    rwa [show (2 * φ + 2 * ψ) / 2 = φ + ψ by ring])]
  rw [show (2 * φ) / 2 = φ by ring, show (2 * φ + 2 * ψ) / 2 = φ + ψ by ring,
    show (2 * ψ) / 2 = ψ by ring]

/-- From `θ = ∠(u,v)` and positive oriented area: `v` is the image of `u` under the rotation
through `θ`, rescaled by the length ratio. -/
theorem m6_rotate_relation {u v : E} {θ : ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hang : θ = InnerProductGeometry.angle u v) (hpos : 0 < orientedArea o u v) :
    v = (‖v‖ / ‖u‖) • rotateVector o u θ := by
  apply toComplex_injective o
  rw [toComplex_smul, toComplex_rotateVector]
  set a := toComplex o u with ha
  set b := toComplex o v with hb
  have ha0 : a ≠ 0 := by simpa [ha] using hu
  have h1 : (conj a * b).re = ⟪u, v⟫ := by
    simpa [ha, hb] using (toComplex_inner o u v).symm
  have h2 : (conj a * b).im = orientedArea o u v := by
    simpa [ha, hb, orientedArea] using (areaForm_complex (E := E) o u v).symm
  have hcos : Real.cos θ * (‖u‖ * ‖v‖) = ⟪u, v⟫ := by
    rw [hang]; exact InnerProductGeometry.cos_angle_mul_norm_mul_norm u v
  have hsin : Real.sin θ * (‖u‖ * ‖v‖) = orientedArea o u v := by
    rw [hang, mul_comm (Real.sin (InnerProductGeometry.angle u v)) (‖u‖ * ‖v‖)]
    exact sin_angle_mul_norm_mul_norm o hu hv hpos
  have hkey : conj a * b = ((‖v‖ * ‖u‖ : ℝ) : ℂ) * (Circle.exp θ : ℂ) := by
    rw [m6_circle_exp_eq]
    apply Complex.ext
    · rw [h1]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one]
      rw [← hcos]; ring
    · rw [h2]
      simp only [Complex.mul_im, Complex.add_im, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_mul]
      rw [← hsin]; ring
  have hnorm : conj a * a = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    have hna : ‖a‖ = ‖u‖ := by rw [ha, toComplex_norm]
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm, hna]
  have hcoef : ((‖v‖ / ‖u‖ : ℝ) : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ) = ((‖v‖ * ‖u‖ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    have hu0 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    field_simp
  have hgoal : conj a * (((‖v‖ / ‖u‖ : ℝ) : ℂ) * (a * (Circle.exp θ : ℂ))) =
      ((‖v‖ * ‖u‖ : ℝ) : ℂ) * (Circle.exp θ : ℂ) := by
    calc conj a * (((‖v‖ / ‖u‖ : ℝ) : ℂ) * (a * (Circle.exp θ : ℂ)))
        = ((‖v‖ / ‖u‖ : ℝ) : ℂ) * (conj a * a) * (Circle.exp θ : ℂ) := by ring
      _ = ((‖v‖ / ‖u‖ : ℝ) : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ) * (Circle.exp θ : ℂ) := by rw [hnorm]
      _ = ((‖v‖ * ‖u‖ : ℝ) : ℂ) * (Circle.exp θ : ℂ) := by rw [hcoef]
  have hca : (starRingEnd ℂ) a ≠ 0 := by
    intro h
    exact ha0 (by simpa using congrArg (starRingEnd ℂ) h)
  exact mul_left_cancel₀ hca (hkey.trans hgoal.symm)


theorem m6_angle_ne_collinear_BAC (T : OrientedTriangle E o) :
    ¬Collinear ℝ ({T.B, T.A, T.C} : Set E) := by
  have hset : ({T.B, T.A, T.C} : Set E) = {T.A, T.B, T.C} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]; exact T.noncollinear

theorem m6_angle_ne_collinear_CBA (T : OrientedTriangle E o) :
    ¬Collinear ℝ ({T.C, T.B, T.A} : Set E) := by
  have hset : ({T.C, T.B, T.A} : Set E) = {T.A, T.B, T.C} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]; exact T.noncollinear

theorem m6_angle_ne_collinear_ACB (T : OrientedTriangle E o) :
    ¬Collinear ℝ ({T.A, T.C, T.B} : Set E) := by
  have hset : ({T.A, T.C, T.B} : Set E) = {T.A, T.B, T.C} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]; exact T.noncollinear

theorem m6_alpha_pos (T : OrientedTriangle E o) : 0 < T.alpha := by
  have h := EuclideanGeometry.angle_pos_of_not_collinear T.m6_angle_ne_collinear_BAC
  have h2 : T.alpha = EuclideanGeometry.angle T.B T.A T.C / 3 := rfl
  rw [h2]; linarith

theorem m6_alpha_lt (T : OrientedTriangle E o) : T.alpha < Real.pi / 3 := by
  have h := EuclideanGeometry.angle_lt_pi_of_not_collinear T.m6_angle_ne_collinear_BAC
  have h2 : T.alpha = EuclideanGeometry.angle T.B T.A T.C / 3 := rfl
  rw [h2]; linarith

theorem m6_beta_pos (T : OrientedTriangle E o) : 0 < T.beta := by
  have h := EuclideanGeometry.angle_pos_of_not_collinear T.m6_angle_ne_collinear_CBA
  have h2 : T.beta = EuclideanGeometry.angle T.C T.B T.A / 3 := rfl
  rw [h2]; linarith

theorem m6_beta_lt (T : OrientedTriangle E o) : T.beta < Real.pi / 3 := by
  have h := EuclideanGeometry.angle_lt_pi_of_not_collinear T.m6_angle_ne_collinear_CBA
  have h2 : T.beta = EuclideanGeometry.angle T.C T.B T.A / 3 := rfl
  rw [h2]; linarith

theorem m6_gamma_pos (T : OrientedTriangle E o) : 0 < T.gamma := by
  have h := EuclideanGeometry.angle_pos_of_not_collinear T.m6_angle_ne_collinear_ACB
  have h2 : T.gamma = EuclideanGeometry.angle T.A T.C T.B / 3 := rfl
  rw [h2]; linarith

theorem m6_gamma_lt (T : OrientedTriangle E o) : T.gamma < Real.pi / 3 := by
  have h := EuclideanGeometry.angle_lt_pi_of_not_collinear T.m6_angle_ne_collinear_ACB
  have h2 : T.gamma = EuclideanGeometry.angle T.A T.C T.B / 3 := rfl
  rw [h2]; linarith

theorem m6_beta_add_gamma_bounds (T : OrientedTriangle E o) :
    0 < T.beta + T.gamma ∧ T.beta + T.gamma < Real.pi := by
  have hsum := T.angle_sum
  have h1 := T.m6_alpha_pos
  have h2 := T.m6_alpha_lt
  constructor <;> nlinarith [Real.pi_pos]

theorem m6_gamma_add_alpha_bounds (T : OrientedTriangle E o) :
    0 < T.gamma + T.alpha ∧ T.gamma + T.alpha < Real.pi := by
  have hsum := T.angle_sum
  have h1 := T.m6_beta_pos
  have h2 := T.m6_beta_lt
  constructor <;> nlinarith [Real.pi_pos]

theorem m6_alpha_add_beta_bounds (T : OrientedTriangle E o) :
    0 < T.alpha + T.beta ∧ T.alpha + T.beta < Real.pi := by
  have hsum := T.angle_sum
  have h1 := T.m6_gamma_pos
  have h2 := T.m6_gamma_lt
  constructor <;> nlinarith [Real.pi_pos]

theorem m6_sin_beta_add_gamma_ne_zero (T : OrientedTriangle E o) :
    Real.sin (T.beta + T.gamma) ≠ 0 := by
  obtain ⟨h1, h2⟩ := T.m6_beta_add_gamma_bounds
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)

theorem m6_sin_gamma_add_alpha_ne_zero (T : OrientedTriangle E o) :
    Real.sin (T.gamma + T.alpha) ≠ 0 := by
  obtain ⟨h1, h2⟩ := T.m6_gamma_add_alpha_bounds
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)

theorem m6_sin_alpha_add_beta_ne_zero (T : OrientedTriangle E o) :
    Real.sin (T.alpha + T.beta) ≠ 0 := by
  obtain ⟨h1, h2⟩ := T.m6_alpha_add_beta_bounds
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)

theorem m6_area_CA_CB_pos (T : OrientedTriangle E o) :
    0 < orientedArea o (T.A - T.C) (T.B - T.C) := by
  have h : orientedArea o (T.A - T.C) (T.B - T.C) =
      orientedArea o (T.B - T.A) (T.C - T.A) := by
    rw [show T.A - T.C = -(T.C - T.A) from by abel,
      show T.B - T.C = (T.B - T.A) - (T.C - T.A) from by abel, orientedArea, map_neg,
      LinearMap.neg_apply, map_sub, Orientation.areaForm_apply_self, sub_zero,
      Orientation.areaForm_swap o (T.C - T.A) (T.B - T.A), neg_neg, ← orientedArea]
  rw [h]
  exact T.positive

theorem m6_area_BC_BA_pos (T : OrientedTriangle E o) :
    0 < orientedArea o (T.C - T.B) (T.A - T.B) := by
  have h : orientedArea o (T.C - T.B) (T.A - T.B) =
      orientedArea o (T.B - T.A) (T.C - T.A) := by
    rw [show T.C - T.B = (T.C - T.A) - (T.B - T.A) from by abel,
      show T.A - T.B = -(T.B - T.A) from by abel, orientedArea, map_sub, LinearMap.sub_apply,
      map_neg, map_neg, Orientation.areaForm_apply_self, neg_zero, sub_zero,
      Orientation.areaForm_swap o (T.C - T.A) (T.B - T.A), neg_neg, ← orientedArea]
  rw [h]
  exact T.positive

/-- The trisector relation at `C`. -/
theorem m6_trisector_C (T : OrientedTriangle E o) :
    T.B - T.C = (‖T.B - T.C‖ / ‖T.A - T.C‖) •
      rotateVector o (T.A - T.C) (3 * T.gamma) := by
  refine m6_rotate_relation (sub_ne_zero.mpr T.A_ne_C) (sub_ne_zero.mpr T.B_ne_C) ?_
    T.m6_area_CA_CB_pos
  simp only [OrientedTriangle.gamma, EuclideanGeometry.angle, vsub_eq_sub]
  ring

/-- The trisector relation at `A`. -/
theorem m6_trisector_A (T : OrientedTriangle E o) :
    T.C - T.A = (‖T.C - T.A‖ / ‖T.B - T.A‖) •
      rotateVector o (T.B - T.A) (3 * T.alpha) := by
  refine m6_rotate_relation (sub_ne_zero.mpr T.A_ne_B.symm) (sub_ne_zero.mpr T.A_ne_C.symm) ?_
    T.positive
  simp only [OrientedTriangle.alpha, EuclideanGeometry.angle, vsub_eq_sub]
  ring

/-- The trisector relation at `B`. -/
theorem m6_trisector_B (T : OrientedTriangle E o) :
    T.A - T.B = (‖T.A - T.B‖ / ‖T.C - T.B‖) •
      rotateVector o (T.C - T.B) (3 * T.beta) := by
  refine m6_rotate_relation (sub_ne_zero.mpr T.B_ne_C.symm) (sub_ne_zero.mpr T.A_ne_B) ?_
    T.m6_area_BC_BA_pos
  simp only [OrientedTriangle.beta, EuclideanGeometry.angle, vsub_eq_sub]
  ring


/-! ## Label algebra: the `±1` half-angle shift and sine bounds -/

theorem m6_sin_val_pi (i : TrisectorLabel) : Real.sin ((i.val : ℝ) * Real.pi) = 0 :=
  Real.sin_nat_mul_pi i.val

theorem m6_cos_val_pi_ne_zero (i : TrisectorLabel) : Real.cos ((i.val : ℝ) * Real.pi) ≠ 0 := by
  rw [Real.cos_nat_mul_pi]
  positivity

theorem m6_labelAngle_three_halves (i : TrisectorLabel) :
    3 * labelAngle i / 2 = (i.val : ℝ) * Real.pi := by
  simp only [labelAngle]
  ring

/-- Rotating by `3 * labelAngle i / 2` is the sign change `(-1)^i`, i.e. the same or the
opposite direction: labels act by multiples of `2π/3`, whose triple is a multiple of `2π`. -/
theorem m6_circle_exp_val_pi (i : TrisectorLabel) :
    (Circle.exp ((i.val : ℝ) * Real.pi) : ℂ) = (Real.cos ((i.val : ℝ) * Real.pi) : ℂ) := by
  rw [m6_circle_exp_eq, m6_sin_val_pi]
  simp

/-- Rotating by `3 * labelAngle i / 2` is the sign change `(-1)^i`, i.e. the same or the
opposite direction: labels act by multiples of `2π/3`, whose triple is a multiple of `2π`. -/
theorem m6_rot_label_shift (v : E) (a : ℝ) (i : TrisectorLabel) :
    rotateVector o v (a + 3 * labelAngle i / 2) =
      Real.cos ((i.val : ℝ) * Real.pi) • rotateVector o v a := by
  apply toComplex_injective o
  rw [toComplex_rotateVector, toComplex_smul, toComplex_rotateVector, m6_labelAngle_three_halves]
  have hexp : (Circle.exp (a + (i.val : ℝ) * Real.pi) : ℂ) =
      (Real.cos ((i.val : ℝ) * Real.pi) : ℂ) * (Circle.exp a : ℂ) := by
    rw [Circle.exp_add, Circle.coe_mul, m6_circle_exp_val_pi]
    ring
  rw [hexp]
  ring

theorem m6_sin_sub_nat_pi_three_ne_zero (s : ℝ) (h0 : 0 < s) (h1 : s < Real.pi / 3)
    (n : ℕ) (hn : n ≤ 4) : Real.sin (s - (n : ℝ) * Real.pi / 3) ≠ 0 := by
  have hπ := Real.pi_pos
  interval_cases n <;> push_cast
  · simpa using (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith : s < Real.pi)).ne'
  · have hpos : 0 < Real.sin (Real.pi / 3 - s) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have he : Real.sin (s - (↑1 : ℝ) * Real.pi / 3) = -Real.sin (Real.pi / 3 - s) := by
      rw [show s - (↑1 : ℝ) * Real.pi / 3 = -(Real.pi / 3 - s) by push_cast; ring, Real.sin_neg]
    rw [he]; linarith
  · have hpos : 0 < Real.sin (2 * Real.pi / 3 - s) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have he : Real.sin (s - (↑2 : ℝ) * Real.pi / 3) = -Real.sin (2 * Real.pi / 3 - s) := by
      rw [show s - (↑2 : ℝ) * Real.pi / 3 = -(2 * Real.pi / 3 - s) by push_cast; ring, Real.sin_neg]
    rw [he]; linarith
  · have hpos : 0 < Real.sin (Real.pi - s) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have he : Real.sin (s - (↑3 : ℝ) * Real.pi / 3) = -Real.sin (Real.pi - s) := by
      rw [show s - (↑3 : ℝ) * Real.pi / 3 = -(Real.pi - s) by push_cast; ring, Real.sin_neg]
    rw [he]; linarith
  · have hpos : 0 < Real.sin (s + 2 * Real.pi / 3) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have he : Real.sin (s - (↑4 : ℝ) * Real.pi / 3) = Real.sin (s + 2 * Real.pi / 3) := by
      rw [show s - (↑4 : ℝ) * Real.pi / 3 = (s + 2 * Real.pi / 3) - 2 * Real.pi by
        push_cast; ring, Real.sin_sub_two_pi]
    rw [he]
    exact hpos.ne'

theorem m6_sin_add_nat_two_pi_three_ne_zero (s : ℝ) (h0 : 0 < s) (h1 : s < Real.pi / 3)
    (n : ℕ) (hn : n ≤ 4) : Real.sin (s + (n : ℝ) * (2 * Real.pi / 3)) ≠ 0 := by
  have hπ := Real.pi_pos
  interval_cases n <;> push_cast
  · simpa using (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith : s < Real.pi)).ne'
  · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  · have hneg : Real.sin (s - 2 * Real.pi / 3) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    have he : Real.sin (s + (↑2 : ℝ) * (2 * Real.pi / 3)) = Real.sin (s - 2 * Real.pi / 3) := by
      rw [show s + (↑2 : ℝ) * (2 * Real.pi / 3) = (s - 2 * Real.pi / 3) + 2 * Real.pi by
        push_cast; ring, Real.sin_add_two_pi]
    rw [he]; exact hneg.ne
  · have hpos : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
    have he : Real.sin (s + (↑3 : ℝ) * (2 * Real.pi / 3)) = Real.sin s := by
      rw [show s + (↑3 : ℝ) * (2 * Real.pi / 3) = s + 2 * Real.pi by push_cast; ring,
        Real.sin_add_two_pi]
    rw [he]; exact hpos.ne'
  · have hpos : 0 < Real.sin (s + 2 * Real.pi / 3) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have he : Real.sin (s + (↑4 : ℝ) * (2 * Real.pi / 3)) = Real.sin (s + 2 * Real.pi / 3) := by
      rw [show s + (↑4 : ℝ) * (2 * Real.pi / 3) = (s + 2 * Real.pi / 3) + 2 * Real.pi by
        push_cast; ring, Real.sin_add_two_pi]
    rw [he]
    exact hpos.ne'

/-! ## Bounds on the pairwise sums of the thirds, in `(0, π/3)` -/



theorem m6_beta_add_gamma_bounds_lt (T : OrientedTriangle E o) :
    0 < T.beta + T.gamma ∧ T.beta + T.gamma < Real.pi / 3 := by
  have hsum := T.angle_sum
  have h1 := T.m6_alpha_pos
  have hb := T.m6_beta_pos
  have hg := T.m6_gamma_pos
  constructor <;> nlinarith

theorem m6_gamma_add_alpha_bounds_lt (T : OrientedTriangle E o) :
    0 < T.gamma + T.alpha ∧ T.gamma + T.alpha < Real.pi / 3 := by
  have hsum := T.angle_sum
  have hb := T.m6_beta_pos
  have ha := T.m6_alpha_pos
  have hg := T.m6_gamma_pos
  constructor <;> nlinarith

theorem m6_alpha_add_beta_bounds_lt (T : OrientedTriangle E o) :
    0 < T.alpha + T.beta ∧ T.alpha + T.beta < Real.pi / 3 := by
  have hsum := T.angle_sum
  have hg := T.m6_gamma_pos
  have ha := T.m6_alpha_pos
  have hb := T.m6_beta_pos
  constructor <;> nlinarith


/-! ## The area of the two label-shifted trisector directions -/

theorem m6_im_real_mul_exp (m θ : ℝ) :
    (((m : ℝ) : ℂ) * (Circle.exp θ : ℂ)).im = m * Real.sin θ := by
  rw [m6_circle_exp_eq]
  simp only [Complex.mul_im, Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_mul]
  ring

theorem m6_area_label {P Q R : E} {φ θ ρ : ℝ} (hPR : P ≠ R) (hQR : Q ≠ R) (hρ : ρ ≠ 0)
    (hrel : Q - R = ρ • rotateVector o (P - R) (3 * φ)) (i j : TrisectorLabel) :
    orientedArea o (rotateVector o (R - Q) (θ + labelAngle i))
        (rotateVector o (P - R) (2 * φ - labelAngle j)) =
      ρ * ‖toComplex o (P - R)‖ ^ 2 * Real.sin (θ + φ + labelAngle i + labelAngle j) := by
  set u := toComplex o (P - R) with hu
  set w := toComplex o (Q - R) with hw
  have hu0 : u ≠ 0 := by
    rw [hu, toComplex_sub, sub_ne_zero]
    intro h
    exact hPR (toComplex_injective o h)
  have hnorm : conj u * u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    have hna : ‖u‖ = ‖P - R‖ := by rw [hu, toComplex_norm]
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm, hna]
  have hrel_c : w = (ρ : ℂ) * (u * (Circle.exp (3 * φ) : ℂ)) := by
    rw [hw, hu, hrel, toComplex_smul, toComplex_rotateVector]
  have hRQ : toComplex o (R - Q) = -w := by
    rw [hw, show R - Q = -(Q - R) by abel, toComplex_neg]
  have hkey : conj w * u = ((ρ * ‖u‖ ^ 2 : ℝ) : ℂ) * (Circle.exp (-(3 * φ)) : ℂ) := by
    rw [hrel_c, map_mul, map_mul, Complex.conj_ofReal, m6_conj_circle_exp]
    calc (ρ : ℂ) * (conj u * (Circle.exp (-(3 * φ)) : ℂ)) * u
        = (ρ : ℂ) * (conj u * u) * (Circle.exp (-(3 * φ)) : ℂ) := by ring
      _ = (ρ : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ) * (Circle.exp (-(3 * φ)) : ℂ) := by rw [hnorm]
      _ = ((ρ * ‖u‖ ^ 2 : ℝ) : ℂ) * (Circle.exp (-(3 * φ)) : ℂ) := by
            rw [← Complex.ofReal_mul]
  have hmain : ((-(conj w) * (Circle.exp (-(θ + labelAngle i)) : ℂ)) *
      (u * (Circle.exp (2 * φ - labelAngle j) : ℂ))).im =
      ρ * ‖u‖ ^ 2 * Real.sin (θ + φ + labelAngle i + labelAngle j) := by
    have hcongr : (-(conj w) * (Circle.exp (-(θ + labelAngle i)) : ℂ)) *
        (u * (Circle.exp (2 * φ - labelAngle j) : ℂ))
        = -(((ρ * ‖u‖ ^ 2 : ℝ) : ℂ) *
            (Circle.exp (-(θ + φ + labelAngle i + labelAngle j)) : ℂ)) := by
      have hre : (-(conj w) * (Circle.exp (-(θ + labelAngle i)) : ℂ)) *
          (u * (Circle.exp (2 * φ - labelAngle j) : ℂ))
          = -((conj w * u) * ((Circle.exp (-(θ + labelAngle i)) : ℂ) *
              (Circle.exp (2 * φ - labelAngle j) : ℂ))) := by ring
      have hmul1 : ((Circle.exp (-(θ + labelAngle i)) : ℂ) *
          (Circle.exp (2 * φ - labelAngle j) : ℂ))
          = (Circle.exp (-(θ + labelAngle i) + (2 * φ - labelAngle j)) : ℂ) :=
        m6_circle_exp_mul _ _
      rw [hre, hmul1, hkey]
      have hmul2 : ((Circle.exp (-(3 * φ)) : ℂ) *
          (Circle.exp (-(θ + labelAngle i) + (2 * φ - labelAngle j)) : ℂ))
          = (Circle.exp (-(3 * φ) + (-(θ + labelAngle i) + (2 * φ - labelAngle j))) : ℂ) :=
        m6_circle_exp_mul _ _
      rw [show -(((ρ * ‖u‖ ^ 2 : ℝ) : ℂ) * (Circle.exp (-(3 * φ)) : ℂ) *
          (Circle.exp (-(θ + labelAngle i) + (2 * φ - labelAngle j)) : ℂ))
          = -(((ρ * ‖u‖ ^ 2 : ℝ) : ℂ) * ((Circle.exp (-(3 * φ)) : ℂ) *
            (Circle.exp (-(θ + labelAngle i) + (2 * φ - labelAngle j)) : ℂ))) from by ring, hmul2]
      rw [show -(3 * φ) + (-(θ + labelAngle i) + (2 * φ - labelAngle j))
          = -(θ + φ + labelAngle i + labelAngle j) from by ring]
    rw [hcongr]
    show (-(((ρ * ‖u‖ ^ 2 : ℝ) : ℂ) *
      (Circle.exp (-(θ + φ + labelAngle i + labelAngle j)) : ℂ))).im = _
    rw [Complex.neg_im, m6_im_real_mul_exp, Real.sin_neg]
    ring
  rw [orientedArea, areaForm_complex, toComplex_rotateVector, toComplex_rotateVector, hRQ,
    map_mul, map_neg, m6_conj_circle_exp]
  exact hmain

theorem m6_rfp_P_shift (P Q : E) (φ θ α β : ℝ)
    (h : Real.sin (θ + φ - (α + β) / 2) ≠ 0) :
    rotationFixedPoint o P Q (2 * φ - β) (2 * θ - α) =
      P + (Real.sin (θ - α / 2) / Real.sin (θ + φ - (α + β) / 2)) •
        rotateVector o (Q - P) (-(φ - β / 2)) := by
  have h' : Real.sin (((2 * φ - β) + (2 * θ - α)) / 2) ≠ 0 := by
    rwa [show ((2 * φ - β) + (2 * θ - α)) / 2 = θ + φ - (α + β) / 2 by ring]
  rw [m6_rotationFixedPoint_smul_rotate P Q (2 * φ - β) (2 * θ - α) h']
  rw [show (2 * θ - α) / 2 = θ - α / 2 by ring,
    show ((2 * φ - β) + (2 * θ - α)) / 2 = θ + φ - (α + β) / 2 by ring,
    show -((2 * φ - β) / 2) = -(φ - β / 2) by ring]

theorem m6_rfp_Q_shift (P Q : E) (φ θ α β : ℝ)
    (h : Real.sin (θ + φ - (α + β) / 2) ≠ 0) :
    rotationFixedPoint o P Q (2 * φ - β) (2 * θ - α) =
      Q - (Real.sin (φ - β / 2) / Real.sin (θ + φ - (α + β) / 2)) •
        rotateVector o (Q - P) (θ - α / 2) := by
  have h' : Real.sin (((2 * φ - β) + (2 * θ - α)) / 2) ≠ 0 := by
    rwa [show ((2 * φ - β) + (2 * θ - α)) / 2 = θ + φ - (α + β) / 2 by ring]
  rw [m6_rotationFixedPoint_sub_smul P Q (2 * φ - β) (2 * θ - α) h']
  rw [show (2 * φ - β) / 2 = φ - β / 2 by ring,
    show ((2 * φ - β) + (2 * θ - α)) / 2 = θ + φ - (α + β) / 2 by ring,
    show (2 * θ - α) / 2 = θ - α / 2 by ring]

/-! ## The 27 constellation points as intersections of label-shifted trisectors -/

/-- The explicit position of the constellation point on the first (label-shifted) trisector. -/
theorem m6_constellation_eq_first {P Q R : E} {φ θ : ℝ} (i j : TrisectorLabel)
    (hsin1 : Real.sin (θ + φ - (labelAngle i + labelAngle j) / 2) ≠ 0) :
    rotationFixedPoint o R Q (2 * φ - labelAngle j) (2 * θ - labelAngle i) =
      Q + ((Real.sin (φ - labelAngle j / 2) /
        Real.sin (θ + φ - (labelAngle i + labelAngle j) / 2)) /
          Real.cos ((i.val : ℝ) * Real.pi)) • rotateVector o (R - Q) (θ + labelAngle i) := by
  have hQ := m6_rfp_Q_shift (o := o) R Q φ θ (labelAngle i) (labelAngle j) hsin1
  have hci : Real.cos ((i.val : ℝ) * Real.pi) ≠ 0 := m6_cos_val_pi_ne_zero i
  have hsi : θ - labelAngle i / 2 + 3 * labelAngle i / 2 = θ + labelAngle i := by ring
  have hshift : rotateVector o (R - Q) (θ + labelAngle i) =
      Real.cos ((i.val : ℝ) * Real.pi) • rotateVector o (R - Q) (θ - labelAngle i / 2) := by
    have h := m6_rot_label_shift (o := o) (R - Q) (θ - labelAngle i / 2) i
    rwa [hsi] at h
  have hneg : rotateVector o (Q - R) (θ - labelAngle i / 2) =
      -rotateVector o (R - Q) (θ - labelAngle i / 2) := by
    rw [show Q - R = -(R - Q) by abel, m6_rotateVector_neg]
  rw [hQ, hneg, smul_neg, sub_neg_eq_add, hshift, smul_smul]
  congr 1
  field_simp

/-- The explicit position of the constellation point on the second (label-shifted) trisector. -/
theorem m6_constellation_eq_second {P Q R : E} {φ θ ρ : ℝ} (i j : TrisectorLabel)
    (hρ : ρ ≠ 0) (hrel : Q - R = ρ • rotateVector o (P - R) (3 * φ))
    (hsin1 : Real.sin (θ + φ - (labelAngle i + labelAngle j) / 2) ≠ 0) :
    rotationFixedPoint o R Q (2 * φ - labelAngle j) (2 * θ - labelAngle i) =
      R + ((Real.sin (θ - labelAngle i / 2) /
        Real.sin (θ + φ - (labelAngle i + labelAngle j) / 2)) * ρ *
          Real.cos ((j.val : ℝ) * Real.pi)) • rotateVector o (P - R) (2 * φ - labelAngle j) := by
  have hP := m6_rfp_P_shift (o := o) R Q φ θ (labelAngle i) (labelAngle j) hsin1
  have hsj : 2 * φ - labelAngle j + 3 * labelAngle j / 2 = 2 * φ + labelAngle j / 2 := by ring
  have hrot1 : rotateVector o (Q - R) (-(φ - labelAngle j / 2)) =
      ρ • rotateVector o (P - R) (2 * φ + labelAngle j / 2) := by
    rw [hrel, rotateVector_smul, ← rotateVector_add_angle,
      show -(φ - labelAngle j / 2) + 3 * φ = 2 * φ + labelAngle j / 2 by ring]
  have hshiftj : rotateVector o (P - R) (2 * φ + labelAngle j / 2) =
      Real.cos ((j.val : ℝ) * Real.pi) • rotateVector o (P - R) (2 * φ - labelAngle j) := by
    have h := m6_rot_label_shift (o := o) (P - R) (2 * φ - labelAngle j) j
    rwa [hsj] at h
  rw [hP, hrot1, hshiftj, smul_smul, smul_smul]

/-- The intersection of the two label-shifted trisectors through `Q` and `R` is the
constellation point of that label pair; the lines are given by their base/direction data. -/
theorem m6_constellation_general {P Q R : E} {φ θ ρ : ℝ} (i j : TrisectorLabel)
    (hQR : Q ≠ R) (hPR : P ≠ R) (hρ : ρ ≠ 0)
    (hrel : Q - R = ρ • rotateVector o (P - R) (3 * φ))
    (hsin1 : Real.sin (θ + φ - (labelAngle i + labelAngle j) / 2) ≠ 0)
    (hsin2 : Real.sin (θ + φ + labelAngle i + labelAngle j) ≠ 0)
    (ℓ₁ ℓ₂ : Line E) (h1b : ℓ₁.base = Q)
    (h1d : ℓ₁.direction = rotateVector o (R - Q) (θ + labelAngle i))
    (h2b : ℓ₂.base = R)
    (h2d : ℓ₂.direction = rotateVector o (P - R) (2 * φ - labelAngle j)) :
    rotationFixedPoint o R Q (2 * φ - labelAngle j) (2 * θ - labelAngle i) =
      Line.intersection o ℓ₁ ℓ₂ := by
  have h1 := m6_constellation_eq_first (o := o) (P := P) (Q := Q) (R := R) (φ := φ) (θ := θ) i j hsin1
  have h2 := m6_constellation_eq_second (o := o) (P := P) (Q := Q) (R := R) (φ := φ) (θ := θ)
    (ρ := ρ) i j hρ hrel hsin1
  have hmem1 : ℓ₁.mem (rotationFixedPoint o R Q (2 * φ - labelAngle j) (2 * θ - labelAngle i)) := by
    refine ⟨(Real.sin (φ - labelAngle j / 2) /
      Real.sin (θ + φ - (labelAngle i + labelAngle j) / 2)) /
        Real.cos ((i.val : ℝ) * Real.pi), ?_⟩
    rw [h1b, h1d]
    exact h1
  have hmem2 : ℓ₂.mem (rotationFixedPoint o R Q (2 * φ - labelAngle j) (2 * θ - labelAngle i)) := by
    refine ⟨(Real.sin (θ - labelAngle i / 2) /
      Real.sin (θ + φ - (labelAngle i + labelAngle j) / 2)) * ρ *
        Real.cos ((j.val : ℝ) * Real.pi), ?_⟩
    rw [h2b, h2d]
    exact h2
  have harea := m6_area_label (o := o) (P := P) (Q := Q) (R := R) (φ := φ) (θ := θ) (ρ := ρ)
    hPR hQR hρ hrel i j
  have hρu : ρ * ‖toComplex o (P - R)‖ ^ 2 ≠ 0 := by
    have h2' : toComplex o (P - R) ≠ 0 := by
      rw [toComplex_sub, sub_ne_zero]
      intro h
      exact hPR (toComplex_injective o h)
    have h1' : (0 : ℝ) < ‖toComplex o (P - R)‖ ^ 2 := by positivity
    exact mul_ne_zero hρ h1'.ne'
  have hnp : ¬Line.parallel o ℓ₁ ℓ₂ := by
    rw [Line.parallel, h1d, h2d, harea]
    exact mul_ne_zero hρu hsin2
  exact intersection_unique o ℓ₁ ℓ₂ hnp hmem1 hmem2

/-! ## The three colour families -/

theorem m6_redB_dir (T : OrientedTriangle E o) (i : TrisectorLabel) :
    (T.redB i).direction = rotateVector o (T.C - T.B) (T.beta + labelAngle i) := by
  show rotateVector o (rotateVector o (T.C - T.B) T.beta) (labelAngle i) = _
  rw [← rotateVector_add_angle, add_comm]

theorem m6_redC_dir (T : OrientedTriangle E o) (j : TrisectorLabel) :
    (T.redC j).direction = rotateVector o (T.A - T.C) (2 * T.gamma - labelAngle j) := by
  show rotateVector o (rotateVector o (T.A - T.C) (2 * T.gamma)) (-labelAngle j) = _
  rw [← rotateVector_add_angle, show -labelAngle j + 2 * T.gamma = 2 * T.gamma - labelAngle j by ring]

theorem m6_sin_shift_sub_ne_zero {s : ℝ} (h0 : 0 < s) (h1 : s < Real.pi / 3)
    (i j : TrisectorLabel) :
    Real.sin (s - (labelAngle i + labelAngle j) / 2) ≠ 0 := by
  have hlag : (labelAngle i + labelAngle j) / 2 = ((i.val + j.val : ℕ) : ℝ) * Real.pi / 3 := by
    simp only [labelAngle, Nat.cast_add]; ring
  have hi : i.val < 3 := ZMod.val_lt i
  have hj : j.val < 3 := ZMod.val_lt j
  rw [hlag]
  exact m6_sin_sub_nat_pi_three_ne_zero s h0 h1 (i.val + j.val) (by omega)

theorem m6_sin_shift_add_ne_zero {s : ℝ} (h0 : 0 < s) (h1 : s < Real.pi / 3)
    (i j : TrisectorLabel) :
    Real.sin (s + labelAngle i + labelAngle j) ≠ 0 := by
  have hlag : labelAngle i + labelAngle j = ((i.val + j.val : ℕ) : ℝ) * (2 * Real.pi / 3) := by
    simp only [labelAngle, Nat.cast_add]; ring
  have hi : i.val < 3 := ZMod.val_lt i
  have hj : j.val < 3 := ZMod.val_lt j
  rw [show s + labelAngle i + labelAngle j = s + (labelAngle i + labelAngle j) by ring, hlag]
  exact m6_sin_add_nat_two_pi_three_ne_zero s h0 h1 (i.val + j.val) (by omega)

theorem m6_constellation_red (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    rotationFixedPoint o T.C T.B (2 * T.gamma - labelAngle j) (2 * T.beta - labelAngle i) =
      Line.intersection o (T.redB i) (T.redC j) := by
  obtain ⟨h0, h1⟩ := T.m6_beta_add_gamma_bounds_lt
  have hsin1 := m6_sin_shift_sub_ne_zero h0 h1 i j
  have hsin2 := m6_sin_shift_add_ne_zero h0 h1 i j
  have hρ : ‖T.B - T.C‖ / ‖T.A - T.C‖ ≠ 0 := by
    have h1' : (0 : ℝ) < ‖T.B - T.C‖ := norm_pos_iff.mpr (sub_ne_zero.mpr T.B_ne_C)
    have h2' : (0 : ℝ) < ‖T.A - T.C‖ := norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_C)
    positivity
  exact m6_constellation_general (o := o) (P := T.A) (Q := T.B) (R := T.C)
    (φ := T.gamma) (θ := T.beta) (ρ := ‖T.B - T.C‖ / ‖T.A - T.C‖) i j
    T.B_ne_C T.A_ne_C hρ T.m6_trisector_C hsin1 hsin2
    (T.redB i) (T.redC j) rfl (m6_redB_dir T i) rfl (m6_redC_dir T j)

theorem m6_greenC_dir (T : OrientedTriangle E o) (i : TrisectorLabel) :
    (T.greenC i).direction = rotateVector o (T.A - T.C) (T.gamma + labelAngle i) := by
  show rotateVector o (rotateVector o (T.A - T.C) T.gamma) (labelAngle i) = _
  rw [← rotateVector_add_angle, add_comm]

theorem m6_greenA_dir (T : OrientedTriangle E o) (j : TrisectorLabel) :
    (T.greenA j).direction = rotateVector o (T.B - T.A) (2 * T.alpha - labelAngle j) := by
  show rotateVector o (rotateVector o (T.B - T.A) (2 * T.alpha)) (-labelAngle j) = _
  rw [← rotateVector_add_angle, show -labelAngle j + 2 * T.alpha = 2 * T.alpha - labelAngle j by ring]

theorem m6_constellation_green (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    rotationFixedPoint o T.A T.C (2 * T.alpha - labelAngle j) (2 * T.gamma - labelAngle i) =
      Line.intersection o (T.greenC i) (T.greenA j) := by
  obtain ⟨h0, h1⟩ := T.m6_gamma_add_alpha_bounds_lt
  have hsin1 := m6_sin_shift_sub_ne_zero h0 h1 i j
  have hsin2 := m6_sin_shift_add_ne_zero h0 h1 i j
  have hρ : ‖T.C - T.A‖ / ‖T.B - T.A‖ ≠ 0 := by
    have h1' : (0 : ℝ) < ‖T.C - T.A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_C.symm)
    have h2' : (0 : ℝ) < ‖T.B - T.A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_B.symm)
    positivity
  exact m6_constellation_general (o := o) (P := T.B) (Q := T.C) (R := T.A)
    (φ := T.alpha) (θ := T.gamma) (ρ := ‖T.C - T.A‖ / ‖T.B - T.A‖) i j
    T.A_ne_C.symm T.A_ne_B.symm hρ T.m6_trisector_A hsin1 hsin2
    (T.greenC i) (T.greenA j) rfl (m6_greenC_dir T i) rfl (m6_greenA_dir T j)

theorem m6_blueA_dir (T : OrientedTriangle E o) (i : TrisectorLabel) :
    (T.blueA i).direction = rotateVector o (T.B - T.A) (T.alpha + labelAngle i) := by
  show rotateVector o (rotateVector o (T.B - T.A) T.alpha) (labelAngle i) = _
  rw [← rotateVector_add_angle, add_comm]

theorem m6_blueB_dir (T : OrientedTriangle E o) (j : TrisectorLabel) :
    (T.blueB j).direction = rotateVector o (T.C - T.B) (2 * T.beta - labelAngle j) := by
  show rotateVector o (rotateVector o (T.C - T.B) (2 * T.beta)) (-labelAngle j) = _
  rw [← rotateVector_add_angle, show -labelAngle j + 2 * T.beta = 2 * T.beta - labelAngle j by ring]

theorem m6_constellation_blue (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    rotationFixedPoint o T.B T.A (2 * T.beta - labelAngle j) (2 * T.alpha - labelAngle i) =
      Line.intersection o (T.blueA i) (T.blueB j) := by
  obtain ⟨h0, h1⟩ := T.m6_alpha_add_beta_bounds_lt
  have hsin1 := m6_sin_shift_sub_ne_zero h0 h1 i j
  have hsin2 := m6_sin_shift_add_ne_zero h0 h1 i j
  have hρ : ‖T.A - T.B‖ / ‖T.C - T.B‖ ≠ 0 := by
    have h1' : (0 : ℝ) < ‖T.A - T.B‖ := norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_B)
    have h2' : (0 : ℝ) < ‖T.C - T.B‖ := norm_pos_iff.mpr (sub_ne_zero.mpr T.B_ne_C.symm)
    positivity
  exact m6_constellation_general (o := o) (P := T.C) (Q := T.A) (R := T.B)
    (φ := T.beta) (θ := T.alpha) (ρ := ‖T.A - T.B‖ / ‖T.C - T.B‖) i j
    T.A_ne_B T.B_ne_C.symm hρ T.m6_trisector_B hsin1 hsin2
    (T.blueA i) (T.blueB j) rfl (m6_blueA_dir T i) rfl (m6_blueB_dir T j)


/-! ## Incidence of the constellation points with their trisectors -/

theorem m6_constellation_mem_redB (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    (T.redB i).mem (rotationFixedPoint o T.C T.B (2 * T.gamma - labelAngle j)
      (2 * T.beta - labelAngle i)) := by
  obtain ⟨h0, h1⟩ := T.m6_beta_add_gamma_bounds_lt
  have hsin1 := m6_sin_shift_sub_ne_zero h0 h1 i j
  have heq := m6_constellation_eq_first (o := o) (P := T.A) (Q := T.B) (R := T.C)
    (φ := T.gamma) (θ := T.beta) i j hsin1
  refine ⟨(Real.sin (T.gamma - labelAngle j / 2) /
    Real.sin (T.beta + T.gamma - (labelAngle i + labelAngle j) / 2)) /
      Real.cos ((i.val : ℝ) * Real.pi), ?_⟩
  rw [show (T.redB i).base = T.B from rfl, m6_redB_dir]
  exact heq

theorem m6_constellation_mem_redC (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    (T.redC j).mem (rotationFixedPoint o T.C T.B (2 * T.gamma - labelAngle j)
      (2 * T.beta - labelAngle i)) := by
  obtain ⟨h0, h1⟩ := T.m6_beta_add_gamma_bounds_lt
  have hsin1 := m6_sin_shift_sub_ne_zero h0 h1 i j
  have hρ : ‖T.B - T.C‖ / ‖T.A - T.C‖ ≠ 0 := by
    have h1' : (0 : ℝ) < ‖T.B - T.C‖ := norm_pos_iff.mpr (sub_ne_zero.mpr T.B_ne_C)
    have h2' : (0 : ℝ) < ‖T.A - T.C‖ := norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_C)
    positivity
  have heq := m6_constellation_eq_second (o := o) (P := T.A) (Q := T.B) (R := T.C)
    (φ := T.gamma) (θ := T.beta) (ρ := ‖T.B - T.C‖ / ‖T.A - T.C‖) i j hρ T.m6_trisector_C hsin1
  refine ⟨(Real.sin (T.beta - labelAngle i / 2) /
    Real.sin (T.beta + T.gamma - (labelAngle i + labelAngle j) / 2)) *
      (‖T.B - T.C‖ / ‖T.A - T.C‖) * Real.cos ((j.val : ℝ) * Real.pi), ?_⟩
  rw [show (T.redC j).base = T.C from rfl, m6_redC_dir]
  exact heq

theorem m6_constellation_mem_greenC (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    (T.greenC i).mem (rotationFixedPoint o T.A T.C (2 * T.alpha - labelAngle j)
      (2 * T.gamma - labelAngle i)) := by
  obtain ⟨h0, h1⟩ := T.m6_gamma_add_alpha_bounds_lt
  have hsin1 := m6_sin_shift_sub_ne_zero h0 h1 i j
  have heq := m6_constellation_eq_first (o := o) (P := T.B) (Q := T.C) (R := T.A)
    (φ := T.alpha) (θ := T.gamma) i j hsin1
  refine ⟨(Real.sin (T.alpha - labelAngle j / 2) /
    Real.sin (T.gamma + T.alpha - (labelAngle i + labelAngle j) / 2)) /
      Real.cos ((i.val : ℝ) * Real.pi), ?_⟩
  rw [show (T.greenC i).base = T.C from rfl, m6_greenC_dir]
  exact heq

theorem m6_constellation_mem_greenA (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    (T.greenA j).mem (rotationFixedPoint o T.A T.C (2 * T.alpha - labelAngle j)
      (2 * T.gamma - labelAngle i)) := by
  obtain ⟨h0, h1⟩ := T.m6_gamma_add_alpha_bounds_lt
  have hsin1 := m6_sin_shift_sub_ne_zero h0 h1 i j
  have hρ : ‖T.C - T.A‖ / ‖T.B - T.A‖ ≠ 0 := by
    have h1' : (0 : ℝ) < ‖T.C - T.A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_C.symm)
    have h2' : (0 : ℝ) < ‖T.B - T.A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_B.symm)
    positivity
  have heq := m6_constellation_eq_second (o := o) (P := T.B) (Q := T.C) (R := T.A)
    (φ := T.alpha) (θ := T.gamma) (ρ := ‖T.C - T.A‖ / ‖T.B - T.A‖) i j hρ T.m6_trisector_A hsin1
  refine ⟨(Real.sin (T.gamma - labelAngle i / 2) /
    Real.sin (T.gamma + T.alpha - (labelAngle i + labelAngle j) / 2)) *
      (‖T.C - T.A‖ / ‖T.B - T.A‖) * Real.cos ((j.val : ℝ) * Real.pi), ?_⟩
  rw [show (T.greenA j).base = T.A from rfl, m6_greenA_dir]
  exact heq

theorem m6_constellation_mem_blueA (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    (T.blueA i).mem (rotationFixedPoint o T.B T.A (2 * T.beta - labelAngle j)
      (2 * T.alpha - labelAngle i)) := by
  obtain ⟨h0, h1⟩ := T.m6_alpha_add_beta_bounds_lt
  have hsin1 := m6_sin_shift_sub_ne_zero h0 h1 i j
  have heq := m6_constellation_eq_first (o := o) (P := T.C) (Q := T.A) (R := T.B)
    (φ := T.beta) (θ := T.alpha) i j hsin1
  refine ⟨(Real.sin (T.beta - labelAngle j / 2) /
    Real.sin (T.alpha + T.beta - (labelAngle i + labelAngle j) / 2)) /
      Real.cos ((i.val : ℝ) * Real.pi), ?_⟩
  rw [show (T.blueA i).base = T.A from rfl, m6_blueA_dir]
  exact heq

theorem m6_constellation_mem_blueB (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    (T.blueB j).mem (rotationFixedPoint o T.B T.A (2 * T.beta - labelAngle j)
      (2 * T.alpha - labelAngle i)) := by
  obtain ⟨h0, h1⟩ := T.m6_alpha_add_beta_bounds_lt
  have hsin1 := m6_sin_shift_sub_ne_zero h0 h1 i j
  have hρ : ‖T.A - T.B‖ / ‖T.C - T.B‖ ≠ 0 := by
    have h1' : (0 : ℝ) < ‖T.A - T.B‖ := norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_B)
    have h2' : (0 : ℝ) < ‖T.C - T.B‖ := norm_pos_iff.mpr (sub_ne_zero.mpr T.B_ne_C.symm)
    positivity
  have heq := m6_constellation_eq_second (o := o) (P := T.C) (Q := T.A) (R := T.B)
    (φ := T.beta) (θ := T.alpha) (ρ := ‖T.A - T.B‖ / ‖T.C - T.B‖) i j hρ T.m6_trisector_B hsin1
  refine ⟨(Real.sin (T.alpha - labelAngle i / 2) /
    Real.sin (T.alpha + T.beta - (labelAngle i + labelAngle j) / 2)) *
      (‖T.A - T.B‖ / ‖T.C - T.B‖) * Real.cos ((j.val : ℝ) * Real.pi), ?_⟩
  rw [show (T.blueB j).base = T.B from rfl, m6_blueB_dir]
  exact heq

/-- **The exact constellation formula**: each of the 27 constellation points is the
intersection of the two label-shifted trisectors indexed by its colour and labels. -/
theorem constellationPoint_eq_intersection (T : OrientedTriangle E o)
    (q : ConstellationIndex) :
    T.constellationPoint q =
      Line.intersection o (T.trisectorPair q).1 (T.trisectorPair q).2 := by
  rcases q with ⟨c, i, j⟩
  cases c
  · show rotationFixedPoint o T.C T.B (2 * T.gamma - labelAngle j) (2 * T.beta - labelAngle i) = _
    exact m6_constellation_red T i j
  · show rotationFixedPoint o T.A T.C (2 * T.alpha - labelAngle j) (2 * T.gamma - labelAngle i) = _
    exact m6_constellation_green T i j
  · show rotationFixedPoint o T.B T.A (2 * T.beta - labelAngle j) (2 * T.alpha - labelAngle i) = _
    exact m6_constellation_blue T i j

theorem constellationPoint_fixed_red (T : OrientedTriangle E o) (i j : TrisectorLabel)
    (h : (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
      Circle.exp (2 * T.gamma - labelAngle j) ≠ 1) :
    rotation o T.B (2 * T.beta - labelAngle i)
      (rotation o T.C (2 * T.gamma - labelAngle j)
        (T.constellationPoint ⟨.red, i, j⟩)) = T.constellationPoint ⟨.red, i, j⟩  := by
  have h0 : (1 - (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) * Circle.exp (2 * T.beta - labelAngle i)) ≠ 0 := by
    rw [sub_ne_zero]
    exact Ne.symm (by simpa [mul_comm] using h)
  exact (rotation_rotation_unique_fixedPoint o h0).mpr rfl

theorem constellationPoint_fixed_green (T : OrientedTriangle E o) (i j : TrisectorLabel)
    (h : (Circle.exp (2 * T.gamma - labelAngle i) : ℂ) *
      Circle.exp (2 * T.alpha - labelAngle j) ≠ 1) :
    rotation o T.C (2 * T.gamma - labelAngle i)
      (rotation o T.A (2 * T.alpha - labelAngle j)
        (T.constellationPoint ⟨.green, i, j⟩)) = T.constellationPoint ⟨.green, i, j⟩  := by
  have h0 : (1 - (Circle.exp (2 * T.alpha - labelAngle j) : ℂ) * Circle.exp (2 * T.gamma - labelAngle i)) ≠ 0 := by
    rw [sub_ne_zero]
    exact Ne.symm (by simpa [mul_comm] using h)
  exact (rotation_rotation_unique_fixedPoint o h0).mpr rfl

theorem constellationPoint_fixed_blue (T : OrientedTriangle E o) (i j : TrisectorLabel)
    (h : (Circle.exp (2 * T.alpha - labelAngle i) : ℂ) *
      Circle.exp (2 * T.beta - labelAngle j) ≠ 1) :
    rotation o T.A (2 * T.alpha - labelAngle i)
      (rotation o T.B (2 * T.beta - labelAngle j)
        (T.constellationPoint ⟨.blue, i, j⟩)) = T.constellationPoint ⟨.blue, i, j⟩  := by
  have h0 : (1 - (Circle.exp (2 * T.beta - labelAngle j) : ℂ) * Circle.exp (2 * T.alpha - labelAngle i)) ≠ 0 := by
    rw [sub_ne_zero]
    exact Ne.symm (by simpa [mul_comm] using h)
  exact (rotation_rotation_unique_fixedPoint o h0).mpr rfl

@[simp] theorem constellation_red00 (T : OrientedTriangle E o) :
    T.constellationPoint ⟨.red, 0, 0⟩ = T.X := by
  simp [constellationPoint, X, labelAngle]
@[simp] theorem constellation_green00 (T : OrientedTriangle E o) :
    T.constellationPoint ⟨.green, 0, 0⟩ = T.Y := by
  simp [constellationPoint, Y, labelAngle]
@[simp] theorem constellation_blue00 (T : OrientedTriangle E o) :
    T.constellationPoint ⟨.blue, 0, 0⟩ = T.Z := by
  simp [constellationPoint, Z, labelAngle]

/-- The 27 points are distinct in the nondegenerate configuration. -/
theorem constellation_card (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) : T.constellation.ncard = 27 := by
  rw [constellation, Set.ncard_range_of_injective h, Nat.card_eq_fintype_card]
  native_decide

/-- Each individual trisector carries exactly three same-color constellation
points. -/
-- m3 / swarm smwf96q79 : proof of `OrientedTriangle.redB_points_card`
-- (root md5 ead5e6b679496a9d3e2959427ba6e24f, 7452 lines; theorem at line 7265).
--
-- Insert the whole text below immediately BEFORE
--     theorem redB_points_card (T : OrientedTriangle E o) (i : TrisectorLabel)
-- and delete that theorem's `:= by sorry`  (the proof is the last item in the block).
-- Statements are unchanged; no new hypotheses; no sorry; axioms are
-- [propext, Classical.choice, Quot.sound] only.

theorem mem_of_parallel (ℓ : Line E) {X : E} (h : Parallel ℓ.direction (X - ℓ.base)) :
    ℓ.mem X := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by rw [← ht]; abel⟩

theorem exp_nat_pi (n : ℕ) : (Circle.exp ((n : ℝ) * Real.pi) : ℂ) = (-1 : ℂ) ^ n := by
  rw [Circle.coe_exp]
  have h : (((n : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I = (n : ℂ) * (Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

theorem exp_neg_nat_pi (n : ℕ) : (Circle.exp (-((n : ℝ) * Real.pi)) : ℂ) = (-1 : ℂ) ^ n := by
  have h : (Circle.exp (-((n : ℝ) * Real.pi)) : ℂ) = ((Circle.exp ((n : ℝ) * Real.pi) : ℂ))⁻¹ := by
    rw [Circle.exp_neg, Circle.coe_inv]
  rw [h, exp_nat_pi n, ← inv_pow, inv_neg_one]

theorem labelAngle_three_halves (i : TrisectorLabel) :
    3 * labelAngle i / 2 = (i.val : ℝ) * Real.pi := by
  rw [labelAngle]; push_cast; ring


variable (T : OrientedTriangle E o)

theorem beta_add_gamma_lt_pi_div_three : T.beta + T.gamma < Real.pi / 3 := by
  have h := T.angle_sum
  have hα := m3_alpha_pos T
  linarith

theorem sin_beta_add_gamma_sub (k : ℕ) (hk : k ≤ 4) :
    Real.sin (T.beta + T.gamma - ((k : ℝ) * Real.pi / 3)) ≠ 0 := by
  have h1 : 0 < T.beta + T.gamma := m3_beta_add_gamma_pos T
  have h2 : T.beta + T.gamma < Real.pi / 3 := T.beta_add_gamma_lt_pi_div_three
  interval_cases k
  · have hx : T.beta + T.gamma - ((0 : ℕ) : ℝ) * Real.pi / 3 = T.beta + T.gamma := by norm_num
    rw [hx]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 (by linarith))
  · have hx : T.beta + T.gamma - ((1 : ℕ) : ℝ) * Real.pi / 3
        = T.beta + T.gamma - Real.pi / 3 := by norm_num
    rw [hx]
    exact ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))
  · have hx : T.beta + T.gamma - ((2 : ℕ) : ℝ) * Real.pi / 3
        = T.beta + T.gamma - 2 * Real.pi / 3 := by norm_num
    rw [hx]
    exact ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))
  · have hx : T.beta + T.gamma - ((3 : ℕ) : ℝ) * Real.pi / 3
        = T.beta + T.gamma - Real.pi := by norm_num
    rw [hx]
    exact ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))
  · have hx : T.beta + T.gamma - ((4 : ℕ) : ℝ) * Real.pi / 3
        = -(Real.pi + (Real.pi / 3 - (T.beta + T.gamma))) := by norm_num; ring
    rw [hx, Real.sin_neg, show Real.pi + (Real.pi / 3 - (T.beta + T.gamma))
      = (Real.pi / 3 - (T.beta + T.gamma)) + Real.pi from by ring, Real.sin_add_pi, neg_neg]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

/-- `toComplex` of the `redB` direction. -/
theorem toComplex_redB_direction (i : TrisectorLabel) :
    toComplex o (T.redB i).direction
      = toComplex o (T.C - T.B) * Circle.exp (T.beta + labelAngle i) := by
  have hdir : (T.redB i).direction
      = rotateVector o (rotateVector o (T.C - T.B) T.beta) (labelAngle i) := rfl
  rw [hdir, ← rotateVector_add_angle, toComplex_rotateVector,
    show labelAngle i + T.beta = T.beta + labelAngle i from by ring]

theorem toComplex_redC_direction (j : TrisectorLabel) :
    toComplex o (T.redC j).direction
      = toComplex o (T.A - T.C) * Circle.exp (2 * T.gamma - labelAngle j) := by
  have hdir : (T.redC j).direction
      = rotateVector o (rotateVector o (T.A - T.C) (2 * T.gamma)) (-labelAngle j) := rfl
  rw [hdir, ← rotateVector_add_angle, toComplex_rotateVector,
    show -labelAngle j + 2 * T.gamma = 2 * T.gamma - labelAngle j from by ring]


variable (T : OrientedTriangle E o)

theorem constellationPoint_red_eq (i j : TrisectorLabel) :
    T.constellationPoint ⟨.red, i, j⟩ =
      rotationFixedPoint o T.C T.B (2 * T.gamma - labelAngle j) (2 * T.beta - labelAngle i) :=
  rfl

theorem constellationPoint_mem_redB (i j : TrisectorLabel) :
    (T.redB i).mem (T.constellationPoint ⟨.red, i, j⟩) := by
  set ψ : ℝ := 2 * T.beta - labelAngle i with hψ
  set φ : ℝ := 2 * T.gamma - labelAngle j with hφ
  have hsin : Real.sin ((φ + ψ) / 2) ≠ 0 := by
    have h2 : (φ + ψ) / 2 = T.beta + T.gamma - ((↑i.val + ↑j.val : ℝ) * Real.pi / 3) := by
      rw [hψ, hφ, labelAngle, labelAngle]; push_cast; ring
    rw [h2]
    have h4 : i.val + j.val ≤ 4 := by
      have h1 := ZMod.val_lt i; have h2' := ZMod.val_lt j; omega
    have h5 := sin_beta_add_gamma_sub T (i.val + j.val) h4
    rw [show ((↑i.val + ↑j.val : ℝ)) = ((i.val + j.val : ℕ) : ℝ) from by push_cast; ring]
    exact h5
  have hF : toComplex o (T.constellationPoint ⟨.red, i, j⟩ - T.C)
      = toComplex o (T.B - T.C) *
        ((1 - (Circle.exp ψ : ℂ)) / (1 - (Circle.exp φ : ℂ) * Circle.exp ψ)) := by
    rw [constellationPoint_red_eq, toComplex_sub, toComplex_rotationFixedPoint
      (o := o) (P := T.C) (Q := T.B)]
    ring
  have hratio : ((1 - (Circle.exp ψ : ℂ)) / (1 - (Circle.exp φ : ℂ) * Circle.exp ψ) - 1)
      = -(((Real.sin (φ / 2) / Real.sin ((φ + ψ) / 2) : ℝ)) : ℂ) * Circle.exp (ψ / 2) := by
    have h : ψ / 2 + φ / 2 = (φ + ψ) / 2 := by ring
    have h' := m3_ratio_sub (θ := ψ / 2) (ψ := φ / 2) (h ▸ hsin)
    rw [show 2 * (ψ / 2) = ψ from by ring, show 2 * (φ / 2) = φ from by ring, h] at h'
    have hmc : ((Circle.exp ψ : ℂ)) * ((Circle.exp φ : ℂ)) = ((Circle.exp φ : ℂ)) * ((Circle.exp ψ : ℂ)) :=
      mul_comm _ _
    rw [hmc] at h'
    simpa [neg_mul] using h'
  have hFB : toComplex o (T.constellationPoint ⟨.red, i, j⟩ - T.B)
      = toComplex o (T.C - T.B) *
        (((Real.sin (φ / 2) / Real.sin ((φ + ψ) / 2) : ℝ)) : ℂ) * Circle.exp (ψ / 2) := by
    have h1 : T.constellationPoint ⟨.red, i, j⟩ - T.B
        = (T.constellationPoint ⟨.red, i, j⟩ - T.C) + (T.C - T.B) := by abel
    rw [h1, toComplex_add, hF]
    have hBC : toComplex o (T.B - T.C) = - toComplex o (T.C - T.B) := by
      rw [toComplex_sub, toComplex_sub]; ring
    rw [hBC]
    linear_combination (-(toComplex o (T.C - T.B))) * hratio
  refine mem_of_parallel _ ⟨(Real.sin (φ / 2) / Real.sin ((φ + ψ) / 2)) * (-1 : ℝ) ^ i.val, ?_⟩
  show T.constellationPoint ⟨.red, i, j⟩ - T.B
      = ((Real.sin (φ / 2) / Real.sin ((φ + ψ) / 2)) * (-1 : ℝ) ^ i.val) • (T.redB i).direction
  apply toComplex_injective o
  rw [toComplex_smul, toComplex_redB_direction, hFB]
  have hexp : (Circle.exp (ψ / 2) : ℂ)
      = (Circle.exp (T.beta + labelAngle i) : ℂ) * ((-1 : ℂ) ^ i.val) := by
    have harg : ψ / 2 = (T.beta + labelAngle i) + (-((i.val : ℝ) * Real.pi)) := by
      rw [hψ]
      have h3 := labelAngle_three_halves i
      linear_combination -h3
    rw [harg, ← m3_exp_mul_exp, exp_neg_nat_pi i.val]
  rw [hexp]
  push_cast
  ring


theorem redB_points_card (T : OrientedTriangle E o) (i : TrisectorLabel)
    (h : Injective T.constellationPoint) :
    {X ∈ T.constellation | ∃ j : TrisectorLabel,
      X = T.constellationPoint ⟨.red, i, j⟩ ∧ (T.redB i).mem X}.ncard = 3 := by
  have hset : {X ∈ T.constellation | ∃ j : TrisectorLabel,
      X = T.constellationPoint ⟨.red, i, j⟩ ∧ (T.redB i).mem X}
      = Set.range (fun j : TrisectorLabel => T.constellationPoint ⟨.red, i, j⟩) := by
    ext X
    constructor
    · rintro ⟨-, j, rfl, -⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨⟨.red, i, j⟩, rfl⟩, j, rfl, constellationPoint_mem_redB T i j⟩
  rw [hset, Set.ncard_range_of_injective]
  · rw [Nat.card_eq_fintype_card]
    decide
  · intro a b hab
    have h1 : (⟨.red, i, a⟩ : ConstellationIndex) = ⟨.red, i, b⟩ := h hab
    simpa using congrArg ConstellationIndex.second h1
-- m4 / swarm smwf9bxwn : labelled-constellation block (Appendix B catalogue).
-- PROVED: `redB_points_card` and `redC_points_card` (root) plus the label/rotation
-- dictionary (labelAngle values, ZMod-3 trichotomy, half-label sign law
-- `exists s, rot v (x - l_i/2) = s • rot v (x + l_i)`, period `rot v (x + 2 l_i) =
-- rot v (x - l_i)`, `sin (b+g+m*pi/3) != 0` for all m : Z), and the cyclic side
-- relation `exists r, B - C = r • rot (A - C) (3g)`.
-- Placement: inside `namespace OrientedTriangle` with `{o}` in scope, immediately
-- before `theorem redB_points_card`, deleting the original `redB_points_card` and
-- `redC_points_card` (both supplied here). No existing name is shadowed (all m4_).
-- Verified: current root + block compiles, no errors (`XamboMorley_m4d.lean`, 8020
-- lines); #print axioms on the two cardinals: [propext, Classical.choice, Quot.sound].

theorem m4_circle_exp_eq (θ : ℝ) :
    (Circle.exp θ : ℂ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  rw [Circle.coe_exp, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- `Circle.exp (-(π/2))` is `-I`. -/
theorem m4_circle_exp_neg_pi_div_two : (Circle.exp (-(Real.pi / 2)) : ℂ) = -Complex.I := by
  rw [m4_circle_exp_eq, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast
  ring

theorem m4_circle_exp_ne_zero (θ : ℝ) : (Circle.exp θ : ℂ) ≠ 0 := by
  rw [Circle.coe_exp]
  exact Complex.exp_ne_zero _

/-- `exp (-a) * exp (a + b) = exp b`. -/
theorem m4_circle_exp_neg_mul_exp_add (a b : ℝ) :
    (Circle.exp (-a) : ℂ) * (Circle.exp (a + b) : ℂ) = (Circle.exp b : ℂ) := by
  rw [← Circle.coe_mul, ← Circle.exp_add]
  congr 1
  ring

theorem m4_neg_two_i_sin_mul_exp_ne_zero (θ : ℝ) (h : Real.sin θ ≠ 0) :
    (-2 * Complex.I * (Real.sin θ : ℂ)) * Circle.exp θ ≠ 0 :=
  mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℂ) ≠ 0) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr h))
    (m4_circle_exp_ne_zero θ)

/-- Sine form of `1 - exp (2θ)`. -/
theorem m4_one_sub_unit_exp_two (θ : ℝ) :
    (1 - Circle.exp (2 * θ) : ℂ) = (-2 * Complex.I * (Real.sin θ : ℂ)) * Circle.exp θ := by
  rw [one_sub_unit_eq (2 * θ)]
  have hθ : 2 * θ / 2 = θ := by ring
  have hsplit : (Circle.exp (θ - Real.pi / 2) : ℂ) =
      (Circle.exp θ : ℂ) * (Circle.exp (-(Real.pi / 2)) : ℂ) := by
    rw [show θ - Real.pi / 2 = θ + -(Real.pi / 2) by ring, Circle.exp_add, Circle.coe_mul]
  rw [hθ, hsplit, m4_circle_exp_neg_pi_div_two]
  try (push_cast; ring)

theorem m4_ofReal_mul_circle_exp (r θ : ℝ) :
    ((r : ℂ) * Circle.exp θ) =
      ((r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * Complex.I := by
  rw [m4_circle_exp_eq]
  push_cast
  ring

theorem m4_ofReal_mul_circle_exp_re (r θ : ℝ) :
    (((r : ℂ) * Circle.exp θ)).re = r * Real.cos θ := by
  rw [m4_ofReal_mul_circle_exp, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem m4_ofReal_mul_circle_exp_im (r θ : ℝ) :
    (((r : ℂ) * Circle.exp θ)).im = r * Real.sin θ := by
  rw [m4_ofReal_mul_circle_exp, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- A real addition formula, read in `ℂ`. -/
theorem m4_sin_add_sub (a b : ℝ) :
    (Real.sin (a + b) : ℂ) - (Real.sin b : ℂ) * Circle.exp (-a) =
      (Real.sin a : ℂ) * Circle.exp b := by
  rw [m4_circle_exp_eq (-a), m4_circle_exp_eq b, Real.sin_add, Real.sin_neg, Real.cos_neg]
  push_cast
  ring

/-- The basic ratio identity for the first Morley coordinate expression. -/
theorem m4_ratio_one (a b : ℝ) (h : Real.sin (a + b) ≠ 0) :
    (1 - Circle.exp (2 * b) : ℂ) / (1 - (Circle.exp (2 * a) : ℂ) * Circle.exp (2 * b)) =
      ((Real.sin b / Real.sin (a + b) : ℝ) : ℂ) * Circle.exp (-a) := by
  have hc : ((Real.sin (a + b) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr h
  have hone : (1 - (Circle.exp (2 * (a + b)) : ℂ)) ≠ 0 := by
    rw [m4_one_sub_unit_exp_two (a + b)]
    exact m4_neg_two_i_sin_mul_exp_ne_zero (a + b) h
  have hD : (1 - (Circle.exp (2 * a) : ℂ) * Circle.exp (2 * b)) ≠ 0 := by
    rw [show (1 - (Circle.exp (2 * a) : ℂ) * Circle.exp (2 * b)) =
      (1 - (Circle.exp (2 * (a + b)) : ℂ)) by
      rw [← Circle.coe_mul, ← Circle.exp_add]
      congr 2
      ring]
    exact hone
  rw [show (1 - (Circle.exp (2 * a) : ℂ) * Circle.exp (2 * b)) =
      (1 - (Circle.exp (2 * (a + b)) : ℂ)) by
    rw [← Circle.coe_mul, ← Circle.exp_add]
    congr 2
    ring]
  rw [m4_one_sub_unit_exp_two b, m4_one_sub_unit_exp_two (a + b)]
  rw [div_eq_iff (by
    rw [show (-2 * Complex.I * (Real.sin (a + b) : ℂ)) * Circle.exp (a + b) =
      (-2 * Complex.I) * ((Real.sin (a + b) : ℂ) * Circle.exp (a + b)) from by ring]
    exact mul_ne_zero (by norm_num : (-2 : ℂ) * Complex.I ≠ 0)
      (mul_ne_zero hc (m4_circle_exp_ne_zero _)))]
  rw [Complex.ofReal_div]
  conv_lhs => rw [← m4_circle_exp_neg_mul_exp_add a b]
  field_simp
  try ring

/-- The ratio identity for the third Morley coordinate expression. -/
theorem m4_ratio_two (a b : ℝ) (h : Real.sin (a + b) ≠ 0) :
    1 - (1 - Circle.exp (2 * b) : ℂ) / (1 - (Circle.exp (2 * a) : ℂ) * Circle.exp (2 * b)) =
      ((Real.sin a / Real.sin (a + b) : ℝ) : ℂ) * Circle.exp b := by
  have hc : ((Real.sin (a + b) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr h
  have h1 : ((Real.sin b / Real.sin (a + b) : ℝ) : ℂ) =
      (Real.sin b : ℂ) / (Real.sin (a + b) : ℂ) := by
    push_cast
    ring
  have h2 : ((Real.sin a / Real.sin (a + b) : ℝ) : ℂ) =
      (Real.sin a : ℂ) / (Real.sin (a + b) : ℂ) := by
    push_cast
    ring
  have key := m4_sin_add_sub a b
  rw [m4_ratio_one a b h, h1, h2]
  field_simp
  try exact key


theorem m4_coef_sum (a b : ℝ) (h : Real.sin (a + b) ≠ 0) :
    ((Real.sin b / Real.sin (a + b) : ℝ) : ℂ) * Circle.exp (-a) +
      ((Real.sin a / Real.sin (a + b) : ℝ) : ℂ) * Circle.exp b = 1 := by
  have hc : ((Real.sin (a + b) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr h
  have h1 : ((Real.sin b / Real.sin (a + b) : ℝ) : ℂ) =
      (Real.sin b : ℂ) / (Real.sin (a + b) : ℂ) := by
    push_cast
    ring
  have h2 : ((Real.sin a / Real.sin (a + b) : ℝ) : ℂ) =
      (Real.sin a : ℂ) / (Real.sin (a + b) : ℂ) := by
    push_cast
    ring
  have key := m4_sin_add_sub a b
  rw [h1, h2]
  field_simp
  rw [← key]
  ring

/-! ### m4: the two general coordinate laws -/

theorem m4_second (P Q : E) (a b : ℝ) (h : Real.sin (a + b) ≠ 0) :
    rotationFixedPoint o P Q (2 * a) (2 * b) =
      P + (Real.sin b / Real.sin (a + b)) • rotateVector o (Q - P) (-a) := by
  have hq := m4_ratio_one a b h
  apply toComplex_injective o
  rw [toComplex_rotationFixedPoint, hq, toComplex_add, toComplex_smul, toComplex_rotateVector,
    toComplex_sub]
  ring

theorem m4_third (P Q : E) (a b : ℝ) (h : Real.sin (a + b) ≠ 0) :
    rotationFixedPoint o P Q (2 * a) (2 * b) =
      Q + (Real.sin a / Real.sin (a + b)) • rotateVector o (P - Q) b := by
  have hsum := m4_coef_sum a b h
  have hq : (1 - Circle.exp (2 * b) : ℂ) /
      (1 - (Circle.exp (2 * a) : ℂ) * Circle.exp (2 * b)) =
      1 - ((Real.sin a / Real.sin (a + b) : ℝ) : ℂ) * Circle.exp b := by
    rw [m4_ratio_one a b h, ← hsum]
    ring
  apply toComplex_injective o
  rw [toComplex_rotationFixedPoint, hq, toComplex_add, toComplex_smul, toComplex_rotateVector,
    toComplex_sub, toComplex_sub]
  ring


/-! ### m4: positivity of the angles and of the sines of the pair sums -/

theorem m4_alpha_pos (T : OrientedTriangle E o) : 0 < T.alpha := by
  have h := EuclideanGeometry.angle_pos_of_not_collinear (p₁ := T.B) (p₂ := T.A) (p₃ := T.C)
    (by
      have hset : ({T.B, T.A, T.C} : Set E) = {T.A, T.B, T.C} := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hset]
      exact T.noncollinear)
  have h3 : T.alpha = EuclideanGeometry.angle T.B T.A T.C / 3 := rfl
  rw [h3]
  linarith

theorem m4_beta_pos (T : OrientedTriangle E o) : 0 < T.beta := by
  have h := EuclideanGeometry.angle_pos_of_not_collinear (p₁ := T.C) (p₂ := T.B) (p₃ := T.A)
    (by
      have hset : ({T.C, T.B, T.A} : Set E) = {T.A, T.B, T.C} := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hset]
      exact T.noncollinear)
  have h3 : T.beta = EuclideanGeometry.angle T.C T.B T.A / 3 := rfl
  rw [h3]
  linarith

theorem m4_gamma_pos (T : OrientedTriangle E o) : 0 < T.gamma := by
  have h := EuclideanGeometry.angle_pos_of_not_collinear (p₁ := T.A) (p₂ := T.C) (p₃ := T.B)
    (by
      have hset : ({T.A, T.C, T.B} : Set E) = {T.A, T.B, T.C} := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hset]
      exact T.noncollinear)
  have h3 : T.gamma = EuclideanGeometry.angle T.A T.C T.B / 3 := rfl
  rw [h3]
  linarith

theorem m4_angles_sum (T : OrientedTriangle E o) : T.alpha + T.beta + T.gamma = Real.pi / 3 := by
  have h := T.angle_sum
  linarith

theorem m4_sin_pair_pos (T : OrientedTriangle E o) (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y < Real.pi) : 0 < Real.sin (x + y) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) hxy

theorem m4_sin_beta_add_gamma_ne (T : OrientedTriangle E o) : Real.sin (T.beta + T.gamma) ≠ 0 :=
  ne_of_gt (m4_sin_pair_pos T T.beta T.gamma T.m4_beta_pos T.m4_gamma_pos (by
    nlinarith [T.m4_angles_sum, T.m4_alpha_pos, Real.pi_pos]))

theorem m4_sin_gamma_add_alpha_ne (T : OrientedTriangle E o) :
    Real.sin (T.gamma + T.alpha) ≠ 0 :=
  ne_of_gt (m4_sin_pair_pos T T.gamma T.alpha T.m4_gamma_pos T.m4_alpha_pos (by
    nlinarith [T.m4_angles_sum, T.m4_beta_pos, Real.pi_pos]))

theorem m4_sin_alpha_add_beta_ne (T : OrientedTriangle E o) :
    Real.sin (T.alpha + T.beta) ≠ 0 :=
  ne_of_gt (m4_sin_pair_pos T T.alpha T.beta T.m4_alpha_pos T.m4_beta_pos (by
    nlinarith [T.m4_angles_sum, T.m4_gamma_pos, Real.pi_pos]))


/-! ### m4: complex coordinates of the oriented area and inner product -/

theorem m4_complexIsometryEquiv_positiveBasis (o : Orientation ℝ E (Fin 2)) (i : Fin 2) :
    complexIsometryEquiv o (positiveBasis o i) = Complex.orthonormalBasisOneI i := by
  simp [complexIsometryEquiv, OrthonormalBasis.equiv]

theorem m4_toComplex_positiveBasis (o : Orientation ℝ E (Fin 2)) (i : Fin 2) :
    toComplex o (positiveBasis o i) = Complex.orthonormalBasisOneI i :=
  m4_complexIsometryEquiv_positiveBasis o i

theorem m4_toComplex_eq_coord (o : Orientation ℝ E (Fin 2)) (v : E) :
    toComplex o v =
      ((positiveBasis o).repr v 0 : ℝ) + ((positiveBasis o).repr v 1 : ℝ) * Complex.I := by
  have hsum := (positiveBasis o).sum_repr v
  conv_lhs => rw [← hsum]
  simp [m4_toComplex_positiveBasis, Fin.sum_univ_two]

/-- The oriented area form is the imaginary part of the complex product. -/
theorem m4_areaForm_toComplex (o : Orientation ℝ E (Fin 2)) (v w : E) :
    orientedArea o v w = (conj (toComplex o v) * toComplex o w).im := by
  have hb : (positiveBasis o).toBasis.orientation = o :=
    o.finOrthonormalBasis_orientation (by norm_num) Fact.out
  have hvol : o.volumeForm = (positiveBasis o).toBasis.det :=
    o.volumeForm_robust (positiveBasis o) hb
  rw [orientedArea, Orientation.areaForm_to_volumeForm, hvol, Module.Basis.det_apply,
    m4_toComplex_eq_coord o v, m4_toComplex_eq_coord o w]
  simp [Module.Basis.toMatrix_apply, Matrix.det_fin_two, Complex.mul_im, Complex.mul_re]
  ring

/-- The real inner product is the real part of the complex product. -/
theorem m4_toComplex_inner (o : Orientation ℝ E (Fin 2)) (v w : E) :
    ⟪v, w⟫ = (conj (toComplex o v) * toComplex o w).re := by
  rw [show (⟪v, w⟫ : ℝ) = ⟪toComplex o v, toComplex o w⟫ from
    (LinearIsometryEquiv.inner_map_map (complexIsometryEquiv o) v w).symm]
  rw [Complex.inner]
  simp [toComplex, mul_comm]

/-- Lagrange's identity in the plane. -/
theorem m4_lagrange_area (o : Orientation ℝ E (Fin 2)) (v w : E) :
    ⟪v, v⟫ * ⟪w, w⟫ - ⟪v, w⟫ * ⟪v, w⟫ = orientedArea o v w ^ 2 := by
  have hv : ⟪v, v⟫ = Complex.normSq (toComplex o v) := by
    rw [real_inner_self_eq_norm_sq,
      show ‖v‖ = ‖toComplex o v‖ from (toComplex_norm o v).symm, Complex.sq_norm]
  have hw : ⟪w, w⟫ = Complex.normSq (toComplex o w) := by
    rw [real_inner_self_eq_norm_sq,
      show ‖w‖ = ‖toComplex o w‖ from (toComplex_norm o w).symm, Complex.sq_norm]
  have hvw : ⟪v, w⟫ = (conj (toComplex o v) * toComplex o w).re := m4_toComplex_inner o v w
  rw [hv, hw, hvw, m4_areaForm_toComplex]
  have hmul : Complex.normSq (toComplex o v) * Complex.normSq (toComplex o w) =
      Complex.normSq (conj (toComplex o v) * toComplex o w) := by
    rw [Complex.normSq_mul, Complex.normSq_conj]
  rw [hmul, Complex.normSq_apply]
  ring

/-- The sine of the angle between two nonzero vectors. -/
theorem m4_sin_angle_eq_area (o : Orientation ℝ E (Fin 2)) {v w : E} (hv : v ≠ 0)
    (hw : w ≠ 0) :
    Real.sin (InnerProductGeometry.angle v w) = |orientedArea o v w| / (‖v‖ * ‖w‖) := by
  rw [InnerProductGeometry.sin_angle hv hw, m4_lagrange_area o v w, Real.sqrt_sq_eq_abs]

/-- The signed sine form, for positive orientation. -/
theorem m4_sin_angle_mul_norm_mul_norm (o : Orientation ℝ E (Fin 2)) {v w : E} (hv : v ≠ 0)
    (hw : w ≠ 0) (hpos : 0 < orientedArea o v w) :
    ‖v‖ * ‖w‖ * Real.sin (InnerProductGeometry.angle v w) = orientedArea o v w := by
  rw [m4_sin_angle_eq_area o hv hw, abs_of_pos hpos]
  field_simp

/-- Polar form of `conj z_v * z_w`. -/
theorem m4_conj_mul_polar (o : Orientation ℝ E (Fin 2)) {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (hpos : 0 < orientedArea o u v) :
    conj (toComplex o u) * toComplex o v =
      ((‖u‖ * ‖v‖ : ℝ) : ℂ) * Circle.exp (InnerProductGeometry.angle u v) := by
  apply Complex.ext
  · rw [m4_ofReal_mul_circle_exp_re, ← m4_toComplex_inner o u v,
      ← InnerProductGeometry.cos_angle_mul_norm_mul_norm]
    ring
  · rw [m4_ofReal_mul_circle_exp_im, ← m4_areaForm_toComplex o u v,
      ← m4_sin_angle_mul_norm_mul_norm o hu hv hpos]
    try ring

/-- The conjugate of a unit complex number. -/
theorem m4_conj_circle_exp (θ : ℝ) : conj (Circle.exp θ : ℂ) = (Circle.exp (-θ) : ℂ) := by
  rw [Circle.coe_exp, Circle.coe_exp, ← Complex.exp_conj]
  congr 1
  simp

/-! ### m4: area computations for the three trisector intersections -/

theorem m4_area_cycle_CB_AC (T : OrientedTriangle E o) :
    orientedArea o (T.C - T.B) (T.A - T.C) =
      orientedArea o (T.B - T.A) (T.C - T.A) := by
  have h1 : T.C - T.B = (T.C - T.A) - (T.B - T.A) := by abel
  have h2 : T.A - T.C = -(T.C - T.A) := by abel
  rw [h1, h2, orientedArea, map_sub, LinearMap.sub_apply, LinearMap.map_neg,
    LinearMap.map_neg, Orientation.areaForm_apply_self, neg_zero, zero_sub, neg_neg, orientedArea]

theorem m4_area_cycle_AC_BA (T : OrientedTriangle E o) :
    orientedArea o (T.A - T.C) (T.B - T.A) =
      orientedArea o (T.B - T.A) (T.C - T.A) := by
  rw [show T.A - T.C = -(T.C - T.A) by abel, orientedArea, Orientation.areaForm_swap,
    map_neg, neg_neg, orientedArea]

theorem m4_area_cycle_BA_CB (T : OrientedTriangle E o) :
    orientedArea o (T.B - T.A) (T.C - T.B) =
      orientedArea o (T.B - T.A) (T.C - T.A) := by
  have h1 : T.C - T.B = (T.C - T.A) - (T.B - T.A) := by abel
  rw [h1, orientedArea, map_sub, Orientation.areaForm_apply_self, sub_zero, orientedArea]

theorem m4_angle_CB_AC (T : OrientedTriangle E o) :
    InnerProductGeometry.angle (T.C - T.B) (T.A - T.C) = Real.pi - 3 * T.gamma := by
  have hγ : 3 * T.gamma = InnerProductGeometry.angle (T.A - T.C) (T.B - T.C) := by
    have h1 : 3 * T.gamma = EuclideanGeometry.angle T.A T.C T.B := by
      simp only [OrientedTriangle.gamma, EuclideanGeometry.angle, vsub_eq_sub]
      ring
    rw [h1]
    rfl
  rw [show T.C - T.B = -(T.B - T.C) by abel, InnerProductGeometry.angle_neg_left,
    InnerProductGeometry.angle_comm, ← hγ]

theorem m4_angle_AC_BA (T : OrientedTriangle E o) :
    InnerProductGeometry.angle (T.A - T.C) (T.B - T.A) = Real.pi - 3 * T.alpha := by
  have hα : 3 * T.alpha = InnerProductGeometry.angle (T.B - T.A) (T.C - T.A) := by
    have h1 : 3 * T.alpha = EuclideanGeometry.angle T.B T.A T.C := by
      simp only [OrientedTriangle.alpha, EuclideanGeometry.angle, vsub_eq_sub]
      ring
    rw [h1]
    rfl
  rw [show T.A - T.C = -(T.C - T.A) by abel, InnerProductGeometry.angle_neg_left,
    InnerProductGeometry.angle_comm, ← hα]

theorem m4_angle_BA_CB (T : OrientedTriangle E o) :
    InnerProductGeometry.angle (T.B - T.A) (T.C - T.B) = Real.pi - 3 * T.beta := by
  have hβ : 3 * T.beta = InnerProductGeometry.angle (T.C - T.B) (T.A - T.B) := by
    have h1 : 3 * T.beta = EuclideanGeometry.angle T.C T.B T.A := by
      simp only [OrientedTriangle.beta, EuclideanGeometry.angle, vsub_eq_sub]
      ring
    rw [h1]
    rfl
  rw [show T.B - T.A = -(T.A - T.B) by abel, InnerProductGeometry.angle_neg_left,
    InnerProductGeometry.angle_comm, ← hβ]

theorem m4_im_R_exp2 (r a b : ℝ) :
    (((r : ℂ) * Circle.exp a) * Circle.exp b).im = r * Real.sin (a + b) := by
  have h : ((r : ℂ) * Circle.exp a) * Circle.exp b = (r : ℂ) * Circle.exp (a + b) := by
    rw [mul_assoc, ← Circle.coe_mul, ← Circle.exp_add]
  rw [h, m4_ofReal_mul_circle_exp_im]

theorem m4_im_R_exp3 (r a b c : ℝ) :
    (((r : ℂ) * Circle.exp a) * (Circle.exp b * Circle.exp c)).im =
      r * Real.sin (a + b + c) := by
  have hb : ((Circle.exp b : ℂ) * Circle.exp c) = (Circle.exp (b + c) : ℂ) := by
    rw [← Circle.coe_mul, Circle.exp_add]
  rw [hb]
  have h : ((r : ℂ) * Circle.exp a) * Circle.exp (b + c) =
      (r : ℂ) * Circle.exp (a + (b + c)) := by
    rw [mul_assoc, ← Circle.coe_mul, ← Circle.exp_add]
  rw [h, m4_ofReal_mul_circle_exp_im, show a + (b + c) = a + b + c by ring]

/-- General area quotient for the three trisector intersections. -/
theorem m4_area_quotient_gen (o : Orientation ℝ E (Fin 2)) {u v : E} (a b : ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hpos : 0 < orientedArea o u v)
    (hθ : InnerProductGeometry.angle u v = Real.pi - 3 * a) (hsin : Real.sin (a + b) ≠ 0) :
    orientedArea o u (rotateVector o v (2 * a)) /
        orientedArea o (rotateVector o u b) (rotateVector o v (2 * a)) =
      Real.sin a / Real.sin (a + b) := by
  have hpolar := m4_conj_mul_polar o hu hv hpos
  have hR : (‖u‖ * ‖v‖) ≠ 0 :=
    ne_of_gt (mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv))
  have hnum : orientedArea o u (rotateVector o v (2 * a)) =
      (‖u‖ * ‖v‖) * Real.sin (InnerProductGeometry.angle u v + 2 * a) := by
    rw [m4_areaForm_toComplex, toComplex_rotateVector,
      show conj (toComplex o u) * (toComplex o v * (Circle.exp (2 * a) : ℂ)) =
        (conj (toComplex o u) * toComplex o v) * Circle.exp (2 * a) by ring,
      hpolar, m4_im_R_exp2]
  have hden : orientedArea o (rotateVector o u b) (rotateVector o v (2 * a)) =
      (‖u‖ * ‖v‖) * Real.sin (InnerProductGeometry.angle u v - b + 2 * a) := by
    rw [m4_areaForm_toComplex, toComplex_rotateVector, toComplex_rotateVector, map_mul,
      m4_conj_circle_exp,
      show conj (toComplex o u) * (Circle.exp (-b) : ℂ) *
          (toComplex o v * (Circle.exp (2 * a) : ℂ)) =
        (conj (toComplex o u) * toComplex o v) *
          ((Circle.exp (-b) : ℂ) * Circle.exp (2 * a)) by ring,
      hpolar, m4_im_R_exp3,
      show InnerProductGeometry.angle u v + -b + 2 * a =
        InnerProductGeometry.angle u v - b + 2 * a by ring]
  rw [hnum, hden, hθ]
  have e1 : Real.sin (Real.pi - 3 * a + 2 * a) = Real.sin a := by
    rw [show Real.pi - 3 * a + 2 * a = Real.pi - a by ring, Real.sin_pi_sub]
  have e2 : Real.sin (Real.pi - 3 * a - b + 2 * a) = Real.sin (a + b) := by
    rw [show Real.pi - 3 * a - b + 2 * a = Real.pi - (a + b) by ring, Real.sin_pi_sub]
  rw [e1, e2]
  field_simp



/-! ### m4: rotation and label algebra for the labelled constellation -/

theorem m4_rotateVector_neg_pi (v : E) : rotateVector o v (-Real.pi) = -v := by
  rw [rotateVector_eq_cos_add_perp, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]
  simp

theorem m4_rotateVector_neg_two_pi (v : E) : rotateVector o v (-(2 * Real.pi)) = v := by
  rw [rotateVector_eq_cos_add_perp, Real.cos_neg, Real.sin_neg, Real.cos_two_pi, Real.sin_two_pi]
  simp

theorem m4_rotateVector_period (v : E) (x : ℝ) :
    rotateVector o v (x + 2 * Real.pi) = rotateVector o v x := by
  rw [rotateVector_eq_cos_add_perp, rotateVector_eq_cos_add_perp, Real.cos_add_two_pi,
    Real.sin_add_two_pi]

theorem m4_rotateVector_period_nat (v : E) (x : ℝ) (k : ℕ) :
    rotateVector o v (x + k * (2 * Real.pi)) = rotateVector o v x := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h : ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
      push_cast
      ring
    rw [h, show x + ((n : ℝ) * (2 * Real.pi) + 2 * Real.pi) =
        (x + (n : ℝ) * (2 * Real.pi)) + 2 * Real.pi by ring, m4_rotateVector_period, ih]

theorem m4_labelAngle_zero : labelAngle (0 : TrisectorLabel) = 0 := by
  simp [labelAngle]

theorem m4_labelAngle_one : labelAngle (1 : TrisectorLabel) = 2 * Real.pi / 3 := by
  have h : ((1 : TrisectorLabel).val) = 1 := by decide
  simp [labelAngle, h]

theorem m4_labelAngle_two : labelAngle (2 : TrisectorLabel) = 4 * Real.pi / 3 := by
  have h : ((2 : TrisectorLabel).val) = 2 := by decide
  simp [labelAngle, h]
  ring

theorem m4_label_cases (i : TrisectorLabel) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i
  decide

/-- Rotating by half a label angle equals, up to an explicit real factor, rotating by
the full label angle on the other side. -/
theorem m4_rot_half_smul (v : E) (x : ℝ) (i : TrisectorLabel) :
    ∃ s : ℝ, rotateVector o v (x - labelAngle i / 2) =
      s • rotateVector o v (x + labelAngle i) := by
  rcases m4_label_cases i with rfl | rfl | rfl
  · refine ⟨1, ?_⟩
    rw [m4_labelAngle_zero]
    norm_num
  · refine ⟨-1, ?_⟩
    rw [m4_labelAngle_one,
      show x - (2 * Real.pi / 3) / 2 = (-Real.pi) + (x + 2 * Real.pi / 3) by ring,
      rotateVector_add_angle, m4_rotateVector_neg_pi]
    simp
  · refine ⟨1, ?_⟩
    rw [m4_labelAngle_two,
      show x - (4 * Real.pi / 3) / 2 = (-(2 * Real.pi)) + (x + 4 * Real.pi / 3) by ring,
      rotateVector_add_angle, m4_rotateVector_neg_two_pi]
    simp

/-- Two label angles equal one full label angle minus a third: `2λ = 2π k - λ`. -/
theorem m4_rot_add_two_label (v : E) (x : ℝ) (i : TrisectorLabel) :
    rotateVector o v (x + 2 * labelAngle i) = rotateVector o v (x - labelAngle i) := by
  have hk : 3 * labelAngle i = (i.val : ℝ) * (2 * Real.pi) := by
    simp only [labelAngle]
    push_cast
    ring
  rw [show x + 2 * labelAngle i = (x - labelAngle i) + (i.val : ℝ) * (2 * Real.pi) by
    rw [← hk]
    ring]
  exact m4_rotateVector_period_nat v (x - labelAngle i) i.val

/-- `sin (β + γ + m·π/3) ≠ 0` for every integer `m`. -/
theorem m4_sin_bg_add_ne (T : OrientedTriangle E o) (m : ℤ) :
    Real.sin (T.beta + T.gamma + (m : ℝ) * (Real.pi / 3)) ≠ 0 := by
  have hs0 : 0 < T.beta + T.gamma := by
    have := T.m4_beta_pos
    have := T.m4_gamma_pos
    linarith
  have hs1 : T.beta + T.gamma < Real.pi / 3 := by
    have := T.m4_angles_sum
    have := T.m4_alpha_pos
    linarith
  intro h0
  rw [Real.sin_eq_zero_iff] at h0
  obtain ⟨k, hk⟩ := h0
  have hs : T.beta + T.gamma = ((3 * k - m : ℤ) : ℝ) * (Real.pi / 3) := by
    have hk' : ((k : ℝ) * Real.pi) = T.beta + T.gamma + (m : ℝ) * (Real.pi / 3) := hk
    have hexp : ((3 * k - m : ℤ) : ℝ) * (Real.pi / 3) =
        (k : ℝ) * Real.pi - (m : ℝ) * (Real.pi / 3) := by
      push_cast
      ring
    rw [hexp, hk']
    ring
  have hpi : (0 : ℝ) < Real.pi / 3 := by positivity
  have hq0 : (0 : ℝ) < ((3 * k - m : ℤ) : ℝ) := by
    by_contra hc
    push_neg at hc
    nlinarith [hs, hs0, hpi]
  have hq1 : ((3 * k - m : ℤ) : ℝ) < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith [hs, hs1, hpi]
  have hq0' : (0 : ℤ) < 3 * k - m := by exact_mod_cast hq0
  have hq1' : 3 * k - m < 1 := by exact_mod_cast hq1
  omega

theorem m4_sin_two_half_ne (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    Real.sin ((T.gamma - labelAngle j / 2) + (T.beta - labelAngle i / 2)) ≠ 0 := by
  have h : (T.gamma - labelAngle j / 2) + (T.beta - labelAngle i / 2) =
      T.beta + T.gamma + (-((i.val : ℤ) + (j.val : ℤ)) : ℤ) * (Real.pi / 3) := by
    simp only [labelAngle]
    push_cast
    ring
  rw [h]
  exact T.m4_sin_bg_add_ne _

theorem m4_cp_red_mem_redB (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    (T.redB i).mem (T.constellationPoint ⟨.red, i, j⟩) := by
  have hsq := T.m4_sin_two_half_ne i j
  have hthird := m4_third (o := o) (P := T.C) (Q := T.B)
    (a := T.gamma - labelAngle j / 2) (b := T.beta - labelAngle i / 2) hsq
  rw [show 2 * (T.gamma - labelAngle j / 2) = 2 * T.gamma - labelAngle j by ring,
    show 2 * (T.beta - labelAngle i / 2) = 2 * T.beta - labelAngle i by ring] at hthird
  obtain ⟨s, hs⟩ := m4_rot_half_smul (o := o) (T.C - T.B) T.beta i
  refine ⟨s * (Real.sin (T.gamma - labelAngle j / 2) /
    Real.sin ((T.gamma - labelAngle j / 2) + (T.beta - labelAngle i / 2))), ?_⟩
  rw [show T.constellationPoint ⟨.red, i, j⟩ =
    rotationFixedPoint o T.C T.B (2 * T.gamma - labelAngle j) (2 * T.beta - labelAngle i)
    from rfl, hthird]
  simp only [redB, BX]
  rw [show rotateVector o (rotateVector o (T.C - T.B) T.beta) (labelAngle i) =
      rotateVector o (T.C - T.B) (T.beta + labelAngle i) by
    rw [show T.beta + labelAngle i = labelAngle i + T.beta by ring, rotateVector_add_angle],
    hs, smul_comm, ← smul_smul]

/-! ### m4: counting the red constellation points on one red trisector -/

theorem m4_red_points_on_redB (T : OrientedTriangle E o) (i : TrisectorLabel) :
    {X ∈ T.constellation | ∃ j : TrisectorLabel,
      X = T.constellationPoint ⟨.red, i, j⟩ ∧ (T.redB i).mem X} =
      (fun j : TrisectorLabel => T.constellationPoint ⟨.red, i, j⟩) '' Set.univ := by
  ext X
  constructor
  · rintro ⟨hX, j, hXj, hmem⟩
    exact ⟨j, Set.mem_univ j, hXj.symm⟩
  · rintro ⟨j, -, hXj⟩
    exact ⟨⟨_, hXj⟩, j, hXj.symm, hXj ▸ T.m4_cp_red_mem_redB i j⟩


theorem m4_area_AC_BC_pos (T : OrientedTriangle E o) :
    0 < orientedArea o (T.A - T.C) (T.B - T.C) := by
  have h1 : T.B - T.C = (T.B - T.A) - (T.C - T.A) := by abel
  have h2 : (o.areaForm (T.A - T.C)) (T.C - T.A) = 0 := by
    rw [show T.C - T.A = -(T.A - T.C) by abel, map_neg,
      Orientation.areaForm_apply_self, neg_zero]
  rw [h1, orientedArea, map_sub, h2, sub_zero, ← orientedArea, m4_area_cycle_AC_BA]
  exact T.positive

theorem m4_angle_AC_BC (T : OrientedTriangle E o) :
    InnerProductGeometry.angle (T.A - T.C) (T.B - T.C) = 3 * T.gamma := by
  have h3 : 3 * T.gamma = EuclideanGeometry.angle T.A T.C T.B := by
    simp only [OrientedTriangle.gamma, EuclideanGeometry.angle, vsub_eq_sub]
    ring
  rw [h3]
  rfl

theorem m4_BC_smul_rot (T : OrientedTriangle E o) :
    ∃ r : ℝ, T.B - T.C = r • rotateVector o (T.A - T.C) (3 * T.gamma) := by
  have hu : T.A - T.C ≠ 0 := sub_ne_zero.mpr T.A_ne_C
  have hv : T.B - T.C ≠ 0 := sub_ne_zero.mpr T.B_ne_C
  have hpos := T.m4_area_AC_BC_pos
  have hpolar := m4_conj_mul_polar o hu hv hpos
  rw [T.m4_angle_AC_BC] at hpolar
  refine ⟨‖T.B - T.C‖ / ‖T.A - T.C‖, ?_⟩
  apply toComplex_injective o
  rw [toComplex_smul, toComplex_rotateVector]
  have hyne : toComplex o (T.A - T.C) ≠ 0 := fun h => hu ((toComplex_eq_zero o _).mp h)
  have hcy : conj (toComplex o (T.A - T.C)) ≠ 0 := fun h =>
    hyne (by simpa using congrArg conj h)
  refine mul_right_cancel₀ hcy ?_
  have hpar : toComplex o (T.B - T.C) * conj (toComplex o (T.A - T.C)) =
      ((‖T.A - T.C‖ * ‖T.B - T.C‖ : ℝ) : ℂ) * Circle.exp (3 * T.gamma) := by
    rw [mul_comm, ← hpolar]
  rw [hpar]
  have hnorm : ‖toComplex o (T.A - T.C)‖ = ‖T.A - T.C‖ := toComplex_norm o _
  have hconj : toComplex o (T.A - T.C) * conj (toComplex o (T.A - T.C)) =
      ((‖T.A - T.C‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
  rw [show ((‖T.B - T.C‖ / ‖T.A - T.C‖ : ℝ) : ℂ) *
        (toComplex o (T.A - T.C) * Circle.exp (3 * T.gamma)) *
        conj (toComplex o (T.A - T.C)) =
      ((‖T.B - T.C‖ / ‖T.A - T.C‖ : ℝ) : ℂ) *
        (toComplex o (T.A - T.C) * conj (toComplex o (T.A - T.C))) *
        Circle.exp (3 * T.gamma) by ring,
    hconj]
  have hA : ((‖T.A - T.C‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu)
  push_cast
  field_simp
  try ring

theorem m4_cp_red_mem_redC (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    (T.redC j).mem (T.constellationPoint ⟨.red, i, j⟩) := by
  have hsq := T.m4_sin_two_half_ne i j
  have hsecond := m4_second (o := o) (P := T.C) (Q := T.B)
    (a := T.gamma - labelAngle j / 2) (b := T.beta - labelAngle i / 2) hsq
  rw [show 2 * (T.gamma - labelAngle j / 2) = 2 * T.gamma - labelAngle j by ring,
    show 2 * (T.beta - labelAngle i / 2) = 2 * T.beta - labelAngle i by ring] at hsecond
  obtain ⟨r, hr⟩ := T.m4_BC_smul_rot
  obtain ⟨s, hs⟩ := m4_rot_half_smul (o := o) (T.A - T.C) (2 * T.gamma + labelAngle j) j
  refine ⟨(Real.sin (T.beta - labelAngle i / 2) /
    Real.sin ((T.gamma - labelAngle j / 2) + (T.beta - labelAngle i / 2))) * r * s, ?_⟩
  rw [show T.constellationPoint ⟨.red, i, j⟩ =
    rotationFixedPoint o T.C T.B (2 * T.gamma - labelAngle j) (2 * T.beta - labelAngle i)
    from rfl, hsecond]
  simp only [redC, CX]
  have hstep1 : rotateVector o (T.B - T.C) (-(T.gamma - labelAngle j / 2)) =
      r • rotateVector o (T.A - T.C) (2 * T.gamma + labelAngle j / 2) := by
    rw [show -(T.gamma - labelAngle j / 2) = -T.gamma + labelAngle j / 2 by ring, hr,
      rotateVector_smul, ← rotateVector_add_angle,
      show -T.gamma + labelAngle j / 2 + 3 * T.gamma =
        2 * T.gamma + labelAngle j / 2 by ring]
  have hstep2 : rotateVector o (T.A - T.C) (2 * T.gamma + labelAngle j / 2) =
      s • rotateVector o (T.A - T.C) (2 * T.gamma - labelAngle j) := by
    rw [show 2 * T.gamma + labelAngle j / 2 =
        (2 * T.gamma + labelAngle j) - labelAngle j / 2 by ring, hs,
      show 2 * T.gamma + labelAngle j + labelAngle j =
        2 * T.gamma + 2 * labelAngle j by ring, m4_rot_add_two_label]
  rw [hstep1, hstep2,
    show rotateVector o (rotateVector o (T.A - T.C) (2 * T.gamma)) (-labelAngle j) =
      rotateVector o (T.A - T.C) (2 * T.gamma - labelAngle j) by
      rw [show 2 * T.gamma - labelAngle j = -labelAngle j + 2 * T.gamma by ring,
        rotateVector_add_angle],
    smul_smul, smul_smul, mul_assoc]

theorem m4_red_points_on_redC (T : OrientedTriangle E o) (j : TrisectorLabel) :
    {X ∈ T.constellation | ∃ i : TrisectorLabel,
      X = T.constellationPoint ⟨.red, i, j⟩ ∧ (T.redC j).mem X} =
      (fun i : TrisectorLabel => T.constellationPoint ⟨.red, i, j⟩) '' Set.univ := by
  ext X
  constructor
  · rintro ⟨hX, i, hXi, hmem⟩
    exact ⟨i, Set.mem_univ i, hXi.symm⟩
  · rintro ⟨i, -, hXi⟩
    exact ⟨⟨_, hXi⟩, i, hXi.symm, hXi ▸ T.m4_cp_red_mem_redC i j⟩

theorem redC_points_card (T : OrientedTriangle E o) (j : TrisectorLabel)
    (h : Injective T.constellationPoint) :
    {X ∈ T.constellation | ∃ i : TrisectorLabel,
      X = T.constellationPoint ⟨.red, i, j⟩ ∧ (T.redC j).mem X}.ncard = 3 := by
  have hinj0 : Injective (fun i : TrisectorLabel =>
      (⟨TrisectorColor.red, i, j⟩ : ConstellationIndex)) := by
    intro a b hab
    simpa using congrArg ConstellationIndex.first hab
  have hinj : Injective (fun i : TrisectorLabel => T.constellationPoint ⟨.red, i, j⟩) :=
    h.comp hinj0
  rw [T.m4_red_points_on_redC j, Set.ncard_image_of_injective Set.univ hinj,
    Set.ncard_univ TrisectorLabel, Nat.card_eq_fintype_card, ZMod.card]

def parallelToMorleySide (T : OrientedTriangle E o) (v : E) : Prop :=
  Parallel (T.Y - T.X) v ∨ Parallel (T.Z - T.Y) v ∨ Parallel (T.X - T.Z) v

/-- The nine exceptional lines in Figure A3.  Incidence with six constellation
points, two of each color, makes these lines unique in the nondegenerate case. -/
def IsGuideLine (T : OrientedTriangle E o) (ℓ : Line E) : Prop :=
  T.parallelToMorleySide ℓ.direction ∧
    {q : ConstellationIndex | ℓ.mem (T.constellationPoint q)}.ncard = 6 ∧
      ∀ c : TrisectorColor,
        {q : ConstellationIndex | q.color = c ∧ ℓ.mem (T.constellationPoint q)}.ncard = 2

/-- A normalized representative of a geometric line. The unit direction fixes the
scale, the perpendicular foot fixes the base, and the angular sector fixes the sign. -/
def Line.isCanonical (o : Orientation ℝ E (Fin 2)) (ℓ : Line E) : Prop :=
  ‖ℓ.direction‖ = 1 ∧ ⟪ℓ.base, ℓ.direction⟫ = 0 ∧
    (o.oangle (e₁ o) ℓ.direction).toReal ∈ Set.Ico 0 Real.pi

/-- The set of nine geometric lines in Figure A3, represented canonically. Without
this restriction, rescaling a direction would create infinitely many `Line` structures
that have the same guide-line property. -/
def guideLines (T : OrientedTriangle E o) : Set (Line E) :=
  {ℓ | T.IsGuideLine ℓ ∧ Line.isCanonical o ℓ}

/-! ### The label arithmetic behind the nine guide lines

Numerically (five scalene triangles, exact floating point) the nine guide lines are
exactly the joins of the pairs of red points `red p`, `red q` with `p ≠ q` and equal
label sum `p.1 + p.2 = q.1 + q.2`; the direction of such a join is the one indexed by
`i - j + 1` where `(i,j)` is the third label of the sum class.  The declarations below
verify the *arithmetic* of that description: 18 ordered pairs (= 9 unordered), 2
partners for every label, and 3 pairs per direction.  They are `ZMod 3` computations, so
they are proved by evaluation; the geometric content (that these nine joins are exactly
the lines carrying six constellation points, two of each colour) is separate. -/

/-- Two distinct labels in the same sum class `L_s = {(0,s),(1,s-1),(2,s-2)}`. -/
def EqualSumPair (p q : TrisectorLabel × TrisectorLabel) : Prop :=
  p ≠ q ∧ p.1 + p.2 = q.1 + q.2

/-- The third label of the sum class of `p` and `q`. -/
def thirdLabel (p q : TrisectorLabel × TrisectorLabel) : TrisectorLabel × TrisectorLabel :=
  (-(p.1 + q.1), p.1 + p.2 + p.1 + q.1)

/-- Direction index (`0,1,2` for `Y-X`, `Z-Y`, `X-Z`) attached to an equal-sum pair. -/
def pairDirection (p q : TrisectorLabel × TrisectorLabel) : TrisectorLabel :=
  (thirdLabel p q).1 - (thirdLabel p q).2 + 1

theorem thirdLabel_spec :
    ∀ p q : TrisectorLabel × TrisectorLabel, p ≠ q → p.1 + p.2 = q.1 + q.2 →
      thirdLabel p q ≠ p ∧ thirdLabel p q ≠ q ∧
        p.1 + p.2 = (thirdLabel p q).1 + (thirdLabel p q).2 := by
  native_decide

theorem sumClass_ncard (s : TrisectorLabel) :
    {p : TrisectorLabel × TrisectorLabel | p.1 + p.2 = s}.ncard = 3 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  native_decide +revert

/-- Nine unordered equal-sum pairs, counted as 18 ordered ones. -/
theorem equalSumPair_ordered_ncard :
    {r : (TrisectorLabel × TrisectorLabel) × (TrisectorLabel × TrisectorLabel) |
      r.1 ≠ r.2 ∧ r.1.1 + r.1.2 = r.2.1 + r.2.2}.ncard = 18 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  native_decide

/-- Each label has exactly two equal-sum partners: the `ncard = 2` of
`point_on_two_guideLines` at the level of labels. -/
theorem equalSumPair_partners (p : TrisectorLabel × TrisectorLabel) :
    {q : TrisectorLabel × TrisectorLabel | p ≠ q ∧ p.1 + p.2 = q.1 + q.2}.ncard = 2 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  native_decide +revert

/-- Three unordered pairs in each direction, counted as 6 ordered ones: the `ncard = 3`
of `guideLines_direction_card` at the level of labels. -/
theorem equalSumPair_direction_ncard (d : TrisectorLabel) :
    {r : (TrisectorLabel × TrisectorLabel) × (TrisectorLabel × TrisectorLabel) |
      r.1 ≠ r.2 ∧ r.1.1 + r.1.2 = r.2.1 + r.2.2 ∧ pairDirection r.1 r.2 = d}.ncard = 6 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  native_decide +revert


def lineScale (ℓ : Line E) (r : ℝ) (hr : r ≠ 0) : Line E :=
  ⟨ℓ.base, r • ℓ.direction, smul_ne_zero hr ℓ.direction_ne_zero⟩

theorem lineScale_mem (ℓ : Line E) {r : ℝ} (hr : r ≠ 0) (X : E) :
    (lineScale ℓ r hr).mem X ↔ ℓ.mem X := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t * r, ?_⟩
    rw [ht]
    show ℓ.base + t • (r • ℓ.direction) = ℓ.base + (t * r) • ℓ.direction
    rw [smul_smul]
  · rintro ⟨t, ht⟩
    refine ⟨t / r, ?_⟩
    rw [ht]
    show ℓ.base + t • ℓ.direction = ℓ.base + (t / r) • (r • ℓ.direction)
    rw [smul_smul, div_mul_cancel₀ _ hr]

theorem parallel_smul_direction {v d : E} {r : ℝ} (hr : r ≠ 0) :
    Parallel v (r • d) ↔ Parallel v d := by
  constructor
  · rintro ⟨ρ, hρ⟩
    refine ⟨r⁻¹ * ρ, ?_⟩
    calc d = r⁻¹ • (r • d) := by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
      _ = r⁻¹ • (ρ • v) := by rw [hρ]
      _ = (r⁻¹ * ρ) • v := by rw [smul_smul]
  · rintro ⟨ρ, hρ⟩
    exact ⟨r * ρ, by rw [hρ, smul_smul]⟩

theorem isCanonical_direction_norm {ℓ : Line E}
    (h : Line.isCanonical o ℓ) : ‖ℓ.direction‖ = 1 := h.1

theorem isCanonical_base_perp {ℓ : Line E}
    (h : Line.isCanonical o ℓ) : ⟪ℓ.base, ℓ.direction⟫ = 0 := h.2.1

theorem isCanonical_angle_mem {ℓ : Line E} (h : Line.isCanonical o ℓ) :
    (o.oangle (e₁ o) ℓ.direction).toReal ∈ Set.Ico 0 Real.pi := h.2.2

/-- `IsGuideLine` sees only the affine point set and the parallel class of the
direction, so it is invariant under rescaling the direction; this is why the repaired
`guideLines` has to add `Line.isCanonical`. -/
theorem isGuideLine_lineScale (T : OrientedTriangle E o) {ℓ : Line E} (hℓ : T.IsGuideLine ℓ)
    {r : ℝ} (hr : r ≠ 0) : T.IsGuideLine (lineScale ℓ r hr) := by
  obtain ⟨hpar, h6, h2⟩ := hℓ
  refine ⟨?_, ?_, ?_⟩
  · simpa only [parallelToMorleySide, lineScale, parallel_smul_direction hr] using hpar
  · have hset : {q : ConstellationIndex | (lineScale ℓ r hr).mem (T.constellationPoint q)}
        = {q : ConstellationIndex | ℓ.mem (T.constellationPoint q)} := by
      ext q
      exact lineScale_mem ℓ hr (T.constellationPoint q)
    rw [hset, h6]
  · intro c
    have hset : {q : ConstellationIndex |
          q.color = c ∧ (lineScale ℓ r hr).mem (T.constellationPoint q)}
        = {q : ConstellationIndex | q.color = c ∧ ℓ.mem (T.constellationPoint q)} := by
      ext q
      simp only [Set.mem_setOf_eq]
      rw [lineScale_mem ℓ hr (T.constellationPoint q)]
    rw [hset, h2 c]

/-! ### Canonicity: a geometric line has at most one canonical representative

This is what makes the repaired `guideLines` well posed: without it a line could have two
canonical representatives and the asserted counts could be doubled.  The only subtle point
is the sign of the direction, which the angular sector `[0,π)` of `Line.isCanonical` pins
down because an angle and the same angle plus `π` cannot both lie in `[0,π)`. -/

/-- An angle and that angle plus `π` cannot both have their real representative in
`[0,π)`. -/
theorem angle_sector_add_pi (θ : Real.Angle) :
    ¬ (θ.toReal ∈ Set.Ico 0 Real.pi ∧
      (θ + (Real.pi : Real.Angle)).toReal ∈ Set.Ico 0 Real.pi) := by
  rintro ⟨h1, h2⟩
  rcases lt_or_eq_of_le h1.1 with hpos | hzero
  · have hψ : θ + (Real.pi : Real.Angle) = ((θ.toReal - Real.pi : ℝ) : Real.Angle) := by
      conv_lhs => rw [← Real.Angle.coe_toReal θ]
      rw [← Real.Angle.coe_add]
      rw [show θ.toReal + Real.pi = (θ.toReal - Real.pi) + 2 * Real.pi by ring]
      rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
    have hval : (θ + (Real.pi : Real.Angle)).toReal = θ.toReal - Real.pi := by
      rw [hψ, Real.Angle.toReal_coe_eq_self_iff]
      constructor
      · linarith [hpos]
      · linarith [h1.2]
    rw [hval] at h2
    linarith [h1.2, h2.1]
  · have hθ0 : θ = 0 := by
      conv_lhs => rw [← Real.Angle.coe_toReal θ]
      simp [← hzero]
    have hval : (θ + (Real.pi : Real.Angle)).toReal = Real.pi := by
      rw [hθ0, zero_add, Real.Angle.toReal_pi]
    rw [hval] at h2
    exact absurd h2.2 (lt_irrefl Real.pi)

theorem isCanonical_eq_of_mem_iff {ℓ ℓ' : Line E}
    (hℓ : Line.isCanonical o ℓ) (hℓ' : Line.isCanonical o ℓ')
    (hmem : ∀ X : E, ℓ.mem X ↔ ℓ'.mem X) : ℓ = ℓ' := by
  -- two distinct common points determine the two directions
  have hbase_mem' : ℓ'.mem ℓ.base := (hmem ℓ.base).mp ℓ.mem_base
  have hYmem : ℓ.mem (ℓ.base + ℓ.direction) := by simpa using ℓ.mem_add_smul 1
  have hYmem' : ℓ'.mem (ℓ.base + ℓ.direction) := (hmem _).mp hYmem
  have hXY : ℓ.base ≠ ℓ.base + ℓ.direction := by
    intro h
    have h0 : ℓ.direction = 0 := by
      have h1 := congrArg (fun z : E => z - ℓ.base) h
      simpa using h1.symm
    exact ℓ.direction_ne_zero h0
  have hpar : Parallel ℓ.direction ℓ'.direction :=
    Line.parallel_of_mem_sub' hXY ℓ.mem_base hYmem hbase_mem' hYmem'
  obtain ⟨r, hr⟩ := hpar
  -- the common base point is forced by perpendicularity
  obtain ⟨s, hs⟩ := (hmem ℓ'.base).mpr ℓ'.mem_base
  have hrne : r ≠ 0 := by
    rintro h0
    rw [h0, zero_smul] at hr
    exact ℓ'.direction_ne_zero hr
  have hs0 : s = 0 := by
    have h1 : ⟪ℓ'.base, ℓ.direction⟫ = s * ⟪ℓ.direction, ℓ.direction⟫ := by
      rw [hs, inner_add_left, real_inner_smul_left, hℓ.2.1, zero_add]
    have h2 : ⟪ℓ'.base, ℓ.direction⟫ = 0 := by
      have hdir : ℓ.direction = r⁻¹ • ℓ'.direction := by
        rw [hr, smul_smul, inv_mul_cancel₀ hrne, one_smul]
      rw [hdir, real_inner_smul_right, hℓ'.2.1, mul_zero]
    have h3 : ⟪ℓ.direction, ℓ.direction⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hℓ.1]
      norm_num
    rw [h2, h3, mul_one] at h1
    exact h1.symm
  have hbase : ℓ'.base = ℓ.base := by rw [hs, hs0, zero_smul, add_zero]
  -- the unit directions agree up to sign, and the sector fixes the sign
  have habs : |r| = 1 := by
    have h : ‖ℓ'.direction‖ = |r| * ‖ℓ.direction‖ := by
      rw [hr, norm_smul, Real.norm_eq_abs]
    rw [hℓ'.1, hℓ.1, mul_one] at h
    linarith
  have hsq : r ^ 2 = 1 := by
    calc r ^ 2 = |r| ^ 2 := by rw [sq_abs]
      _ = 1 := by rw [habs]; norm_num
  have he1 : e₁ o ≠ 0 := by
    intro h0
    have h : ‖e₁ o‖ = 1 := (positiveBasis o).orthonormal.1 0
    rw [h0, norm_zero] at h
    norm_num at h
  have hdir : ℓ'.direction = ℓ.direction := by
    rcases sq_eq_one_iff.mp hsq with h1 | h1
    · rw [hr, h1, one_smul]
    · exfalso
      rw [h1, neg_one_smul] at hr
      have hneg : o.oangle (e₁ o) ℓ'.direction
          = o.oangle (e₁ o) ℓ.direction + (Real.pi : Real.Angle) := by
        rw [hr]
        exact Orientation.oangle_neg_right (o := o) he1 ℓ.direction_ne_zero
      have hsec : (o.oangle (e₁ o) ℓ.direction).toReal ∈ Set.Ico 0 Real.pi := hℓ.2.2
      have hsec' : ((o.oangle (e₁ o) ℓ.direction + (Real.pi : Real.Angle))).toReal
          ∈ Set.Ico 0 Real.pi := by
        rw [← hneg]
        exact hℓ'.2.2
      exact angle_sector_add_pi (o.oangle (e₁ o) ℓ.direction) ⟨hsec, hsec'⟩
  exact Line.ext hbase.symm hdir.symm

theorem guideLines_mem_iff (T : OrientedTriangle E o) (ℓ : Line E) :
    ℓ ∈ T.guideLines ↔ T.IsGuideLine ℓ ∧ Line.isCanonical o ℓ := Iff.rfl

theorem guideLines_isCanonical (T : OrientedTriangle E o) {ℓ : Line E}
    (h : ℓ ∈ T.guideLines) : Line.isCanonical o ℓ := h.2

theorem guideLines_six_points (T : OrientedTriangle E o) {ℓ : Line E}
    (h : ℓ ∈ T.guideLines) :
    {q : ConstellationIndex | ℓ.mem (T.constellationPoint q)}.ncard = 6 := h.1.2.1

theorem guideLines_two_per_color (T : OrientedTriangle E o) {ℓ : Line E}
    (h : ℓ ∈ T.guideLines) (c : TrisectorColor) :
    {q : ConstellationIndex | q.color = c ∧ ℓ.mem (T.constellationPoint q)}.ncard = 2 :=
  h.1.2.2 c




-- Every constellation point is incident with exactly two guide lines.


-- For each direction there are three parallel guide lines.


/-- Action of `U` on the circumference with center `O` and radius `r`, from the
last paragraph of Appendix B. -/
def circumference (O : E) (r : ℝ) : Set E := {X | dist X O = r}

theorem rotation_maps_circumference (O X : E) (r φ : ℝ)
    (hX : X ∈ circumference O r) : rotation o O φ X ∈ circumference O r := by
  change dist (rotation o O φ X) O = r
  calc
    dist (rotation o O φ X) O = dist (rotation o O φ X) (rotation o O φ O) := by
      rw [rotation_fixed_center]
    _ = dist X O := (rotation_isIsometry o O φ).dist_eq X O
    _ = r := hX

/-! ### The 36 triangles in Figures A3 and A4–A17 -/

/-- Three points, kept as an ordered triple so that orientation is available. -/
structure TriangleVertices (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  first : E
  second : E
  third : E

/-- A label `ijk` for a tricolor Morley triangle. -/
structure TricolorIndex where
  i : TrisectorLabel
  j : TrisectorLabel
  k : TrisectorLabel
  deriving DecidableEq, Fintype

/-- The tricolor triangle whose red, green and blue vertices are respectively
`ij`, `jk`, and `ki`. -/
def tricolorTriangle (T : OrientedTriangle E o) (q : TricolorIndex) : TriangleVertices E where
  first := T.constellationPoint ⟨.red, q.i, q.j⟩
  second := T.constellationPoint ⟨.green, q.j, q.k⟩
  third := T.constellationPoint ⟨.blue, q.k, q.i⟩

/-- Nine monochrome triangles, indexed by their color and by `s=0,1,2`.
For fixed `s`, the first coordinates are `s,s+1,s+2`, giving respectively
`00-12-21`, `01-10-22`, and `02-11-20`. -/
def monochromeTriangle (T : OrientedTriangle E o) (c : TrisectorColor)
    (s : TrisectorLabel) : TriangleVertices E where
  first := T.constellationPoint ⟨c, s, 0⟩
  second := T.constellationPoint ⟨c, s + 1, 2⟩
  third := T.constellationPoint ⟨c, s + 2, 1⟩

/-- Index type for the complete gallery: 27 tricolor and 9 monochrome labels. -/
abbrev GalleryIndex := TricolorIndex ⊕ (TrisectorColor × TrisectorLabel)

/-- One of the 36 ordered triangles in the gallery. -/
def galleryTriangle (T : OrientedTriangle E o) : GalleryIndex → TriangleVertices E
  | .inl q => T.tricolorTriangle q
  | .inr (c, s) => T.monochromeTriangle c s


/- Every monochrome Morley triangle is equilateral: proved by the pencil construction below. -/

/-! ### The two-vertex pencil lemma

For a vertex pair `P`, `Q` and any two real angles, the three constellation positions
`rf P Q φ0 ψ0`, `rf P Q (φ0-2λ) (ψ0-λ)`, `rf P Q (φ0-λ) (ψ0-2λ)` (`λ = 2π/3`) form an
equilateral triangle: all three share one denominator and the numerators differ by powers of
`ω = e^{iλ}`, so the only arithmetic input is `ω^4 = ω`. -/

theorem omega_ne_zero' : (omega : ℂ) ≠ 0 := by
  intro h
  have h3 := omega_cubed
  rw [h] at h3
  norm_num at h3

theorem omega_pow_four : (omega : ℂ) ^ 4 = (omega : ℂ) := by
  have h : (omega : ℂ) ^ 4 = (omega : ℂ) ^ 3 * (omega : ℂ) := by ring
  rw [h, omega_cubed, one_mul]

theorem omega_norm_one : ‖(omega : ℂ)‖ = 1 := Circle.norm_coe omega

theorem omega_sq_norm_one : ‖((omega : ℂ) ^ 2)‖ = 1 := by
  rw [norm_pow, omega_norm_one, one_pow]

/-- The coefficient relation behind the pencil lemma. -/
theorem pencil_coeff_relation (B : ℂ) :
    (1 - B * (omega : ℂ)) - (1 - B * (omega : ℂ) ^ 2) =
      (omega : ℂ) ^ 2 * ((1 - B * (omega : ℂ) ^ 2) - (1 - B)) := by
  have h4 : (omega : ℂ) ^ 4 = (omega : ℂ) := omega_pow_four
  have e : (omega : ℂ) ^ 2 * ((1 - B * (omega : ℂ) ^ 2) - (1 - B)) =
      B * (omega : ℂ) ^ 2 - B * (omega : ℂ) ^ 4 := by ring
  rw [e, h4]
  ring

/-- The same relation after dividing by the common denominator. -/
theorem pencil_coeff_rel_div (A B : ℂ) (hD : (1 - A * B) ≠ 0) :
    (1 - B * (omega : ℂ)) / (1 - A * B) - (1 - B * (omega : ℂ) ^ 2) / (1 - A * B) =
      (omega : ℂ) ^ 2 * ((1 - B * (omega : ℂ) ^ 2) / (1 - A * B) - (1 - B) / (1 - A * B)) := by
  rw [div_sub_div_same, div_sub_div_same, pencil_coeff_relation B, mul_div_assoc]

/-- **The two-vertex pencil lemma.** -/
theorem pencil_equilateral_coeff (P : E) (V A B : ℂ) (hD : (1 - A * B) ≠ 0) :
    Equilateral
      (P + ofComplex o (V * ((1 - B) / (1 - A * B))))
      (P + ofComplex o (V * ((1 - B * (omega : ℂ) ^ 2) / (1 - A * B))))
      (P + ofComplex o (V * ((1 - B * (omega : ℂ)) / (1 - A * B)))) := by
  have hrel := pencil_coeff_rel_div A B hD
  have h23 : (1 - B * (omega : ℂ) ^ 2) / (1 - A * B) - (1 - B * (omega : ℂ)) / (1 - A * B) =
      -((omega : ℂ) ^ 2 * ((1 - B * (omega : ℂ) ^ 2) / (1 - A * B) - (1 - B) / (1 - A * B))) := by
    rw [← hrel]; ring
  have h31 : (1 - B * (omega : ℂ)) / (1 - A * B) - (1 - B) / (1 - A * B) =
      (-(omega : ℂ)) * ((1 - B * (omega : ℂ) ^ 2) / (1 - A * B) - (1 - B) / (1 - A * B)) := by
    have hnum : (1 - B * (omega : ℂ)) - (1 - B) =
        (-(omega : ℂ)) * ((1 - B * (omega : ℂ) ^ 2) - (1 - B)) := by
      have h3 := omega_cubed
      linear_combination (-B) * h3
    rw [div_sub_div_same, div_sub_div_same, hnum, mul_div_assoc]
  have d12 : dist (P + ofComplex o (V * ((1 - B) / (1 - A * B))))
      (P + ofComplex o (V * ((1 - B * (omega : ℂ) ^ 2) / (1 - A * B)))) =
      ‖V‖ * ‖(1 - B) / (1 - A * B) - (1 - B * (omega : ℂ) ^ 2) / (1 - A * B)‖ := by
    rw [dist_eq_norm, show P + ofComplex o (V * ((1 - B) / (1 - A * B))) -
        (P + ofComplex o (V * ((1 - B * (omega : ℂ) ^ 2) / (1 - A * B)))) =
        ofComplex o (V * ((1 - B) / (1 - A * B) - (1 - B * (omega : ℂ) ^ 2) / (1 - A * B))) from by
      rw [add_sub_add_left_eq_sub, ← ofComplex_sub]; congr 1; ring]
    rw [ofComplex_norm, norm_mul]
  have d23 : dist (P + ofComplex o (V * ((1 - B * (omega : ℂ) ^ 2) / (1 - A * B))))
      (P + ofComplex o (V * ((1 - B * (omega : ℂ)) / (1 - A * B)))) =
      ‖V‖ * ‖(1 - B * (omega : ℂ) ^ 2) / (1 - A * B) - (1 - B * (omega : ℂ)) / (1 - A * B)‖ := by
    rw [dist_eq_norm, show P + ofComplex o (V * ((1 - B * (omega : ℂ) ^ 2) / (1 - A * B))) -
        (P + ofComplex o (V * ((1 - B * (omega : ℂ)) / (1 - A * B)))) =
        ofComplex o (V * ((1 - B * (omega : ℂ) ^ 2) / (1 - A * B) - (1 - B * (omega : ℂ)) / (1 - A * B))) from by
      rw [add_sub_add_left_eq_sub, ← ofComplex_sub]; congr 1; ring]
    rw [ofComplex_norm, norm_mul]
  have d31 : dist (P + ofComplex o (V * ((1 - B * (omega : ℂ)) / (1 - A * B))))
      (P + ofComplex o (V * ((1 - B) / (1 - A * B)))) =
      ‖V‖ * ‖(1 - B * (omega : ℂ)) / (1 - A * B) - (1 - B) / (1 - A * B)‖ := by
    rw [dist_eq_norm, show P + ofComplex o (V * ((1 - B * (omega : ℂ)) / (1 - A * B))) -
        (P + ofComplex o (V * ((1 - B) / (1 - A * B)))) =
        ofComplex o (V * ((1 - B * (omega : ℂ)) / (1 - A * B) - (1 - B) / (1 - A * B))) from by
      rw [add_sub_add_left_eq_sub, ← ofComplex_sub]; congr 1; ring]
    rw [ofComplex_norm, norm_mul]
  refine ⟨?_, ?_⟩
  · rw [d12, d23]
    congr 1
    simp only [h23, norm_neg, norm_mul, omega_sq_norm_one, one_mul, norm_sub_rev]
  · rw [d23, d31]
    congr 1
    simp only [h23, h31, norm_neg, norm_mul, omega_sq_norm_one, omega_norm_one, one_mul]

/-! ### The label-angle exponentials -/

theorem labelAngle_exp (j : TrisectorLabel) :
    (Circle.exp (labelAngle j) : ℂ) = (omega : ℂ) ^ (j.val) := by
  have h : labelAngle j = (j.val : ℝ) * (2 * Real.pi / 3) := rfl
  rw [h, Circle.exp_natCast_mul]
  norm_cast

theorem zmod3_cases (s : ZMod 3) : s = 0 ∨ s = 1 ∨ s = 2 := by revert s; decide

theorem labelAngle_zero : labelAngle (0 : TrisectorLabel) = 0 := by
  have h : ((0 : ZMod 3)).val = 0 := by decide
  simp [labelAngle, h]

theorem labelAngle_one : labelAngle (1 : TrisectorLabel) = 2 * Real.pi / 3 := by
  have h : ((1 : ZMod 3)).val = 1 := by decide
  simp [labelAngle, h]

theorem labelAngle_two : labelAngle (2 : TrisectorLabel) = 2 * (2 * Real.pi / 3) := by
  have h : ((2 : ZMod 3)).val = 2 := by decide
  simp [labelAngle, h]

theorem omega_inv' : (omega : ℂ)⁻¹ = (omega : ℂ) ^ 2 := by
  have h : (omega : ℂ) * (omega : ℂ) ^ 2 = 1 := by
    rw [← pow_succ']; exact omega_cubed
  exact inv_eq_of_mul_eq_one_right h

theorem omega_sq_mul : (omega : ℂ) ^ 2 * (omega : ℂ) = 1 := by
  rw [← pow_succ]; exact omega_cubed

theorem omega_mul_sq : (omega : ℂ) * (omega : ℂ) ^ 2 = 1 := by
  rw [← pow_succ']; exact omega_cubed

/-- `exp (i·labelAngle (s+1)) = exp (i·labelAngle s)·ω`. -/
theorem labelAngle_succ_exp (s : TrisectorLabel) :
    (Circle.exp (labelAngle (s + 1)) : ℂ) = (Circle.exp (labelAngle s) : ℂ) * (omega : ℂ) := by
  rw [labelAngle_exp, labelAngle_exp]
  rcases zmod3_cases s with rfl | rfl | rfl
  · rw [show ((0 : ZMod 3) + 1) = 1 from by decide,
      show ((1 : ZMod 3)).val = 1 from by decide,
      show ((0 : ZMod 3)).val = 0 from by decide, pow_one, pow_zero, one_mul]
  · rw [show ((1 : ZMod 3) + 1) = 2 from by decide,
      show ((2 : ZMod 3)).val = 2 from by decide,
      show ((1 : ZMod 3)).val = 1 from by decide, pow_one,
      show (2 : ℕ) = 1 + 1 by norm_num, pow_add, pow_one]
  · rw [show ((2 : ZMod 3) + 1) = 0 from by decide,
      show ((0 : ZMod 3)).val = 0 from by decide,
      show ((2 : ZMod 3)).val = 2 from by decide, pow_zero, omega_sq_mul]

/-- `exp (i·labelAngle (s+2)) = exp (i·labelAngle s)·ω²`. -/
theorem labelAngle_add_two_exp (s : TrisectorLabel) :
    (Circle.exp (labelAngle (s + 2)) : ℂ) = (Circle.exp (labelAngle s) : ℂ) * (omega : ℂ) ^ 2 := by
  rw [labelAngle_exp, labelAngle_exp]
  rcases zmod3_cases s with rfl | rfl | rfl
  · rw [show ((0 : ZMod 3) + 2) = 2 from by decide,
      show ((2 : ZMod 3)).val = 2 from by decide,
      show ((0 : ZMod 3)).val = 0 from by decide, pow_zero, one_mul]
  · rw [show ((1 : ZMod 3) + 2) = 0 from by decide,
      show ((0 : ZMod 3)).val = 0 from by decide,
      show ((1 : ZMod 3)).val = 1 from by decide, pow_zero, pow_one, omega_mul_sq]
  · rw [show ((2 : ZMod 3) + 2) = 1 from by decide,
      show ((1 : ZMod 3)).val = 1 from by decide,
      show ((2 : ZMod 3)).val = 2 from by decide, pow_one,
      show ((omega : ℂ) ^ 2 * (omega : ℂ) ^ 2) = (omega : ℂ) from by
        calc (omega : ℂ) ^ 2 * (omega : ℂ) ^ 2 = (omega : ℂ) ^ 4 := by ring
          _ = (omega : ℂ) ^ 3 * (omega : ℂ) := by ring
          _ = (omega : ℂ) := by rw [omega_cubed, one_mul]]

/-- `exp (i(c - labelAngle j)) = exp (ic)·(exp (i·labelAngle j))⁻¹`. -/
theorem exp_sub_labelAngle (c : ℝ) (j : TrisectorLabel) :
    (Circle.exp (c - labelAngle j) : ℂ) =
      (Circle.exp c : ℂ) * ((Circle.exp (labelAngle j) : ℂ))⁻¹ := by
  rw [sub_eq_add_neg, ← Circle.coe_inv, ← Circle.exp_neg, ← Circle.coe_mul, ← Circle.exp_add]

/-- **The two-vertex pencil lemma, unconditional.** -/
theorem pencil_equilateral (P : E) (V A B : ℂ) :
    Equilateral
      (P + ofComplex o (V * ((1 - B) / (1 - A * B))))
      (P + ofComplex o (V * ((1 - B * (omega : ℂ) ^ 2) / (1 - A * B))))
      (P + ofComplex o (V * ((1 - B * (omega : ℂ)) / (1 - A * B)))) := by
  by_cases hD : (1 - A * B) = 0
  · simp only [hD, div_zero, mul_zero, ofComplex_zero, add_zero]
    exact ⟨rfl, rfl⟩
  · exact pencil_equilateral_coeff P V A B hD


/-! ### Exponential identities for the monochrome positions -/

theorem omega_sq_inv : ((omega : ℂ) ^ 2)⁻¹ = (omega : ℂ) := by
  exact inv_eq_of_mul_eq_one_right omega_sq_mul

theorem labelAngle_zero_exp : (Circle.exp (labelAngle (0 : TrisectorLabel)) : ℂ) = 1 := by
  rw [labelAngle_zero]; simp

/-- The monochrome triple of one vertex pair `(P,Q)` with angles `a` at `P`, `b` at `Q`. -/
theorem monochrome_family (P Q : E) (a b : ℝ) (s : TrisectorLabel) :
    Equilateral
      (rotationFixedPoint o P Q (2 * a - labelAngle (0 : TrisectorLabel)) (2 * b - labelAngle s))
      (rotationFixedPoint o P Q (2 * a - labelAngle (2 : TrisectorLabel)) (2 * b - labelAngle (s + 1)))
      (rotationFixedPoint o P Q (2 * a - labelAngle (1 : TrisectorLabel)) (2 * b - labelAngle (s + 2))) := by
  set A : ℂ := (Circle.exp (2 * a) : ℂ) with hA
  set B : ℂ := (Circle.exp (2 * b - labelAngle s) : ℂ) with hB
  -- value of `B` as a product
  have hBval : B = (Circle.exp (2 * b) : ℂ) * ((Circle.exp (labelAngle s) : ℂ))⁻¹ := by
    rw [hB, exp_sub_labelAngle]
  -- the six exponential identities
  have e0 : (Circle.exp (2 * a - labelAngle (0 : TrisectorLabel)) : ℂ) = A := by
    rw [labelAngle_zero, sub_zero, hA]
  have e1 : (Circle.exp (2 * a - labelAngle (2 : TrisectorLabel)) : ℂ) = A * (omega : ℂ) := by
    rw [exp_sub_labelAngle, labelAngle_exp, show ((2 : ZMod 3)).val = 2 from by decide,
      omega_sq_inv, hA]
  have e2 : (Circle.exp (2 * a - labelAngle (1 : TrisectorLabel)) : ℂ) = A * (omega : ℂ) ^ 2 := by
    rw [exp_sub_labelAngle, labelAngle_exp, show ((1 : ZMod 3)).val = 1 from by decide, pow_one,
      omega_inv', hA]
  have f0 : (Circle.exp (2 * b - labelAngle s) : ℂ) = B := hB.symm
  have f1 : (Circle.exp (2 * b - labelAngle (s + 1)) : ℂ) = B * (omega : ℂ) ^ 2 := by
    rw [exp_sub_labelAngle, labelAngle_succ_exp, mul_inv, omega_inv', hBval]
    ring
  have f2 : (Circle.exp (2 * b - labelAngle (s + 2)) : ℂ) = B * (omega : ℂ) := by
    rw [exp_sub_labelAngle, labelAngle_add_two_exp, mul_inv, omega_sq_inv, hBval]
    ring
  -- the denominators agree
  have hAB2 : (A * (omega : ℂ)) * (B * (omega : ℂ) ^ 2) = A * B := by
    have h3 := omega_cubed
    linear_combination (A * B) * h3
  have hAB3 : (A * (omega : ℂ) ^ 2) * (B * (omega : ℂ)) = A * B := by
    have h3 := omega_cubed
    linear_combination (A * B) * h3
  have hp := pencil_equilateral (o := o) P (toComplex o (Q - P)) A B
  have q1 : rotationFixedPoint o P Q (2 * a - labelAngle (0 : TrisectorLabel))
      (2 * b - labelAngle s) =
      P + ofComplex o (toComplex o (Q - P) * ((1 - B) / (1 - A * B))) := by
    simp only [rotationFixedPoint]
    rw [e0, f0]
  have q2 : rotationFixedPoint o P Q (2 * a - labelAngle (2 : TrisectorLabel))
      (2 * b - labelAngle (s + 1)) =
      P + ofComplex o (toComplex o (Q - P) * ((1 - B * (omega : ℂ) ^ 2) / (1 - A * B))) := by
    simp only [rotationFixedPoint]
    rw [e1, f1, hAB2]
  have q3 : rotationFixedPoint o P Q (2 * a - labelAngle (1 : TrisectorLabel))
      (2 * b - labelAngle (s + 2)) =
      P + ofComplex o (toComplex o (Q - P) * ((1 - B * (omega : ℂ)) / (1 - A * B))) := by
    simp only [rotationFixedPoint]
    rw [e2, f2, hAB3]
  rw [q1, q2, q3]
  exact hp

/-! ### `monochrome_equilateral` -/

/-- **Every monochrome Morley triangle is equilateral** (the file's `monochrome_equilateral`,
proved). -/
theorem monochrome_equilateral_proof (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (c : TrisectorColor) (s : TrisectorLabel) :
    Equilateral (T.monochromeTriangle c s).first (T.monochromeTriangle c s).second
      (T.monochromeTriangle c s).third := by
  cases c
  · exact monochrome_family (o := o) T.C T.B T.gamma T.beta s
  · exact monochrome_family (o := o) T.A T.C T.alpha T.gamma s
  · exact monochrome_family (o := o) T.B T.A T.beta T.alpha s
theorem monochrome_equilateral (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (c : TrisectorColor) (s : TrisectorLabel) :
    Equilateral (T.monochromeTriangle c s).first (T.monochromeTriangle c s).second
      (T.monochromeTriangle c s).third := by exact monochrome_equilateral_proof T h c s



theorem toComplex_B_sub_C (T : OrientedTriangle E o) :
    toComplex o (T.B - T.C) = ((T.delta * Real.sin (3 * T.alpha)) : ℂ) *
      (Circle.exp (-3 * T.beta) : ℂ) * toComplex o T.cStar := by
  have h1 : T.B - T.C = -(T.a) := by rw [OrientedTriangle.a]; abel
  have h2 : toComplex o T.aStar =
      -(Circle.exp (-3 * T.beta) : ℂ) * toComplex o T.cStar := by
    rw [T.aStar_relation, toComplex_neg, toComplex_rotateVector]
    ring
  rw [h1, toComplex_neg, T.a_eq, toComplex_smul, h2, T.side_lengths_sine.1]
  push_cast
  ring_nf

theorem toComplex_C_sub_A (T : OrientedTriangle E o) :
    toComplex o (T.C - T.A) = ((T.delta * Real.sin (3 * T.beta)) : ℂ) *
      (Circle.exp (3 * T.alpha) : ℂ) * toComplex o T.cStar := by
  have hE : (Circle.exp (3 * T.alpha) : ℂ) * (Circle.exp (-3 * T.alpha) : ℂ) = 1 := by
    rw [m3_exp_mul_exp, show 3 * T.alpha + (-3 * T.alpha) = 0 from by ring, Circle.exp_zero,
      Circle.coe_one]
  have hc : toComplex o T.cStar =
      (Circle.exp (-3 * T.alpha) : ℂ) * (-(toComplex o T.bStar)) := by
    rw [T.cStar_relation, toComplex_neg, toComplex_rotateVector]
    ring
  have hb : toComplex o T.bStar =
      -(Circle.exp (3 * T.alpha) : ℂ) * toComplex o T.cStar := by
    have hc' : (Circle.exp (-3 * T.alpha) : ℂ) * toComplex o T.bStar =
        -(toComplex o T.cStar) := by rw [hc]; ring
    calc toComplex o T.bStar
        = ((Circle.exp (3 * T.alpha) : ℂ) * (Circle.exp (-3 * T.alpha) : ℂ)) *
          toComplex o T.bStar := by rw [hE, one_mul]
      _ = (Circle.exp (3 * T.alpha) : ℂ) *
          ((Circle.exp (-3 * T.alpha) : ℂ) * toComplex o T.bStar) := by ring
      _ = (Circle.exp (3 * T.alpha) : ℂ) * (-(toComplex o T.cStar)) := by rw [hc']
      _ = -(Circle.exp (3 * T.alpha) : ℂ) * toComplex o T.cStar := by ring
  have h1 : T.C - T.A = -(T.b) := by rw [OrientedTriangle.b]; abel
  rw [h1, toComplex_neg, T.b_eq, toComplex_smul, hb, T.side_lengths_sine.2.1]
  push_cast
  ring

theorem toComplex_A_sub_B (T : OrientedTriangle E o) :
    toComplex o (T.A - T.B) = -((T.delta * Real.sin (3 * T.gamma)) : ℂ) *
      toComplex o T.cStar := by
  have h1 : T.A - T.B = -(T.c) := by rw [OrientedTriangle.c]; abel
  rw [h1, toComplex_neg, T.c_eq, toComplex_smul, T.side_lengths_sine.2.2]
  push_cast
  ring

theorem sin_exp_add_neg (u v : ℝ) :
    (Real.sin u : ℂ) * (Circle.exp v : ℂ) + (Real.sin v : ℂ) * (Circle.exp (-u) : ℂ)
      = (Real.sin (u + v) : ℂ) := by
  rw [Circle.coe_exp, Circle.coe_exp, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
    Real.cos_neg, Real.sin_neg, Real.sin_add]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_add, mul_one, mul_zero, sub_zero, zero_add, add_zero, sub_self]
    ring
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_add, mul_one, mul_zero, sub_zero, zero_add, add_zero, sub_self]
    ring



theorem sin_shift_identity (g : ℝ) :
    (Real.sin (g - 2 * Real.pi / 3) : ℂ) * (Circle.exp (-(Real.pi / 3)) : ℂ) + (Real.sin g : ℂ)
      = (Real.sin (Real.pi / 3) : ℂ) * (Circle.exp (2 * Real.pi / 3 - g) : ℂ) := by
  have hc : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
  have hs : Real.sin (2 * Real.pi / 3) = Real.sin (Real.pi / 3) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring, Real.sin_pi_sub]
  rw [Circle.coe_exp, Circle.coe_exp, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_three]
  simp only [Real.sin_sub, Real.cos_sub, hc, hs]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_neg, Complex.ofReal_ofNat, mul_one, mul_zero, sub_zero, zero_add, add_zero,
      sub_self]
    have h3 := Real.sin_sq_add_cos_sq (Real.pi / 3)
    have h2 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    have h4 : Real.sin (Real.pi / 3) ^ 2 = 3 / 4 := by nlinarith [h3, h2]
    have h5 : Real.sin (Real.pi * (1 / 3)) ^ 2 = 3 / 4 := by rw [← h4]; ring_nf
    ring_nf
    try rw [h4]
    rw [h5]
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_neg, Complex.ofReal_ofNat, mul_one, mul_zero, sub_zero, zero_add, add_zero,
      sub_self]
    ring_nf

#print axioms XamboMorley.OrientedTriangle.sin_shift_identity

#print axioms XamboMorley.OrientedTriangle.toComplex_B_sub_C
#print axioms XamboMorley.OrientedTriangle.toComplex_C_sub_A
#print axioms XamboMorley.OrientedTriangle.toComplex_A_sub_B
#print axioms XamboMorley.OrientedTriangle.sin_exp_add_neg
#print axioms XamboMorley.OrientedTriangle.sin_shift_identity





/-- There are 18 equilateral and 9 non-equilateral tricolor triangles. -/
theorem equilateral_tricolor_count :
    {q : TricolorIndex | q.i + q.j + q.k ≠ 1}.ncard = 18 ∧
      {q : TricolorIndex | q.i + q.j + q.k = 1}.ncard = 9 := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  native_decide

/-- The full gallery has 36 triangles and 27 equilateral triangles. -/
theorem gallery_card (T : OrientedTriangle E o) (h : Injective T.galleryTriangle) :
    (Set.range T.galleryTriangle).ncard = 36 := by
  rw [Set.ncard_range_of_injective h, Nat.card_eq_fintype_card]
  native_decide

/-! ### The gallery count -/

/-- The colour-blind label predicate that decides equilateralism in the gallery. -/
def galleryGood : GalleryIndex → Bool
  | .inl q => decide (q.i + q.j + q.k ≠ 1)
  | .inr _ => true

/-- The gallery has 27 equilateral triangles, from the two equilateral criteria. -/
theorem gallery_equilateral_card_of_criteria (T : OrientedTriangle E o)
    (h : Injective T.galleryTriangle)
    (htri : ∀ q : TricolorIndex, Equilateral (T.tricolorTriangle q).first
      (T.tricolorTriangle q).second (T.tricolorTriangle q).third ↔ q.i + q.j + q.k ≠ 1)
    (hmono : ∀ (c : TrisectorColor) (s : TrisectorLabel),
      Equilateral (T.monochromeTriangle c s).first (T.monochromeTriangle c s).second
        (T.monochromeTriangle c s).third) :
    {t ∈ Set.range T.galleryTriangle | Equilateral t.first t.second t.third}.ncard = 27 := by
  classical
  have himg : {t ∈ Set.range T.galleryTriangle | Equilateral t.first t.second t.third}
      = T.galleryTriangle '' {g : GalleryIndex | Equilateral (T.galleryTriangle g).first
          (T.galleryTriangle g).second (T.galleryTriangle g).third} := by
    ext t
    constructor
    · rintro ⟨⟨g, rfl⟩, hg⟩
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, rfl⟩, hg⟩
  rw [himg, Set.ncard_image_of_injective _ h]
  have hset : {g : GalleryIndex | Equilateral (T.galleryTriangle g).first
        (T.galleryTriangle g).second (T.galleryTriangle g).third}
      = {g : GalleryIndex | galleryGood g = true} := by
    ext g
    rcases g with q | ⟨c, s⟩
    · show Equilateral (T.tricolorTriangle q).first (T.tricolorTriangle q).second
          (T.tricolorTriangle q).third ↔ galleryGood (.inl q) = true
      rw [htri q]
      simp [galleryGood]
    · show Equilateral (T.monochromeTriangle c s).first (T.monochromeTriangle c s).second
          (T.monochromeTriangle c s).third ↔ galleryGood (.inr (c, s)) = true
      have hg : galleryGood (.inr (c, s)) = true := rfl
      rw [hg]
      exact ⟨fun _ => rfl, fun _ => hmono c s⟩
  rw [hset, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  native_decide

/-- Positive and negative orientation, corresponding to `⟲` and `⟳`. -/
def PositivelyOriented (t : TriangleVertices E) : Prop :=
  0 < orientedArea o (t.second - t.first) (t.third - t.first)
def NegativelyOriented (t : TriangleVertices E) : Prop :=
  orientedArea o (t.second - t.first) (t.third - t.first) < 0

-- Orientation of the tricolor labels as marked in Figures A4–A14: sum zero is
-- positive, sum two negative; among the non-equilateral sum-one triangles, the
-- `112` family is positive and the `001` and `022` families are negative.



/-- The red monochrome triples in Figure A15; green and blue are obtained by
changing the color argument in `monochromeTriangle`. -/
def redMonochromeTriangles (T : OrientedTriangle E o) : Fin 3 → TriangleVertices E :=
  ![T.monochromeTriangle .red 0, T.monochromeTriangle .red 1, T.monochromeTriangle .red 2]

theorem m7_norm_aStar (T : OrientedTriangle E o) : ‖T.aStar‖ = 1 := by
  rw [OrientedTriangle.aStar, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos T.aLength_pos]
  exact inv_mul_cancel₀ (ne_of_gt T.aLength_pos)

theorem m7_norm_bStar (T : OrientedTriangle E o) : ‖T.bStar‖ = 1 := by
  rw [OrientedTriangle.bStar, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos T.bLength_pos]
  exact inv_mul_cancel₀ (ne_of_gt T.bLength_pos)

theorem m7_norm_cStar (T : OrientedTriangle E o) : ‖T.cStar‖ = 1 := by
  rw [OrientedTriangle.cStar, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos T.cLength_pos]
  exact inv_mul_cancel₀ (ne_of_gt T.cLength_pos)

theorem m7_alpha_lt_pi (T : OrientedTriangle E o) : T.alpha < Real.pi := by
  have h := m3_three_alpha_lt_pi T
  linarith [Real.pi_pos]

theorem m7_beta_lt_pi (T : OrientedTriangle E o) : T.beta < Real.pi := by
  have h := m3_three_beta_lt_pi T
  linarith [Real.pi_pos]

theorem m7_gamma_lt_pi (T : OrientedTriangle E o) : T.gamma < Real.pi := by
  have h := m3_three_gamma_lt_pi T
  linarith [Real.pi_pos]

theorem m7_sin_alpha_pos (T : OrientedTriangle E o) : 0 < Real.sin T.alpha :=
  Real.sin_pos_of_pos_of_lt_pi (m3_alpha_pos T) (m7_alpha_lt_pi T)

theorem m7_sin_beta_pos (T : OrientedTriangle E o) : 0 < Real.sin T.beta :=
  Real.sin_pos_of_pos_of_lt_pi (m3_beta_pos T) (m7_beta_lt_pi T)

theorem m7_sin_gamma_pos (T : OrientedTriangle E o) : 0 < Real.sin T.gamma :=
  Real.sin_pos_of_pos_of_lt_pi (m3_gamma_pos T) (m7_gamma_lt_pi T)

theorem m7_delta_pos (T : OrientedTriangle E o) : 0 < T.delta := by
  rw [OrientedTriangle.delta]
  exact div_pos T.aLength_pos (m3_sin_three_alpha_pos T)

theorem m7_complexMulVector_mul (z w : ℂ) (v : E) :
    complexMulVector o (z * w) v = complexMulVector o z (complexMulVector o w v) := by
  apply toComplex_injective o
  simp only [w9_toComplex_complexMulVector]
  ring

theorem m7_complexMulVector_ofReal (r : ℝ) (v : E) :
    complexMulVector o (r : ℂ) v = r • v := by
  apply toComplex_injective o
  simp only [w9_toComplex_complexMulVector, toComplex_smul]
  exact mul_comm _ _

theorem m7_complexMulVector_smul (z : ℂ) (r : ℝ) (v : E) :
    complexMulVector o z (r • v) = r • complexMulVector o z v := by
  apply toComplex_injective o
  simp only [w9_toComplex_complexMulVector, toComplex_smul, Complex.real_smul]
  ring

theorem m7_complexMulVector_ofReal_mul (r : ℝ) (z : ℂ) (v : E) :
    complexMulVector o ((r : ℂ) * z) v = r • complexMulVector o z v := by
  rw [m7_complexMulVector_mul, m7_complexMulVector_ofReal]

theorem m7_cmv_add (z w : ℂ) (v : E) :
    complexMulVector o (z + w) v = complexMulVector o z v + complexMulVector o w v := by
  apply toComplex_injective o
  simp only [w9_toComplex_complexMulVector, toComplex_add, mul_add]

theorem m7_cmv_sub (z w : ℂ) (v : E) :
    complexMulVector o (z - w) v = complexMulVector o z v - complexMulVector o w v := by
  apply toComplex_injective o
  simp only [w9_toComplex_complexMulVector, toComplex_sub, mul_sub]

theorem m7_cmv_add_v (z : ℂ) (v w : E) :
    complexMulVector o z (v + w) = complexMulVector o z v + complexMulVector o z w := by
  apply toComplex_injective o
  simp only [w9_toComplex_complexMulVector, toComplex_add, add_mul]

theorem m7_cmv_sub_v (z : ℂ) (v w : E) :
    complexMulVector o z (v - w) = complexMulVector o z v - complexMulVector o z w := by
  apply toComplex_injective o
  simp only [w9_toComplex_complexMulVector, toComplex_sub, sub_mul]

theorem m7_bStar_eq_inv (T : OrientedTriangle E o) :
    T.bStar = (T.bLength)⁻¹ • T.b := by
  rw [T.b_eq, smul_smul, inv_mul_cancel₀ (ne_of_gt T.bLength_pos), one_smul]

theorem m7_c_eq_rotate (T : OrientedTriangle E o) :
    T.c = -((T.cLength / T.bLength) • rotateVector o T.b (-3 * T.alpha)) := by
  conv_lhs => rw [T.c_eq, T.cStar_relation, m7_bStar_eq_inv T, rotateVector_smul]
  rw [smul_neg, smul_smul]
  congr 2

theorem m7_rotate_c_eq (T : OrientedTriangle E o) :
    rotateVector o T.c T.alpha =
      -((T.cLength / T.bLength) • rotateVector o T.b (-2 * T.alpha)) := by
  conv_lhs => rw [m7_c_eq_rotate T]
  rw [show -((T.cLength / T.bLength) • rotateVector o T.b (-3 * T.alpha))
      = (-(T.cLength / T.bLength)) • rotateVector o T.b (-3 * T.alpha) from by rw [neg_smul],
    rotateVector_smul, ← rotateVector_add_angle,
    show T.alpha + -3 * T.alpha = -2 * T.alpha from by ring, neg_smul]

theorem m7_sin_theta_beta (T : OrientedTriangle E o) :
    Real.sin (thetaStar T.beta) = Real.sin (T.gamma + T.alpha) := by
  dsimp [thetaStar]
  congr 1
  have h := T.angle_sum
  linarith

theorem m7_sin_theta_gamma (T : OrientedTriangle E o) :
    Real.sin (thetaStar T.gamma) = Real.sin (T.alpha + T.beta) := by
  dsimp [thetaStar]
  congr 1
  have h := T.angle_sum
  linarith

theorem m7_sin_ga_ne (T : OrientedTriangle E o) : Real.sin (T.gamma + T.alpha) ≠ 0 :=
  ne_of_gt (m3_sin_gamma_add_alpha_pos T)

theorem m7_sin_ab_ne (T : OrientedTriangle E o) : Real.sin (T.alpha + T.beta) ≠ 0 :=
  ne_of_gt (m3_sin_alpha_add_beta_pos T)

theorem m7_exp_neg_two (T : OrientedTriangle E o) :
    (Circle.exp (-T.alpha) : ℂ) * Circle.exp (-T.alpha) = (Circle.exp (-2 * T.alpha) : ℂ) := by
  rw [m3_exp_mul_exp]
  rw [show -T.alpha + (-T.alpha) = (-2 : ℝ) * T.alpha from by ring]

theorem m7_key_trig (T : OrientedTriangle E o) :
    (Real.sin (T.gamma + T.alpha) : ℂ) =
      (Real.sin T.alpha : ℂ) * (Circle.exp T.gamma : ℂ) +
        (Real.sin T.gamma : ℂ) * (Circle.exp (-T.alpha) : ℂ) := by
  have eγ : (Circle.exp T.gamma : ℂ) =
      (Real.cos T.gamma : ℂ) + (Real.sin T.gamma : ℂ) * Complex.I := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I]
  have eα : (Circle.exp (-T.alpha) : ℂ) =
      (Real.cos T.alpha : ℂ) - (Real.sin T.alpha : ℂ) * Complex.I := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [eγ, eα, Real.sin_add]
  push_cast
  ring

theorem m7_bLength_div (T : OrientedTriangle E o) :
    T.bLength * Real.sin T.gamma / Real.sin (thetaStar T.beta) =
      4 * T.delta * Real.sin T.beta * Real.sin T.gamma * Real.sin (thetaStarStar T.beta) := by
  have hb : T.bLength = T.delta * Real.sin (3 * T.beta) := T.side_lengths_sine.2.1
  have hst : Real.sin (thetaStar T.beta) ≠ 0 := by
    have h : Real.sin (thetaStar T.beta) = Real.sin (T.gamma + T.alpha) := by
      dsimp [thetaStar]
      congr 1
      have hh := T.angle_sum
      linarith
    rw [h]; exact ne_of_gt (m3_sin_gamma_add_alpha_pos T)
  rw [hb, trigonometric_identity_A4 T.beta]
  field_simp

theorem m7_cLength_div (T : OrientedTriangle E o) :
    T.cLength * Real.sin T.beta / Real.sin (thetaStar T.gamma) =
      4 * T.delta * Real.sin T.beta * Real.sin T.gamma * Real.sin (thetaStarStar T.gamma) := by
  have hc : T.cLength = T.delta * Real.sin (3 * T.gamma) := T.side_lengths_sine.2.2
  have hst : Real.sin (thetaStar T.gamma) ≠ 0 := by
    have h : Real.sin (thetaStar T.gamma) = Real.sin (T.alpha + T.beta) := by
      dsimp [thetaStar]
      congr 1
      have hh := T.angle_sum
      linarith
    rw [h]; exact ne_of_gt (m3_sin_alpha_add_beta_pos T)
  rw [hc, trigonometric_identity_A4 T.gamma]
  field_simp

theorem m7_ZY_form (T : OrientedTriangle E o) :
    T.Z - T.Y = T.b + (Real.sin T.beta / Real.sin (T.alpha + T.beta)) • rotateVector o T.c T.alpha
      - (Real.sin T.alpha / Real.sin (T.gamma + T.alpha)) • rotateVector o T.b T.gamma := by
  rw [T.Z_third, T.Y_third]
  simp only [OrientedTriangle.b, OrientedTriangle.c]
  abel

theorem m7_main (T : OrientedTriangle E o) :
    T.b = (Real.sin T.alpha / Real.sin (T.gamma + T.alpha)) • rotateVector o T.b T.gamma
      + (Real.sin T.gamma / Real.sin (T.gamma + T.alpha)) • rotateVector o T.b (-T.alpha) := by
  have h := m7_key_trig T
  have hsm : (Real.sin (T.gamma + T.alpha)) • T.b =
      (Real.sin T.alpha) • rotateVector o T.b T.gamma
        + (Real.sin T.gamma) • rotateVector o T.b (-T.alpha) := by
    apply toComplex_injective o
    simp only [toComplex_smul, toComplex_rotateVector, toComplex_add, Complex.real_smul]
    linear_combination (toComplex o T.b) * h
  have h2 := congrArg (fun v => (Real.sin (T.gamma + T.alpha))⁻¹ • v) hsm
  simp only [smul_add, smul_smul] at h2
  rw [inv_mul_cancel₀ (m7_sin_ga_ne T), one_smul] at h2
  simpa [div_eq_mul_inv, mul_comm] using h2

theorem m7_coef1 (T : OrientedTriangle E o) :
    (T.bLength * Real.sin T.gamma / Real.sin (T.gamma + T.alpha) : ℝ) * (T.bLength)⁻¹
      = Real.sin T.gamma / Real.sin (T.gamma + T.alpha) := by
  have hb : T.bLength ≠ 0 := ne_of_gt T.bLength_pos
  have hs : Real.sin (T.gamma + T.alpha) ≠ 0 := m7_sin_ga_ne T
  field_simp

theorem m7_coef2 (T : OrientedTriangle E o) :
    (T.cLength * Real.sin T.beta / Real.sin (T.alpha + T.beta) : ℝ) * (T.bLength)⁻¹
      = (T.cLength / T.bLength) * (Real.sin T.beta / Real.sin (T.alpha + T.beta)) := by
  have hb : T.bLength ≠ 0 := ne_of_gt T.bLength_pos
  have hs : Real.sin (T.alpha + T.beta) ≠ 0 := m7_sin_ab_ne T
  field_simp

theorem m7_RHS_form (T : OrientedTriangle E o) :
    complexMulVector o (Circle.exp (-T.alpha))
      (complexMulVector o
        ((T.bLength * Real.sin T.gamma / Real.sin (thetaStar T.beta) : ℝ) -
          (T.cLength * Real.sin T.beta / Real.sin (thetaStar T.gamma) : ℝ) *
            Circle.exp (-T.alpha)) T.bStar)
      = (Real.sin T.gamma / Real.sin (T.gamma + T.alpha)) • rotateVector o T.b (-T.alpha)
        - ((T.cLength / T.bLength) * (Real.sin T.beta / Real.sin (T.alpha + T.beta))) •
            rotateVector o T.b (-2 * T.alpha) := by
  rw [m7_sin_theta_beta T, m7_sin_theta_gamma T]
  have h1 : complexMulVector o (((T.bLength * Real.sin T.gamma / Real.sin (T.gamma + T.alpha) : ℝ) : ℂ) -
      ((T.cLength * Real.sin T.beta / Real.sin (T.alpha + T.beta) : ℝ) : ℂ) *
        (Circle.exp (-T.alpha) : ℂ)) T.bStar
      = (T.bLength * Real.sin T.gamma / Real.sin (T.gamma + T.alpha) : ℝ) • T.bStar
        - (T.cLength * Real.sin T.beta / Real.sin (T.alpha + T.beta) : ℝ) •
            rotateVector o T.bStar (-T.alpha) := by
    rw [m7_cmv_sub, m7_complexMulVector_mul, m7_complexMulVector_ofReal,
      m7_complexMulVector_ofReal]
    rfl
  have h2 : complexMulVector o (Circle.exp (-T.alpha))
      ((T.bLength * Real.sin T.gamma / Real.sin (T.gamma + T.alpha) : ℝ) • T.bStar
        - (T.cLength * Real.sin T.beta / Real.sin (T.alpha + T.beta) : ℝ) •
            rotateVector o T.bStar (-T.alpha))
      = (T.bLength * Real.sin T.gamma / Real.sin (T.gamma + T.alpha) : ℝ) •
          rotateVector o T.bStar (-T.alpha)
        - (T.cLength * Real.sin T.beta / Real.sin (T.alpha + T.beta) : ℝ) •
            rotateVector o T.bStar (-2 * T.alpha) := by
    rw [m7_cmv_sub_v, m7_complexMulVector_smul, m7_complexMulVector_smul]
    have hb1 : complexMulVector o (Circle.exp (-T.alpha)) T.bStar =
        rotateVector o T.bStar (-T.alpha) := rfl
    have hb2 : complexMulVector o (Circle.exp (-T.alpha)) (rotateVector o T.bStar (-T.alpha)) =
        rotateVector o T.bStar (-2 * T.alpha) := by
      rw [show rotateVector o T.bStar (-T.alpha) =
          complexMulVector o (Circle.exp (-T.alpha)) T.bStar from rfl, ← m7_complexMulVector_mul,
        m7_exp_neg_two T]
      rfl
    rw [hb1, hb2]
  rw [h1, h2]
  rw [show (T.bLength * Real.sin T.gamma / Real.sin (T.gamma + T.alpha) : ℝ) • rotateVector o T.bStar (-T.alpha)
      = (Real.sin T.gamma / Real.sin (T.gamma + T.alpha)) • rotateVector o T.b (-T.alpha) from by
    rw [m7_bStar_eq_inv T, rotateVector_smul, smul_smul, m7_coef1 T]]
  rw [show (T.cLength * Real.sin T.beta / Real.sin (T.alpha + T.beta) : ℝ) • rotateVector o T.bStar (-2 * T.alpha)
      = ((T.cLength / T.bLength) * (Real.sin T.beta / Real.sin (T.alpha + T.beta))) •
          rotateVector o T.b (-2 * T.alpha) from by
    rw [m7_bStar_eq_inv T, rotateVector_smul, smul_smul, m7_coef2 T]]

/-- The expression for `Z-Y` preceding Equation (18), exactly as in `⋄14`. -/
theorem Z_sub_Y_preliminary (T : OrientedTriangle E o) :
    T.Z - T.Y = complexMulVector o (Circle.exp (-T.alpha))
      (complexMulVector o
        ((T.bLength * Real.sin T.gamma / Real.sin (thetaStar T.beta) : ℝ) -
          (T.cLength * Real.sin T.beta / Real.sin (thetaStar T.gamma) : ℝ) *
            Circle.exp (-T.alpha)) T.bStar) := by
  have key : T.b - (Real.sin T.alpha / Real.sin (T.gamma + T.alpha)) • rotateVector o T.b T.gamma
      = (Real.sin T.gamma / Real.sin (T.gamma + T.alpha)) • rotateVector o T.b (-T.alpha) := by
    nth_rewrite 1 [m7_main T]
    abel
  rw [m7_ZY_form T, m7_RHS_form T, ← key, m7_rotate_c_eq T, smul_neg, smul_smul]
  module

/-- The same expression after using Equations (A2) and (A4). -/
theorem Z_sub_Y_delta (T : OrientedTriangle E o) :
    T.Z - T.Y = (4 * T.delta * Real.sin T.beta * Real.sin T.gamma) •
      complexMulVector o (Circle.exp (-T.alpha))
        (complexMulVector o ((Real.sin (thetaStarStar T.beta) : ℂ) -
            Real.sin (thetaStarStar T.gamma) * Circle.exp (-T.alpha)) T.bStar) := by
  have h1 := T.m7_bLength_div
  have h2 := T.m7_cLength_div
  have hs : (((T.bLength * Real.sin T.gamma / Real.sin (thetaStar T.beta) : ℝ) : ℂ) -
        ((T.cLength * Real.sin T.beta / Real.sin (thetaStar T.gamma) : ℝ) : ℂ) *
          (Circle.exp (-T.alpha) : ℂ))
      = (4 * T.delta * Real.sin T.beta * Real.sin T.gamma : ℂ) *
        ((Real.sin (thetaStarStar T.beta) : ℂ) -
          Real.sin (thetaStarStar T.gamma) * (Circle.exp (-T.alpha) : ℂ)) := by
    have h1' : ((T.bLength * Real.sin T.gamma / Real.sin (thetaStar T.beta) : ℝ) : ℂ)
        = ((4 * T.delta * Real.sin T.beta * Real.sin T.gamma *
            Real.sin (thetaStarStar T.beta) : ℝ) : ℂ) := by rw [h1]
    have h2' : ((T.cLength * Real.sin T.beta / Real.sin (thetaStar T.gamma) : ℝ) : ℂ)
        = ((4 * T.delta * Real.sin T.beta * Real.sin T.gamma *
            Real.sin (thetaStarStar T.gamma) : ℝ) : ℂ) := by rw [h2]
    rw [h1', h2']
    push_cast
    ring
  have hcast : (4 * (T.delta : ℂ) * (Real.sin T.beta : ℂ) * (Real.sin T.gamma : ℂ))
      = ((4 * T.delta * Real.sin T.beta * Real.sin T.gamma : ℝ) : ℂ) := by push_cast; ring
  rw [T.Z_sub_Y_preliminary, hs, hcast, m7_complexMulVector_ofReal_mul, m7_complexMulVector_smul]

/-- Equation (18). -/
theorem Z_sub_Y (T : OrientedTriangle E o) :
    T.Z - T.Y = (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) •
      rotateVector o T.bStar (T.beta + 2 * T.gamma) := by
  have hangle : -T.alpha + thetaPrime T.gamma = T.beta + 2 * T.gamma := by
    dsimp [thetaPrime]
    linear_combination (-(1:ℝ)/3) * T.angle_sum
  have hexp : (Circle.exp (-T.alpha) : ℂ) * (Real.sin T.alpha * Circle.exp (thetaPrime T.gamma)) =
      (Real.sin T.alpha : ℂ) * (Circle.exp (T.beta + 2 * T.gamma) : ℂ) := by
    rw [show (Circle.exp (-T.alpha) : ℂ) * (Real.sin T.alpha * Circle.exp (thetaPrime T.gamma))
        = (Real.sin T.alpha : ℂ) *
            ((Circle.exp (-T.alpha) : ℂ) * Circle.exp (thetaPrime T.gamma)) from by ring]
    rw [m3_exp_mul_exp, hangle]
  have hstep : complexMulVector o ((Circle.exp (-T.alpha) : ℂ) *
      (Real.sin T.alpha * Circle.exp (thetaPrime T.gamma))) T.bStar =
      Real.sin T.alpha • rotateVector o T.bStar (T.beta + 2 * T.gamma) := by
    rw [hexp, m7_complexMulVector_mul, m7_complexMulVector_ofReal]
    rfl
  rw [T.Z_sub_Y_delta, T.sin_star_difference, ← m7_complexMulVector_mul, hstep, smul_smul]
  congr 1
  ring

def m7_cyclic (T : OrientedTriangle E o) : OrientedTriangle E o where
  A := T.B
  B := T.C
  C := T.A
  noncollinear := by
    have h : ({T.B, T.C, T.A} : Set E) = {T.A, T.B, T.C} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    show ¬ Collinear ℝ ({T.B, T.C, T.A} : Set E)
    rw [h]; exact T.noncollinear
  positive := by
    show 0 < orientedArea o (T.C - T.B) (T.A - T.B)
    have hsign : orientedArea o T.a (-T.c) = orientedArea o T.a T.b := by
      have h := congrArg (fun x => (o.areaForm T.a) x) T.a_add_b_add_c
      simp only [map_add, map_zero] at h
      have haa : (o.areaForm T.a) T.a = 0 := Orientation.areaForm_apply_self o T.a
      show (o.areaForm T.a) (-T.c) = (o.areaForm T.a) T.b
      rw [map_neg]
      linarith
    have h1 : orientedArea o (T.C - T.B) (T.A - T.B) = orientedArea o T.a (-T.c) := by
      rw [show T.C - T.B = T.a from rfl,
        show T.A - T.B = -T.c from by simp [OrientedTriangle.c]]
    rw [h1, hsign]; exact T.orientedArea_a_b_pos

theorem m7_cyclic_alpha (T : OrientedTriangle E o) : (m7_cyclic T).alpha = T.beta := rfl

theorem m7_cyclic_beta (T : OrientedTriangle E o) : (m7_cyclic T).beta = T.gamma := rfl

theorem m7_cyclic_gamma (T : OrientedTriangle E o) : (m7_cyclic T).gamma = T.alpha := rfl

theorem m7_cyclic_aLength (T : OrientedTriangle E o) : (m7_cyclic T).aLength = T.bLength := rfl

theorem m7_cyclic_bLength (T : OrientedTriangle E o) : (m7_cyclic T).bLength = T.cLength := rfl

theorem m7_cyclic_cLength (T : OrientedTriangle E o) : (m7_cyclic T).cLength = T.aLength := rfl

theorem m7_cyclic_aStar (T : OrientedTriangle E o) : (m7_cyclic T).aStar = T.bStar := rfl

theorem m7_cyclic_bStar (T : OrientedTriangle E o) : (m7_cyclic T).bStar = T.cStar := rfl

theorem m7_cyclic_cStar (T : OrientedTriangle E o) : (m7_cyclic T).cStar = T.aStar := rfl

theorem m7_cyclic_X (T : OrientedTriangle E o) : (m7_cyclic T).X = T.Y := rfl

theorem m7_cyclic_Y (T : OrientedTriangle E o) : (m7_cyclic T).Y = T.Z := rfl

theorem m7_cyclic_Z (T : OrientedTriangle E o) : (m7_cyclic T).Z = T.X := rfl

theorem m7_cyclic_delta (T : OrientedTriangle E o) : (m7_cyclic T).delta = T.delta := by
  have h := T.law_of_sines
  rw [OrientedTriangle.delta, OrientedTriangle.delta, m7_cyclic_aLength, m7_cyclic_alpha]
  exact h.1.symm

/-- Equation (18a). -/
theorem X_sub_Z (T : OrientedTriangle E o) :
    T.X - T.Z = (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) •
      rotateVector o T.cStar (T.gamma + 2 * T.alpha) := by
  have h := Z_sub_Y (m7_cyclic T)
  rw [m7_cyclic_Z, m7_cyclic_Y, m7_cyclic_delta, m7_cyclic_alpha, m7_cyclic_beta,
    m7_cyclic_gamma, m7_cyclic_bStar] at h
  refine h.trans (Eq.symm ?_)
  congr 1
  ring

/-- Equation (18b). -/
theorem Y_sub_X (T : OrientedTriangle E o) :
    T.Y - T.X = (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) •
      rotateVector o T.aStar (T.alpha + 2 * T.beta) := by
  have hZ : (m7_cyclic (m7_cyclic T)).Z = T.Y := by rw [m7_cyclic_Z, m7_cyclic_X]
  have hY : (m7_cyclic (m7_cyclic T)).Y = T.X := by rw [m7_cyclic_Y, m7_cyclic_Z]
  have hα : (m7_cyclic (m7_cyclic T)).alpha = T.gamma := by
    rw [m7_cyclic_alpha, m7_cyclic_beta]
  have hβ : (m7_cyclic (m7_cyclic T)).beta = T.alpha := by
    rw [m7_cyclic_beta, m7_cyclic_gamma]
  have hγ : (m7_cyclic (m7_cyclic T)).gamma = T.beta := by
    rw [m7_cyclic_gamma, m7_cyclic_alpha]
  have hδ : (m7_cyclic (m7_cyclic T)).delta = T.delta := by
    rw [m7_cyclic_delta, m7_cyclic_delta]
  have hb : (m7_cyclic (m7_cyclic T)).bStar = T.aStar := by
    rw [m7_cyclic_bStar, m7_cyclic_cStar]
  have h := Z_sub_Y (m7_cyclic (m7_cyclic T))
  rw [hZ, hY, hδ, hα, hβ, hγ, hb] at h
  refine h.trans (Eq.symm ?_)
  congr 1
  ring

/-- The strengthened form of Morley's theorem obtained in `⋄14`. -/
theorem morley_side_lengths (T : OrientedTriangle E o) :
    dist T.X T.Y = 4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma ∧
    dist T.Y T.Z = 4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma ∧
    dist T.Z T.X = 4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma := by
  have hpos : 0 < 4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma := by
    have h1 := m7_delta_pos T; have h2 := m7_sin_alpha_pos T
    have h3 := m7_sin_beta_pos T; have h4 := m7_sin_gamma_pos T
    positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [dist_eq_norm, ← norm_neg, neg_sub, Y_sub_X, norm_smul, rotateVector_norm,
      m7_norm_aStar, mul_one, Real.norm_eq_abs, abs_of_pos hpos]
  · rw [dist_eq_norm, ← norm_neg, neg_sub, Z_sub_Y, norm_smul, rotateVector_norm,
      m7_norm_bStar, mul_one, Real.norm_eq_abs, abs_of_pos hpos]
  · rw [dist_eq_norm, ← norm_neg, neg_sub, X_sub_Z, norm_smul, rotateVector_norm,
      m7_norm_cStar, mul_one, Real.norm_eq_abs, abs_of_pos hpos]

/-- **Morley's Trisector Theorem.**  This proof uses only the strengthened
statement `morley_side_lengths` from this file, not the earlier theorem `morley`. -/
theorem morley_trisector (T : OrientedTriangle E o) : Equilateral T.X T.Y T.Z := by
  change dist T.X T.Y = dist T.Y T.Z ∧ dist T.Y T.Z = dist T.Z T.X
  rcases T.morley_side_lengths with ⟨hXY, hYZ, hZX⟩
  exact ⟨hXY.trans hYZ.symm, hYZ.trans hZX.symm⟩

/-- **Theorem 1 (Frank Morley, 1899).** -/
theorem morley (T : OrientedTriangle E o) : Equilateral T.X T.Y T.Z := T.morley_trisector
theorem m4_ncard_union_of_disjoint {α : Type*} {s t : Set α} (hs : s.Finite) (ht : t.Finite)
    (h : Disjoint s t) : (s ∪ t).ncard = s.ncard + t.ncard := by
  classical
  have hdisj : Disjoint hs.toFinset ht.toFinset := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    rw [Set.Finite.mem_toFinset] at ha ha'
    exact Set.disjoint_left.mp h ha ha'
  have hst : (s ∪ t).Finite := hs.union ht
  rw [Set.ncard_eq_toFinset_card _ hst, Set.ncard_eq_toFinset_card _ hs,
    Set.ncard_eq_toFinset_card _ ht, Set.Finite.toFinset_union hs ht,
    Finset.card_union_of_disjoint hdisj]


/-- `ncard` of the part of a finite set selected by a decidable predicate. -/
theorem m4_ncard_sep {α : Type*} {s : Set α} (p : α → Prop) [DecidablePred p] (hs : s.Finite) :
    {x ∈ s | p x}.ncard = (hs.toFinset.filter p).card := by
  classical
  have hsub : {x ∈ s | p x} ⊆ s := fun x hx => hx.1
  have hfin' : {x ∈ s | p x}.Finite := hs.subset hsub
  have hEq : hfin'.toFinset = hs.toFinset.filter p := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_ofPred_eq]
  rw [Set.ncard_eq_toFinset_card _ hfin', hEq]

/-- Two distinct common points force two lines to have the same point set. -/
theorem m4_mem_iff_of_two_mem {ℓ ℓ' : Line E} {X Y : E} (hXY : X ≠ Y)
    (h1 : ℓ.mem X) (h2 : ℓ.mem Y) (h3 : ℓ'.mem X) (h4 : ℓ'.mem Y) :
    ∀ Z : E, ℓ.mem Z ↔ ℓ'.mem Z := by
  have key : ∀ (m m' : Line E), m.mem X → m.mem Y → m'.mem X → m'.mem Y →
      ∀ Z : E, m.mem Z → m'.mem Z := by
    intro m m' hmX hmY hm'X hm'Y
    have hp : Parallel m.direction m'.direction :=
      Line.parallel_of_mem_sub' hXY hmX hmY hm'X hm'Y
    obtain ⟨t, ht⟩ := hm'X
    have hXb : X - m'.base = t • m'.direction := by rw [ht]; abel
    obtain ⟨s, hs⟩ := hmX
    have hXm : X - m.base = s • m.direction := by rw [hs]; abel
    intro Z hZ
    obtain ⟨r, hr⟩ := (Line.mem_iff_parallel m Z).mp hZ
    obtain ⟨q, hq⟩ := hp
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hq
      exact m'.direction_ne_zero hq
    have hq' : m.direction = q⁻¹ • m'.direction := by
      rw [hq, smul_smul, inv_mul_cancel₀ hq0, one_smul]
    refine (Line.mem_iff_parallel m' Z).mpr ⟨(r - s) * q⁻¹ + t, ?_⟩
    rw [show Z - m'.base = ((Z - m.base) - (X - m.base)) + (X - m'.base) from by abel,
      hr, hXm, hXb, ← sub_smul, hq', smul_smul, ← add_smul]
  exact fun Z => ⟨key ℓ ℓ' h1 h2 h3 h4 Z, key ℓ' ℓ h3 h4 h1 h2 Z⟩

/-- The finite set of constellation labels whose points lie on a line. -/
noncomputable def m4_ptsOn (T : OrientedTriangle E o) (ℓ : Line E) : Finset ConstellationIndex := by
  classical exact Finset.univ.filter (fun q => ℓ.mem (T.constellationPoint q))

theorem m4_ptsOn_card (T : OrientedTriangle E o) (ℓ : Line E) :
    (m4_ptsOn T ℓ).card = {q : ConstellationIndex | ℓ.mem (T.constellationPoint q)}.ncard := by
  classical
  rw [m4_ptsOn]
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- Every guide line carries exactly six constellation points, as a `Finset` statement. -/
theorem m4_ptsOn_card_of_mem (T : OrientedTriangle E o) {ℓ : Line E}
    (hℓ : ℓ ∈ T.guideLines) : (m4_ptsOn T ℓ).card = 6 := by
  rw [m4_ptsOn_card]
  exact guideLines_six_points T hℓ

/-- The finite set of guide lines through a constellation point. -/
noncomputable def m4_linesOn (T : OrientedTriangle E o) (hfin : T.guideLines.Finite)
    (q : ConstellationIndex) : Finset (Line E) := by
  classical exact hfin.toFinset.filter (fun ℓ => ℓ.mem (T.constellationPoint q))

/-- **The set of guide lines is finite.** -/
theorem m4_guideLines_finite (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.guideLines.Finite := by
  classical
  have hinj : Function.Injective (fun ℓ : {ℓ : Line E // ℓ ∈ T.guideLines} =>
      m4_ptsOn T (ℓ : Line E)) := by
    rintro ⟨ℓ, hℓ⟩ ⟨ℓ', hℓ'⟩ heq
    simp only [Subtype.mk.injEq]
    have hmemq : ∀ q : ConstellationIndex,
        ℓ.mem (T.constellationPoint q) ↔ ℓ'.mem (T.constellationPoint q) := by
      intro q
      have hq := Finset.ext_iff.mp heq q
      simp only [m4_ptsOn, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      exact hq
    have hcard : (m4_ptsOn T ℓ).card = 6 := m4_ptsOn_card_of_mem T hℓ
    obtain ⟨q1, hq1, q2, hq2, hne⟩ := Finset.one_lt_card.mp (by rw [hcard]; norm_num)
    have hm1 : ℓ.mem (T.constellationPoint q1) := by
      have := (Finset.mem_filter.mp hq1).2
      simpa only [m4_ptsOn, Finset.mem_filter, Finset.mem_univ, true_and] using this
    have hm2 : ℓ.mem (T.constellationPoint q2) := by
      have := (Finset.mem_filter.mp hq2).2
      simpa only [m4_ptsOn, Finset.mem_filter, Finset.mem_univ, true_and] using this
    have hpne : T.constellationPoint q1 ≠ T.constellationPoint q2 := fun hc => hne (h hc)
    refine isCanonical_eq_of_mem_iff hℓ.2 hℓ'.2 ?_
    exact m4_mem_iff_of_two_mem hpne hm1 hm2 ((hmemq q1).mp hm1) ((hmemq q2).mp hm2)
  have hfin : Finite {ℓ : Line E // ℓ ∈ T.guideLines} := Finite.of_injective _ hinj
  exact Set.finite_coe_iff.mpr hfin

/-- **Guide-line count.**  If every constellation point lies on exactly two guide lines,
then there are exactly nine guide lines (double counting of the incidence relation). -/
theorem m4_guideLines_card_of_two_per_point (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint)
    (h2 : ∀ q : ConstellationIndex,
      {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard = 2) :
    T.guideLines.ncard = 9 := by
  classical
  have hfin : T.guideLines.Finite := m4_guideLines_finite T h
  have hcard27 : Fintype.card ConstellationIndex = 27 := by decide
  have hpt : ∀ q : ConstellationIndex,
      (hfin.toFinset.filter (fun ℓ => ℓ.mem (T.constellationPoint q))).card = 2 := by
    intro q
    rw [← h2 q, m4_ncard_sep (fun ℓ => ℓ.mem (T.constellationPoint q)) hfin]
  have hline : ∀ ℓ ∈ hfin.toFinset, (m4_ptsOn T ℓ).card = 6 := by
    intro ℓ hℓ
    exact m4_ptsOn_card_of_mem T (hfin.mem_toFinset.mp hℓ)
  have hL : Finset.sum hfin.toFinset (fun ℓ => (m4_ptsOn T ℓ).card)
      = hfin.toFinset.card * 6 := by
    rw [Finset.sum_congr rfl hline, Finset.sum_const, smul_eq_mul]
  have hR : Finset.sum Finset.univ (fun q : ConstellationIndex =>
      (hfin.toFinset.filter (fun ℓ => ℓ.mem (T.constellationPoint q))).card) = 27 * 2 := by
    rw [Finset.sum_congr rfl (fun q _ => hpt q), Finset.sum_const, smul_eq_mul,
      Finset.card_univ, hcard27]
  have hcomm : Finset.sum hfin.toFinset (fun ℓ => (m4_ptsOn T ℓ).card)
      = Finset.sum Finset.univ (fun q : ConstellationIndex =>
        (hfin.toFinset.filter (fun ℓ => ℓ.mem (T.constellationPoint q))).card) := by
    simp only [m4_ptsOn, Finset.card_filter]
    exact Finset.sum_comm
  rw [hL, hR] at hcomm
  rw [Set.ncard_eq_toFinset_card _ hfin]
  omega

/-! ### Reading off the guide-line count from the three direction classes -/

/-- Two vectors parallel to the same nonzero vector are parallel. -/
theorem m4_parallel_of_parallel_of_parallel {u v w : E} (hw : w ≠ 0)
    (h1 : Parallel u w) (h2 : Parallel v w) : Parallel u v := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hb
    exact hw hb
  refine ⟨b⁻¹ * a, ?_⟩
  calc v = b⁻¹ • (b • v) := by rw [smul_smul, inv_mul_cancel₀ hb0, one_smul]
    _ = b⁻¹ • (a • u) := by rw [← hb, ha]
    _ = (b⁻¹ * a) • u := by rw [smul_smul]

/-- If `u` and `v` have the same positive length `ρ` and so does `u + v`, then `u` and `v`
are not parallel. -/
theorem m4_no_parallel_of_sum {u v : E} {ρ : ℝ} (hρ : 0 < ρ) (hu : ‖u‖ = ρ) (hv : ‖v‖ = ρ)
    (huv : ‖u + v‖ = ρ) : ¬ Parallel u v := by
  intro hcon
  obtain ⟨r, hr⟩ := hcon
  have h1 : |r| = 1 := by
    have h : ‖v‖ = |r| * ‖u‖ := by rw [hr, norm_smul, Real.norm_eq_abs]
    rw [hu, hv] at h
    have h' : |r| * ρ = 1 * ρ := by rw [one_mul]; exact h.symm
    exact mul_right_cancel₀ (ne_of_gt hρ) h'
  have h2 : |1 + r| = 1 := by
    have hsum : u + v = (1 + r) • u := by rw [hr, add_smul, one_smul]
    have h : ‖u + v‖ = |1 + r| * ‖u‖ := by rw [hsum, norm_smul, Real.norm_eq_abs]
    rw [hu, huv] at h
    have h' : |1 + r| * ρ = 1 * ρ := by rw [one_mul]; exact h.symm
    exact mul_right_cancel₀ (ne_of_gt hρ) h'
  have hr2 : r ^ 2 = 1 := by nlinarith [abs_nonneg r, sq_abs r]
  rcases sq_eq_one_iff.mp hr2 with h | h
  · rw [h] at h2
    norm_num at h2
  · rw [h] at h2
    norm_num at h2

/-- The three Morley side vectors are pairwise non-parallel (they form a nondegenerate
equilateral triangle). -/
theorem m4_not_parallel_morley (T : OrientedTriangle E o) :
    ¬ Parallel (T.Y - T.X) (T.Z - T.Y) ∧
      ¬ Parallel (T.Z - T.Y) (T.X - T.Z) ∧
        ¬ Parallel (T.X - T.Z) (T.Y - T.X) := by
  obtain ⟨hXY, hYZ, hZX⟩ := T.morley_side_lengths
  set ρ := 4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]
    have h1 := m7_delta_pos T
    have h2 := m7_sin_alpha_pos T
    have h3 := m7_sin_beta_pos T
    have h4 := m7_sin_gamma_pos T
    positivity
  have hu : ‖T.Y - T.X‖ = ρ := by rw [← hXY, dist_eq_norm]; exact norm_sub_rev _ _
  have hv : ‖T.Z - T.Y‖ = ρ := by rw [← hYZ, dist_eq_norm]; exact norm_sub_rev _ _
  have hw : ‖T.X - T.Z‖ = ρ := by rw [← hZX, dist_eq_norm]; exact norm_sub_rev _ _
  refine ⟨m4_no_parallel_of_sum hρ hu hv ?_, m4_no_parallel_of_sum hρ hv hw ?_,
    m4_no_parallel_of_sum hρ hw hu ?_⟩
  · rw [show T.Y - T.X + (T.Z - T.Y) = T.Z - T.X from by abel, ← hZX, dist_eq_norm,
      norm_sub_rev]
  · rw [show T.Z - T.Y + (T.X - T.Z) = T.X - T.Y from by abel, ← hXY, dist_eq_norm]
  · rw [show T.X - T.Z + (T.Y - T.X) = T.Y - T.Z from by abel, ← hYZ, dist_eq_norm,
      norm_sub_rev]

/-- **Guide-line count from the three direction classes.**  If each of the three Morley side
directions is carried by exactly three guide lines, then there are exactly nine guide
lines. -/
theorem m4_guideLines_card_of_direction_card (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint)
    (h3 : ∀ v : E, v = T.Y - T.X ∨ v = T.Z - T.Y ∨ v = T.X - T.Z →
      {ℓ ∈ T.guideLines | Parallel v ℓ.direction}.ncard = 3) :
    T.guideLines.ncard = 9 := by
  classical
  have hfin : T.guideLines.Finite := m4_guideLines_finite T h
  have hsub1 : {ℓ ∈ T.guideLines | Parallel (T.Y - T.X) ℓ.direction} ⊆ T.guideLines :=
    fun ℓ hℓ => hℓ.1
  have hsub2 : {ℓ ∈ T.guideLines | Parallel (T.Z - T.Y) ℓ.direction} ⊆ T.guideLines :=
    fun ℓ hℓ => hℓ.1
  have hsub3 : {ℓ ∈ T.guideLines | Parallel (T.X - T.Z) ℓ.direction} ⊆ T.guideLines :=
    fun ℓ hℓ => hℓ.1
  have hf1 : {ℓ ∈ T.guideLines | Parallel (T.Y - T.X) ℓ.direction}.Finite := hfin.subset hsub1
  have hf2 : {ℓ ∈ T.guideLines | Parallel (T.Z - T.Y) ℓ.direction}.Finite := hfin.subset hsub2
  have hf3 : {ℓ ∈ T.guideLines | Parallel (T.X - T.Z) ℓ.direction}.Finite := hfin.subset hsub3
  obtain ⟨hn1, hn2, hn3⟩ := m4_not_parallel_morley T
  have hc1 : {ℓ ∈ T.guideLines | Parallel (T.Y - T.X) ℓ.direction}.ncard = 3 :=
    h3 _ (Or.inl rfl)
  have hc2 : {ℓ ∈ T.guideLines | Parallel (T.Z - T.Y) ℓ.direction}.ncard = 3 :=
    h3 _ (Or.inr (Or.inl rfl))
  have hc3 : {ℓ ∈ T.guideLines | Parallel (T.X - T.Z) ℓ.direction}.ncard = 3 :=
    h3 _ (Or.inr (Or.inr rfl))
  have hcover : T.guideLines =
      ({ℓ ∈ T.guideLines | Parallel (T.Y - T.X) ℓ.direction} ∪
        {ℓ ∈ T.guideLines | Parallel (T.Z - T.Y) ℓ.direction}) ∪
        {ℓ ∈ T.guideLines | Parallel (T.X - T.Z) ℓ.direction} := by
    ext ℓ
    simp only [guideLines, IsGuideLine, parallelToMorleySide, Set.mem_ofPred_eq, Set.mem_union]
    tauto
  have hd12 : Disjoint {ℓ ∈ T.guideLines | Parallel (T.Y - T.X) ℓ.direction}
      {ℓ ∈ T.guideLines | Parallel (T.Z - T.Y) ℓ.direction} := by
    rw [Set.disjoint_left]
    rintro ℓ ⟨-, hp1⟩ ⟨-, hp2⟩
    exact hn1 (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hp1 hp2)
  have hd23 : Disjoint {ℓ ∈ T.guideLines | Parallel (T.Z - T.Y) ℓ.direction}
      {ℓ ∈ T.guideLines | Parallel (T.X - T.Z) ℓ.direction} := by
    rw [Set.disjoint_left]
    rintro ℓ ⟨-, hp1⟩ ⟨-, hp2⟩
    exact hn2 (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hp1 hp2)
  have hd13 : Disjoint {ℓ ∈ T.guideLines | Parallel (T.Y - T.X) ℓ.direction}
      {ℓ ∈ T.guideLines | Parallel (T.X - T.Z) ℓ.direction} := by
    rw [Set.disjoint_left]
    rintro ℓ ⟨-, hp1⟩ ⟨-, hp2⟩
    exact hn3 (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hp2 hp1)
  have hd123 : Disjoint ({ℓ ∈ T.guideLines | Parallel (T.Y - T.X) ℓ.direction} ∪
      {ℓ ∈ T.guideLines | Parallel (T.Z - T.Y) ℓ.direction})
      {ℓ ∈ T.guideLines | Parallel (T.X - T.Z) ℓ.direction} := by
    rw [Set.disjoint_left]
    rintro ℓ (hℓ | hℓ) hℓ'
    · exact Set.disjoint_left.mp hd13 hℓ hℓ'
    · exact Set.disjoint_left.mp hd23 hℓ hℓ'
  rw [hcover, m4_ncard_union_of_disjoint (hf1.union hf2) hf3 hd123,
    m4_ncard_union_of_disjoint hf1 hf2 hd12, hc1, hc2, hc3]

/-! ### Structural facts about guide lines -/

/-- Two guide lines with parallel directions through a common point coincide. -/
theorem m4_guideLine_eq_of_parallel_of_mem (T : OrientedTriangle E o) {ℓ ℓ' : Line E}
    (hℓ : ℓ ∈ T.guideLines) (hℓ' : ℓ' ∈ T.guideLines) (hpar : Parallel ℓ.direction ℓ'.direction)
    {X : E} (hX : ℓ.mem X) (hX' : ℓ'.mem X) : ℓ = ℓ' := by
  obtain ⟨r, hr⟩ := hpar
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hr
    exact ℓ'.direction_ne_zero hr
  have hdir : ℓ.direction = r⁻¹ • ℓ'.direction := by
    rw [hr, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  -- `X + ℓ.direction` lies on both lines
  have hY1 : ℓ.mem (X + ℓ.direction) := by
    obtain ⟨t, ht⟩ := hX
    refine ⟨t + 1, ?_⟩
    rw [ht, add_smul, one_smul]
    abel
  have hY2 : ℓ'.mem (X + ℓ.direction) := by
    obtain ⟨s, hs⟩ := hX'
    refine ⟨s + r⁻¹, ?_⟩
    rw [hs, hdir, add_smul]
    abel
  have hXY : X ≠ X + ℓ.direction := by
    intro h
    have h0 : ℓ.direction = 0 := by
      have := congrArg (fun z => z - X) h
      simpa using this.symm
    exact ℓ.direction_ne_zero h0
  refine isCanonical_eq_of_mem_iff hℓ.2 hℓ'.2 ?_
  exact m4_mem_iff_of_two_mem hXY hX hY1 hX' hY2

/-- No line carrying three constellation points of one colour is a guide line: a guide line
carries exactly two points of each colour. -/
theorem m4_not_isGuideLine_of_three_same_color (T : OrientedTriangle E o) {ℓ : Line E}
    {c : TrisectorColor} {q1 q2 q3 : ConstellationIndex}
    (hc1 : q1.color = c) (hc2 : q2.color = c) (hc3 : q3.color = c)
    (hm1 : ℓ.mem (T.constellationPoint q1)) (hm2 : ℓ.mem (T.constellationPoint q2))
    (hm3 : ℓ.mem (T.constellationPoint q3))
    (d12 : q1 ≠ q2) (d13 : q1 ≠ q3) (d23 : q2 ≠ q3) : ¬ T.IsGuideLine ℓ := by
  intro hgl
  have h2 := hgl.2.2 c
  have hsub : ({q1, q2, q3} : Set ConstellationIndex) ⊆
      {q : ConstellationIndex | q.color = c ∧ ℓ.mem (T.constellationPoint q)} := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨hc1, hm1⟩
    · exact ⟨hc2, hm2⟩
    · exact ⟨hc3, hm3⟩
  have h3 : ({q1, q2, q3} : Set ConstellationIndex).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [d12, d13]),
      Set.ncard_insert_of_notMem (by simp [d23]), Set.ncard_singleton]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-- `0 ≠ 1` in `ZMod 3`. -/
theorem m4_zmod3_ne_01 : (0 : TrisectorLabel) ≠ 1 := by decide
/-- `0 ≠ 2` in `ZMod 3`. -/
theorem m4_zmod3_ne_02 : (0 : TrisectorLabel) ≠ 2 := by decide
/-- `1 ≠ 2` in `ZMod 3`. -/
theorem m4_zmod3_ne_12 : (1 : TrisectorLabel) ≠ 2 := by decide

/-- The red trisectors are not guide lines (three red constellation points on each). -/
theorem m4_redB_not_isGuideLine (T : OrientedTriangle E o) (i : TrisectorLabel) :
    ¬ T.IsGuideLine (T.redB i) := by
  refine m4_not_isGuideLine_of_three_same_color (T := T) (ℓ := T.redB i) (c := .red)
    (q1 := ⟨.red, i, 0⟩) (q2 := ⟨.red, i, 1⟩) (q3 := ⟨.red, i, 2⟩)
    rfl rfl rfl (constellationPoint_mem_redB (T := T) i 0)
    (constellationPoint_mem_redB (T := T) i 1) (constellationPoint_mem_redB (T := T) i 2)
    ?_ ?_ ?_
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.second h) m4_zmod3_ne_01
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.second h) m4_zmod3_ne_02
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.second h) m4_zmod3_ne_12

/-- The red trisectors at `C` are not guide lines. -/
theorem m4_redC_not_isGuideLine (T : OrientedTriangle E o) (j : TrisectorLabel) :
    ¬ T.IsGuideLine (T.redC j) := by
  refine m4_not_isGuideLine_of_three_same_color (T := T) (ℓ := T.redC j) (c := .red)
    (q1 := ⟨.red, 0, j⟩) (q2 := ⟨.red, 1, j⟩) (q3 := ⟨.red, 2, j⟩)
    rfl rfl rfl (m4_cp_red_mem_redC T 0 j) (m4_cp_red_mem_redC T 1 j)
    (m4_cp_red_mem_redC T 2 j) ?_ ?_ ?_
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.first h) m4_zmod3_ne_01
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.first h) m4_zmod3_ne_02
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.first h) m4_zmod3_ne_12

/-- The green trisectors at `C` are not guide lines. -/
theorem m4_greenC_not_isGuideLine (T : OrientedTriangle E o) (i : TrisectorLabel) :
    ¬ T.IsGuideLine (T.greenC i) := by
  refine m4_not_isGuideLine_of_three_same_color (T := T) (ℓ := T.greenC i) (c := .green)
    (q1 := ⟨.green, i, 0⟩) (q2 := ⟨.green, i, 1⟩) (q3 := ⟨.green, i, 2⟩)
    rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [constellationPoint] using m6_constellation_mem_greenC T i 0
  · simpa only [constellationPoint] using m6_constellation_mem_greenC T i 1
  · simpa only [constellationPoint] using m6_constellation_mem_greenC T i 2
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.second h) m4_zmod3_ne_01
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.second h) m4_zmod3_ne_02
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.second h) m4_zmod3_ne_12

/-- The green trisectors at `A` are not guide lines. -/
theorem m4_greenA_not_isGuideLine (T : OrientedTriangle E o) (j : TrisectorLabel) :
    ¬ T.IsGuideLine (T.greenA j) := by
  refine m4_not_isGuideLine_of_three_same_color (T := T) (ℓ := T.greenA j) (c := .green)
    (q1 := ⟨.green, 0, j⟩) (q2 := ⟨.green, 1, j⟩) (q3 := ⟨.green, 2, j⟩)
    rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [constellationPoint] using m6_constellation_mem_greenA T 0 j
  · simpa only [constellationPoint] using m6_constellation_mem_greenA T 1 j
  · simpa only [constellationPoint] using m6_constellation_mem_greenA T 2 j
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.first h) m4_zmod3_ne_01
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.first h) m4_zmod3_ne_02
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.first h) m4_zmod3_ne_12

/-- The blue trisectors at `A` are not guide lines. -/
theorem m4_blueA_not_isGuideLine (T : OrientedTriangle E o) (i : TrisectorLabel) :
    ¬ T.IsGuideLine (T.blueA i) := by
  refine m4_not_isGuideLine_of_three_same_color (T := T) (ℓ := T.blueA i) (c := .blue)
    (q1 := ⟨.blue, i, 0⟩) (q2 := ⟨.blue, i, 1⟩) (q3 := ⟨.blue, i, 2⟩)
    rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [constellationPoint] using m6_constellation_mem_blueA T i 0
  · simpa only [constellationPoint] using m6_constellation_mem_blueA T i 1
  · simpa only [constellationPoint] using m6_constellation_mem_blueA T i 2
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.second h) m4_zmod3_ne_01
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.second h) m4_zmod3_ne_02
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.second h) m4_zmod3_ne_12

/-- The blue trisectors at `B` are not guide lines. -/
theorem m4_blueB_not_isGuideLine (T : OrientedTriangle E o) (j : TrisectorLabel) :
    ¬ T.IsGuideLine (T.blueB j) := by
  refine m4_not_isGuideLine_of_three_same_color (T := T) (ℓ := T.blueB j) (c := .blue)
    (q1 := ⟨.blue, 0, j⟩) (q2 := ⟨.blue, 1, j⟩) (q3 := ⟨.blue, 2, j⟩)
    rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [constellationPoint] using m6_constellation_mem_blueB T 0 j
  · simpa only [constellationPoint] using m6_constellation_mem_blueB T 1 j
  · simpa only [constellationPoint] using m6_constellation_mem_blueB T 2 j
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.first h) m4_zmod3_ne_01
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.first h) m4_zmod3_ne_02
  · rintro h
    exact absurd (by simpa using congrArg ConstellationIndex.first h) m4_zmod3_ne_12


/-- The double count behind the guide-line number: summing per line or per point gives the
same total. -/
theorem m4_double_count (T : OrientedTriangle E o) (hfin : T.guideLines.Finite) :
    Finset.sum hfin.toFinset (fun ℓ => (m4_ptsOn T ℓ).card)
      = Finset.sum Finset.univ (fun q : ConstellationIndex => (m4_linesOn T hfin q).card) := by
  classical
  simp only [m4_ptsOn, m4_linesOn, Finset.card_filter]
  exact Finset.sum_comm

/-- Upper-bound half of the guide-line count: if no constellation point lies on more than
two guide lines, then there are at most nine guide lines. -/
theorem m4_guideLines_ncard_le_of_point_le (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint)
    (hle : ∀ q : ConstellationIndex,
      {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard ≤ 2) :
    T.guideLines.ncard ≤ 9 := by
  classical
  have hfin : T.guideLines.Finite := m4_guideLines_finite T h
  have hcard27 : Fintype.card ConstellationIndex = 27 := by decide
  have hptle : ∀ q : ConstellationIndex, (m4_linesOn T hfin q).card ≤ 2 := by
    intro q
    rw [m4_linesOn, ← m4_ncard_sep (fun ℓ => ℓ.mem (T.constellationPoint q)) hfin]
    exact hle q
  have hline : ∀ ℓ ∈ hfin.toFinset, (m4_ptsOn T ℓ).card = 6 := by
    intro ℓ hℓ
    exact m4_ptsOn_card_of_mem T (hfin.mem_toFinset.mp hℓ)
  have hbound : Finset.sum Finset.univ (fun q : ConstellationIndex => (m4_linesOn T hfin q).card)
      ≤ 27 * 2 := by
    have h1 : Finset.sum Finset.univ (fun q : ConstellationIndex => (m4_linesOn T hfin q).card)
        ≤ Finset.sum Finset.univ (fun _ => 2) := Finset.sum_le_sum (fun q _ => hptle q)
    have h2 : Finset.sum Finset.univ (fun _ => 2 : ConstellationIndex → ℕ) = 27 * 2 := by
      rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, hcard27]
    omega
  have hL : Finset.sum hfin.toFinset (fun ℓ => (m4_ptsOn T ℓ).card) = hfin.toFinset.card * 6 := by
    rw [Finset.sum_congr rfl hline, Finset.sum_const, smul_eq_mul]
  have hsp : Finset.sum hfin.toFinset (fun ℓ => (m4_ptsOn T ℓ).card) ≤ 27 * 2 := by
    rw [m4_double_count T hfin]
    exact hbound
  have h1 : hfin.toFinset.card * 6 ≤ 27 * 2 := by
    rw [← hL]
    exact hsp
  have h2 : hfin.toFinset.card ≤ 9 := by omega
  rwa [Set.ncard_eq_toFinset_card _ hfin]


/-- Conversely, nine guide lines together with the point bound `≤ 2` force every
constellation point to lie on exactly two guide lines. -/
theorem m4_two_per_point_of_card_of_le (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (hcard : T.guideLines.ncard = 9)
    (hle : ∀ q : ConstellationIndex,
      {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard ≤ 2) :
    ∀ q : ConstellationIndex,
      {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard = 2 := by
  classical
  have hfin : T.guideLines.Finite := m4_guideLines_finite T h
  have hcard27 : Fintype.card ConstellationIndex = 27 := by decide
  have hptle : ∀ q : ConstellationIndex,
      (hfin.toFinset.filter (fun ℓ => ℓ.mem (T.constellationPoint q))).card ≤ 2 := by
    intro q
    rw [← m4_ncard_sep (fun ℓ => ℓ.mem (T.constellationPoint q)) hfin]
    exact hle q
  have hline : ∀ ℓ ∈ hfin.toFinset, (m4_ptsOn T ℓ).card = 6 := by
    intro ℓ hℓ
    exact m4_ptsOn_card_of_mem T (hfin.mem_toFinset.mp hℓ)
  have hL : Finset.sum hfin.toFinset (fun ℓ => (m4_ptsOn T ℓ).card) = 9 * 6 := by
    rw [Finset.sum_congr rfl hline, Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin,
      hcard]
  have hsum : Finset.sum Finset.univ (fun q : ConstellationIndex => (m4_linesOn T hfin q).card)
      = 27 * 2 := by
    rw [← m4_double_count T hfin, hL]
  intro q
  set g : ConstellationIndex → ℕ := fun q => (m4_linesOn T hfin q).card with hg
  have hptle' : ∀ x : ConstellationIndex, g x ≤ 2 := fun x => hptle x
  have hsumg : Finset.sum Finset.univ g = 27 * 2 := hsum
  have hsplit : Finset.sum Finset.univ g = g q + Finset.sum (Finset.univ.erase q) g := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q)]
  have hrest2 : Finset.sum (Finset.univ.erase q) g ≤ 52 := by
    have h1 : Finset.sum (Finset.univ.erase q) g
        ≤ Finset.sum (Finset.univ.erase q) (fun _ => 2) :=
      Finset.sum_le_sum (fun x _ => hptle' x)
    have h2 : Finset.sum (Finset.univ.erase q) (fun _ => 2) = 52 := by
      rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ q),
        Finset.card_univ, hcard27]
    omega
  have hq2 : g q = 2 := by
    have h1 := hptle' q
    omega
  have hconv : {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard = g q := by
    rw [m4_ncard_sep (fun ℓ => ℓ.mem (T.constellationPoint q)) hfin, hg]
    simp only [m4_linesOn]
  rw [hconv, hq2]

theorem m3_pos_red (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    T.constellationPoint ⟨.red, i, j⟩ =
      T.B + (Real.sin (T.gamma - labelAngle j / 2) /
        Real.sin (T.beta + T.gamma - (labelAngle i + labelAngle j) / 2)) •
          rotateVector o T.a (T.beta - labelAngle i / 2) := by
  have h := m6_rfp_Q_shift (o := o) T.C T.B T.gamma T.beta (labelAngle i) (labelAngle j)
    (m6_sin_shift_sub_ne_zero T.m6_beta_add_gamma_bounds_lt.1 T.m6_beta_add_gamma_bounds_lt.2 i j)
  show rotationFixedPoint o T.C T.B (2 * T.gamma - labelAngle j) (2 * T.beta - labelAngle i) = _
  rw [h, show T.B - T.C = -T.a from by rw [OrientedTriangle.a]; abel,
    m6_rotateVector_neg, smul_neg, sub_neg_eq_add]

theorem m3_pos_green (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    T.constellationPoint ⟨.green, i, j⟩ =
      T.C + (Real.sin (T.alpha - labelAngle j / 2) /
        Real.sin (T.gamma + T.alpha - (labelAngle i + labelAngle j) / 2)) •
          rotateVector o T.b (T.gamma - labelAngle i / 2) := by
  have h := m6_rfp_Q_shift (o := o) T.A T.C T.alpha T.gamma (labelAngle i) (labelAngle j)
    (m6_sin_shift_sub_ne_zero T.m6_gamma_add_alpha_bounds_lt.1 T.m6_gamma_add_alpha_bounds_lt.2 i j)
  show rotationFixedPoint o T.A T.C (2 * T.alpha - labelAngle j) (2 * T.gamma - labelAngle i) = _
  rw [h, show T.C - T.A = -T.b from by rw [OrientedTriangle.b]; abel,
    m6_rotateVector_neg, smul_neg, sub_neg_eq_add]

theorem m3_pos_blue (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    T.constellationPoint ⟨.blue, i, j⟩ =
      T.A + (Real.sin (T.beta - labelAngle j / 2) /
        Real.sin (T.alpha + T.beta - (labelAngle i + labelAngle j) / 2)) •
          rotateVector o T.c (T.alpha - labelAngle i / 2) := by
  have h := m6_rfp_Q_shift (o := o) T.B T.A T.beta T.alpha (labelAngle i) (labelAngle j)
    (m6_sin_shift_sub_ne_zero T.m6_alpha_add_beta_bounds_lt.1 T.m6_alpha_add_beta_bounds_lt.2 i j)
  show rotationFixedPoint o T.B T.A (2 * T.beta - labelAngle j) (2 * T.alpha - labelAngle i) = _
  rw [h, show T.A - T.B = -T.c from by rw [OrientedTriangle.c]; abel,
    m6_rotateVector_neg, smul_neg, sub_neg_eq_add]

/-! ### Exact trig values and power eliminations used by the arithmetic engine -/

theorem m3_sin_pi_div_six : Real.sin (Real.pi/6) = 1/2 := by
  rw [show Real.pi/6 = Real.pi/2 - Real.pi/3 by ring, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_three]
theorem m3_cos_pi_div_six : Real.cos (Real.pi/6) = √3/2 := by
  rw [show Real.pi/6 = Real.pi/2 - Real.pi/3 by ring, Real.cos_pi_div_two_sub,
    Real.sin_pi_div_three]
theorem m3_sin_two_pi_div_three : Real.sin (2*Real.pi/3) = √3/2 := by
  rw [show 2*Real.pi/3 = Real.pi - Real.pi/3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
theorem m3_cos_two_pi_div_three : Real.cos (2*Real.pi/3) = -(1/2) := by
  rw [show 2*Real.pi/3 = Real.pi - Real.pi/3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
theorem m3_sin_four_pi_div_three : Real.sin (4*Real.pi/3) = -(√3/2) := by
  rw [show 4*Real.pi/3 = Real.pi + Real.pi/3 by ring, Real.sin_add, Real.sin_pi, Real.cos_pi,
    Real.sin_pi_div_three, Real.cos_pi_div_three]
  ring
theorem m3_cos_four_pi_div_three : Real.cos (4*Real.pi/3) = -(1/2) := by
  rw [show 4*Real.pi/3 = Real.pi + Real.pi/3 by ring, Real.cos_add, Real.sin_pi, Real.cos_pi,
    Real.sin_pi_div_three, Real.cos_pi_div_three]
  ring

theorem m3_cos_sq_elim (x : ℝ) : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
  linarith [Real.sin_sq_add_cos_sq x]
theorem m3_cos_cu_elim (x : ℝ) : Real.cos x ^ 3 = Real.cos x * (1 - Real.sin x ^ 2) := by
  have h := m3_cos_sq_elim x
  linear_combination (Real.cos x) * h
theorem m3_cos_fo_elim (x : ℝ) : Real.cos x ^ 4 = (1 - Real.sin x ^ 2) ^ 2 := by
  have h := m3_cos_sq_elim x
  linear_combination (Real.cos x ^ 2 + (1 - Real.sin x ^ 2)) * h
theorem m3_cos_fi_elim (x : ℝ) :
    Real.cos x ^ 5 = Real.cos x * (1 - Real.sin x ^ 2) ^ 2 := by
  rw [show (5:ℕ) = 2 + 2 + 1 by norm_num, pow_add, pow_add, pow_one, m3_cos_sq_elim]
  ring
theorem m3_cos_si_elim (x : ℝ) :
    Real.cos x ^ 6 = (1 - Real.sin x ^ 2) ^ 3 := by
  rw [show (6:ℕ) = 2 + 2 + 2 by norm_num, pow_add, pow_add, m3_cos_sq_elim]
  ring
theorem m3_sin_pi_o_3 : Real.sin (Real.pi * (1/3)) = √3/2 := by
  rw [show Real.pi * (1/3) = Real.pi/3 by ring]; exact Real.sin_pi_div_three
theorem m3_cos_pi_o_3 : Real.cos (Real.pi * (1/3)) = 1/2 := by
  rw [show Real.pi * (1/3) = Real.pi/3 by ring]; exact Real.cos_pi_div_three
theorem m3_sin_pi_t_3 : Real.sin (Real.pi * (2/3)) = √3/2 := by
  rw [show Real.pi * (2/3) = 2*Real.pi/3 by ring]; exact m3_sin_two_pi_div_three
theorem m3_cos_pi_t_3 : Real.cos (Real.pi * (2/3)) = -(1/2) := by
  rw [show Real.pi * (2/3) = 2*Real.pi/3 by ring]; exact m3_cos_two_pi_div_three
theorem m3_sin_pi_4_3 : Real.sin (Real.pi * (4/3)) = -(√3/2) := by
  rw [show Real.pi * (4/3) = 4*Real.pi/3 by ring]; exact m3_sin_four_pi_div_three
theorem m3_cos_pi_4_3 : Real.cos (Real.pi * (4/3)) = -(1/2) := by
  rw [show Real.pi * (4/3) = 4*Real.pi/3 by ring]; exact m3_cos_four_pi_div_three

/-! ### Star-vector area forms -/

theorem m3_conj_aStar_mul_aStar (T : OrientedTriangle E o) :
    conj (toComplex o T.aStar) * toComplex o T.aStar = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm, toComplex_norm, T.m7_norm_aStar]
  norm_num

theorem m3_toComplex_bStar (T : OrientedTriangle E o) :
    toComplex o T.bStar = -(toComplex o T.aStar * (Circle.exp (-(3 * T.gamma)) : ℂ)) := by
  rw [← toComplex_rotateVector, T.bStar_relation, toComplex_neg,
    show -3 * T.gamma = -(3 * T.gamma) from by ring]

theorem m3_im_exp (t : ℝ) : ((Circle.exp t : ℂ)).im = Real.sin t := by
  have h := m3_real_mul_exp_im 1 t
  simpa using h

/-- The area form of two rotations of the unit vector `aStar`. -/
theorem m3_area_star_self (T : OrientedTriangle E o) (θ ψ : ℝ) :
    o.areaForm (rotateVector o T.aStar θ) (rotateVector o T.aStar ψ) = Real.sin (ψ - θ) := by
  have hc := T.m3_conj_aStar_mul_aStar
  have key : conj (toComplex o (rotateVector o T.aStar θ)) *
      toComplex o (rotateVector o T.aStar ψ) = (Circle.exp (ψ - θ) : ℂ) := by
    rw [toComplex_rotateVector, toComplex_rotateVector, map_mul, m3_conj_exp]
    rw [show conj (toComplex o T.aStar) * (Circle.exp (-θ) : ℂ) *
          (toComplex o T.aStar * Circle.exp ψ)
        = (conj (toComplex o T.aStar) * toComplex o T.aStar) *
            ((Circle.exp (-θ) : ℂ) * Circle.exp ψ) from by ring]
    rw [hc, one_mul, m3_exp_mul_exp,
      show -θ + ψ = ψ - θ from by ring]
  rw [areaForm_complex, key, m3_im_exp]

/-- The area form of a rotation of `aStar` against a rotation of `bStar`. -/
theorem m3_area_star_ab (T : OrientedTriangle E o) (θ ψ : ℝ) :
    o.areaForm (rotateVector o T.aStar θ) (rotateVector o T.bStar ψ)
      = Real.sin (3 * T.gamma - ψ + θ) := by
  have hc := T.m3_conj_aStar_mul_aStar
  have hb := T.m3_toComplex_bStar
  have key : conj (toComplex o (rotateVector o T.aStar θ)) *
      toComplex o (rotateVector o T.bStar ψ)
      = (-1 : ℂ) * (Circle.exp (-(3 * T.gamma - ψ + θ)) : ℂ) := by
    rw [toComplex_rotateVector, toComplex_rotateVector, hb, map_mul, m3_conj_exp]
    rw [show conj (toComplex o T.aStar) * (Circle.exp (-θ) : ℂ) *
          (-(toComplex o T.aStar * (Circle.exp (-(3 * T.gamma)) : ℂ)) * Circle.exp ψ)
        = -((conj (toComplex o T.aStar) * toComplex o T.aStar) *
            ((Circle.exp (-θ) : ℂ) * (Circle.exp (-(3 * T.gamma)) : ℂ) * Circle.exp ψ))
        from by ring]
    rw [hc, one_mul, m3_exp_mul_exp, m3_exp_mul_exp]
    rw [show -θ + -(3 * T.gamma) + ψ = -(3 * T.gamma - ψ + θ) from by ring]
    push_cast
    ring
  rw [areaForm_complex, key]
  rw [show ((-1 : ℂ) * (Circle.exp (-(3 * T.gamma - ψ + θ)) : ℂ))
      = (((-1 : ℝ)) : ℂ) * Circle.exp (-(3 * T.gamma - ψ + θ)) from by push_cast; ring]
  rw [m3_real_mul_exp_im, Real.sin_neg]
  ring

/-- Area form of the side `a` against a rotation of `aStar`. -/
theorem m3_area_a_star (T : OrientedTriangle E o) (θ : ℝ) :
    o.areaForm T.a (rotateVector o T.aStar θ) = T.aLength * Real.sin θ := by
  have h := m3_area_star_self T 0 θ
  rw [rotateVector_zero_angle, sub_zero] at h
  rw [T.a_eq, map_smul, LinearMap.smul_apply, smul_eq_mul, h]

/-! ### The cyclic action on the constellation -/

theorem m3_cp_cyclic_red (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    (m7_cyclic T).constellationPoint ⟨.red, i, j⟩ = T.constellationPoint ⟨.green, i, j⟩ := rfl

theorem m3_cp_cyclic_green (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    (m7_cyclic T).constellationPoint ⟨.green, i, j⟩ = T.constellationPoint ⟨.blue, i, j⟩ := rfl

theorem m3_cp_cyclic_blue (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    (m7_cyclic T).constellationPoint ⟨.blue, i, j⟩ = T.constellationPoint ⟨.red, i, j⟩ := rfl

theorem m3_parallelToMorleySide_cyclic (T : OrientedTriangle E o) (v : E) :
    (m7_cyclic T).parallelToMorleySide v ↔ T.parallelToMorleySide v := by
  unfold parallelToMorleySide
  rw [m7_cyclic_X, m7_cyclic_Y, m7_cyclic_Z]
  tauto

/-- **The cyclic transport.** The three-sides-parallel statement for the tricolor label
`(j,k,i)` at `m7_cyclic T` is the same statement for the label `(i,j,k)` at `T`.
Hence the eighteen sum-`≠1` labels fall into eight cyclic orbits, one proof each. -/
theorem m3_tricolor_sides_cyclic (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    ((m7_cyclic T).parallelToMorleySide
        ((m7_cyclic T).constellationPoint ⟨.green, k, i⟩ -
          (m7_cyclic T).constellationPoint ⟨.red, j, k⟩) ∧
      (m7_cyclic T).parallelToMorleySide
        ((m7_cyclic T).constellationPoint ⟨.blue, i, j⟩ -
          (m7_cyclic T).constellationPoint ⟨.green, k, i⟩) ∧
      (m7_cyclic T).parallelToMorleySide
        ((m7_cyclic T).constellationPoint ⟨.red, j, k⟩ -
          (m7_cyclic T).constellationPoint ⟨.blue, i, j⟩)) ↔
    (T.parallelToMorleySide
        (T.constellationPoint ⟨.green, j, k⟩ - T.constellationPoint ⟨.red, i, j⟩) ∧
      T.parallelToMorleySide
        (T.constellationPoint ⟨.blue, k, i⟩ - T.constellationPoint ⟨.green, j, k⟩) ∧
      T.parallelToMorleySide
        (T.constellationPoint ⟨.red, i, j⟩ - T.constellationPoint ⟨.blue, k, i⟩)) := by
  rw [m3_cp_cyclic_red, m3_cp_cyclic_green, m3_cp_cyclic_blue,
    m3_parallelToMorleySide_cyclic, m3_parallelToMorleySide_cyclic,
    m3_parallelToMorleySide_cyclic]
  tauto


theorem m1_orientedArea_add_right (v w w' : E) :
    orientedArea o v (w + w') = orientedArea o v w + orientedArea o v w' := by
  rw [areaForm_toComplex, areaForm_toComplex, areaForm_toComplex, toComplex_add, mul_add,
    Complex.add_im]

theorem m1_orientedArea_smul_right (r : ℝ) (v w : E) :
    orientedArea o v (r • w) = r * orientedArea o v w := by
  rw [areaForm_toComplex, areaForm_toComplex, toComplex_smul]
  have h : (starRingEnd ℂ) (toComplex o v) * ((r : ℂ) * toComplex o w)
      = (r : ℂ) * ((starRingEnd ℂ) (toComplex o v) * toComplex o w) := by ring
  rw [h]
  simp [Complex.mul_im]

theorem m1_orientedArea_smul_left (r : ℝ) (v w : E) :
    orientedArea o (r • v) w = r * orientedArea o v w := by
  rw [areaForm_toComplex, areaForm_toComplex, toComplex_smul, map_mul, Complex.conj_ofReal]
  have h : (r : ℂ) * (starRingEnd ℂ) (toComplex o v) * toComplex o w
      = (r : ℂ) * ((starRingEnd ℂ) (toComplex o v) * toComplex o w) := by ring
  rw [h]
  simp [Complex.mul_im]

theorem m1_orientedArea_self (v : E) : orientedArea o v v = 0 :=
  Orientation.areaForm_apply_self o v

theorem m1_XY (T : OrientedTriangle E o) :
    T.Y - T.X =
      ((4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) * T.aLength⁻¹) •
        rotateVector o T.a (T.alpha + 2 * T.beta) := by
  rw [Y_sub_X, OrientedTriangle.aStar, rotateVector_smul, smul_smul]

theorem m1_ZY (T : OrientedTriangle E o) :
    T.Z - T.Y =
      ((4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) * T.bLength⁻¹) •
        rotateVector o T.b (T.beta + 2 * T.gamma) := by
  rw [Z_sub_Y, OrientedTriangle.bStar, rotateVector_smul, smul_smul]

theorem m1_area_smul_pair (r s : ℝ) (u v : E) :
    orientedArea o (r • u) (s • v + r • u) = r * (s * orientedArea o u v) := by
  simp only [m1_orientedArea_add_right, m1_orientedArea_smul_right, m1_orientedArea_smul_left,
    m1_orientedArea_self, add_zero]
  ring

theorem m1_XYZ_pos (T : OrientedTriangle E o) :
    0 < orientedArea o (T.Y - T.X) (T.Z - T.X) := by
  have ha_rot : rotateVector o T.a (T.alpha + 2 * T.beta)
      = (-1 : ℝ) • rotateVector o (T.B - T.C) (T.alpha + 2 * T.beta) := by
    rw [show T.a = -(T.B - T.C) from by rw [OrientedTriangle.a]; abel, m6_rotateVector_neg,
      neg_one_smul]
  have hkey := m3_area_rot_general (o := o) (x := T.B - T.C) (y := T.A - T.C)
    (θ := 3 * T.gamma) (R := ‖T.B - T.C‖ * ‖T.A - T.C‖) (m3_key_C T) (1 : ℝ)
    (T.alpha + 2 * T.beta) (T.beta + 2 * T.gamma)
  rw [one_smul] at hkey
  have harg : T.beta + 2 * T.gamma - (T.alpha + 2 * T.beta) - 3 * T.gamma = -(Real.pi / 3) := by
    have h := T.angle_sum; linarith
  rw [harg, Real.sin_neg] at hkey
  set r : ℝ :=
    (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) * T.aLength⁻¹ * (-1)
    with hr
  set s : ℝ :=
    (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) * T.bLength⁻¹ with hs
  set u : E := rotateVector o (T.B - T.C) (T.alpha + 2 * T.beta) with hu
  set v : E := rotateVector o (T.A - T.C) (T.beta + 2 * T.gamma) with hv
  have hXY : T.Y - T.X = r • u := by
    rw [hr, hu, m1_XY, ha_rot, smul_smul]
  have hZX : T.Z - T.X = s • v + r • u := by
    rw [hs, hv, hr, hu, show T.Z - T.X = (T.Z - T.Y) + (T.Y - T.X) from by abel, m1_ZY,
      show T.b = T.A - T.C from rfl, m1_XY, ha_rot, smul_smul]
  have hA : orientedArea o u v
      = 1 * ((‖T.B - T.C‖ * ‖T.A - T.C‖) * -Real.sin (Real.pi / 3)) := by
    rw [hu, hv]; exact hkey
  have hDpos : 0 < 4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma := by
    have h1 := m7_delta_pos T; have h2 := m7_sin_alpha_pos T
    have h3 := m7_sin_beta_pos T; have h4 := m7_sin_gamma_pos T
    positivity
  have hRpos : 0 < ‖T.B - T.C‖ * ‖T.A - T.C‖ :=
    mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr T.B_ne_C))
      (norm_pos_iff.mpr (sub_ne_zero.mpr T.A_ne_C))
  have hsin : 0 < Real.sin (Real.pi / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hrneg : r < 0 := by
    rw [hr]
    have h : 0 < (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) * T.aLength⁻¹ :=
      mul_pos hDpos (inv_pos.mpr T.aLength_pos)
    nlinarith [h]
  have hspos : 0 < s := by
    rw [hs]; exact mul_pos hDpos (inv_pos.mpr T.bLength_pos)
  rw [hXY, hZX, m1_area_smul_pair, hA]
  have hneg : (‖T.B - T.C‖ * ‖T.A - T.C‖) * -Real.sin (Real.pi / 3) < 0 :=
    mul_neg_of_pos_of_neg hRpos (by linarith)
  have h2 : s * (1 * ((‖T.B - T.C‖ * ‖T.A - T.C‖) * -Real.sin (Real.pi / 3))) < 0 := by
    have := mul_neg_of_pos_of_neg hspos hneg
    simpa using this
  exact mul_pos_of_neg_of_neg hrneg h2

/-- The `⟨0,0,0⟩` case of `tricolor_diagonal_positive`: the interior Morley triangle
`XYZ` is positively oriented. -/
theorem m1_diagonal_zero_pos (T : OrientedTriangle E o)
    (_h : Injective T.constellationPoint) :
    PositivelyOriented (o := o) (T.tricolorTriangle ⟨0, 0, 0⟩) := by
  have hpos := m1_XYZ_pos T
  show 0 < orientedArea o
    ((T.tricolorTriangle ⟨0, 0, 0⟩).second - (T.tricolorTriangle ⟨0, 0, 0⟩).first)
    ((T.tricolorTriangle ⟨0, 0, 0⟩).third - (T.tricolorTriangle ⟨0, 0, 0⟩).first)
  simpa [tricolorTriangle] using hpos

theorem m1_orientedArea_add_left (u v w : E) :
    orientedArea o (u + v) w = orientedArea o u w + orientedArea o v w := by
  rw [areaForm_toComplex, areaForm_toComplex, areaForm_toComplex, toComplex_add, map_add,
    add_mul, Complex.add_im]

theorem m1_orientedArea_swap (u v : E) :
    orientedArea o u v = -orientedArea o v u := by
  rw [areaForm_toComplex, areaForm_toComplex]
  have h : (starRingEnd ℂ) ((starRingEnd ℂ) (toComplex o u) * toComplex o v)
      = (starRingEnd ℂ) (toComplex o v) * toComplex o u := by
    rw [map_mul, Complex.conj_conj, mul_comm]
  have him := congrArg Complex.im h
  simp only [Complex.conj_im] at him
  linarith [him]

theorem m1_orientedArea_neg_left (u v : E) :
    orientedArea o (-u) v = -orientedArea o u v := by
  rw [show -u = (-1 : ℝ) • u from by rw [neg_one_smul], m1_orientedArea_smul_left]
  ring

theorem m1_orientedArea_neg_right (u v : E) :
    orientedArea o u (-v) = -orientedArea o u v := by
  rw [show -v = (-1 : ℝ) • v from by rw [neg_one_smul], m1_orientedArea_smul_right]
  ring

theorem m1_orientedArea_sub_left (u v w : E) :
    orientedArea o (u - v) w = orientedArea o u w - orientedArea o v w := by
  rw [sub_eq_add_neg, m1_orientedArea_add_left, m1_orientedArea_neg_left, sub_eq_add_neg]

theorem m1_orientedArea_sub_right (u v w : E) :
    orientedArea o u (v - w) = orientedArea o u v - orientedArea o u w := by
  rw [sub_eq_add_neg, m1_orientedArea_add_right, m1_orientedArea_neg_right, sub_eq_add_neg]

/-- `orientedArea` is invariant under rotating both arguments by the same angle. -/
theorem m1_orientedArea_rot_rot (x y : E) (φ : ℝ) :
    orientedArea o (rotateVector o x φ) (rotateVector o y φ) = orientedArea o x y := by
  rw [areaForm_toComplex, areaForm_toComplex, toComplex_rotateVector, toComplex_rotateVector,
    map_mul, m6_conj_circle_exp]
  have h : (Circle.exp (-φ) : ℂ) * (Circle.exp φ : ℂ) = 1 := by
    rw [m3_exp_mul_exp, show -φ + φ = 0 from by ring, Circle.exp_zero, Circle.coe_one]
  rw [show (starRingEnd ℂ) (toComplex o x) * (Circle.exp (-φ) : ℂ) *
      (toComplex o y * (Circle.exp φ : ℂ))
      = (starRingEnd ℂ) (toComplex o x) * toComplex o y *
        ((Circle.exp (-φ) : ℂ) * (Circle.exp φ : ℂ)) from by ring, h, mul_one]

/-- Positivity of the oriented area is invariant under a rotation about the origin
composed with a nonzero rescaling. -/
theorem m1_pos_rot_smul {r : ℝ} (hr : r ≠ 0) (x y : E) (φ : ℝ) :
    0 < orientedArea o (r • rotateVector o x φ) (r • rotateVector o y φ) ↔
      0 < orientedArea o x y := by
  rw [m1_orientedArea_smul_left, m1_orientedArea_smul_right, m1_orientedArea_rot_rot,
    show r * (r * orientedArea o x y) = (r * r) * orientedArea o x y from by ring]
  exact mul_pos_iff_of_pos_left (mul_self_pos.mpr hr)

/-- The oriented area of a triangle is unchanged by a cyclic permutation of its vertices. -/
theorem m1_orientedArea_cycle (P Q R : E) :
    orientedArea o (R - Q) (P - Q) = orientedArea o (Q - P) (R - P) := by
  have h1 : R - Q = (R - P) - (Q - P) := by abel
  have h2 : P - Q = -(Q - P) := by abel
  rw [h1, h2, m1_orientedArea_sub_left, m1_orientedArea_neg_right, m1_orientedArea_neg_right,
    m1_orientedArea_self]
  rw [show -orientedArea o (R - P) (Q - P) - -0 = -orientedArea o (R - P) (Q - P) from by ring,
    m1_orientedArea_swap (R - P) (Q - P), neg_neg]

theorem m1_pos_cycle {t : TriangleVertices E} (h : PositivelyOriented (o := o) t) :
    PositivelyOriented (o := o) ⟨t.second, t.third, t.first⟩ := by
  show 0 < orientedArea o (t.third - t.second) (t.first - t.second)
  rw [m1_orientedArea_cycle t.first t.second t.third]
  exact h

theorem m1_orientedArea_smul_smul (a b : ℝ) (u v : E) :
    orientedArea o (a • u) (b • v) = a * b * orientedArea o u v := by
  rw [m1_orientedArea_smul_left, m1_orientedArea_smul_right]
  ring

/-- Bridge: a triangle whose two side vectors from the first vertex are *positive*
multiples of `Y-X` and `Z-X` is positively oriented.  Together with
`m1_XYZ_pos` this converts any proof of `tricolor_sides_parallel` with positive
scalars into an orientation statement (`tricolor_diagonal_positive`,
`tricolor_orientation`). -/
theorem m1_positivelyOriented_of_smul (T : OrientedTriangle E o) {P Q R : E} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (h1 : Q - P = a • (T.Y - T.X))
    (h2 : R - P = b • (T.Z - T.X)) :
    PositivelyOriented (o := o) ⟨P, Q, R⟩ := by
  show 0 < orientedArea o (Q - P) (R - P)
  rw [h1, h2, m1_orientedArea_smul_smul]
  exact mul_pos (mul_pos ha hb) (m1_XYZ_pos T)

/-- The same bridge with the opposite orientation. -/
theorem m1_negativelyOriented_of_smul (T : OrientedTriangle E o) {P Q R : E} {a b : ℝ}
    (h : a * b < 0) (h1 : Q - P = a • (T.Y - T.X)) (h2 : R - P = b • (T.Z - T.X)) :
    NegativelyOriented (o := o) ⟨P, Q, R⟩ := by
  show orientedArea o (Q - P) (R - P) < 0
  rw [h1, h2, m1_orientedArea_smul_smul]
  exact mul_neg_of_neg_of_pos h (m1_XYZ_pos T)

theorem m5_one_sub_exp_pi3 : (1 : ℂ) - (Circle.exp (Real.pi / 3) : ℂ) =
    (Circle.exp (-(Real.pi / 3)) : ℂ) := by
  rw [m6_circle_exp_eq (Real.pi / 3), m6_circle_exp_eq (-(Real.pi / 3)),
    Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_neg, Real.sin_neg]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem m5_one_sub_exp_neg_pi3 : (1 : ℂ) - (Circle.exp (-(Real.pi / 3)) : ℂ) =
    (Circle.exp (Real.pi / 3) : ℂ) := by
  rw [m6_circle_exp_eq (Real.pi / 3), m6_circle_exp_eq (-(Real.pi / 3)),
    Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_neg, Real.sin_neg]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem m5_sub_rot_pi3 (v : E) :
    v - rotateVector o v (Real.pi / 3) = rotateVector o v (-(Real.pi / 3)) := by
  apply toComplex_injective o
  calc toComplex o (v - rotateVector o v (Real.pi / 3))
      = toComplex o v - toComplex o v * (Circle.exp (Real.pi / 3) : ℂ) := by
        rw [toComplex_sub, toComplex_rotateVector]
    _ = toComplex o v * ((1 : ℂ) - (Circle.exp (Real.pi / 3) : ℂ)) := by ring
    _ = toComplex o v * (Circle.exp (-(Real.pi / 3)) : ℂ) := by rw [m5_one_sub_exp_pi3]
    _ = toComplex o (rotateVector o v (-(Real.pi / 3))) := by rw [toComplex_rotateVector]

theorem m5_sub_rot_neg_pi3 (v : E) :
    v - rotateVector o v (-(Real.pi / 3)) = rotateVector o v (Real.pi / 3) := by
  apply toComplex_injective o
  calc toComplex o (v - rotateVector o v (-(Real.pi / 3)))
      = toComplex o v - toComplex o v * (Circle.exp (-(Real.pi / 3)) : ℂ) := by
        rw [toComplex_sub, toComplex_rotateVector]
    _ = toComplex o v * ((1 : ℂ) - (Circle.exp (-(Real.pi / 3)) : ℂ)) := by ring
    _ = toComplex o v * (Circle.exp (Real.pi / 3) : ℂ) := by rw [m5_one_sub_exp_neg_pi3]
    _ = toComplex o (rotateVector o v (Real.pi / 3)) := by rw [toComplex_rotateVector]

theorem m5_complex_eq_exp_of_norm (z : ℂ) (h1 : ‖z‖ = 1) (h2 : ‖z - 1‖ = 1) :
    z = (Circle.exp (Real.pi / 3) : ℂ) ∨ z = (Circle.exp (-(Real.pi / 3)) : ℂ) := by
  have hn1 : z.re * z.re + z.im * z.im = 1 := by
    have h : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, h1]; norm_num
    rwa [Complex.normSq_apply] at h
  have hn2 : (z.re - 1) * (z.re - 1) + z.im * z.im = 1 := by
    have h : Complex.normSq (z - 1) = 1 := by rw [Complex.normSq_eq_norm_sq, h2]; norm_num
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero] at h
    exact h
  have hx : z.re = 1 / 2 := by nlinarith
  have hy2 : z.im * z.im = 3 / 4 := by nlinarith
  have hy : z.im = √3 / 2 ∨ z.im = -(√3 / 2) := by
    have hsq : z.im ^ 2 = (√3 / 2) ^ 2 := by
      rw [pow_two, hy2, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
      norm_num
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  rcases hy with hy | hy
  · left
    have hre : z.re = Real.cos (Real.pi / 3) := by rw [hx, Real.cos_pi_div_three]
    have him : z.im = Real.sin (Real.pi / 3) := by rw [hy, Real.sin_pi_div_three]
    rw [m6_circle_exp_eq]
    apply Complex.ext <;> simp [hre, him]
  · right
    have hre : z.re = Real.cos (-(Real.pi / 3)) := by
      rw [hx, Real.cos_neg, Real.cos_pi_div_three]
    have him : z.im = Real.sin (-(Real.pi / 3)) := by
      rw [hy, Real.sin_neg, Real.sin_pi_div_three]
    rw [m6_circle_exp_eq]
    apply Complex.ext <;> simp [hre, him]


theorem m5_equilateral_iff_rotate (P Q R : E) (hPR : P ≠ R) :
    Equilateral P Q R ↔
      (Q - P = rotateVector o (R - P) (Real.pi / 3) ∨
        Q - P = rotateVector o (R - P) (-(Real.pi / 3))) := by
  constructor
  · intro he
    unfold Equilateral at he
    obtain ⟨h1, h2⟩ := he
    set u := R - P with hu
    set v := Q - P with hv
    have hu0 : u ≠ 0 := by rw [hu]; exact sub_ne_zero.mpr (Ne.symm hPR)
    have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
    have hvu : ‖v‖ = ‖u‖ := by
      have e1 : ‖v‖ = dist P Q := by rw [hv, dist_eq_norm, norm_sub_rev]
      have e2 : ‖u‖ = dist R P := by rw [hu, dist_eq_norm]
      rw [e1, e2]; linarith
    have hwu : ‖Q - R‖ = ‖u‖ := by
      have e2 : ‖u‖ = dist R P := by rw [hu, dist_eq_norm]
      rw [e2, ← h2, dist_eq_norm]
    have hu0c : toComplex o u ≠ 0 := by
      rw [← norm_ne_zero_iff, toComplex_norm]; exact hun
    have hz1 : ‖toComplex o v * (toComplex o u)⁻¹‖ = 1 := by
      rw [norm_mul, norm_inv, toComplex_norm, toComplex_norm, hvu]
      exact mul_inv_cancel₀ hun
    have hz2 : ‖toComplex o v * (toComplex o u)⁻¹ - 1‖ = 1 := by
      have hsub : toComplex o v * (toComplex o u)⁻¹ - 1 =
          (toComplex o v - toComplex o u) * (toComplex o u)⁻¹ := by
        rw [sub_mul, mul_inv_cancel₀ hu0c]
      have hq : v - u = Q - R := by rw [hv, hu]; abel
      rw [hsub, norm_mul, norm_inv, toComplex_norm,
        show toComplex o v - toComplex o u = toComplex o (Q - R) by
          rw [← toComplex_sub, hq]]
      rw [toComplex_norm, hwu]
      exact mul_inv_cancel₀ hun
    obtain hz | hz := m5_complex_eq_exp_of_norm _ hz1 hz2
    · left
      have hthis : toComplex o v = (Circle.exp (Real.pi / 3) : ℂ) * toComplex o u := by
        calc toComplex o v = (toComplex o v * (toComplex o u)⁻¹) * toComplex o u := by
              rw [mul_assoc, inv_mul_cancel₀ hu0c, mul_one]
          _ = (Circle.exp (Real.pi / 3) : ℂ) * toComplex o u := by rw [hz]
      refine toComplex_injective o ?_
      rw [toComplex_rotateVector, mul_comm]
      exact hthis
    · right
      have hthis : toComplex o v = (Circle.exp (-(Real.pi / 3)) : ℂ) * toComplex o u := by
        calc toComplex o v = (toComplex o v * (toComplex o u)⁻¹) * toComplex o u := by
              rw [mul_assoc, inv_mul_cancel₀ hu0c, mul_one]
          _ = (Circle.exp (-(Real.pi / 3)) : ℂ) * toComplex o u := by rw [hz]
      refine toComplex_injective o ?_
      rw [toComplex_rotateVector, mul_comm]
      exact hthis
  · intro h
    unfold Equilateral
    rcases h with h | h
    · have hQR : Q - R = -rotateVector o (R - P) (-(Real.pi / 3)) := by
        have hs := m5_sub_rot_pi3 (o := o) (R - P)
        have hRQ : R - Q = rotateVector o (R - P) (-(Real.pi / 3)) := by rw [← hs, ← h]; abel
        rw [← hRQ]; abel
      constructor
      · rw [dist_eq_norm, dist_eq_norm, norm_sub_rev P Q, h, rotateVector_norm, hQR, norm_neg,
          rotateVector_norm]
      · rw [dist_eq_norm, dist_eq_norm, hQR, norm_neg, rotateVector_norm]
    · have hQR : Q - R = -rotateVector o (R - P) (Real.pi / 3) := by
        have hs := m5_sub_rot_neg_pi3 (o := o) (R - P)
        have hRQ : R - Q = rotateVector o (R - P) (Real.pi / 3) := by rw [← hs, ← h]; abel
        rw [← hRQ]; abel
      constructor
      · rw [dist_eq_norm, dist_eq_norm, norm_sub_rev P Q, h, rotateVector_norm, hQR, norm_neg,
          rotateVector_norm]
      · rw [dist_eq_norm, dist_eq_norm, hQR, norm_neg, rotateVector_norm]


def m5_redPt (T : OrientedTriangle E o) (p : TrisectorLabel × TrisectorLabel) : E :=
  T.constellationPoint ⟨.red, p.1, p.2⟩

theorem m5_mem_redPt_of_mem {T : OrientedTriangle E o} {q : ConstellationIndex}
    (hq : q.color = .red) :
    T.m5_redPt (q.first, q.second) = T.constellationPoint q := by
  rcases q with ⟨c, a, b⟩
  cases c <;> simp_all [m5_redPt]

theorem m5_ci_ext {q q' : ConstellationIndex} (hc : q.color = q'.color)
    (h1 : q.first = q'.first) (h2 : q.second = q'.second) : q = q' := by
  obtain ⟨c, a, b⟩ := q
  obtain ⟨c', a', b'⟩ := q'
  simp only at hc h1 h2
  subst hc; subst h1; subst h2; rfl

theorem m5_isGuideLine_congr (T : OrientedTriangle E o) {ℓ ℓ' : Line E}
    (hpar : Parallel ℓ.direction ℓ'.direction) (hmem : ∀ X : E, ℓ.mem X ↔ ℓ'.mem X)
    (h : T.IsGuideLine ℓ) : T.IsGuideLine ℓ' := by
  obtain ⟨hdir, h6, h2⟩ := h
  have hpar' : Parallel ℓ'.direction ℓ.direction :=
    parallel_comm ℓ.direction_ne_zero ℓ'.direction_ne_zero hpar
  refine ⟨?_, ?_, ?_⟩
  · rcases hdir with hd | hd | hd
    · exact Or.inl (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hd hpar')
    · exact Or.inr (Or.inl (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hd hpar'))
    · exact Or.inr (Or.inr (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hd hpar'))
  · have hset : {q : ConstellationIndex | ℓ'.mem (T.constellationPoint q)}
        = {q : ConstellationIndex | ℓ.mem (T.constellationPoint q)} := by
      ext q
      exact (hmem _).symm
    rw [hset, h6]
  · intro c
    have hset : {q : ConstellationIndex | q.color = c ∧ ℓ'.mem (T.constellationPoint q)}
        = {q : ConstellationIndex | q.color = c ∧ ℓ.mem (T.constellationPoint q)} := by
      ext q
      exact ⟨fun hq => ⟨hq.1, (hmem _).mpr hq.2⟩, fun hq => ⟨hq.1, (hmem _).mp hq.2⟩⟩
    rw [hset, h2 c]

theorem m5_guide_red_first (T : OrientedTriangle E o) {ℓ : Line E}
    (hℓ : ℓ ∈ T.guideLines) (h : Injective T.constellationPoint)
    {p q : TrisectorLabel × TrisectorLabel} (hpq : p ≠ q)
    (hp : ℓ.mem (T.m5_redPt p)) (hq : ℓ.mem (T.m5_redPt q)) : p.1 ≠ q.1 := by
  intro heq
  have hpt : T.m5_redPt p ≠ T.m5_redPt q := by
    intro hc
    have hidx := h hc
    exact hpq (Prod.ext (congrArg ConstellationIndex.first hidx)
      (congrArg ConstellationIndex.second hidx))
  have hBp : (T.redB p.1).mem (T.m5_redPt p) := m4_cp_red_mem_redB T p.1 p.2
  have hBq : (T.redB p.1).mem (T.m5_redPt q) := by
    rw [heq]
    exact m4_cp_red_mem_redB T q.1 q.2
  have hiff := m4_mem_iff_of_two_mem hpt hp hq hBp hBq
  have hpar := Line.parallel_of_mem_sub' hpt hp hq hBp hBq
  exact m4_redB_not_isGuideLine T p.1 (m5_isGuideLine_congr T hpar hiff hℓ.1)

theorem m5_guide_red_second (T : OrientedTriangle E o) {ℓ : Line E}
    (hℓ : ℓ ∈ T.guideLines) (h : Injective T.constellationPoint)
    {p q : TrisectorLabel × TrisectorLabel} (hpq : p ≠ q)
    (hp : ℓ.mem (T.m5_redPt p)) (hq : ℓ.mem (T.m5_redPt q)) : p.2 ≠ q.2 := by
  intro heq
  have hpt : T.m5_redPt p ≠ T.m5_redPt q := by
    intro hc
    have hidx := h hc
    exact hpq (Prod.ext (congrArg ConstellationIndex.first hidx)
      (congrArg ConstellationIndex.second hidx))
  have hCp : (T.redC p.2).mem (T.m5_redPt p) := m4_cp_red_mem_redC T p.1 p.2
  have hCq : (T.redC p.2).mem (T.m5_redPt q) := by
    rw [heq]
    exact m4_cp_red_mem_redC T q.1 q.2
  have hiff := m4_mem_iff_of_two_mem hpt hp hq hCp hCq
  have hpar := Line.parallel_of_mem_sub' hpt hp hq hCp hCq
  exact m4_redC_not_isGuideLine T p.2 (m5_isGuideLine_congr T hpar hiff hℓ.1)

theorem m5_pairs18_ncard :
    {r : (TrisectorLabel × TrisectorLabel) × (TrisectorLabel × TrisectorLabel) |
      r.1 ≠ r.2 ∧ r.1.1 ≠ r.2.1 ∧ r.1.2 ≠ r.2.2}.ncard = 36 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  native_decide

theorem m5_ncard_le_eighteen (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.guideLines.ncard ≤ 18 := by
  classical
  set G := T.guideLines with hG
  have hex : ∀ ℓ : {ℓ : Line E // ℓ ∈ G}, ∃ q₁ q₂ : ConstellationIndex, q₁ ≠ q₂ ∧
      {q : ConstellationIndex | q.color = .red ∧ (ℓ : Line E).mem (T.constellationPoint q)}
        = {q₁, q₂} := by
    intro ℓ
    exact Set.ncard_eq_two.mp (ℓ.2.1.2.2 TrisectorColor.red)
  choose f₁ f₂ hf using hex
  have hmem₁ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      (f₁ ℓ).color = .red ∧ (ℓ : Line E).mem (T.constellationPoint (f₁ ℓ)) := by
    intro ℓ
    have hins : f₁ ℓ ∈ {q : ConstellationIndex |
        q.color = .red ∧ (ℓ : Line E).mem (T.constellationPoint q)} := by
      rw [(hf ℓ).2]; exact Set.mem_insert _ _
    exact hins
  have hmem₂ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      (f₂ ℓ).color = .red ∧ (ℓ : Line E).mem (T.constellationPoint (f₂ ℓ)) := by
    intro ℓ
    have hins : f₂ ℓ ∈ {q : ConstellationIndex |
        q.color = .red ∧ (ℓ : Line E).mem (T.constellationPoint q)} := by
      rw [(hf ℓ).2]; exact Set.mem_insert_of_mem _ rfl
    exact hins
  have hlab : ∀ ℓ : {ℓ : Line E // ℓ ∈ G}, ((f₁ ℓ).first, (f₁ ℓ).second) ≠ ((f₂ ℓ).first, (f₂ ℓ).second) := by
    intro ℓ heq
    have h1 : (f₁ ℓ).first = (f₂ ℓ).first := congrArg Prod.fst heq
    have h2 : (f₁ ℓ).second = (f₂ ℓ).second := congrArg Prod.snd heq
    have hc : (f₁ ℓ).color = (f₂ ℓ).color := by rw [(hmem₁ ℓ).1, (hmem₂ ℓ).1]
    exact (hf ℓ).1 (m5_ci_ext hc h1 h2)
  have hpt : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      T.constellationPoint (f₁ ℓ) ≠ T.constellationPoint (f₂ ℓ) := by
    intro ℓ hc
    exact (hf ℓ).1 (h hc)
  have hshared : ∀ ℓ ℓ' : {ℓ : Line E // ℓ ∈ G},
      (ℓ : Line E).mem (T.constellationPoint (f₁ ℓ)) →
      (ℓ : Line E).mem (T.constellationPoint (f₂ ℓ)) →
      (ℓ' : Line E).mem (T.constellationPoint (f₁ ℓ)) →
      (ℓ' : Line E).mem (T.constellationPoint (f₂ ℓ)) → ℓ = ℓ' := by
    intro ℓ ℓ' h1 h2 h3 h4
    have hiff := m4_mem_iff_of_two_mem (hpt ℓ) h1 h2 h3 h4
    exact Subtype.ext (isCanonical_eq_of_mem_iff ℓ.2.2 ℓ'.2.2 hiff)
  let P₀ : {ℓ : Line E // ℓ ∈ G} →
      (TrisectorLabel × TrisectorLabel) × (TrisectorLabel × TrisectorLabel) :=
    fun ℓ => (((f₁ ℓ).first, (f₁ ℓ).second), ((f₂ ℓ).first, (f₂ ℓ).second))
  let P₁ : {ℓ : Line E // ℓ ∈ G} →
      (TrisectorLabel × TrisectorLabel) × (TrisectorLabel × TrisectorLabel) :=
    fun ℓ => (((f₂ ℓ).first, (f₂ ℓ).second), ((f₁ ℓ).first, (f₁ ℓ).second))
  have hval₀ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      (ℓ : Line E).mem (T.m5_redPt (P₀ ℓ).1) ∧ (ℓ : Line E).mem (T.m5_redPt (P₀ ℓ).2) := by
    intro ℓ
    refine ⟨?_, ?_⟩
    · show (ℓ : Line E).mem (T.m5_redPt ((f₁ ℓ).first, (f₁ ℓ).second))
      rw [m5_mem_redPt_of_mem (hmem₁ ℓ).1]
      exact (hmem₁ ℓ).2
    · show (ℓ : Line E).mem (T.m5_redPt ((f₂ ℓ).first, (f₂ ℓ).second))
      rw [m5_mem_redPt_of_mem (hmem₂ ℓ).1]
      exact (hmem₂ ℓ).2
  have hval₁ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      (ℓ : Line E).mem (T.m5_redPt (P₁ ℓ).1) ∧ (ℓ : Line E).mem (T.m5_redPt (P₁ ℓ).2) := by
    intro ℓ
    refine ⟨?_, ?_⟩
    · show (ℓ : Line E).mem (T.m5_redPt ((f₂ ℓ).first, (f₂ ℓ).second))
      rw [m5_mem_redPt_of_mem (hmem₂ ℓ).1]
      exact (hmem₂ ℓ).2
    · show (ℓ : Line E).mem (T.m5_redPt ((f₁ ℓ).first, (f₁ ℓ).second))
      rw [m5_mem_redPt_of_mem (hmem₁ ℓ).1]
      exact (hmem₁ ℓ).2
  have hd₁ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G}, (f₁ ℓ).first ≠ (f₂ ℓ).first := by
    intro ℓ
    refine m5_guide_red_first T ℓ.2 h (hlab ℓ) ?_ ?_
    · rw [m5_mem_redPt_of_mem (hmem₁ ℓ).1]; exact (hmem₁ ℓ).2
    · rw [m5_mem_redPt_of_mem (hmem₂ ℓ).1]; exact (hmem₂ ℓ).2
  have hd₂ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G}, (f₁ ℓ).second ≠ (f₂ ℓ).second := by
    intro ℓ
    refine m5_guide_red_second T ℓ.2 h (hlab ℓ) ?_ ?_
    · rw [m5_mem_redPt_of_mem (hmem₁ ℓ).1]; exact (hmem₁ ℓ).2
    · rw [m5_mem_redPt_of_mem (hmem₂ ℓ).1]; exact (hmem₂ ℓ).2
  have heq₀ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G}, P₀ ℓ = (((f₁ ℓ).first, (f₁ ℓ).second), ((f₂ ℓ).first, (f₂ ℓ).second)) := fun ℓ => rfl
  have heq₁ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G}, P₁ ℓ = (((f₂ ℓ).first, (f₂ ℓ).second), ((f₁ ℓ).first, (f₁ ℓ).second)) := fun ℓ => rfl
  have hP₀inj : Function.Injective P₀ := by
    intro ℓ ℓ' heq
    have he : (((f₁ ℓ).first, (f₁ ℓ).second), ((f₂ ℓ).first, (f₂ ℓ).second)) =
        (((f₁ ℓ').first, (f₁ ℓ').second), ((f₂ ℓ').first, (f₂ ℓ').second)) := by
      rw [← heq₀ ℓ, ← heq₀ ℓ']; exact heq
    have h1 : ((f₁ ℓ).first, (f₁ ℓ).second) = ((f₁ ℓ').first, (f₁ ℓ').second) := congrArg Prod.fst he
    have h2 : ((f₂ ℓ).first, (f₂ ℓ).second) = ((f₂ ℓ').first, (f₂ ℓ').second) := congrArg Prod.snd he
    have e1 : T.constellationPoint (f₁ ℓ) = T.constellationPoint (f₁ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₁ ℓ).1, ← m5_mem_redPt_of_mem (hmem₁ ℓ').1, h1]
    have e2 : T.constellationPoint (f₂ ℓ) = T.constellationPoint (f₂ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₂ ℓ).1, ← m5_mem_redPt_of_mem (hmem₂ ℓ').1, h2]
    exact hshared ℓ ℓ' (hmem₁ ℓ).2 (hmem₂ ℓ).2 (e1 ▸ (hmem₁ ℓ').2) (e2 ▸ (hmem₂ ℓ').2)
  have hP₁inj : Function.Injective P₁ := by
    intro ℓ ℓ' heq
    have he : (((f₂ ℓ).first, (f₂ ℓ).second), ((f₁ ℓ).first, (f₁ ℓ).second)) =
        (((f₂ ℓ').first, (f₂ ℓ').second), ((f₁ ℓ').first, (f₁ ℓ').second)) := by
      rw [← heq₁ ℓ, ← heq₁ ℓ']; exact heq
    have h1 : ((f₂ ℓ).first, (f₂ ℓ).second) = ((f₂ ℓ').first, (f₂ ℓ').second) := congrArg Prod.fst he
    have h2 : ((f₁ ℓ).first, (f₁ ℓ).second) = ((f₁ ℓ').first, (f₁ ℓ').second) := congrArg Prod.snd he
    have e1 : T.constellationPoint (f₂ ℓ) = T.constellationPoint (f₂ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₂ ℓ).1, ← m5_mem_redPt_of_mem (hmem₂ ℓ').1, h1]
    have e2 : T.constellationPoint (f₁ ℓ) = T.constellationPoint (f₁ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₁ ℓ).1, ← m5_mem_redPt_of_mem (hmem₁ ℓ').1, h2]
    exact hshared ℓ ℓ' (hmem₁ ℓ).2 (hmem₂ ℓ).2 (e2 ▸ (hmem₁ ℓ').2) (e1 ▸ (hmem₂ ℓ').2)
  have hdisj : Disjoint (P₀ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G}))
      (P₁ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G})) := by
    rw [Set.disjoint_left]
    rintro p hp₀ hp₁
    obtain ⟨ℓ, -, rfl⟩ := hp₀
    obtain ⟨ℓ', -, heq⟩ := hp₁
    have he : (((f₁ ℓ).first, (f₁ ℓ).second), ((f₂ ℓ).first, (f₂ ℓ).second)) =
        (((f₂ ℓ').first, (f₂ ℓ').second), ((f₁ ℓ').first, (f₁ ℓ').second)) := by
      rw [← heq₀ ℓ, ← heq₁ ℓ']; exact heq.symm
    have h1 : ((f₁ ℓ).first, (f₁ ℓ).second) = ((f₂ ℓ').first, (f₂ ℓ').second) := congrArg Prod.fst he
    have h2 : ((f₂ ℓ).first, (f₂ ℓ).second) = ((f₁ ℓ').first, (f₁ ℓ').second) := congrArg Prod.snd he
    have e1 : T.constellationPoint (f₁ ℓ) = T.constellationPoint (f₂ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₁ ℓ).1, ← m5_mem_redPt_of_mem (hmem₂ ℓ').1, h1]
    have e2 : T.constellationPoint (f₂ ℓ) = T.constellationPoint (f₁ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₂ ℓ).1, ← m5_mem_redPt_of_mem (hmem₁ ℓ').1, h2]
    have hll : ℓ = ℓ' := hshared ℓ ℓ' (hmem₁ ℓ).2 (hmem₂ ℓ).2
      (e1 ▸ (hmem₂ ℓ').2) (e2 ▸ (hmem₁ ℓ').2)
    subst hll
    exact hlab ℓ h1
  have hsub : (P₀ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G}) ∪
      P₁ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G})) ⊆
      {r : (TrisectorLabel × TrisectorLabel) × (TrisectorLabel × TrisectorLabel) |
        r.1 ≠ r.2 ∧ r.1.1 ≠ r.2.1 ∧ r.1.2 ≠ r.2.2} := by
    rintro _ (hp | hp)
    · obtain ⟨ℓ, -, rfl⟩ := hp
      exact ⟨hlab ℓ, hd₁ ℓ, hd₂ ℓ⟩
    · obtain ⟨ℓ, -, rfl⟩ := hp
      show ((f₂ ℓ).first, (f₂ ℓ).second) ≠ ((f₁ ℓ).first, (f₁ ℓ).second) ∧
        (f₂ ℓ).first ≠ (f₁ ℓ).first ∧ (f₂ ℓ).second ≠ (f₁ ℓ).second
      exact ⟨fun hc => hlab ℓ hc.symm, fun hc => hd₁ ℓ hc.symm, fun hc => hd₂ ℓ hc.symm⟩
  have hI₀ : (P₀ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G})).ncard = G.ncard := by
    rw [Set.ncard_image_of_injective _ hP₀inj, Set.ncard_univ, ← Nat.card_coe_set_eq]
  have hI₁ : (P₁ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G})).ncard = G.ncard := by
    rw [Set.ncard_image_of_injective _ hP₁inj, Set.ncard_univ, ← Nat.card_coe_set_eq]
  have hunion : ((P₀ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G}) ∪
      P₁ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G}))).ncard = G.ncard + G.ncard := by
    rw [m4_ncard_union_of_disjoint (Set.toFinite _) (Set.toFinite _) hdisj, hI₀, hI₁]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hunion, m5_pairs18_ncard] at hle
  rw [hG] at hle ⊢
  omega

theorem m5_ncard_le_nine (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hclass : ∀ (ℓ : Line E), ℓ ∈ T.guideLines → ∀ p q : TrisectorLabel × TrisectorLabel,
      ℓ.mem (T.m5_redPt p) → ℓ.mem (T.m5_redPt q) → p.1 + p.2 = q.1 + q.2) :
    T.guideLines.ncard ≤ 9 := by
  classical
  set G := T.guideLines with hG
  have hex : ∀ ℓ : {ℓ : Line E // ℓ ∈ G}, ∃ q₁ q₂ : ConstellationIndex, q₁ ≠ q₂ ∧
      {q : ConstellationIndex | q.color = .red ∧ (ℓ : Line E).mem (T.constellationPoint q)}
        = {q₁, q₂} := by
    intro ℓ
    exact Set.ncard_eq_two.mp (ℓ.2.1.2.2 TrisectorColor.red)
  choose f₁ f₂ hf using hex
  have hmem₁ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      (f₁ ℓ).color = .red ∧ (ℓ : Line E).mem (T.constellationPoint (f₁ ℓ)) := by
    intro ℓ
    have hins : f₁ ℓ ∈ {q : ConstellationIndex |
        q.color = .red ∧ (ℓ : Line E).mem (T.constellationPoint q)} := by
      rw [(hf ℓ).2]; exact Set.mem_insert _ _
    exact hins
  have hmem₂ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      (f₂ ℓ).color = .red ∧ (ℓ : Line E).mem (T.constellationPoint (f₂ ℓ)) := by
    intro ℓ
    have hins : f₂ ℓ ∈ {q : ConstellationIndex |
        q.color = .red ∧ (ℓ : Line E).mem (T.constellationPoint q)} := by
      rw [(hf ℓ).2]; exact Set.mem_insert_of_mem _ rfl
    exact hins
  have hlab : ∀ ℓ : {ℓ : Line E // ℓ ∈ G}, ((f₁ ℓ).first, (f₁ ℓ).second) ≠ ((f₂ ℓ).first, (f₂ ℓ).second) := by
    intro ℓ heq
    have h1 : (f₁ ℓ).first = (f₂ ℓ).first := congrArg Prod.fst heq
    have h2 : (f₁ ℓ).second = (f₂ ℓ).second := congrArg Prod.snd heq
    have hc : (f₁ ℓ).color = (f₂ ℓ).color := by rw [(hmem₁ ℓ).1, (hmem₂ ℓ).1]
    exact (hf ℓ).1 (m5_ci_ext hc h1 h2)
  have hpt : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      T.constellationPoint (f₁ ℓ) ≠ T.constellationPoint (f₂ ℓ) := by
    intro ℓ hc
    exact (hf ℓ).1 (h hc)
  have hshared : ∀ ℓ ℓ' : {ℓ : Line E // ℓ ∈ G},
      (ℓ : Line E).mem (T.constellationPoint (f₁ ℓ)) →
      (ℓ : Line E).mem (T.constellationPoint (f₂ ℓ)) →
      (ℓ' : Line E).mem (T.constellationPoint (f₁ ℓ)) →
      (ℓ' : Line E).mem (T.constellationPoint (f₂ ℓ)) → ℓ = ℓ' := by
    intro ℓ ℓ' h1 h2 h3 h4
    have hiff := m4_mem_iff_of_two_mem (hpt ℓ) h1 h2 h3 h4
    exact Subtype.ext (isCanonical_eq_of_mem_iff ℓ.2.2 ℓ'.2.2 hiff)
  let P₀ : {ℓ : Line E // ℓ ∈ G} →
      (TrisectorLabel × TrisectorLabel) × (TrisectorLabel × TrisectorLabel) :=
    fun ℓ => (((f₁ ℓ).first, (f₁ ℓ).second), ((f₂ ℓ).first, (f₂ ℓ).second))
  let P₁ : {ℓ : Line E // ℓ ∈ G} →
      (TrisectorLabel × TrisectorLabel) × (TrisectorLabel × TrisectorLabel) :=
    fun ℓ => (((f₂ ℓ).first, (f₂ ℓ).second), ((f₁ ℓ).first, (f₁ ℓ).second))
  have hval₀ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      (ℓ : Line E).mem (T.m5_redPt (P₀ ℓ).1) ∧ (ℓ : Line E).mem (T.m5_redPt (P₀ ℓ).2) := by
    intro ℓ
    refine ⟨?_, ?_⟩
    · show (ℓ : Line E).mem (T.m5_redPt ((f₁ ℓ).first, (f₁ ℓ).second))
      rw [m5_mem_redPt_of_mem (hmem₁ ℓ).1]
      exact (hmem₁ ℓ).2
    · show (ℓ : Line E).mem (T.m5_redPt ((f₂ ℓ).first, (f₂ ℓ).second))
      rw [m5_mem_redPt_of_mem (hmem₂ ℓ).1]
      exact (hmem₂ ℓ).2
  have hval₁ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      (ℓ : Line E).mem (T.m5_redPt (P₁ ℓ).1) ∧ (ℓ : Line E).mem (T.m5_redPt (P₁ ℓ).2) := by
    intro ℓ
    refine ⟨?_, ?_⟩
    · show (ℓ : Line E).mem (T.m5_redPt ((f₂ ℓ).first, (f₂ ℓ).second))
      rw [m5_mem_redPt_of_mem (hmem₂ ℓ).1]
      exact (hmem₂ ℓ).2
    · show (ℓ : Line E).mem (T.m5_redPt ((f₁ ℓ).first, (f₁ ℓ).second))
      rw [m5_mem_redPt_of_mem (hmem₁ ℓ).1]
      exact (hmem₁ ℓ).2
  have heq₀ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G}, P₀ ℓ = (((f₁ ℓ).first, (f₁ ℓ).second), ((f₂ ℓ).first, (f₂ ℓ).second)) := fun ℓ => rfl
  have heq₁ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G}, P₁ ℓ = (((f₂ ℓ).first, (f₂ ℓ).second), ((f₁ ℓ).first, (f₁ ℓ).second)) := fun ℓ => rfl
  have hP₀inj : Function.Injective P₀ := by
    intro ℓ ℓ' heq
    have he : (((f₁ ℓ).first, (f₁ ℓ).second), ((f₂ ℓ).first, (f₂ ℓ).second)) =
        (((f₁ ℓ').first, (f₁ ℓ').second), ((f₂ ℓ').first, (f₂ ℓ').second)) := by
      rw [← heq₀ ℓ, ← heq₀ ℓ']; exact heq
    have h1 : ((f₁ ℓ).first, (f₁ ℓ).second) = ((f₁ ℓ').first, (f₁ ℓ').second) := congrArg Prod.fst he
    have h2 : ((f₂ ℓ).first, (f₂ ℓ).second) = ((f₂ ℓ').first, (f₂ ℓ').second) := congrArg Prod.snd he
    have e1 : T.constellationPoint (f₁ ℓ) = T.constellationPoint (f₁ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₁ ℓ).1, ← m5_mem_redPt_of_mem (hmem₁ ℓ').1, h1]
    have e2 : T.constellationPoint (f₂ ℓ) = T.constellationPoint (f₂ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₂ ℓ).1, ← m5_mem_redPt_of_mem (hmem₂ ℓ').1, h2]
    exact hshared ℓ ℓ' (hmem₁ ℓ).2 (hmem₂ ℓ).2 (e1 ▸ (hmem₁ ℓ').2) (e2 ▸ (hmem₂ ℓ').2)
  have hP₁inj : Function.Injective P₁ := by
    intro ℓ ℓ' heq
    have he : (((f₂ ℓ).first, (f₂ ℓ).second), ((f₁ ℓ).first, (f₁ ℓ).second)) =
        (((f₂ ℓ').first, (f₂ ℓ').second), ((f₁ ℓ').first, (f₁ ℓ').second)) := by
      rw [← heq₁ ℓ, ← heq₁ ℓ']; exact heq
    have h1 : ((f₂ ℓ).first, (f₂ ℓ).second) = ((f₂ ℓ').first, (f₂ ℓ').second) := congrArg Prod.fst he
    have h2 : ((f₁ ℓ).first, (f₁ ℓ).second) = ((f₁ ℓ').first, (f₁ ℓ').second) := congrArg Prod.snd he
    have e1 : T.constellationPoint (f₂ ℓ) = T.constellationPoint (f₂ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₂ ℓ).1, ← m5_mem_redPt_of_mem (hmem₂ ℓ').1, h1]
    have e2 : T.constellationPoint (f₁ ℓ) = T.constellationPoint (f₁ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₁ ℓ).1, ← m5_mem_redPt_of_mem (hmem₁ ℓ').1, h2]
    exact hshared ℓ ℓ' (hmem₁ ℓ).2 (hmem₂ ℓ).2 (e2 ▸ (hmem₁ ℓ').2) (e1 ▸ (hmem₂ ℓ').2)
  have hdisj : Disjoint (P₀ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G}))
      (P₁ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G})) := by
    rw [Set.disjoint_left]
    rintro p hp₀ hp₁
    obtain ⟨ℓ, -, rfl⟩ := hp₀
    obtain ⟨ℓ', -, heq⟩ := hp₁
    have he : (((f₁ ℓ).first, (f₁ ℓ).second), ((f₂ ℓ).first, (f₂ ℓ).second)) =
        (((f₂ ℓ').first, (f₂ ℓ').second), ((f₁ ℓ').first, (f₁ ℓ').second)) := by
      rw [← heq₀ ℓ, ← heq₁ ℓ']; exact heq.symm
    have h1 : ((f₁ ℓ).first, (f₁ ℓ).second) = ((f₂ ℓ').first, (f₂ ℓ').second) := congrArg Prod.fst he
    have h2 : ((f₂ ℓ).first, (f₂ ℓ).second) = ((f₁ ℓ').first, (f₁ ℓ').second) := congrArg Prod.snd he
    have e1 : T.constellationPoint (f₁ ℓ) = T.constellationPoint (f₂ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₁ ℓ).1, ← m5_mem_redPt_of_mem (hmem₂ ℓ').1, h1]
    have e2 : T.constellationPoint (f₂ ℓ) = T.constellationPoint (f₁ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₂ ℓ).1, ← m5_mem_redPt_of_mem (hmem₁ ℓ').1, h2]
    have hll : ℓ = ℓ' := hshared ℓ ℓ' (hmem₁ ℓ).2 (hmem₂ ℓ).2
      (e1 ▸ (hmem₂ ℓ').2) (e2 ▸ (hmem₁ ℓ').2)
    subst hll
    exact hlab ℓ h1
  have hsub : (P₀ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G}) ∪
      P₁ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G})) ⊆
      {r : (TrisectorLabel × TrisectorLabel) × (TrisectorLabel × TrisectorLabel) |
        r.1 ≠ r.2 ∧ r.1.1 + r.1.2 = r.2.1 + r.2.2} := by
    rintro _ (hp | hp)
    · obtain ⟨ℓ, -, rfl⟩ := hp
      have hv := hval₀ ℓ
      exact ⟨hlab ℓ, hclass ℓ.1 ℓ.2 _ _ hv.1 hv.2⟩
    · obtain ⟨ℓ, -, rfl⟩ := hp
      have hv := hval₁ ℓ
      exact ⟨fun hc => hlab ℓ hc.symm, (hclass ℓ.1 ℓ.2 _ _ hv.2 hv.1).symm⟩
  have hI₀ : (P₀ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G})).ncard = G.ncard := by
    rw [Set.ncard_image_of_injective _ hP₀inj, Set.ncard_univ, ← Nat.card_coe_set_eq]
  have hI₁ : (P₁ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G})).ncard = G.ncard := by
    rw [Set.ncard_image_of_injective _ hP₁inj, Set.ncard_univ, ← Nat.card_coe_set_eq]
  have hunion : ((P₀ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G}) ∪
      P₁ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G}))).ncard = G.ncard + G.ncard := by
    rw [m4_ncard_union_of_disjoint (Set.toFinite _) (Set.toFinite _) hdisj, hI₀, hI₁]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hunion, equalSumPair_ordered_ncard] at hle
  rw [hG] at hle ⊢
  omega



def m1sigma (l : TrisectorLabel) : ℂ := (Circle.exp (-(labelAngle l)) : ℂ)

theorem m1sigma_zero : m1sigma (0 : TrisectorLabel) = 1 := by
  simp [m1sigma, labelAngle]

theorem omega_cubed' : (omega : ℂ) ^ 3 - 1 = 0 := by
  rw [omega_cubed]; ring

theorem omega_sq_neg : (omega : ℂ) ^ 2 = -1 - (omega : ℂ) := by
  linear_combination omega_sum

theorem m1omega_sq_inv : (omega : ℂ) ^ 2 = (omega : ℂ)⁻¹ := by
  have hmul : (omega : ℂ) * (omega : ℂ) ^ 2 = 1 := by
    linear_combination omega_cubed
  exact (inv_eq_of_mul_eq_one_right hmul).symm

theorem omega_four : (omega : ℂ) ^ 4 = (omega : ℂ) := by
  linear_combination ((omega : ℂ) * ((omega : ℂ) - 1)) * omega_sum

theorem omega_five : (omega : ℂ) ^ 5 = (omega : ℂ) ^ 2 := by
  linear_combination ((omega : ℂ) ^ 2 * ((omega : ℂ) - 1)) * omega_sum

theorem m1labelAngle_zero : labelAngle (0 : TrisectorLabel) = 0 := by
  simp [labelAngle]

theorem m1labelAngle_one : labelAngle (1 : TrisectorLabel) = 2 * Real.pi / 3 := by
  have hv : ((1 : TrisectorLabel).val : ℝ) = 1 := by
    have h : ((1 : TrisectorLabel).val) = 1 := by decide
    rw [h]; norm_num
  rw [labelAngle, hv]; ring

theorem m1labelAngle_two : labelAngle (2 : TrisectorLabel) = 4 * Real.pi / 3 := by
  have hv : ((2 : TrisectorLabel).val : ℝ) = 2 := by
    have h : ((2 : TrisectorLabel).val) = 2 := by decide
    rw [h]; norm_num
  rw [labelAngle, hv]; ring

theorem circle_exp_two_pi_three : ((Circle.exp (2 * Real.pi / 3) : Circle) : ℂ) = (omega : ℂ) := rfl

theorem circle_exp_four_pi_three :
    ((Circle.exp (4 * Real.pi / 3) : Circle) : ℂ) = (omega : ℂ) ^ 2 := by
  have h : (4 * Real.pi / 3 : ℝ) = 2 * Real.pi / 3 + 2 * Real.pi / 3 := by ring
  rw [h, Circle.exp_add, Circle.coe_mul, circle_exp_two_pi_three, ← pow_two]

theorem m1sigma_one : m1sigma (1 : TrisectorLabel) = (omega : ℂ) ^ 2 := by
  rw [m1sigma, m1labelAngle_one,
    show (Circle.exp (-(2 * Real.pi / 3)) : ℂ)
      = ((Circle.exp (2 * Real.pi / 3) : Circle) : ℂ)⁻¹ from by
      rw [Circle.exp_neg, Circle.coe_inv],
    circle_exp_two_pi_three]
  exact m1omega_sq_inv.symm

theorem m1sigma_two : m1sigma (2 : TrisectorLabel) = (omega : ℂ) := by
  rw [m1sigma, m1labelAngle_two,
    show (Circle.exp (-(4 * Real.pi / 3)) : ℂ)
      = ((Circle.exp (4 * Real.pi / 3) : Circle) : ℂ)⁻¹ from by
      rw [Circle.exp_neg, Circle.coe_inv],
    circle_exp_four_pi_three]
  have hmul : (omega : ℂ) ^ 2 * (omega : ℂ) = 1 := by
    linear_combination omega_cubed
  exact inv_eq_of_mul_eq_one_right hmul

theorem omega_sq_mul_sq : (omega : ℂ) ^ 2 * (omega : ℂ) ^ 2 = (omega : ℂ) := by
  rw [show (omega : ℂ) ^ 2 * (omega : ℂ) ^ 2 = (omega : ℂ) ^ 3 * (omega : ℂ) from by ring,
    omega_cubed, one_mul]

theorem m1omega_sq_mul : (omega : ℂ) ^ 2 * (omega : ℂ) = 1 := by
  rw [show (omega : ℂ) ^ 2 * (omega : ℂ) = (omega : ℂ) ^ 3 from by ring, omega_cubed]

theorem m1sigma_add_one (l : TrisectorLabel) :
    m1sigma (l + 1) = m1sigma l * (omega : ℂ) ^ 2 := by
  have h : l = 0 ∨ l = 1 ∨ l = 2 := by revert l; decide
  rcases h with rfl | rfl | rfl
  · rw [zero_add, m1sigma_zero, m1sigma_one, one_mul]
  · rw [show (1 : TrisectorLabel) + 1 = 2 from by decide, m1sigma_one, m1sigma_two, omega_sq_mul_sq]
  · rw [show (2 : TrisectorLabel) + 1 = 0 from by decide, m1sigma_two, m1sigma_zero,
      show (omega : ℂ) * (omega : ℂ) ^ 2 = (omega : ℂ) ^ 3 from by ring, omega_cubed]

theorem m1sigma_add_two (l : TrisectorLabel) :
    m1sigma (l + 2) = m1sigma l * (omega : ℂ) := by
  have h : l = 0 ∨ l = 1 ∨ l = 2 := by revert l; decide
  rcases h with rfl | rfl | rfl
  · rw [zero_add, m1sigma_zero, m1sigma_two, one_mul]
  · rw [show (1 : TrisectorLabel) + 2 = 0 from by decide, m1sigma_one, m1sigma_zero, m1omega_sq_mul]
  · rw [show (2 : TrisectorLabel) + 2 = 1 from by decide, m1sigma_two, m1sigma_one]
    ring

/-! ### The exponential factor of `2β - labelAngle i` etc. -/

theorem exp_two_beta_sub (T : OrientedTriangle E o) (i : TrisectorLabel) :
    (Circle.exp (2 * T.beta - labelAngle i) : ℂ)
      = (Circle.exp (2 * T.beta) : ℂ) * m1sigma i := by
  rw [m1sigma, ← Circle.coe_mul, ← Circle.exp_add]
  try congr 1
  try ring

theorem exp_two_gamma_sub (T : OrientedTriangle E o) (i : TrisectorLabel) :
    (Circle.exp (2 * T.gamma - labelAngle i) : ℂ)
      = (Circle.exp (2 * T.gamma) : ℂ) * m1sigma i := by
  rw [m1sigma, ← Circle.coe_mul, ← Circle.exp_add]
  try congr 1
  try ring

theorem exp_two_alpha_sub (T : OrientedTriangle E o) (i : TrisectorLabel) :
    (Circle.exp (2 * T.alpha - labelAngle i) : ℂ)
      = (Circle.exp (2 * T.alpha) : ℂ) * m1sigma i := by
  rw [m1sigma, ← Circle.coe_mul, ← Circle.exp_add]
  try congr 1
  try ring

/-! ### Complex coordinates of the constellation points -/

theorem toComplex_constellationPoint_red (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, i, j⟩) =
      toComplex o T.C + toComplex o (T.B - T.C) *
        ((1 - (Circle.exp (2 * T.beta - labelAngle i) : ℂ)) /
          (1 - (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) *
            (Circle.exp (2 * T.beta - labelAngle i) : ℂ))) := by
  simp [constellationPoint, toComplex_rotationFixedPoint]

theorem toComplex_constellationPoint_green (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.green, i, j⟩) =
      toComplex o T.A + toComplex o (T.C - T.A) *
        ((1 - (Circle.exp (2 * T.gamma - labelAngle i) : ℂ)) /
          (1 - (Circle.exp (2 * T.alpha - labelAngle j) : ℂ) *
            (Circle.exp (2 * T.gamma - labelAngle i) : ℂ))) := by
  simp [constellationPoint, toComplex_rotationFixedPoint]

theorem toComplex_constellationPoint_blue (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.blue, i, j⟩) =
      toComplex o T.B + toComplex o (T.A - T.B) *
        ((1 - (Circle.exp (2 * T.alpha - labelAngle i) : ℂ)) /
          (1 - (Circle.exp (2 * T.beta - labelAngle j) : ℂ) *
            (Circle.exp (2 * T.alpha - labelAngle i) : ℂ))) := by
  simp [constellationPoint, toComplex_rotationFixedPoint]
theorem one_sub_exp_two_ne_of_lt (θ : ℝ) (h1 : 0 < θ) (h2 : θ < Real.pi / 3)
    (s : TrisectorLabel) :
    (1 : ℂ) - (Circle.exp (2 * (θ - labelAngle s / 2)) : ℂ) ≠ 0 := by
  refine m3_one_sub_exp_two_ne (θ - labelAngle s / 2) ?_
  have hs : s = 0 ∨ s = 1 ∨ s = 2 := by revert s; decide
  have hp := Real.pi_pos
  rcases hs with rfl | rfl | rfl
  · rw [m1labelAngle_zero]
    have hz : θ - 0 / 2 = θ := by ring
    rw [hz]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 (by linarith))
  · rw [m1labelAngle_one]
    have hlt : θ - 2 * Real.pi / 3 / 2 < 0 := by linarith
    have hgt : -(Real.pi) < θ - 2 * Real.pi / 3 / 2 := by linarith
    exact ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt hlt hgt)
  · rw [m1labelAngle_two]
    have hlt : θ - 4 * Real.pi / 3 / 2 < 0 := by linarith
    have hgt : -(Real.pi) < θ - 4 * Real.pi / 3 / 2 := by linarith
    exact ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt hlt hgt)

theorem beta_add_gamma_bounds (T : OrientedTriangle E o) :
    0 < T.beta + T.gamma ∧ T.beta + T.gamma < Real.pi / 3 := by
  have h := T.angle_sum
  have ha := m3_alpha_pos T
  have hb := m3_beta_pos T
  have hg := m3_gamma_pos T
  constructor <;> linarith

theorem gamma_add_alpha_bounds (T : OrientedTriangle E o) :
    0 < T.gamma + T.alpha ∧ T.gamma + T.alpha < Real.pi / 3 := by
  have h := T.angle_sum
  have ha := m3_alpha_pos T
  have hb := m3_beta_pos T
  have hg := m3_gamma_pos T
  constructor <;> linarith

theorem alpha_add_beta_bounds (T : OrientedTriangle E o) :
    0 < T.alpha + T.beta ∧ T.alpha + T.beta < Real.pi / 3 := by
  have h := T.angle_sum
  have ha := m3_alpha_pos T
  have hb := m3_beta_pos T
  have hg := m3_gamma_pos T
  constructor <;> linarith

theorem red_den_ne (T : OrientedTriangle E o) (s : TrisectorLabel) :
    (1 : ℂ) - (Circle.exp (2 * T.beta) : ℂ) * (Circle.exp (2 * T.gamma) : ℂ) * m1sigma s ≠ 0 := by
  obtain ⟨h1, h2⟩ := beta_add_gamma_bounds T
  have e : (Circle.exp (2 * T.beta) : ℂ) * (Circle.exp (2 * T.gamma) : ℂ) * m1sigma s
      = (Circle.exp (2 * (T.beta + T.gamma - labelAngle s / 2)) : ℂ) := by
    rw [m1sigma, ← Circle.coe_mul, ← Circle.exp_add, ← Circle.coe_mul, ← Circle.exp_add,
      show 2 * T.beta + 2 * T.gamma + -(labelAngle s) = 2 * (T.beta + T.gamma - labelAngle s / 2) from by ring]
  rw [e]
  exact one_sub_exp_two_ne_of_lt (T.beta + T.gamma) h1 h2 s

theorem green_den_ne (T : OrientedTriangle E o) (s : TrisectorLabel) :
    (1 : ℂ) - (Circle.exp (2 * T.alpha) : ℂ) * (Circle.exp (2 * T.gamma) : ℂ) * m1sigma s ≠ 0 := by
  obtain ⟨h1, h2⟩ := gamma_add_alpha_bounds T
  have e : (Circle.exp (2 * T.alpha) : ℂ) * (Circle.exp (2 * T.gamma) : ℂ) * m1sigma s
      = (Circle.exp (2 * (T.alpha + T.gamma - labelAngle s / 2)) : ℂ) := by
    rw [m1sigma, ← Circle.coe_mul, ← Circle.exp_add, ← Circle.coe_mul, ← Circle.exp_add,
      show 2 * T.alpha + 2 * T.gamma + -(labelAngle s) = 2 * (T.alpha + T.gamma - labelAngle s / 2) from by ring]
  rw [e]
  exact one_sub_exp_two_ne_of_lt (T.alpha + T.gamma) (by linarith) (by linarith) s

theorem blue_den_ne (T : OrientedTriangle E o) (s : TrisectorLabel) :
    (1 : ℂ) - (Circle.exp (2 * T.beta) : ℂ) * (Circle.exp (2 * T.alpha) : ℂ) * m1sigma s ≠ 0 := by
  obtain ⟨h1, h2⟩ := alpha_add_beta_bounds T
  have e : (Circle.exp (2 * T.beta) : ℂ) * (Circle.exp (2 * T.alpha) : ℂ) * m1sigma s
      = (Circle.exp (2 * (T.beta + T.alpha - labelAngle s / 2)) : ℂ) := by
    rw [m1sigma, ← Circle.coe_mul, ← Circle.exp_add, ← Circle.coe_mul, ← Circle.exp_add,
      show 2 * T.beta + 2 * T.alpha + -(labelAngle s) = 2 * (T.beta + T.alpha - labelAngle s / 2) from by ring]
  rw [e]
  exact one_sub_exp_two_ne_of_lt (T.beta + T.alpha) (by linarith) (by linarith) s


/-! ## The sum-class structure of the constellation points

With `P = exp (2 i β)`, `Q = exp (2 i γ)`, `R = exp (2 i α)` and `σ l = exp (-i · labelAngle l)`,
every constellation point is an affine function of two reference vertices whose denominator
depends on `i + j` only.  Two points of the same colour with the same label sum `i + j = s`
therefore differ by the fixed vector `(ref - base) · (P or Q or R) · (σ i' - σ i) / (1 - … σ s)`.
This is the algebraic content of the "equal label sum" classification behind the nine guide
lines: the join of two same-coloured constellation points with equal label sum is parallel to a
vector that depends on the labels alone, never on the shape of `ABC`. -/

theorem m1sigma_mul (i j : TrisectorLabel) : m1sigma (i + j) = m1sigma i * m1sigma j := by
  obtain h | h | h := zmod3_cases j
  · rw [h, add_zero, m1sigma_zero, mul_one]
  · rw [h, m1sigma_add_one, m1sigma_one]
  · rw [h, m1sigma_add_two, m1sigma_two]

theorem m1sigma_mul' (i j : TrisectorLabel) : m1sigma i * m1sigma j = m1sigma (i + j) :=
  (m1sigma_mul i j).symm

/-- `P = exp (2 i β)`. -/
def m1P (T : OrientedTriangle E o) : ℂ := (Circle.exp (2 * T.beta) : ℂ)
/-- `Q = exp (2 i γ)`. -/
def m1Q (T : OrientedTriangle E o) : ℂ := (Circle.exp (2 * T.gamma) : ℂ)
/-- `R = exp (2 i α)`. -/
def m1R (T : OrientedTriangle E o) : ℂ := (Circle.exp (2 * T.alpha) : ℂ)

/-- `exp (2 i α) · exp (2 i β) · exp (2 i γ) = ω`, since `α + β + γ = π/3`. -/
theorem m1_PQR (T : OrientedTriangle E o) : m1P T * m1Q T * m1R T = (omega : ℂ) := by
  have h2 : T.beta + T.gamma + T.alpha = Real.pi / 3 := by
    have h := T.angle_sum; linarith
  have hPQ : m1P T * m1Q T = (Circle.exp (2 * T.beta + 2 * T.gamma) : ℂ) := by
    rw [m1P, m1Q, ← Circle.coe_mul, ← Circle.exp_add]
  calc m1P T * m1Q T * m1R T
      = (Circle.exp (2 * T.beta + 2 * T.gamma) : ℂ) * m1R T := by rw [hPQ]
    _ = (Circle.exp (2 * T.beta + 2 * T.gamma + 2 * T.alpha) : ℂ) := by
        rw [m1R, ← Circle.coe_mul, ← Circle.exp_add]
    _ = (Circle.exp (2 * (T.beta + T.gamma + T.alpha)) : ℂ) := by
        rw [show 2 * T.beta + 2 * T.gamma + 2 * T.alpha
          = 2 * (T.beta + T.gamma + T.alpha) from by ring]
    _ = (Circle.exp (2 * (Real.pi / 3)) : ℂ) := by rw [h2]
    _ = (omega : ℂ) := by rw [omega]; congr 2; ring

theorem m1P_ne_zero (T : OrientedTriangle E o) : m1P T ≠ 0 := by
  simp only [m1P]; exact Circle.coe_ne_zero _

theorem m1Q_ne_zero (T : OrientedTriangle E o) : m1Q T ≠ 0 := by
  simp only [m1Q]; exact Circle.coe_ne_zero _

theorem m1R_ne_zero (T : OrientedTriangle E o) : m1R T ≠ 0 := by
  simp only [m1R]; exact Circle.coe_ne_zero _

/-! ### The three sum-class normal forms -/

/-- Red normal form: the denominator only sees the label sum `i + j`. -/
theorem m1_red_nf (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, i, j⟩) =
      toComplex o T.C + toComplex o (T.B - T.C) *
        ((1 - m1P T * m1sigma i) / (1 - m1P T * m1Q T * m1sigma (i + j))) := by
  rw [toComplex_constellationPoint_red T i j, exp_two_gamma_sub, exp_two_beta_sub]
  have h : (Circle.exp (2 * T.gamma) : ℂ) * m1sigma j * ((Circle.exp (2 * T.beta) : ℂ) * m1sigma i)
      = (Circle.exp (2 * T.beta) : ℂ) * (Circle.exp (2 * T.gamma) : ℂ) * m1sigma (i + j) := by
    rw [m1sigma_mul]; ring
  rw [h]
  rfl

/-- Green normal form. -/
theorem m1_green_nf (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.green, i, j⟩) =
      toComplex o T.A + toComplex o (T.C - T.A) *
        ((1 - m1Q T * m1sigma i) / (1 - m1Q T * m1R T * m1sigma (i + j))) := by
  rw [toComplex_constellationPoint_green T i j, exp_two_gamma_sub, exp_two_alpha_sub]
  have h : (Circle.exp (2 * T.alpha) : ℂ) * m1sigma j * ((Circle.exp (2 * T.gamma) : ℂ) * m1sigma i)
      = (Circle.exp (2 * T.gamma) : ℂ) * (Circle.exp (2 * T.alpha) : ℂ) * m1sigma (i + j) := by
    rw [m1sigma_mul]; ring
  rw [h]
  rfl

/-- Blue normal form. -/
theorem m1_blue_nf (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.blue, i, j⟩) =
      toComplex o T.B + toComplex o (T.A - T.B) *
        ((1 - m1R T * m1sigma i) / (1 - m1R T * m1P T * m1sigma (i + j))) := by
  rw [toComplex_constellationPoint_blue T i j, exp_two_alpha_sub, exp_two_beta_sub]
  have h : (Circle.exp (2 * T.beta) : ℂ) * m1sigma j * ((Circle.exp (2 * T.alpha) : ℂ) * m1sigma i)
      = (Circle.exp (2 * T.alpha) : ℂ) * (Circle.exp (2 * T.beta) : ℂ) * m1sigma (i + j) := by
    rw [m1sigma_mul]; ring
  rw [h]
  rfl

/-! ### Nonvanishing of the class denominators -/

theorem m1_red_den_ne (T : OrientedTriangle E o) (s : TrisectorLabel) :
    (1 : ℂ) - m1P T * m1Q T * m1sigma s ≠ 0 := by
  simpa only [m1P, m1Q] using red_den_ne T s

theorem m1_green_den_ne (T : OrientedTriangle E o) (s : TrisectorLabel) :
    (1 : ℂ) - m1Q T * m1R T * m1sigma s ≠ 0 := by
  have h := green_den_ne T s
  have e : (1 : ℂ) - m1Q T * m1R T * m1sigma s
      = (1 : ℂ) - (Circle.exp (2 * T.alpha) : ℂ) * (Circle.exp (2 * T.gamma) : ℂ) * m1sigma s := by
    simp only [m1Q, m1R]; ring
  rw [e]; exact h

theorem m1_blue_den_ne (T : OrientedTriangle E o) (s : TrisectorLabel) :
    (1 : ℂ) - m1R T * m1P T * m1sigma s ≠ 0 := by
  have h := blue_den_ne T s
  have e : (1 : ℂ) - m1R T * m1P T * m1sigma s
      = (1 : ℂ) - (Circle.exp (2 * T.beta) : ℂ) * (Circle.exp (2 * T.alpha) : ℂ) * m1sigma s := by
    simp only [m1R, m1P]; ring
  rw [e]; exact h

/-! ### The sum-class difference formulas -/

theorem m1_red_class_diff (T : OrientedTriangle E o) (i j i' j' : TrisectorLabel)
    (hs : i + j = i' + j') :
    toComplex o (T.constellationPoint ⟨.red, i, j⟩) -
        toComplex o (T.constellationPoint ⟨.red, i', j'⟩) =
      toComplex o (T.B - T.C) * m1P T * (m1sigma i' - m1sigma i) /
        (1 - m1P T * m1Q T * m1sigma (i + j)) := by
  rw [m1_red_nf, m1_red_nf, ← hs]
  have hd : (1 : ℂ) - m1P T * m1Q T * m1sigma (i' + j') ≠ 0 := by
    rw [← hs]; exact m1_red_den_ne T _
  field_simp
  ring

theorem m1_green_class_diff (T : OrientedTriangle E o) (i j i' j' : TrisectorLabel)
    (hs : i + j = i' + j') :
    toComplex o (T.constellationPoint ⟨.green, i, j⟩) -
        toComplex o (T.constellationPoint ⟨.green, i', j'⟩) =
      toComplex o (T.C - T.A) * m1Q T * (m1sigma i' - m1sigma i) /
        (1 - m1Q T * m1R T * m1sigma (i + j)) := by
  rw [m1_green_nf, m1_green_nf, ← hs]
  have hd : (1 : ℂ) - m1Q T * m1R T * m1sigma (i' + j') ≠ 0 := by
    rw [← hs]; exact m1_green_den_ne T _
  field_simp
  ring

theorem m1_blue_class_diff (T : OrientedTriangle E o) (i j i' j' : TrisectorLabel)
    (hs : i + j = i' + j') :
    toComplex o (T.constellationPoint ⟨.blue, i, j⟩) -
        toComplex o (T.constellationPoint ⟨.blue, i', j'⟩) =
      toComplex o (T.A - T.B) * m1R T * (m1sigma i' - m1sigma i) /
        (1 - m1R T * m1P T * m1sigma (i + j)) := by
  rw [m1_blue_nf, m1_blue_nf, ← hs]
  have hd : (1 : ℂ) - m1R T * m1P T * m1sigma (i' + j') ≠ 0 := by
    rw [← hs]; exact m1_blue_den_ne T _
  field_simp
  ring

/-! ### The three joins of a sum class are the sides of an equilateral triangle

For a fixed label sum `s` the three same-coloured points `⟨c, 0, s⟩`, `⟨c, 1, s-1⟩`,
`⟨c, 2, s-2⟩` are the vertices of `monochromeTriangle c s`, which is equilateral
(`monochrome_equilateral`).  Hence the nine equal-sum joins are exactly the sides of the nine
monochrome equilateral triangles. -/

theorem m1_equilateral_cycle {P Q R : E} (h : Equilateral P Q R) : Equilateral Q R P :=
  ⟨h.2, h.2.symm.trans h.1.symm⟩

theorem m1_equilateral_cycle' {P Q R : E} (h : Equilateral P Q R) : Equilateral R P Q :=
  ⟨h.2.symm.trans h.1.symm, h.1⟩

theorem m1_red_class_equilateral (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (s : TrisectorLabel) :
    Equilateral (T.constellationPoint ⟨.red, 0, s⟩) (T.constellationPoint ⟨.red, 1, s - 1⟩)
      (T.constellationPoint ⟨.red, 2, s - 2⟩) := by
  obtain hs | hs | hs := zmod3_cases s
  · rw [hs]
    have h1 := monochrome_equilateral T h .red 0
    simp only [monochromeTriangle] at h1
    rw [show (0 + (1 : TrisectorLabel)) = 1 from by decide,
        show (0 + (2 : TrisectorLabel)) = 2 from by decide] at h1
    rw [show ((0 : TrisectorLabel) - 1) = 2 from by decide,
        show ((0 : TrisectorLabel) - 2) = 1 from by decide]
    exact h1
  · rw [hs]
    have h1 := monochrome_equilateral T h .red 1
    simp only [monochromeTriangle] at h1
    rw [show (1 + (1 : TrisectorLabel)) = 2 from by decide,
        show (1 + (2 : TrisectorLabel)) = 0 from by decide] at h1
    rw [show ((1 : TrisectorLabel) - 1) = 0 from by decide,
        show ((1 : TrisectorLabel) - 2) = 2 from by decide]
    exact m1_equilateral_cycle' h1
  · rw [hs]
    have h1 := monochrome_equilateral T h .red 2
    simp only [monochromeTriangle] at h1
    rw [show (2 + (1 : TrisectorLabel)) = 0 from by decide,
        show (2 + (2 : TrisectorLabel)) = 1 from by decide] at h1
    rw [show ((2 : TrisectorLabel) - 1) = 1 from by decide,
        show ((2 : TrisectorLabel) - 2) = 0 from by decide]
    exact m1_equilateral_cycle h1

theorem m1_green_class_equilateral (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (s : TrisectorLabel) :
    Equilateral (T.constellationPoint ⟨.green, 0, s⟩) (T.constellationPoint ⟨.green, 1, s - 1⟩)
      (T.constellationPoint ⟨.green, 2, s - 2⟩) := by
  obtain hs | hs | hs := zmod3_cases s
  · rw [hs]
    have h1 := monochrome_equilateral T h .green 0
    simp only [monochromeTriangle] at h1
    rw [show (0 + (1 : TrisectorLabel)) = 1 from by decide,
        show (0 + (2 : TrisectorLabel)) = 2 from by decide] at h1
    rw [show ((0 : TrisectorLabel) - 1) = 2 from by decide,
        show ((0 : TrisectorLabel) - 2) = 1 from by decide]
    exact h1
  · rw [hs]
    have h1 := monochrome_equilateral T h .green 1
    simp only [monochromeTriangle] at h1
    rw [show (1 + (1 : TrisectorLabel)) = 2 from by decide,
        show (1 + (2 : TrisectorLabel)) = 0 from by decide] at h1
    rw [show ((1 : TrisectorLabel) - 1) = 0 from by decide,
        show ((1 : TrisectorLabel) - 2) = 2 from by decide]
    exact m1_equilateral_cycle' h1
  · rw [hs]
    have h1 := monochrome_equilateral T h .green 2
    simp only [monochromeTriangle] at h1
    rw [show (2 + (1 : TrisectorLabel)) = 0 from by decide,
        show (2 + (2 : TrisectorLabel)) = 1 from by decide] at h1
    rw [show ((2 : TrisectorLabel) - 1) = 1 from by decide,
        show ((2 : TrisectorLabel) - 2) = 0 from by decide]
    exact m1_equilateral_cycle h1

theorem m1_blue_class_equilateral (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (s : TrisectorLabel) :
    Equilateral (T.constellationPoint ⟨.blue, 0, s⟩) (T.constellationPoint ⟨.blue, 1, s - 1⟩)
      (T.constellationPoint ⟨.blue, 2, s - 2⟩) := by
  obtain hs | hs | hs := zmod3_cases s
  · rw [hs]
    have h1 := monochrome_equilateral T h .blue 0
    simp only [monochromeTriangle] at h1
    rw [show (0 + (1 : TrisectorLabel)) = 1 from by decide,
        show (0 + (2 : TrisectorLabel)) = 2 from by decide] at h1
    rw [show ((0 : TrisectorLabel) - 1) = 2 from by decide,
        show ((0 : TrisectorLabel) - 2) = 1 from by decide]
    exact h1
  · rw [hs]
    have h1 := monochrome_equilateral T h .blue 1
    simp only [monochromeTriangle] at h1
    rw [show (1 + (1 : TrisectorLabel)) = 2 from by decide,
        show (1 + (2 : TrisectorLabel)) = 0 from by decide] at h1
    rw [show ((1 : TrisectorLabel) - 1) = 0 from by decide,
        show ((1 : TrisectorLabel) - 2) = 2 from by decide]
    exact m1_equilateral_cycle' h1
  · rw [hs]
    have h1 := monochrome_equilateral T h .blue 2
    simp only [monochromeTriangle] at h1
    rw [show (2 + (1 : TrisectorLabel)) = 0 from by decide,
        show (2 + (2 : TrisectorLabel)) = 1 from by decide] at h1
    rw [show ((2 : TrisectorLabel) - 1) = 1 from by decide,
        show ((2 : TrisectorLabel) - 2) = 0 from by decide]
    exact m1_equilateral_cycle h1


/-- The three same-class points are pairwise distinct, so every equal-sum pair spans a line. -/
theorem m1_red_class_point_ne (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) {s : TrisectorLabel} {i i' : TrisectorLabel}
    (hii : i ≠ i') :
    T.constellationPoint ⟨.red, i, s - i⟩ ≠ T.constellationPoint ⟨.red, i', s - i'⟩ := by
  intro hc
  have hidx : (⟨.red, i, s - i⟩ : ConstellationIndex) = ⟨.red, i', s - i'⟩ := h hc
  exact hii (by simpa using congrArg ConstellationIndex.first hidx)

/-- **The class-ratio lemma (red).**  For a fixed label sum the quotient of two equal-sum joins is
a constant of the label algebra: the complex number `σ 2 - σ 0` normalises both.  It therefore
never involves the shape of `ABC`, and all three joins of a sum class are determined by one. -/
theorem m1_red_class_ratio (T : OrientedTriangle E o) (i j i' j' s : TrisectorLabel)
    (h1 : i + j = s) (h2 : i' + j' = s) :
    (toComplex o (T.constellationPoint ⟨.red, i, j⟩) -
        toComplex o (T.constellationPoint ⟨.red, i', j'⟩)) *
      (m1sigma 2 - m1sigma 0) =
    (toComplex o (T.constellationPoint ⟨.red, 0, s⟩) -
        toComplex o (T.constellationPoint ⟨.red, 2, s - 2⟩)) *
      (m1sigma i' - m1sigma i) := by
  have hA := m1_red_class_diff T i j i' j' (by rw [h1, h2])
  have hB := m1_red_class_diff T 0 s 2 (s - 2) (by rw [zero_add]; abel)
  rw [hA, hB, h1]
  rw [zero_add]
  field_simp

/-- Class-ratio lemma (green). -/
theorem m1_green_class_ratio (T : OrientedTriangle E o) (i j i' j' s : TrisectorLabel)
    (h1 : i + j = s) (h2 : i' + j' = s) :
    (toComplex o (T.constellationPoint ⟨.green, i, j⟩) -
        toComplex o (T.constellationPoint ⟨.green, i', j'⟩)) *
      (m1sigma 2 - m1sigma 0) =
    (toComplex o (T.constellationPoint ⟨.green, 0, s⟩) -
        toComplex o (T.constellationPoint ⟨.green, 2, s - 2⟩)) *
      (m1sigma i' - m1sigma i) := by
  have hA := m1_green_class_diff T i j i' j' (by rw [h1, h2])
  have hB := m1_green_class_diff T 0 s 2 (s - 2) (by rw [zero_add]; abel)
  rw [hA, hB, h1]
  rw [zero_add]
  field_simp

/-- Class-ratio lemma (blue). -/
theorem m1_blue_class_ratio (T : OrientedTriangle E o) (i j i' j' s : TrisectorLabel)
    (h1 : i + j = s) (h2 : i' + j' = s) :
    (toComplex o (T.constellationPoint ⟨.blue, i, j⟩) -
        toComplex o (T.constellationPoint ⟨.blue, i', j'⟩)) *
      (m1sigma 2 - m1sigma 0) =
    (toComplex o (T.constellationPoint ⟨.blue, 0, s⟩) -
        toComplex o (T.constellationPoint ⟨.blue, 2, s - 2⟩)) *
      (m1sigma i' - m1sigma i) := by
  have hA := m1_blue_class_diff T i j i' j' (by rw [h1, h2])
  have hB := m1_blue_class_diff T 0 s 2 (s - 2) (by rw [zero_add]; abel)
  rw [hA, hB, h1]
  rw [zero_add]
  field_simp

/-! ### The scalar identities behind the direction of the equal-sum joins -/

theorem m1_exp_mul (a b : ℝ) :
    (Circle.exp a : ℂ) * (Circle.exp b : ℂ) = (Circle.exp (a + b) : ℂ) := by
  rw [← Circle.coe_mul, Circle.exp_add]

/-- Merge two exponentials separated by a complex factor. -/
theorem m1_exp_left_one (a b : ℝ) (w : ℂ) :
    (Circle.exp a : ℂ) * (w * (Circle.exp b : ℂ)) = w * (Circle.exp (a + b) : ℂ) := by
  rw [← m1_exp_mul]; ring

/-- Merge two exponentials separated by arbitrary complex coefficients. -/
theorem m1_exp_left (a b : ℝ) (z w : ℂ) :
    z * (Circle.exp a : ℂ) * (w * (Circle.exp b : ℂ)) = z * w * (Circle.exp (a + b) : ℂ) := by
  rw [← m1_exp_mul]; ring

/-- `1 - e^{2iθ} = -2i e^{iθ} sin θ`. -/
theorem m1_one_sub_exp_two (θ : ℝ) :
    (1 : ℂ) - (Circle.exp (2 * θ) : ℂ) =
      -(2 * Complex.I) * (Circle.exp θ : ℂ) * (Real.sin θ : ℂ) := by
  have hu : (Circle.exp θ : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hexp : (Circle.exp (2 * θ) : ℂ) = (Circle.exp θ : ℂ) * (Circle.exp θ : ℂ) := by
    rw [m1_exp_mul, show θ + θ = 2 * θ from by ring]
  have hinv : ((Circle.exp θ : ℂ))⁻¹ = (Circle.exp (-θ) : ℂ) := by
    rw [← Circle.coe_inv, ← Circle.exp_neg]
  have hdiff : (Circle.exp θ : ℂ) - (Circle.exp (-θ) : ℂ) = 2 * Complex.I * (Real.sin θ : ℂ) := by
    have hp : (Circle.exp θ : ℂ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := m6_circle_exp_eq θ
    have hn : (Circle.exp (-θ) : ℂ) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
      rw [m6_circle_exp_eq (-θ), Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    rw [hp, hn]; ring
  rw [hexp]
  have hstep : (1 : ℂ) - (Circle.exp θ : ℂ) * (Circle.exp θ : ℂ)
      = -((Circle.exp θ : ℂ) * ((Circle.exp θ : ℂ) - ((Circle.exp θ : ℂ))⁻¹)) := by
    rw [mul_sub, mul_inv_cancel₀ hu]
    ring
  rw [hstep, hinv, hdiff]
  ring

/-- `σ 2 - σ 0 = √3 · i · e^{iπ/3}`. -/
theorem m1_sigma_two_sub_zero :
    m1sigma (2 : TrisectorLabel) - m1sigma (0 : TrisectorLabel)
      = (Real.sqrt 3 : ℂ) * Complex.I * (Circle.exp (Real.pi / 3) : ℂ) := by
  have h := m1_one_sub_exp_two (Real.pi / 3)
  have h2 : (Circle.exp (2 * (Real.pi / 3)) : ℂ) = (omega : ℂ) := by
    rw [show 2 * (Real.pi / 3) = 2 * Real.pi / 3 from by ring]
    rfl
  rw [h2] at h
  have hsqrt : (2 : ℂ) * (Real.sin (Real.pi / 3) : ℂ) = (Real.sqrt 3 : ℂ) := by
    rw [Real.sin_pi_div_three]; push_cast; ring
  rw [m1sigma_two, m1sigma_zero]
  linear_combination -h + (Circle.exp (Real.pi / 3) : ℂ) * Complex.I * hsqrt

/-- The class-0 key: `P (σ 2 - σ 0)` is the real number `-√3/(2 sin (β+γ))` times the unit
`e^{i(α+2β)}` of the Morley side `Y - X`, times the class-0 denominator. -/
theorem m1_class_zero_key (T : OrientedTriangle E o) :
    m1P T * (m1sigma (2 : TrisectorLabel) - m1sigma (0 : TrisectorLabel)) =
      -(((Real.sqrt 3 / (2 * Real.sin (T.beta + T.gamma)) : ℝ)) : ℂ)
          * (Circle.exp (T.alpha + 2 * T.beta) : ℂ)
          * (1 - m1P T * m1Q T * m1sigma (0 : TrisectorLabel)) := by
  have hsin : Real.sin (T.beta + T.gamma) ≠ 0 := T.m6_sin_beta_add_gamma_ne_zero
  have hPQ : m1P T * m1Q T * m1sigma (0 : TrisectorLabel)
      = (Circle.exp (2 * (T.beta + T.gamma)) : ℂ) := by
    rw [m1sigma_zero, mul_one, m1P, m1Q, m1_exp_mul,
      show 2 * T.beta + 2 * T.gamma = 2 * (T.beta + T.gamma) from by ring]
  have hang : T.alpha + 2 * T.beta = (2 * T.beta + Real.pi / 3) - (T.beta + T.gamma) := by
    have h := T.angle_sum; linear_combination (1/3) * h
  have hang2 : T.alpha + 3 * T.beta + T.gamma = 2 * T.beta + Real.pi / 3 := by
    have h := T.angle_sum; linear_combination (1/3) * h
  have hsum : (2 * T.beta + Real.pi / 3) - (T.beta + T.gamma) + (T.beta + T.gamma)
      = 2 * T.beta + Real.pi / 3 := by ring
  have hL : m1P T * (m1sigma (2 : TrisectorLabel) - m1sigma (0 : TrisectorLabel))
      = (Real.sqrt 3 : ℂ) * Complex.I * (Circle.exp (2 * T.beta + Real.pi / 3) : ℂ) := by
    rw [m1_sigma_two_sub_zero, m1P]
    rw [m1_exp_left_one]
  have hR : -(((Real.sqrt 3 / (2 * Real.sin (T.beta + T.gamma)) : ℝ)) : ℂ)
        * (Circle.exp (T.alpha + 2 * T.beta) : ℂ)
        * (1 - m1P T * m1Q T * m1sigma (0 : TrisectorLabel))
      = (Real.sqrt 3 : ℂ) * Complex.I * (Circle.exp (2 * T.beta + Real.pi / 3) : ℂ) := by
    rw [hPQ, m1_one_sub_exp_two, hang]
    rw [show -(2 * Complex.I) * (Circle.exp (T.beta + T.gamma) : ℂ)
        * (Real.sin (T.beta + T.gamma) : ℂ)
        = (-(2 * Complex.I) * (Real.sin (T.beta + T.gamma) : ℂ))
          * (Circle.exp (T.beta + T.gamma) : ℂ) from by ring]
    rw [m1_exp_left, hsum]
    push_cast
    field_simp
    have hsinC : Complex.sin ((T.beta : ℂ) + (T.gamma : ℂ)) ≠ 0 := by
      have h1 : ((T.beta : ℂ) + (T.gamma : ℂ)) = ((T.beta + T.gamma : ℝ) : ℂ) := by push_cast; ring
      rw [h1, ← Complex.ofReal_sin]
      exact_mod_cast hsin
    exact mul_inv_cancel₀ hsinC
  rw [hL, hR]

/-! ### The class-0 join through the Morley vertices is parallel to the Morley side `XY`

`red(0,0) = X`, and the join of `X` with the second point `red(2,1)` of its sum class is
parallel to `Y - X`.  This is the first of the nine direction claims behind `guideLines`. -/

theorem m1_toComplex_B_sub_C (T : OrientedTriangle E o) :
    toComplex o (T.B - T.C) = -((T.aLength : ℝ) : ℂ) * toComplex o T.aStar := by
  have h1 : T.B - T.C = -T.a := by rw [a]; abel
  rw [h1, a_eq, toComplex_neg, toComplex_smul]
  ring

theorem m1_join_red00_red21_parallel (T : OrientedTriangle E o) :
    Parallel (T.constellationPoint ⟨.red, 0, 0⟩ - T.constellationPoint ⟨.red, 2, 1⟩) (T.Y - T.X) := by
  have hsin : Real.sin (T.beta + T.gamma) ≠ 0 := T.m6_sin_beta_add_gamma_ne_zero
  have haL : T.aLength ≠ 0 := by
    rw [aLength]; exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr T.B_ne_C.symm)
  have hdelta : T.delta ≠ 0 := ne_of_gt (m7_delta_pos T)
  have hsa : Real.sin T.alpha ≠ 0 := ne_of_gt (m7_sin_alpha_pos T)
  have hsb : Real.sin T.beta ≠ 0 := ne_of_gt (m7_sin_beta_pos T)
  have hsg : Real.sin T.gamma ≠ 0 := ne_of_gt (m7_sin_gamma_pos T)
  have hsqrt : (Real.sqrt 3 : ℝ) ≠ 0 := by positivity
  refine ⟨4 * (T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) /
      (T.aLength * (Real.sqrt 3 / (2 * Real.sin (T.beta + T.gamma)))), ?_⟩
  apply toComplex_injective o
  rw [toComplex_smul, toComplex_sub, toComplex_sub,
    m1_red_class_diff T 0 0 2 1 (by decide),
    show ((0 : TrisectorLabel) + 0) = 0 from by decide]
  rw [show toComplex o T.Y - toComplex o T.X = toComplex o (T.Y - T.X) from by rw [toComplex_sub],
    Y_sub_X, toComplex_smul, toComplex_rotateVector, m1_toComplex_B_sub_C]
  have hD : (1 : ℂ) - m1P T * m1Q T * m1sigma (0 : TrisectorLabel) ≠ 0 := m1_red_den_ne T 0
  have hkey : m1P T * (m1sigma (2 : TrisectorLabel) - m1sigma 0)
        / (1 - m1P T * m1Q T * m1sigma 0)
      = -(((Real.sqrt 3 / (2 * Real.sin (T.beta + T.gamma)) : ℝ)) : ℂ)
          * (Circle.exp (T.alpha + 2 * T.beta) : ℂ) := by
    rw [div_eq_iff hD]
    exact m1_class_zero_key T
  rw [show -((T.aLength : ℝ) : ℂ) * toComplex o T.aStar * m1P T
        * (m1sigma (2 : TrisectorLabel) - m1sigma 0)
        / (1 - m1P T * m1Q T * m1sigma (0 : TrisectorLabel))
      = -((T.aLength : ℝ) : ℂ) * toComplex o T.aStar *
          (m1P T * (m1sigma (2 : TrisectorLabel) - m1sigma 0)
            / (1 - m1P T * m1Q T * m1sigma 0)) from by ring]
  rw [hkey]
  have hsinC : Complex.sin ((T.beta : ℂ) + (T.gamma : ℂ)) ≠ 0 := by
    have h1 : ((T.beta : ℂ) + (T.gamma : ℂ)) = ((T.beta + T.gamma : ℝ) : ℂ) := by push_cast; ring
    rw [h1, ← Complex.ofReal_sin]
    exact_mod_cast hsin
  have haLC : ((T.aLength : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact haL
  push_cast
  field_simp

theorem m8_omega_sq : (omega : ℂ) ^ 2 = -1 - (omega : ℂ) := by
  linear_combination omega_sum

theorem m8_omega_ne_zero : (omega : ℂ) ≠ 0 := by
  intro h0
  have h3 := omega_cubed
  rw [h0] at h3
  norm_num at h3

theorem m8_omega_im_pos : 0 < (omega : ℂ).im := w9_omega_im_pos

theorem m8_weighted_diffs {p q r : ℂ}
    (h : p + (omega : ℂ) * q + (omega : ℂ) ^ 2 * r = 0) :
    r - q = (omega : ℂ) * (q - p) ∧ p - r = (omega : ℂ) ^ 2 * (q - p) := by
  have hsq := m8_omega_sq
  have hr0 : (omega : ℂ) ^ 2 * r = -(p + (omega : ℂ) * q) := by linear_combination h
  have hr : r = -((omega : ℂ) * p) - (omega : ℂ) ^ 2 * q := by
    have hmul : (omega : ℂ) * ((omega : ℂ) ^ 2 * r) =
        (omega : ℂ) * (-(p + (omega : ℂ) * q)) := by rw [hr0]
    have h3 : (omega : ℂ) * ((omega : ℂ) ^ 2 * r) = r := by
      rw [← mul_assoc, show (omega : ℂ) * (omega : ℂ) ^ 2 = (omega : ℂ) ^ 3 by ring,
        omega_cubed, one_mul]
    rw [h3] at hmul
    rw [hmul]; ring
  constructor
  · rw [hr, hsq]; ring
  · rw [hr, hsq]; ring

theorem m8_weighted_norms {p q r : ℂ}
    (h : p + (omega : ℂ) * q + (omega : ℂ) ^ 2 * r = 0) :
    ‖q - p‖ = ‖r - q‖ ∧ ‖r - q‖ = ‖p - r‖ := by
  obtain ⟨h1, h2⟩ := m8_weighted_diffs h
  constructor
  · rw [h1, norm_mul, omega_norm_one, one_mul]
  · rw [h1, h2, norm_mul, norm_mul, omega_norm_one, omega_sq_norm_one, one_mul]

theorem m8_weighted_area {p q r : ℂ}
    (h : p + (omega : ℂ) * q + (omega : ℂ) ^ 2 * r = 0) :
    (conj (q - p) * (r - p)).im = (omega : ℂ).im * ‖q - p‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := m8_weighted_diffs h
  have hrp : r - p = -((omega : ℂ) ^ 2 * (q - p)) := by
    rw [← h2]; ring
  have ht : conj (q - p) * (q - p) = ((‖q - p‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.sq_norm]
  have hval : conj (q - p) * (r - p) =
      -((omega : ℂ) ^ 2 * ((‖q - p‖ ^ 2 : ℝ) : ℂ)) := by
    rw [hrp, ← ht]; ring
  have him : ((omega : ℂ) ^ 2).im = -((omega : ℂ).im) := by
    rw [m8_omega_sq]; simp
  rw [hval, Complex.neg_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, him]
  ring

theorem m8_weighted_pos {p q r : ℂ}
    (h : p + (omega : ℂ) * q + (omega : ℂ) ^ 2 * r = 0) (hne : q ≠ p) :
    0 < (conj (q - p) * (r - p)).im := by
  rw [m8_weighted_area h]
  have h1 : (0 : ℝ) < ‖q - p‖ ^ 2 := by
    have h0 : q - p ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have h2 := m8_omega_im_pos
  positivity

theorem m8_neg_weighted_diffs {p q r : ℂ}
    (h : p + (omega : ℂ) ^ 2 * q + (omega : ℂ) * r = 0) :
    r - q = (omega : ℂ) ^ 2 * (q - p) ∧ p - r = (omega : ℂ) * (q - p) := by
  have hsq := m8_omega_sq
  have hr0 : (omega : ℂ) * r = -(p + (omega : ℂ) ^ 2 * q) := by linear_combination h
  have hω4 : (omega : ℂ) ^ 2 * (omega : ℂ) ^ 2 = (omega : ℂ) := by
    rw [show (omega : ℂ) ^ 2 * (omega : ℂ) ^ 2 = (omega : ℂ) ^ 3 * (omega : ℂ) from by ring,
      omega_cubed, one_mul]
  have hr : r = -((omega : ℂ) ^ 2 * p) - (omega : ℂ) * q := by
    have hmul : (omega : ℂ) ^ 2 * ((omega : ℂ) * r) =
        (omega : ℂ) ^ 2 * (-(p + (omega : ℂ) ^ 2 * q)) := by rw [hr0]
    have h3 : (omega : ℂ) ^ 2 * ((omega : ℂ) * r) = r := by
      rw [← mul_assoc, show (omega : ℂ) ^ 2 * (omega : ℂ) = (omega : ℂ) ^ 3 by ring,
        omega_cubed, one_mul]
    rw [h3] at hmul
    rw [hmul, mul_neg, mul_add, ← mul_assoc, hω4]
    ring
  constructor
  · rw [hr, hsq]; ring
  · rw [hr, hsq]; ring

theorem m8_neg_weighted_area {p q r : ℂ}
    (h : p + (omega : ℂ) ^ 2 * q + (omega : ℂ) * r = 0) :
    (conj (q - p) * (r - p)).im = -((omega : ℂ).im * ‖q - p‖ ^ 2) := by
  obtain ⟨h1, h2⟩ := m8_neg_weighted_diffs h
  have hrp : r - p = -((omega : ℂ) * (q - p)) := by
    rw [← h2]; ring
  have ht : conj (q - p) * (q - p) = ((‖q - p‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.sq_norm]
  have hval : conj (q - p) * (r - p) = -((omega : ℂ) * ((‖q - p‖ ^ 2 : ℝ) : ℂ)) := by
    rw [hrp, ← ht]; ring
  rw [hval, Complex.neg_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]
  ring

theorem m8_neg_weighted_neg {p q r : ℂ}
    (h : p + (omega : ℂ) ^ 2 * q + (omega : ℂ) * r = 0) (hne : q ≠ p) :
    (conj (q - p) * (r - p)).im < 0 := by
  rw [m8_neg_weighted_area h]
  have h1 : (0 : ℝ) < ‖q - p‖ ^ 2 := by
    have h0 : q - p ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have h2 := m8_omega_im_pos
  nlinarith

theorem m8_neg_weighted_norms {p q r : ℂ}
    (h : p + (omega : ℂ) ^ 2 * q + (omega : ℂ) * r = 0) :
    ‖q - p‖ = ‖r - q‖ ∧ ‖r - q‖ = ‖p - r‖ := by
  obtain ⟨h1, h2⟩ := m8_neg_weighted_diffs h
  constructor
  · rw [h1, norm_mul, omega_sq_norm_one, one_mul]
  · rw [h1, h2, norm_mul, norm_mul, omega_sq_norm_one, omega_norm_one, one_mul]

theorem m8_positivelyOriented_of_weighted {t : TriangleVertices E}
    (h : toComplex o t.first + (omega : ℂ) * toComplex o t.second +
      (omega : ℂ) ^ 2 * toComplex o t.third = 0) (hne : t.first ≠ t.second) :
    PositivelyOriented (o := o) t := by
  show 0 < orientedArea o (t.second - t.first) (t.third - t.first)
  rw [w9_areaForm_eq_im, toComplex_sub, toComplex_sub]
  refine m8_weighted_pos h ?_
  intro hc
  exact hne (toComplex_injective o hc).symm

theorem m8_negativelyOriented_of_weighted {t : TriangleVertices E}
    (h : toComplex o t.first + (omega : ℂ) ^ 2 * toComplex o t.second +
      (omega : ℂ) * toComplex o t.third = 0) (hne : t.first ≠ t.second) :
    NegativelyOriented (o := o) t := by
  show orientedArea o (t.second - t.first) (t.third - t.first) < 0
  rw [w9_areaForm_eq_im, toComplex_sub, toComplex_sub]
  refine m8_neg_weighted_neg h ?_
  intro hc
  exact hne (toComplex_injective o hc).symm

theorem m8_equilateral_of_weighted {t : TriangleVertices E}
    (h : toComplex o t.first + (omega : ℂ) * toComplex o t.second +
      (omega : ℂ) ^ 2 * toComplex o t.third = 0) :
    Equilateral t.first t.second t.third := by
  obtain ⟨h1, h2⟩ := m8_weighted_norms h
  have hd : ∀ P Q : E, dist P Q = ‖toComplex o P - toComplex o Q‖ := by
    intro P Q
    rw [dist_eq_norm, ← toComplex_norm o (P - Q), toComplex_sub]
  show dist t.first t.second = dist t.second t.third ∧
    dist t.second t.third = dist t.third t.first
  rw [hd, hd, hd]
  constructor
  · rw [norm_sub_rev (toComplex o t.first) (toComplex o t.second),
      norm_sub_rev (toComplex o t.second) (toComplex o t.third)]
    exact h1
  · rw [norm_sub_rev (toComplex o t.second) (toComplex o t.third),
      norm_sub_rev (toComplex o t.third) (toComplex o t.first)]
    exact h2

theorem m8_equilateral_of_neg_weighted {t : TriangleVertices E}
    (h : toComplex o t.first + (omega : ℂ) ^ 2 * toComplex o t.second +
      (omega : ℂ) * toComplex o t.third = 0) :
    Equilateral t.first t.second t.third := by
  obtain ⟨h1, h2⟩ := m8_neg_weighted_norms h
  have hd : ∀ P Q : E, dist P Q = ‖toComplex o P - toComplex o Q‖ := by
    intro P Q
    rw [dist_eq_norm, ← toComplex_norm o (P - Q), toComplex_sub]
  show dist t.first t.second = dist t.second t.third ∧
    dist t.second t.third = dist t.third t.first
  rw [hd, hd, hd]
  constructor
  · rw [norm_sub_rev (toComplex o t.first) (toComplex o t.second),
      norm_sub_rev (toComplex o t.second) (toComplex o t.third)]
    exact h1
  · rw [norm_sub_rev (toComplex o t.second) (toComplex o t.third),
      norm_sub_rev (toComplex o t.third) (toComplex o t.first)]
    exact h2

theorem m8_constellationIndex_ne {c c' : TrisectorColor} (h : c ≠ c')
    (a b a' b' : TrisectorLabel) :
    (⟨c, a, b⟩ : ConstellationIndex) ≠ ⟨c', a', b'⟩ := by
  intro hh
  exact h (congrArg ConstellationIndex.color hh)

theorem m8_tricolor_vertices_ne (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (q : TricolorIndex) :
    (T.tricolorTriangle q).first ≠ (T.tricolorTriangle q).second ∧
      (T.tricolorTriangle q).second ≠ (T.tricolorTriangle q).third ∧
        (T.tricolorTriangle q).third ≠ (T.tricolorTriangle q).first := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun hh => m8_constellationIndex_ne (c := .red) (c' := .green) (by decide)
      q.i q.j q.j q.k (h hh)
  · exact fun hh => m8_constellationIndex_ne (c := .green) (c' := .blue) (by decide)
      q.j q.k q.k q.i (h hh)
  · exact fun hh => m8_constellationIndex_ne (c := .blue) (c' := .red) (by decide)
      q.k q.i q.i q.j (h hh)

theorem m8_constellation_red_form (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    T.constellationPoint ⟨.red, i, j⟩ =
      T.C + (Real.sin (T.beta - labelAngle i / 2) /
        Real.sin (T.beta + T.gamma - (labelAngle i + labelAngle j) / 2)) •
        rotateVector o (T.B - T.C) (-(T.gamma - labelAngle j / 2)) := by
  rw [T.constellationPoint_red_eq]
  have hsin : Real.sin
      (((2 * T.gamma - labelAngle j) + (2 * T.beta - labelAngle i)) / 2) ≠ 0 := by
    rw [show ((2 * T.gamma - labelAngle j) + (2 * T.beta - labelAngle i)) / 2 =
      T.beta + T.gamma - (labelAngle i + labelAngle j) / 2 from by ring]
    exact m6_sin_shift_sub_ne_zero (T.m6_beta_add_gamma_bounds_lt).1
      (T.m6_beta_add_gamma_bounds_lt).2 i j
  refine (m6_rotationFixedPoint_smul_rotate (o := o) T.C T.B
    (2 * T.gamma - labelAngle j) (2 * T.beta - labelAngle i) hsin).trans ?_
  rw [show (2 * T.beta - labelAngle i) / 2 = T.beta - labelAngle i / 2 from by ring,
    show ((2 * T.gamma - labelAngle j) + (2 * T.beta - labelAngle i)) / 2 =
      T.beta + T.gamma - (labelAngle i + labelAngle j) / 2 from by ring,
    show -((2 * T.gamma - labelAngle j) / 2) = -(T.gamma - labelAngle j / 2) from by ring]

theorem m8_constellation_green_form (T : OrientedTriangle E o) (j k : TrisectorLabel) :
    T.constellationPoint ⟨.green, j, k⟩ =
      T.A + (Real.sin (T.gamma - labelAngle j / 2) /
        Real.sin (T.gamma + T.alpha - (labelAngle j + labelAngle k) / 2)) •
        rotateVector o (T.C - T.A) (-(T.alpha - labelAngle k / 2)) := by
  show rotationFixedPoint o T.A T.C (2 * T.alpha - labelAngle k) (2 * T.gamma - labelAngle j) =
    T.A + (Real.sin (T.gamma - labelAngle j / 2) /
      Real.sin (T.gamma + T.alpha - (labelAngle j + labelAngle k) / 2)) •
      rotateVector o (T.C - T.A) (-(T.alpha - labelAngle k / 2))
  have hsin : Real.sin
      (((2 * T.alpha - labelAngle k) + (2 * T.gamma - labelAngle j)) / 2) ≠ 0 := by
    rw [show ((2 * T.alpha - labelAngle k) + (2 * T.gamma - labelAngle j)) / 2 =
      T.gamma + T.alpha - (labelAngle j + labelAngle k) / 2 from by ring]
    exact m6_sin_shift_sub_ne_zero (T.m6_gamma_add_alpha_bounds_lt).1
      (T.m6_gamma_add_alpha_bounds_lt).2 j k
  refine (m6_rotationFixedPoint_smul_rotate (o := o) T.A T.C
    (2 * T.alpha - labelAngle k) (2 * T.gamma - labelAngle j) hsin).trans ?_
  rw [show (2 * T.gamma - labelAngle j) / 2 = T.gamma - labelAngle j / 2 from by ring,
    show ((2 * T.alpha - labelAngle k) + (2 * T.gamma - labelAngle j)) / 2 =
      T.gamma + T.alpha - (labelAngle j + labelAngle k) / 2 from by ring,
    show -((2 * T.alpha - labelAngle k) / 2) = -(T.alpha - labelAngle k / 2) from by ring]

theorem m8_constellation_blue_form (T : OrientedTriangle E o) (k i : TrisectorLabel) :
    T.constellationPoint ⟨.blue, k, i⟩ =
      T.B + (Real.sin (T.alpha - labelAngle k / 2) /
        Real.sin (T.alpha + T.beta - (labelAngle k + labelAngle i) / 2)) •
        rotateVector o (T.A - T.B) (-(T.beta - labelAngle i / 2)) := by
  show rotationFixedPoint o T.B T.A (2 * T.beta - labelAngle i) (2 * T.alpha - labelAngle k) =
    T.B + (Real.sin (T.alpha - labelAngle k / 2) /
      Real.sin (T.alpha + T.beta - (labelAngle k + labelAngle i) / 2)) •
      rotateVector o (T.A - T.B) (-(T.beta - labelAngle i / 2))
  have hsin : Real.sin
      (((2 * T.beta - labelAngle i) + (2 * T.alpha - labelAngle k)) / 2) ≠ 0 := by
    rw [show ((2 * T.beta - labelAngle i) + (2 * T.alpha - labelAngle k)) / 2 =
      T.alpha + T.beta - (labelAngle k + labelAngle i) / 2 from by ring]
    exact m6_sin_shift_sub_ne_zero (T.m6_alpha_add_beta_bounds_lt).1
      (T.m6_alpha_add_beta_bounds_lt).2 k i
  refine (m6_rotationFixedPoint_smul_rotate (o := o) T.B T.A
    (2 * T.beta - labelAngle i) (2 * T.alpha - labelAngle k) hsin).trans ?_
  rw [show (2 * T.alpha - labelAngle k) / 2 = T.alpha - labelAngle k / 2 from by ring,
    show ((2 * T.beta - labelAngle i) + (2 * T.alpha - labelAngle k)) / 2 =
      T.alpha + T.beta - (labelAngle k + labelAngle i) / 2 from by ring,
    show -((2 * T.beta - labelAngle i) / 2) = -(T.beta - labelAngle i / 2) from by ring]

theorem m8_toComplex_constellation_red (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, i, j⟩) =
      toComplex o T.C +
        ((Real.sin (T.beta - labelAngle i / 2) /
          Real.sin (T.beta + T.gamma - (labelAngle i + labelAngle j) / 2) : ℝ) : ℂ) *
          (Circle.exp (-(T.gamma - labelAngle j / 2)) : ℂ) * toComplex o (T.B - T.C) := by
  rw [m8_constellation_red_form, toComplex_add, toComplex_smul, toComplex_rotateVector]
  ring

theorem m8_toComplex_constellation_green (T : OrientedTriangle E o) (j k : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.green, j, k⟩) =
      toComplex o T.A +
        ((Real.sin (T.gamma - labelAngle j / 2) /
          Real.sin (T.gamma + T.alpha - (labelAngle j + labelAngle k) / 2) : ℝ) : ℂ) *
          (Circle.exp (-(T.alpha - labelAngle k / 2)) : ℂ) * toComplex o (T.C - T.A) := by
  rw [m8_constellation_green_form, toComplex_add, toComplex_smul, toComplex_rotateVector]
  ring

theorem m8_toComplex_constellation_blue (T : OrientedTriangle E o) (k i : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.blue, k, i⟩) =
      toComplex o T.B +
        ((Real.sin (T.alpha - labelAngle k / 2) /
          Real.sin (T.alpha + T.beta - (labelAngle k + labelAngle i) / 2) : ℝ) : ℂ) *
          (Circle.exp (-(T.beta - labelAngle i / 2)) : ℂ) * toComplex o (T.A - T.B) := by
  rw [m8_constellation_blue_form, toComplex_add, toComplex_smul, toComplex_rotateVector]
  ring

/-! #### The closed-form coefficients and the two-term weighted sum

With `u = toComplex(C - B)` and `v = toComplex(A - C)` the weighted sum of a
tricolour triangle collapses to `coeff_u · u + coeff_v · v`.  The two coefficients
below are the whole remaining content of `tricolor_orientation` and
`tricolor_equilateral_iff`: once the identity
`coeff_u · u + coeff_v · v = 0` is checked for the label classes `i+j+k = 0` and
`i+j+k = 2`, the weighted criterion above turns it into positivity, negativity and
equilateralism.  Since `u / v = -(sin 3α / sin 3β) e^{3iγ}`, that identity is a
single complex equation in the angles. -/

/-- The coefficient of `B - C` in the red tricolour vertex. -/
def m8LamR (T : OrientedTriangle E o) (i j : TrisectorLabel) : ℂ :=
  ((Real.sin (T.beta - labelAngle i / 2) /
    Real.sin (T.beta + T.gamma - (labelAngle i + labelAngle j) / 2) : ℝ) : ℂ) *
    (Circle.exp (-(T.gamma - labelAngle j / 2)) : ℂ)

/-- The coefficient of `C - A` in the green tricolour vertex. -/
def m8LamG (T : OrientedTriangle E o) (j k : TrisectorLabel) : ℂ :=
  ((Real.sin (T.gamma - labelAngle j / 2) /
    Real.sin (T.gamma + T.alpha - (labelAngle j + labelAngle k) / 2) : ℝ) : ℂ) *
    (Circle.exp (-(T.alpha - labelAngle k / 2)) : ℂ)

/-- The coefficient of `A - B` in the blue tricolour vertex. -/
def m8LamB (T : OrientedTriangle E o) (k i : TrisectorLabel) : ℂ :=
  ((Real.sin (T.alpha - labelAngle k / 2) /
    Real.sin (T.alpha + T.beta - (labelAngle k + labelAngle i) / 2) : ℝ) : ℂ) *
    (Circle.exp (-(T.beta - labelAngle i / 2)) : ℂ)

theorem m8_toComplex_tricolor_first (T : OrientedTriangle E o) (q : TricolorIndex) :
    toComplex o (T.tricolorTriangle q).first =
      toComplex o T.C + m8LamR T q.i q.j * toComplex o (T.B - T.C) :=
  m8_toComplex_constellation_red T q.i q.j

theorem m8_toComplex_tricolor_second (T : OrientedTriangle E o) (q : TricolorIndex) :
    toComplex o (T.tricolorTriangle q).second =
      toComplex o T.A + m8LamG T q.j q.k * toComplex o (T.C - T.A) :=
  m8_toComplex_constellation_green T q.j q.k

theorem m8_toComplex_tricolor_third (T : OrientedTriangle E o) (q : TricolorIndex) :
    toComplex o (T.tricolorTriangle q).third =
      toComplex o T.B + m8LamB T q.k q.i * toComplex o (T.A - T.B) :=
  m8_toComplex_constellation_blue T q.k q.i

/-- **The two-term weighted sum.** -/
theorem m8_tricolor_weighted_sum (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, i, j⟩) +
        (omega : ℂ) * toComplex o (T.constellationPoint ⟨.green, j, k⟩) +
          (omega : ℂ) ^ 2 * toComplex o (T.constellationPoint ⟨.blue, k, i⟩) =
      ((omega : ℂ) ^ 2 * (m8LamB T k i - 1) - m8LamR T i j) *
          toComplex o (T.C - T.B) +
        ((omega : ℂ) - (omega : ℂ) * m8LamG T j k + (omega : ℂ) ^ 2 * m8LamB T k i) *
          toComplex o (T.A - T.C) := by
  unfold m8LamR m8LamG m8LamB
  rw [m8_toComplex_constellation_red, m8_toComplex_constellation_green,
    m8_toComplex_constellation_blue]
  rw [show toComplex o (T.C - T.A) = -toComplex o (T.A - T.C) from by
      rw [show T.C - T.A = -(T.A - T.C) from by abel, toComplex_neg]]
  rw [show toComplex o (T.B - T.C) = -toComplex o (T.C - T.B) from by
      rw [show T.B - T.C = -(T.C - T.B) from by abel, toComplex_neg]]
  rw [show toComplex o (T.A - T.B) =
      toComplex o (T.A - T.C) + toComplex o (T.C - T.B) from by
    rw [show T.A - T.B = (T.A - T.C) + (T.C - T.B) from by abel, toComplex_add]]
  have hA : toComplex o T.A = toComplex o T.C + toComplex o (T.A - T.C) := by
    rw [← toComplex_add]; congr 1; abel
  rw [hA]
  have hB : toComplex o T.B = toComplex o T.C - toComplex o (T.C - T.B) := by
    rw [← toComplex_sub]; congr 1; abel
  rw [hB]
  linear_combination (toComplex o T.C) * omega_sum

/-! #### Parallelism through complex coordinates

`monochrome_sides_parallel` and `tricolor_sides_parallel` are statements of the form
`∃ r : ℝ, v = r • w`.  In complex coordinates that is exactly "the ratio
`toComplex w / toComplex v` is real", which is how the phase computations are done. -/

theorem m8_parallel_iff_real_ratio {v w : E} :
    Parallel v w ↔ ∃ r : ℝ, toComplex o w = (r : ℂ) * toComplex o v := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [toComplex_smul]⟩
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    apply toComplex_injective o
    rw [toComplex_smul, hr]

theorem m8_parallel_of_real_ratio {v w : E} {r : ℝ}
    (h : toComplex o w = (r : ℂ) * toComplex o v) : Parallel v w := by
  refine ⟨r, ?_⟩
  apply toComplex_injective o
  rw [toComplex_smul, h]

theorem m2_exp_mul (x y : ℝ) : (Circle.exp (x + y) : ℂ) = (Circle.exp x : ℂ) * (Circle.exp y : ℂ) :=
  (m3_exp_mul_exp x y).symm

theorem m2_exp_pi_third_sq : (Circle.exp (Real.pi / 3) : ℂ) ^ 2 = (omega : ℂ) := by
  rw [pow_two]
  have h := m3_exp_mul_exp (Real.pi / 3) (Real.pi / 3)
  rw [show Real.pi / 3 + Real.pi / 3 = 2 * Real.pi / 3 by ring] at h
  exact h

theorem m2_exp_pi : (Circle.exp Real.pi : ℂ) = -1 := by
  rw [Circle.coe_exp]
  rw [show ((Real.pi : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

theorem m2_exp_pi_third_cu : (Circle.exp (Real.pi / 3) : ℂ) ^ 3 = -1 := by
  rw [show (3:ℕ) = 2 + 1 by norm_num, pow_add, m2_exp_pi_third_sq, pow_one]
  have h := m3_exp_mul_exp (2 * Real.pi / 3) (Real.pi / 3)
  rw [show 2 * Real.pi / 3 + Real.pi / 3 = Real.pi by ring, m2_exp_pi] at h
  exact h

theorem m2_exp_pi_third : (Circle.exp (Real.pi / 3) : ℂ) = -((omega : ℂ) ^ 2) := by
  have hkey : (Circle.exp (Real.pi / 3) : ℂ) * (omega : ℂ) = -1 := by
    calc (Circle.exp (Real.pi / 3) : ℂ) * (omega : ℂ)
        = (Circle.exp (Real.pi / 3) : ℂ) * (Circle.exp (Real.pi / 3) : ℂ) ^ 2 := by
          rw [m2_exp_pi_third_sq]
      _ = (Circle.exp (Real.pi / 3) : ℂ) ^ 3 := by ring
      _ = -1 := m2_exp_pi_third_cu
  calc (Circle.exp (Real.pi / 3) : ℂ)
      = (Circle.exp (Real.pi / 3) : ℂ) * ((omega : ℂ) * (omega : ℂ) ^ 2) := by
        rw [omega_mul_sq, mul_one]
    _ = ((Circle.exp (Real.pi / 3) : ℂ) * (omega : ℂ)) * (omega : ℂ) ^ 2 := by ring
    _ = (-1) * (omega : ℂ) ^ 2 := by rw [hkey]
    _ = -((omega : ℂ) ^ 2) := by ring

theorem m2_exp_neg_pi : (Circle.exp (-Real.pi) : ℂ) = -1 := by
  have h : (Circle.exp (-Real.pi) : ℂ) = ((Circle.exp Real.pi : ℂ))⁻¹ := by
    rw [Circle.coe_exp, Circle.coe_exp, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [h, m2_exp_pi, inv_neg_one]

theorem m2_exp_neg_pi_third : (Circle.exp (-(Real.pi / 3)) : ℂ) = -(omega : ℂ) := by
  have h : (Circle.exp (-(Real.pi / 3)) : ℂ) = ((Circle.exp (Real.pi / 3) : ℂ))⁻¹ := by
    rw [Circle.coe_exp, Circle.coe_exp, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [h, m2_exp_pi_third, inv_neg, omega_sq_inv]

theorem m2_labelAngle_half (i : TrisectorLabel) :
    labelAngle i / 2 = (i.val : ℝ) * (Real.pi / 3) := by
  rw [labelAngle]; push_cast; ring

theorem m2_half_label_exp (i : TrisectorLabel) :
    (Circle.exp (labelAngle i / 2) : ℂ) = (Circle.exp (Real.pi / 3) : ℂ) ^ i.val := by
  rw [m2_labelAngle_half]; rw [Circle.exp_natCast_mul]; norm_cast

theorem m2_half_label_exp_neg (i : TrisectorLabel) :
    (Circle.exp (-(labelAngle i / 2)) : ℂ) = ((Circle.exp (Real.pi / 3) : ℂ) ^ i.val)⁻¹ := by
  rw [← m2_half_label_exp, Circle.coe_exp, Circle.coe_exp, ← Complex.exp_neg]
  congr 1; push_cast; ring


theorem m2_two_I_sin (θ : ℝ) :
    2 * Complex.I * (Real.sin θ : ℂ) = (Circle.exp θ : ℂ) - (Circle.exp (-θ) : ℂ) := by
  have h1 : (Circle.exp θ : ℂ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Circle.coe_exp, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have h2 : (Circle.exp (-θ) : ℂ) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    rw [Circle.coe_exp, Complex.exp_mul_I]
    rw [show Complex.cos (((-θ:ℝ):ℂ)) = Complex.cos ((θ:ℝ):ℂ) by
          rw [show ((-θ:ℝ):ℂ) = -((θ:ℝ):ℂ) by push_cast; ring, Complex.cos_neg]]
    rw [show Complex.sin (((-θ:ℝ):ℂ)) = -Complex.sin ((θ:ℝ):ℂ) by
          rw [show ((-θ:ℝ):ℂ) = -((θ:ℝ):ℂ) by push_cast; ring, Complex.sin_neg]]
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  rw [h1, h2]; ring

theorem m2_sin_exp_form (θ : ℝ) :
    (Real.sin θ : ℂ) = ((Circle.exp θ : ℂ) - (Circle.exp (-θ) : ℂ)) / (2 * Complex.I) := by
  rw [← m2_two_I_sin θ]
  have hI : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  field_simp

theorem m2_exp_sub_half (x : ℝ) (i : TrisectorLabel) :
    (Circle.exp (x - labelAngle i / 2) : ℂ) =
      (Circle.exp x : ℂ) * ((Circle.exp (Real.pi / 3) : ℂ) ^ i.val)⁻¹ := by
  rw [show x - labelAngle i / 2 = x + (-(labelAngle i / 2)) by ring, m2_exp_mul]
  rw [m2_half_label_exp_neg]

theorem m2_exp_neg_sub_half (x : ℝ) (i : TrisectorLabel) :
    (Circle.exp (-(x - labelAngle i / 2)) : ℂ) =
      ((Circle.exp x : ℂ))⁻¹ * (Circle.exp (Real.pi / 3) : ℂ) ^ i.val := by
  rw [show -(x - labelAngle i / 2) = -x + labelAngle i / 2 by ring, m2_exp_mul]
  rw [show (-x : ℝ) = -(x) from rfl]
  congr 1
  · rw [Circle.coe_exp, Circle.coe_exp, ← Complex.exp_neg]; congr 1; push_cast; ring
  · rw [m2_half_label_exp]


theorem m2_exp_neg_three_ab_add (T : OrientedTriangle E o) :
    (Circle.exp (3 * T.alpha) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ) =
      -((Circle.exp (-3 * T.beta) : ℂ)) := by
  have harg : 3 * T.alpha + 3 * T.gamma = Real.pi + (-3 * T.beta) := by
    have h := T.angle_sum; linarith
  have h : (Circle.exp (3 * T.alpha + 3 * T.gamma) : ℂ) =
      (Circle.exp Real.pi : ℂ) * (Circle.exp (-3 * T.beta) : ℂ) := by
    rw [harg, m2_exp_mul]
  rw [m2_exp_pi, neg_one_mul] at h
  rw [← h, m3_exp_mul_exp]

theorem m2_side_relation_CB (T : OrientedTriangle E o) :
    toComplex o (T.C - T.B) * (Real.sin (3 * T.beta) : ℂ) =
      -((Real.sin (3 * T.alpha) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ) *
        toComplex o (T.A - T.C)) := by
  have hbc := toComplex_B_sub_C T
  have hca := toComplex_C_sub_A T
  have hkey := m2_exp_neg_three_ab_add T
  have hsβ : ((Real.sin (3 * T.beta)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (m3_sin_three_beta_pos T))
  rw [show T.C - T.B = -(T.B - T.C) from by abel, toComplex_neg, hbc]
  rw [show T.A - T.C = -(T.C - T.A) from by abel, toComplex_neg, hca]
  have hsub : (Circle.exp (-3 * T.beta) : ℂ) =
      -((Circle.exp (3 * T.alpha) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ)) := by
    rw [eq_neg_iff_add_eq_zero]
    linear_combination hkey
  rw [hsub]
  push_cast
  ring


theorem m2_weighted_sum_reduce (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    (toComplex o (T.constellationPoint ⟨.red, i, j⟩) +
        (omega : ℂ) * toComplex o (T.constellationPoint ⟨.green, j, k⟩) +
          (omega : ℂ) ^ 2 * toComplex o (T.constellationPoint ⟨.blue, k, i⟩)) *
        (Real.sin (3 * T.beta) : ℂ) =
      (((omega : ℂ) - (omega : ℂ) * T.m8LamG j k + (omega : ℂ) ^ 2 * T.m8LamB k i) *
          (Real.sin (3 * T.beta) : ℂ) -
        ((omega : ℂ) ^ 2 * (T.m8LamB k i - 1) - T.m8LamR i j) *
          (Real.sin (3 * T.alpha) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ)) *
        toComplex o (T.A - T.C) := by
  set cu : ℂ := (omega : ℂ) ^ 2 * (T.m8LamB k i - 1) - T.m8LamR i j with hcu
  set cv : ℂ := (omega : ℂ) - (omega : ℂ) * T.m8LamG j k + (omega : ℂ) ^ 2 * T.m8LamB k i with hcv
  have hsum := m8_tricolor_weighted_sum (T := T) i j k
  have hrel := m2_side_relation_CB T
  rw [hsum]
  linear_combination cu * hrel

theorem m2_toComplex_A_sub_C_ne (T : OrientedTriangle E o) :
    toComplex o (T.A - T.C) ≠ 0 := by
  intro h
  have h1 : T.A - T.C = 0 := toComplex_injective o (by simpa using h)
  exact T.A_ne_C (sub_eq_zero.mp h1)

theorem m2_weighted_zero_of_scalar (T : OrientedTriangle E o) (i j k : TrisectorLabel)
    (h : ((omega : ℂ) - (omega : ℂ) * T.m8LamG j k + (omega : ℂ) ^ 2 * T.m8LamB k i) *
          (Real.sin (3 * T.beta) : ℂ) =
        ((omega : ℂ) ^ 2 * (T.m8LamB k i - 1) - T.m8LamR i j) *
          (Real.sin (3 * T.alpha) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ)) :
    toComplex o (T.constellationPoint ⟨.red, i, j⟩) +
        (omega : ℂ) * toComplex o (T.constellationPoint ⟨.green, j, k⟩) +
          (omega : ℂ) ^ 2 * toComplex o (T.constellationPoint ⟨.blue, k, i⟩) = 0 := by
  have hred := m2_weighted_sum_reduce (T := T) i j k
  have hsβ : ((Real.sin (3 * T.beta)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (m3_sin_three_beta_pos T))
  rw [h, sub_self, zero_mul] at hred
  exact (mul_eq_zero.mp hred).resolve_right hsβ



/-- The `XYZ` triangle is nondegenerate: `X ≠ Y`. -/
theorem m2_X_ne_Y (T : OrientedTriangle E o) : T.X ≠ T.Y := by
  intro h
  have h1 := T.morley_side_lengths
  have h2 : dist T.X T.Y = 0 := by rw [h]; exact dist_self _
  have h3 := h1.1
  rw [h2] at h3
  have hpos : 0 < 4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma := by
    have h4 := m7_delta_pos T; have h5 := m7_sin_alpha_pos T
    have h6 := m7_sin_beta_pos T; have h7 := m7_sin_gamma_pos T
    positivity
  linarith

theorem m2_Y_sub_X_ne (T : OrientedTriangle E o) : T.Y - T.X ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm T.m2_X_ne_Y)

theorem m2_Z_sub_Y_ne (T : OrientedTriangle E o) : T.Z - T.Y ≠ 0 := by
  intro h
  have h2 : dist T.Y T.Z = 0 := by
    rw [dist_eq_norm, show T.Y - T.Z = -(T.Z - T.Y) from by abel, norm_neg, h, norm_zero]
  have h3 := T.morley_side_lengths
  rw [h3.2.1] at h2
  have hpos : 0 < 4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma := by
    have h4 := m7_delta_pos T; have h5 := m7_sin_alpha_pos T
    have h6 := m7_sin_beta_pos T; have h7 := m7_sin_gamma_pos T
    positivity
  linarith

theorem m2_Y_sub_X_ne' (T : OrientedTriangle E o) : T.Y - T.X ≠ 0 :=
  sub_ne_zero.mpr T.m2_X_ne_Y.symm

/-- Two nonzero, non-parallel vectors are linearly independent over `ℝ`. -/
theorem m2_eq_zero_of_smul_add_of_not_parallel {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : ¬ Parallel u v) {a b : ℝ} (h : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
  constructor
  · by_contra ha
    have hb : b ≠ 0 := by
      rintro rfl
      rw [zero_smul, add_zero] at h
      exact hu ((smul_eq_zero.mp h).resolve_left ha)
    have h1 : a • u = -(b • v) := by rw [eq_neg_iff_add_eq_zero]; exact h
    have h2 : u = (-(b / a)) • v := by
      rw [show u = a⁻¹ • (a • u) by rw [smul_smul, inv_mul_cancel₀ ha, one_smul], h1, smul_neg,
        smul_smul, neg_smul]
      congr 1
      field_simp
    exact huv (parallel_comm hv hu ⟨-(b / a), h2⟩)
  · by_contra hb
    have ha : a ≠ 0 := by
      rintro rfl
      rw [zero_smul, zero_add] at h
      exact hv ((smul_eq_zero.mp h).resolve_left hb)
    have h1 : b • v = -(a • u) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    refine huv ⟨-(a / b), ?_⟩
    rw [show v = b⁻¹ • (b • v) by rw [smul_smul, inv_mul_cancel₀ hb, one_smul], h1, smul_neg,
      smul_smul, neg_smul]
    congr 1
    field_simp

/-- **A closed triangle whose three side vectors lie along the three (distinct)
directions of `XYZ` is equilateral.**  This is the bridge from
`tricolor_sides_parallel` / `monochrome_sides_parallel` to `Equilateral`: the three
Morley side vectors already sum to zero, so the only linear relation among them is the
diagonal one, forcing the three scalar factors to agree. -/
theorem m2_equilateral_of_parallel_triple (T : OrientedTriangle E o) {P Q R : E} {a b c : ℝ}
    (hPQ : Q - P = a • (T.Y - T.X))
    (hQR : R - Q = b • (T.Z - T.Y))
    (hRP : P - R = c • (T.X - T.Z)) : Equilateral P Q R := by
  obtain ⟨hXY, hYZ, hZX⟩ := T.morley_side_lengths
  have hne : T.Y - T.X ≠ 0 := T.m2_Y_sub_X_ne
  have hne2 : T.Z - T.Y ≠ 0 := T.m2_Z_sub_Y_ne
  have hclos : a • (T.Y - T.X) + b • (T.Z - T.Y) + c • (T.X - T.Z) = 0 := by
    rw [← hPQ, ← hQR, ← hRP]; abel
  have htri : (T.Y - T.X) + (T.Z - T.Y) + (T.X - T.Z) = 0 := by abel
  have hsub : (a - c) • (T.Y - T.X) + (b - c) • (T.Z - T.Y) = 0 := by
    have hexp : (a - c) • (T.Y - T.X) + (b - c) • (T.Z - T.Y)
        = (a • (T.Y - T.X) + b • (T.Z - T.Y) + c • (T.X - T.Z))
          - c • ((T.Y - T.X) + (T.Z - T.Y) + (T.X - T.Z)) := by
      rw [smul_add, smul_add, sub_smul, sub_smul]; abel
    rw [hexp, hclos, htri, smul_zero, sub_zero]
  have hnp : ¬ Parallel (T.Y - T.X) (T.Z - T.Y) := T.m4_not_parallel_morley.1
  obtain ⟨hac, hbc⟩ := m2_eq_zero_of_smul_add_of_not_parallel hne hne2 hnp hsub
  have hac' : a = c := sub_eq_zero.mp hac
  have hbc' : b = c := sub_eq_zero.mp hbc
  have hu : ‖T.Y - T.X‖ = ‖T.Z - T.Y‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm T.Y T.X, dist_comm T.Z T.Y]
    exact hXY.trans hYZ.symm
  have hv : ‖T.Z - T.Y‖ = ‖T.X - T.Z‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm T.Z T.Y, dist_comm T.X T.Z]
    exact hYZ.trans hZX.symm
  refine ⟨?_, ?_⟩
  · rw [dist_eq_norm, dist_eq_norm, norm_sub_rev P Q, norm_sub_rev Q R, hPQ, hQR, hac', hbc',
      norm_smul, norm_smul, hu]
  · rw [dist_eq_norm, dist_eq_norm, norm_sub_rev Q R, norm_sub_rev R P, hQR, hRP, hbc',
      norm_smul, norm_smul, hv]


lemma m7b_affine_key (eu ev ew ζ P Q B1 B2 B3 K T lam mu nu : ℂ)
    (hB1 : B1 = 1 - ev * ew) (hB2 : B2 = 1 - ew * eu) (hB3 : B3 = 1 - eu * ev)
    (hK : K = eu ^ 3 * (ev ^ 3 - 1)) (hTdef : T = eu * ev * ew)
    (hlam : lam * B1 = 1 - ev) (hmu : mu * B2 = 1 - ew) (hnu : nu * B3 = 1 - eu)
    (h1 : B1 ≠ 0) (h2 : B2 ≠ 0) (h3 : B3 ≠ 0) (hK' : K ≠ 0)
    (hp : P * K = (eu ^ 3 - 1) * Q)
    (hT : 1 + T + T ^ 2 = 0) (hζ : ζ = -T) :
    (mu - 1) * Q - lam * P = ζ * ((1 - lam - nu) * P - nu * Q) := by
  obtain rfl : K = eu ^ 3 * (ev ^ 3 - 1) := hK
  obtain rfl : T = eu * ev * ew := hTdef
  obtain rfl : ζ = -(eu * ev * ew) := hζ
  have hPi : B1 * B2 * B3 ≠ 0 := mul_ne_zero (mul_ne_zero h1 h2) h3
  have e1 : B1 * B2 * B3 * mu = (1 - ew) * B1 * B3 := by
    rw [show B1 * B2 * B3 * mu = (mu * B2) * (B1 * B3) from by ring, hmu]
    ring
  have e2 : B1 * B2 * B3 * lam = (1 - ev) * B2 * B3 := by
    rw [show B1 * B2 * B3 * lam = (lam * B1) * (B2 * B3) from by ring, hlam]
    ring
  have e3 : B1 * B2 * B3 * nu = (1 - eu) * B1 * B2 := by
    rw [show B1 * B2 * B3 * nu = (nu * B3) * (B1 * B2) from by ring, hnu]
    ring
  have hexpand : B1 * B2 * B3 * ((mu - 1) * Q - lam * P + (eu * ev * ew) * ((1 - lam - nu) * P - nu * Q))
      = ((B1 * B2 * B3 * mu - B1 * B2 * B3) * Q - (B1 * B2 * B3 * lam) * P)
        + (eu * ev * ew) * (((B1 * B2 * B3 - B1 * B2 * B3 * lam - B1 * B2 * B3 * nu) * P)
            - (B1 * B2 * B3 * nu) * Q) := by
    ring
  have hcert : (eu ^ 3 * (ev ^ 3 - 1)) * ((1 - ew) * B1 * B3 - B1 * B2 * B3 + (-(eu * ev * ew)) * (1 - eu) * B1 * B2)
      - (eu ^ 3 - 1) * ((1 - ev) * B2 * B3
          + (-(eu * ev * ew)) * (B1 * B2 * B3 - (1 - ev) * B2 * B3 - (1 - eu) * B1 * B2))
      = (1 + (eu * ev * ew) + (eu * ev * ew) ^ 2) *
        (eu ^ 4 * ev ^ 3 * ew - eu ^ 4 * ev ^ 2 - eu ^ 4 * ev * ew + eu ^ 4 * ev
          - eu ^ 3 * ev ^ 3 * ew + eu ^ 3 * ev + eu ^ 3 * ew - eu ^ 3 + eu * ev ^ 2
          + eu * ev * ew - eu * ev - eu * ew - ev + 1) := by
    rw [hB1, hB2, hB3]
    ring
  have hp' : (eu ^ 3 * (ev ^ 3 - 1)) * P = (eu ^ 3 - 1) * Q := by
    rw [mul_comm]
    exact hp
  have hXform : (eu ^ 3 * (ev ^ 3 - 1)) *
      (((1 - ew) * B1 * B3 - B1 * B2 * B3) * Q - (1 - ev) * B2 * B3 * P
        + (eu * ev * ew) * ((B1 * B2 * B3 - (1 - ev) * B2 * B3 - (1 - eu) * B1 * B2) * P
            - (1 - eu) * B1 * B2 * Q))
      = ((1 - ew) * B1 * B3 - B1 * B2 * B3 + (-(eu * ev * ew)) * (1 - eu) * B1 * B2)
          * ((eu ^ 3 * (ev ^ 3 - 1)) * Q)
        - ((1 - ev) * B2 * B3 + (-(eu * ev * ew)) * (B1 * B2 * B3 - (1 - ev) * B2 * B3
            - (1 - eu) * B1 * B2)) * ((eu ^ 3 * (ev ^ 3 - 1)) * P) := by
    ring
  have hcleared : B1 * B2 * B3 *
      ((mu - 1) * Q - lam * P + (eu * ev * ew) * ((1 - lam - nu) * P - nu * Q)) = 0 := by
    rw [hexpand, e1, e2, e3]
    have hmain : (eu ^ 3 * (ev ^ 3 - 1)) *
        (((1 - ew) * B1 * B3 - B1 * B2 * B3) * Q - (1 - ev) * B2 * B3 * P
          + (eu * ev * ew) * ((B1 * B2 * B3 - (1 - ev) * B2 * B3 - (1 - eu) * B1 * B2) * P
              - (1 - eu) * B1 * B2 * Q)) = 0 := by
      rw [hXform, hp']
      rw [show
        ((1 - ew) * B1 * B3 - B1 * B2 * B3 + (-(eu * ev * ew)) * (1 - eu) * B1 * B2)
            * ((eu ^ 3 * (ev ^ 3 - 1)) * Q)
          - ((1 - ev) * B2 * B3 + (-(eu * ev * ew)) * (B1 * B2 * B3 - (1 - ev) * B2 * B3
              - (1 - eu) * B1 * B2)) * ((eu ^ 3 - 1) * Q)
        = ((eu ^ 3 * (ev ^ 3 - 1)) *
              ((1 - ew) * B1 * B3 - B1 * B2 * B3 + (-(eu * ev * ew)) * (1 - eu) * B1 * B2)
            - (eu ^ 3 - 1) * ((1 - ev) * B2 * B3 + (-(eu * ev * ew)) * (B1 * B2 * B3
                - (1 - ev) * B2 * B3 - (1 - eu) * B1 * B2))) * Q from by ring]
      rw [hcert, hT]
      ring
    exact (mul_eq_zero.mp hmain).resolve_left hK'
  have hcube : (mu - 1) * Q - lam * P + (eu * ev * ew) * ((1 - lam - nu) * P - nu * Q) = 0 :=
    (mul_eq_zero.mp hcleared).resolve_left hPi
  linear_combination hcube


/-! ### Geometric support for the tricolor theorem -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable {o : Orientation ℝ E (Fin 2)}

namespace OrientedTriangle

theorem m7b_exp_ne_zero (θ : ℝ) : (Circle.exp θ : ℂ) ≠ 0 := by
  intro h
  have h1 : ‖(Circle.exp θ : ℂ)‖ = 1 := Circle.norm_coe _
  rw [h, norm_zero] at h1
  norm_num at h1

theorem m7b_one_sub_exp_ne (θ : ℝ) (h : Real.sin (θ / 2) ≠ 0) :
    (1 - (Circle.exp θ : ℂ)) ≠ 0 := by
  rw [one_sub_unit_eq]
  refine mul_ne_zero ?_ (m7b_exp_ne_zero _)
  intro h0
  apply h
  have h4 : (2 * Real.sin (θ / 2) : ℝ) = 0 := by exact_mod_cast h0
  linarith

theorem m7b_one_sub_exp_mul_ne {φ ψ : ℝ} (h : Real.sin ((φ + ψ) / 2) ≠ 0) :
    (1 - (Circle.exp φ : ℂ) * Circle.exp ψ) ≠ 0 := by
  rw [← Circle.coe_mul, ← Circle.exp_add]
  exact m7b_one_sub_exp_ne (φ + ψ) h

theorem m7b_red_form (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, i, j⟩) =
      toComplex o T.C + toComplex o (T.B - T.C) *
        ((1 - (Circle.exp (2 * T.beta - labelAngle i) : ℂ)) /
          (1 - (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) *
            (Circle.exp (2 * T.beta - labelAngle i) : ℂ))) := by
  simp only [constellationPoint, toComplex_rotationFixedPoint]

theorem m7b_green_form (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.green, i, j⟩) =
      toComplex o T.A + toComplex o (T.C - T.A) *
        ((1 - (Circle.exp (2 * T.gamma - labelAngle i) : ℂ)) /
          (1 - (Circle.exp (2 * T.alpha - labelAngle j) : ℂ) *
            (Circle.exp (2 * T.gamma - labelAngle i) : ℂ))) := by
  simp only [constellationPoint, toComplex_rotationFixedPoint]

theorem m7b_blue_form (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.blue, i, j⟩) =
      toComplex o T.B + toComplex o (T.A - T.B) *
        ((1 - (Circle.exp (2 * T.alpha - labelAngle i) : ℂ)) /
          (1 - (Circle.exp (2 * T.beta - labelAngle j) : ℂ) *
            (Circle.exp (2 * T.alpha - labelAngle i) : ℂ))) := by
  simp only [constellationPoint, toComplex_rotationFixedPoint]

end OrientedTriangle
theorem m6_complex_equilateral_iff (p q r : ℂ) :
    (‖p - q‖ = ‖q - r‖ ∧ ‖q - r‖ = ‖r - p‖) ↔
      (p + (omega : ℂ) * q + (omega : ℂ) ^ 2 * r = 0 ∨
        p + (omega : ℂ) ^ 2 * q + (omega : ℂ) * r = 0) := by
  have hω0 : (omega : ℂ) ≠ 0 := Circle.coe_ne_zero omega
  have hω1 : ‖(omega : ℂ)‖ = 1 := Circle.norm_coe omega
  have hω2 : ‖(omega : ℂ) ^ 2‖ = 1 := by rw [← Circle.coe_pow, Circle.norm_coe]
  have hsum : (1 : ℂ) + (omega : ℂ) + (omega : ℂ) ^ 2 = 0 := omega_sum
  have hsum' : (omega : ℂ) + (omega : ℂ) ^ 2 = -1 := by linear_combination omega_sum
  have hsum'' : (1 : ℂ) + (omega : ℂ) = -(omega : ℂ) ^ 2 := by linear_combination omega_sum
  have hsum3 : (1 : ℂ) + (omega : ℂ) ^ 2 = -(omega : ℂ) := by linear_combination omega_sum
  set A := p - q with hA
  set B := q - r with hB
  have hAB : A + B = p - r := by rw [hA, hB]; ring
  have hsq : (omega : ℂ) ^ 2 = -1 - (omega : ℂ) := by linear_combination omega_sum
  have e1 : p + (omega : ℂ) * q + (omega : ℂ) ^ 2 * r = A - (omega : ℂ) ^ 2 * B := by
    rw [hA, hB, hsq]; ring
  have e2 : p + (omega : ℂ) ^ 2 * q + (omega : ℂ) * r = A - (omega : ℂ) * B := by
    rw [hA, hB, hsq]; ring
  have hfac1 : (A - (omega : ℂ) * B) * (A - (omega : ℂ) ^ 2 * B) = A ^ 2 + A * B + B ^ 2 := by
    calc (A - (omega : ℂ) * B) * (A - (omega : ℂ) ^ 2 * B)
        = A ^ 2 - A * B * ((omega : ℂ) + (omega : ℂ) ^ 2) + (omega : ℂ) ^ 3 * B ^ 2 := by ring
      _ = A ^ 2 + A * B + B ^ 2 := by rw [hsum', omega_cubed]; ring
  have hmain : (‖A‖ = ‖B‖ ∧ ‖B‖ = ‖A + B‖) ↔
      (A = (omega : ℂ) ^ 2 * B ∨ A = (omega : ℂ) * B) := by
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hB0 : B = 0
      · have h1' : ‖A‖ = 0 := by rw [hB0, norm_zero] at h1; exact h1
        have hA0 : A = 0 := norm_eq_zero.mp h1'
        left; rw [hA0, hB0]; ring
      · set t := A / B with ht
        have hBpos : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB0
        have htn : ‖t‖ = 1 := by
          rw [ht, norm_div, h1, div_self (ne_of_gt hBpos)]
        have ht1 : ‖t + 1‖ = 1 := by
          have hfac : A + B = B * (t + 1) := by rw [ht]; field_simp
          have hh : ‖A + B‖ = ‖B‖ * ‖t + 1‖ := by rw [hfac, norm_mul]
          rw [hh] at h2
          have := h2.symm
          have h2' : ‖B‖ * ‖t + 1‖ = ‖B‖ * 1 := by rw [mul_one]; exact this
          exact mul_left_cancel₀ (ne_of_gt hBpos) h2'
        have hre1 : t.re ^ 2 + t.im ^ 2 = 1 := by
          have h := Complex.normSq_eq_norm_sq t
          rw [htn] at h
          have h' : Complex.normSq t = t.re * t.re + t.im * t.im := Complex.normSq_apply t
          rw [h'] at h
          nlinarith
        have hre2 : (t + 1).re ^ 2 + (t + 1).im ^ 2 = 1 := by
          have h := Complex.normSq_eq_norm_sq (t + 1)
          rw [ht1] at h
          have h' : Complex.normSq (t + 1) = (t + 1).re * (t + 1).re + (t + 1).im * (t + 1).im :=
            Complex.normSq_apply (t + 1)
          rw [h'] at h
          nlinarith
        have hre : t.re = -(1 / 2) := by
          simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im] at hre2
          nlinarith
        have him : t.im ^ 2 = 3 / 4 := by nlinarith
        have htsq : t ^ 2 + t + 1 = 0 := by
          rw [pow_two]
          apply Complex.ext
          · simp only [Complex.add_re, Complex.mul_re, Complex.one_re, Complex.zero_re]
            nlinarith
          · simp only [Complex.add_im, Complex.mul_im, Complex.one_im, Complex.zero_im]
            nlinarith
        have hAB2 : A ^ 2 + A * B + B ^ 2 = 0 := by
          have h : B ^ 2 * (t ^ 2 + t + 1) = A ^ 2 + A * B + B ^ 2 := by
            rw [ht]; field_simp; try ring
          rw [← h, htsq]; ring
        have hP : (A - (omega : ℂ) * B) * (A - (omega : ℂ) ^ 2 * B) = 0 := by
          rw [hfac1]; exact hAB2
        rcases mul_eq_zero.mp hP with h | h
        · right; linear_combination h
        · left; linear_combination h
    · rintro (h | h)
      · have hAB : A + B = -((omega : ℂ) * B) := by
          rw [h]; linear_combination B * hsum3
        constructor
        · rw [h, norm_mul, hω2, one_mul]
        · rw [hAB, norm_neg, norm_mul, hω1, one_mul]
      · have hAB : A + B = -((omega : ℂ) ^ 2 * B) := by
          rw [h]; linear_combination B * hsum''
        constructor
        · rw [h, norm_mul, hω1, one_mul]
        · rw [hAB, norm_neg, norm_mul, hω2, one_mul]
  have hgoal : (p + (omega : ℂ) * q + (omega : ℂ) ^ 2 * r = 0 ∨
      p + (omega : ℂ) ^ 2 * q + (omega : ℂ) * r = 0) ↔
      (A = (omega : ℂ) ^ 2 * B ∨ A = (omega : ℂ) * B) := by
    constructor
    · rintro (h | h)
      · left; rw [e1] at h; linear_combination h
      · right; rw [e2] at h; linear_combination h
    · rintro (h | h)
      · left; rw [e1]; linear_combination h
      · right; rw [e2]; linear_combination h
  have hdist : (‖p - q‖ = ‖q - r‖ ∧ ‖q - r‖ = ‖r - p‖) ↔ (‖A‖ = ‖B‖ ∧ ‖B‖ = ‖A + B‖) := by
    have hrp : r - p = -(A + B) := by rw [hAB]; abel
    rw [hA, hB, hrp, norm_neg]
  rw [hdist, hmain, hgoal]


/-! ## Transport to `E` -/

section Plane

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable {o : Orientation ℝ E (Fin 2)}

/-- The linear (Napoleon) criterion for an equilateral triangle in `E`. -/
theorem m6_equilateral_iff_napoleon (P Q R : E) :
    Equilateral P Q R ↔
      (toComplex o P + (omega : ℂ) * toComplex o Q + (omega : ℂ) ^ 2 * toComplex o R = 0 ∨
        toComplex o P + (omega : ℂ) ^ 2 * toComplex o Q + (omega : ℂ) * toComplex o R = 0) := by
  have hPQ : dist P Q = ‖toComplex o P - toComplex o Q‖ := by
    rw [dist_eq_norm, ← toComplex_norm o (P - Q), toComplex_sub]
  have hQR : dist Q R = ‖toComplex o Q - toComplex o R‖ := by
    rw [dist_eq_norm, ← toComplex_norm o (Q - R), toComplex_sub]
  have hRP : dist R P = ‖toComplex o R - toComplex o P‖ := by
    rw [dist_eq_norm, ← toComplex_norm o (R - P), toComplex_sub]
  show (dist P Q = dist Q R ∧ dist Q R = dist R P) ↔ _
  rw [hPQ, hQR, hRP]
  exact m6_complex_equilateral_iff _ _ _

/-- `Equilateral` is invariant under the cyclic permutation of its three vertices. -/
theorem m6_equilateral_cyclic (P Q R : E) :
    Equilateral Q R P ↔ Equilateral P Q R := by
  show (dist Q R = dist R P ∧ dist R P = dist P Q) ↔ (dist P Q = dist Q R ∧ dist Q R = dist R P)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2.symm.trans h1.symm, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h2.symm.trans h1.symm⟩

/-- The cyclic shift `(i,j,k) ↦ (j,k,i)` of the triangle is the cyclic action `m7_cyclic`. -/
theorem m6_tricolor_cyclic (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    Equilateral ((T.m7_cyclic).tricolorTriangle ⟨i, j, k⟩).first
        ((T.m7_cyclic).tricolorTriangle ⟨i, j, k⟩).second
        ((T.m7_cyclic).tricolorTriangle ⟨i, j, k⟩).third ↔
      Equilateral (T.tricolorTriangle ⟨k, i, j⟩).first (T.tricolorTriangle ⟨k, i, j⟩).second
        (T.tricolorTriangle ⟨k, i, j⟩).third := by
  have h1 : ((T.m7_cyclic).tricolorTriangle ⟨i, j, k⟩).first =
      T.constellationPoint ⟨.green, i, j⟩ := by
    show (T.m7_cyclic).constellationPoint ⟨.red, i, j⟩ = _
    exact OrientedTriangle.m3_cp_cyclic_red T i j
  have h2 : ((T.m7_cyclic).tricolorTriangle ⟨i, j, k⟩).second =
      T.constellationPoint ⟨.blue, j, k⟩ := by
    show (T.m7_cyclic).constellationPoint ⟨.green, j, k⟩ = _
    exact OrientedTriangle.m3_cp_cyclic_green T j k
  have h3 : ((T.m7_cyclic).tricolorTriangle ⟨i, j, k⟩).third =
      T.constellationPoint ⟨.red, k, i⟩ := by
    show (T.m7_cyclic).constellationPoint ⟨.blue, k, i⟩ = _
    exact OrientedTriangle.m3_cp_cyclic_blue T k i
  rw [h1, h2, h3]
  exact m6_equilateral_cyclic _ _ _

/-- The `(0,0,0)` tricolor triangle is Morley's triangle `XYZ`. -/
theorem m6_tricolor_zero (T : OrientedTriangle E o) :
    Equilateral (T.tricolorTriangle ⟨0, 0, 0⟩).first (T.tricolorTriangle ⟨0, 0, 0⟩).second
      (T.tricolorTriangle ⟨0, 0, 0⟩).third := by
  have hl : labelAngle (0 : TrisectorLabel) = 0 := by simp [labelAngle]
  have h1 : (T.tricolorTriangle ⟨0, 0, 0⟩).first = T.X := by
    show T.constellationPoint ⟨.red, 0, 0⟩ = _
    simp only [OrientedTriangle.constellationPoint, hl, sub_zero]
    rfl
  have h2 : (T.tricolorTriangle ⟨0, 0, 0⟩).second = T.Y := by
    show T.constellationPoint ⟨.green, 0, 0⟩ = _
    simp only [OrientedTriangle.constellationPoint, hl, sub_zero]
    rfl
  have h3 : (T.tricolorTriangle ⟨0, 0, 0⟩).third = T.Z := by
    show T.constellationPoint ⟨.blue, 0, 0⟩ = _
    simp only [OrientedTriangle.constellationPoint, hl, sub_zero]
    rfl
  rw [h1, h2, h3]
  exact OrientedTriangle.morley T

/-- The explicit complex position of the red constellation points. -/
theorem m6_toComplex_cp_red (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, i, j⟩) =
      toComplex o T.B +
        ((Real.sin (T.gamma - labelAngle j / 2) /
            Real.sin (T.beta + T.gamma - (labelAngle i + labelAngle j) / 2) : ℝ) : ℂ) *
          toComplex o T.a * Circle.exp (T.beta - labelAngle i / 2) := by
  rw [OrientedTriangle.m3_pos_red, toComplex_add, toComplex_smul, toComplex_rotateVector]
  push_cast
  ring

/-- The explicit complex position of the green constellation points. -/
theorem m6_toComplex_cp_green (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.green, i, j⟩) =
      toComplex o T.C +
        ((Real.sin (T.alpha - labelAngle j / 2) /
            Real.sin (T.gamma + T.alpha - (labelAngle i + labelAngle j) / 2) : ℝ) : ℂ) *
          toComplex o T.b * Circle.exp (T.gamma - labelAngle i / 2) := by
  rw [OrientedTriangle.m3_pos_green, toComplex_add, toComplex_smul, toComplex_rotateVector]
  push_cast
  ring

/-- The explicit complex position of the blue constellation points. -/
theorem m6_toComplex_cp_blue (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.blue, i, j⟩) =
      toComplex o T.A +
        ((Real.sin (T.beta - labelAngle j / 2) /
            Real.sin (T.alpha + T.beta - (labelAngle i + labelAngle j) / 2) : ℝ) : ℂ) *
          toComplex o T.c * Circle.exp (T.alpha - labelAngle i / 2) := by
  rw [OrientedTriangle.m3_pos_blue, toComplex_add, toComplex_smul, toComplex_rotateVector]
  push_cast
  ring

/-- The Napoleon sum `S₊` of the tricolor triangle with labels `(i,j,k)`. -/
noncomputable def m6_napPlus (T : OrientedTriangle E o) (i j k : TrisectorLabel) : ℂ :=
  toComplex o (T.constellationPoint ⟨.red, i, j⟩) +
    (omega : ℂ) * toComplex o (T.constellationPoint ⟨.green, j, k⟩) +
      (omega : ℂ) ^ 2 * toComplex o (T.constellationPoint ⟨.blue, k, i⟩)

/-- The Napoleon sum `S₋` of the tricolor triangle with labels `(i,j,k)`. -/
noncomputable def m6_napMinus (T : OrientedTriangle E o) (i j k : TrisectorLabel) : ℂ :=
  toComplex o (T.constellationPoint ⟨.red, i, j⟩) +
    (omega : ℂ) ^ 2 * toComplex o (T.constellationPoint ⟨.green, j, k⟩) +
      (omega : ℂ) * toComplex o (T.constellationPoint ⟨.blue, k, i⟩)

/-- The tricolor triangle is equilateral exactly when one of its two Napoleon sums vanishes. -/
theorem m6_tricolor_equilateral_iff_napoleon (T : OrientedTriangle E o)
    (q : OrientedTriangle.TricolorIndex) :
    Equilateral (T.tricolorTriangle q).first (T.tricolorTriangle q).second
        (T.tricolorTriangle q).third ↔
      (m6_napPlus T q.i q.j q.k = 0 ∨ m6_napMinus T q.i q.j q.k = 0) :=
  m6_equilateral_iff_napoleon _ _ _

/-- `S₊` vanishes on the label `(0,0,0)`; this is Morley's theorem in Napoleon form. -/
theorem m6_napPlus_zero_zero_zero (T : OrientedTriangle E o) :
    m6_napPlus T 0 0 0 = 0 := by
  have hl : labelAngle (0 : TrisectorLabel) = 0 := by simp [labelAngle]
  have h1 : T.constellationPoint ⟨.red, 0, 0⟩ = T.X := by
    show T.constellationPoint ⟨.red, 0, 0⟩ = _
    simp only [OrientedTriangle.constellationPoint, hl, sub_zero]
    rfl
  have h2 : T.constellationPoint ⟨.green, 0, 0⟩ = T.Y := by
    show T.constellationPoint ⟨.green, 0, 0⟩ = _
    simp only [OrientedTriangle.constellationPoint, hl, sub_zero]
    rfl
  have h3 : T.constellationPoint ⟨.blue, 0, 0⟩ = T.Z := by
    show T.constellationPoint ⟨.blue, 0, 0⟩ = _
    simp only [OrientedTriangle.constellationPoint, hl, sub_zero]
    rfl
  have hpos : 0 < (conj (toComplex o T.Y - toComplex o T.X) *
      (toComplex o T.Z - toComplex o T.X)).im := by
    have h := OrientedTriangle.m1_XYZ_pos T
    rw [show orientedArea o (T.Y - T.X) (T.Z - T.X)
        = (conj (toComplex o (T.Y - T.X)) * toComplex o (T.Z - T.X)).im from
      areaForm_complex (o := o) (T.Y - T.X) (T.Z - T.X)] at h
    rwa [toComplex_sub, toComplex_sub] at h
  have hXY : dist T.X T.Y = ‖toComplex o T.Y - toComplex o T.X‖ := by
    rw [dist_eq_norm, norm_sub_rev, ← toComplex_norm o (T.Y - T.X), toComplex_sub]
  have hYZ : dist T.Y T.Z = ‖toComplex o T.Z - toComplex o T.Y‖ := by
    rw [dist_eq_norm, norm_sub_rev, ← toComplex_norm o (T.Z - T.Y), toComplex_sub]
  have hZX : dist T.Z T.X = ‖toComplex o T.X - toComplex o T.Z‖ := by
    rw [dist_eq_norm, norm_sub_rev, ← toComplex_norm o (T.X - T.Z), toComplex_sub]
  have heq : toComplex o T.X + (omega : ℂ) * toComplex o T.Y +
      (omega : ℂ) ^ 2 * toComplex o T.Z = 0 := by
    refine (w9_complex_equilateral _ _ _ hpos).mp ⟨?_, ?_⟩
    · rw [← hXY, ← hYZ]; exact (OrientedTriangle.morley T).1
    · rw [← hYZ, ← hZX]; exact (OrientedTriangle.morley T).2
  rw [m6_napPlus, h1, h2, h3]
  exact heq

/-- Cyclic transfer of the `S₊` Napoleon sum: `m7_cyclic` rotates the three colours. -/
theorem m6_napPlus_cyclic (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    m6_napPlus T k i j = (omega : ℂ) * m6_napPlus T.m7_cyclic i j k := by
  have h1 : T.m7_cyclic.constellationPoint ⟨.red, i, j⟩ = T.constellationPoint ⟨.green, i, j⟩ :=
    OrientedTriangle.m3_cp_cyclic_red T i j
  have h2 : T.m7_cyclic.constellationPoint ⟨.green, j, k⟩ = T.constellationPoint ⟨.blue, j, k⟩ :=
    OrientedTriangle.m3_cp_cyclic_green T j k
  have h3 : T.m7_cyclic.constellationPoint ⟨.blue, k, i⟩ = T.constellationPoint ⟨.red, k, i⟩ :=
    OrientedTriangle.m3_cp_cyclic_blue T k i
  have key : ∀ x y z : ℂ, (omega : ℂ) * (x + (omega : ℂ) * y + (omega : ℂ) ^ 2 * z)
      = z + (omega : ℂ) * x + (omega : ℂ) ^ 2 * y := by
    intro x y z
    rw [mul_add, mul_add,
      show (omega : ℂ) * ((omega : ℂ) ^ 2 * z) = (omega : ℂ) ^ 3 * z from by ring, omega_cubed,
      one_mul,
      show (omega : ℂ) * ((omega : ℂ) * y) = (omega : ℂ) ^ 2 * y from by ring]
    ring
  rw [m6_napPlus, m6_napPlus, h1, h2, h3]
  exact (key _ _ _).symm

/-- Cyclic transfer of the `S₋` Napoleon sum. -/
theorem m6_napMinus_cyclic (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    m6_napMinus T k i j = (omega : ℂ) ^ 2 * m6_napMinus T.m7_cyclic i j k := by
  have h1 : T.m7_cyclic.constellationPoint ⟨.red, i, j⟩ = T.constellationPoint ⟨.green, i, j⟩ :=
    OrientedTriangle.m3_cp_cyclic_red T i j
  have h2 : T.m7_cyclic.constellationPoint ⟨.green, j, k⟩ = T.constellationPoint ⟨.blue, j, k⟩ :=
    OrientedTriangle.m3_cp_cyclic_green T j k
  have h3 : T.m7_cyclic.constellationPoint ⟨.blue, k, i⟩ = T.constellationPoint ⟨.red, k, i⟩ :=
    OrientedTriangle.m3_cp_cyclic_blue T k i
  have key : ∀ x y z : ℂ, (omega : ℂ) ^ 2 * (x + (omega : ℂ) ^ 2 * y + (omega : ℂ) * z)
      = z + (omega : ℂ) ^ 2 * x + (omega : ℂ) * y := by
    intro x y z
    rw [mul_add, mul_add,
      show (omega : ℂ) ^ 2 * ((omega : ℂ) * z) = (omega : ℂ) ^ 3 * z from by ring, omega_cubed,
      one_mul,
      show (omega : ℂ) ^ 2 * ((omega : ℂ) ^ 2 * y) = (omega : ℂ) ^ 3 * ((omega : ℂ) * y) from by ring,
      omega_cubed, one_mul]
    ring
  rw [m6_napMinus, m6_napMinus, h1, h2, h3]
  exact (key _ _ _).symm

/-- Vanishing of `S₊` is invariant under the cyclic relabelling `(i,j,k) ↦ (k,i,j)`. -/
theorem m6_napPlus_zero_cyclic (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    m6_napPlus T.m7_cyclic i j k = 0 ↔ m6_napPlus T k i j = 0 := by
  constructor
  · intro h
    rw [m6_napPlus_cyclic, h, mul_zero]
  · intro h
    rw [m6_napPlus_cyclic] at h
    exact (mul_eq_zero.mp h).resolve_left (Circle.coe_ne_zero omega)

/-- Vanishing of `S₋` is invariant under the cyclic relabelling `(i,j,k) ↦ (k,i,j)`. -/
theorem m6_napMinus_zero_cyclic (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    m6_napMinus T.m7_cyclic i j k = 0 ↔ m6_napMinus T k i j = 0 := by
  constructor
  · intro h
    rw [m6_napMinus_cyclic, h, mul_zero]
  · intro h
    rw [m6_napMinus_cyclic] at h
    refine (mul_eq_zero.mp h).resolve_left ?_
    exact pow_ne_zero 2 (Circle.coe_ne_zero omega)

/-- **The remaining obligation, isolated.**  If the two Napoleon sums of the tricolor
triangle vanish on the sum-classes `0` and `2` and are both non-zero on the sum-class `1`,
then `tricolor_equilateral_iff` follows.  All three hypotheses are *linear* identities in
the three vertices; the eight (resp. nine) label patterns are the only missing input. -/
theorem m6_tricolor_equilateral_iff_of_napoleon (T : OrientedTriangle E o)
    (h0 : ∀ i j k : TrisectorLabel, i + j + k = 0 → m6_napPlus T i j k = 0)
    (h2 : ∀ i j k : TrisectorLabel, i + j + k = 2 → m6_napMinus T i j k = 0)
    (h1 : ∀ i j k : TrisectorLabel, i + j + k = 1 →
      m6_napPlus T i j k ≠ 0 ∧ m6_napMinus T i j k ≠ 0)
    (q : OrientedTriangle.TricolorIndex) :
    Equilateral (T.tricolorTriangle q).first (T.tricolorTriangle q).second
        (T.tricolorTriangle q).third ↔ q.i + q.j + q.k ≠ 1 := by
  rw [m6_tricolor_equilateral_iff_napoleon]
  constructor
  · rintro (h | h) hsum
    · exact (h1 q.i q.j q.k hsum).1 h
    · exact (h1 q.i q.j q.k hsum).2 h
  · intro hsum
    rcases OrientedTriangle.m4_label_cases (q.i + q.j + q.k) with hs | hs | hs
    · left; exact h0 q.i q.j q.k hs
    · exact absurd hs hsum
    · right; exact h2 q.i q.j q.k hs


end Plane


noncomputable section
open scoped Real RealInnerProductSpace ComplexConjugate Matrix

namespace OrientedTriangle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable {o : Orientation ℝ E (Fin 2)}

theorem m3p_exp_lab0 (a : ℝ) :
    (Circle.exp (a - labelAngle (0 : TrisectorLabel)) : ℂ) = (Circle.exp a : ℂ) := by
  rw [labelAngle_zero, sub_zero]

theorem m3p_exp_lab1 (a : ℝ) :
    (Circle.exp (a - labelAngle (1 : TrisectorLabel)) : ℂ) = (Circle.exp a : ℂ) * (omega : ℂ) ^ 2 := by
  rw [exp_sub_labelAngle, labelAngle_exp, show ((1 : ZMod 3)).val = 1 from by decide, pow_one,
    omega_inv']

theorem m3p_exp_lab2 (a : ℝ) :
    (Circle.exp (a - labelAngle (2 : TrisectorLabel)) : ℂ) = (Circle.exp a : ℂ) * (omega : ℂ) := by
  rw [exp_sub_labelAngle, labelAngle_exp, show ((2 : ZMod 3)).val = 2 from by decide, omega_sq_inv]

theorem m3p_exp_succ (a : ℝ) (s : TrisectorLabel) :
    (Circle.exp (a - labelAngle (s + 1)) : ℂ) =
      (Circle.exp (a - labelAngle s) : ℂ) * (omega : ℂ) ^ 2 := by
  rw [exp_sub_labelAngle, exp_sub_labelAngle, labelAngle_succ_exp, mul_inv, omega_inv']
  ring

theorem m3p_exp_add_two (a : ℝ) (s : TrisectorLabel) :
    (Circle.exp (a - labelAngle (s + 2)) : ℂ) =
      (Circle.exp (a - labelAngle s) : ℂ) * (omega : ℂ) := by
  rw [exp_sub_labelAngle, exp_sub_labelAngle, labelAngle_add_two_exp, mul_inv, omega_sq_inv]
  ring

theorem m3p_omega_cubed : (omega : ℂ) ^ 3 = 1 := omega_cubed

theorem m3p_one_sub_omega_sq :
    (1 : ℂ) - (omega : ℂ) ^ 2 = -(Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (omega : ℂ)) := by
  have h2 : (omega : ℂ) ^ 2 = (Circle.exp (labelAngle (2 : TrisectorLabel)) : ℂ) := by
    rw [labelAngle_exp, show ((2 : ZMod 3)).val = 2 from by decide]
  rw [h2, m6_one_sub_exp, labelAngle_two, show 2 * (2 * Real.pi / 3) / 2 = 2 * Real.pi / 3 by ring,
    m3_sin_two_pi_div_three]
  have hw : (Circle.exp (2 * Real.pi / 3) : ℂ) = (omega : ℂ) := rfl
  rw [hw]
  push_cast
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable {o : Orientation ℝ E (Fin 2)}

theorem m3p_red_form0 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    T.constellationPoint ⟨.red, s, 0⟩ =
      T.C + ofComplex o (toComplex o (T.B - T.C) *
        ((1 - (Circle.exp (2 * T.beta - labelAngle s) : ℂ)) /
          (1 - (Circle.exp (2 * T.gamma) : ℂ) * (Circle.exp (2 * T.beta - labelAngle s) : ℂ)))) := by
  show rotationFixedPoint o T.C T.B (2 * T.gamma - labelAngle (0 : TrisectorLabel))
      (2 * T.beta - labelAngle s) = _
  rw [rotationFixedPoint, m3p_exp_lab0]

theorem m3p_red_form1 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    T.constellationPoint ⟨.red, s + 1, 2⟩ =
      T.C + ofComplex o (toComplex o (T.B - T.C) *
        ((1 - (Circle.exp (2 * T.beta - labelAngle s) : ℂ) * (omega : ℂ) ^ 2) /
          (1 - (Circle.exp (2 * T.gamma) : ℂ) * (Circle.exp (2 * T.beta - labelAngle s) : ℂ)))) := by
  show rotationFixedPoint o T.C T.B (2 * T.gamma - labelAngle (2 : TrisectorLabel))
      (2 * T.beta - labelAngle (s + 1)) = _
  rw [rotationFixedPoint, m3p_exp_lab2 (2 * T.gamma), m3p_exp_succ (2 * T.beta) s]
  have hAB : ((Circle.exp (2 * T.gamma) : ℂ) * (omega : ℂ)) *
      ((Circle.exp (2 * T.beta - labelAngle s) : ℂ) * (omega : ℂ) ^ 2) =
      (Circle.exp (2 * T.gamma) : ℂ) * (Circle.exp (2 * T.beta - labelAngle s) : ℂ) := by
    linear_combination ((Circle.exp (2 * T.gamma) : ℂ) *
      (Circle.exp (2 * T.beta - labelAngle s) : ℂ)) * m3p_omega_cubed
  rw [hAB]

theorem m3p_red_form2 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    T.constellationPoint ⟨.red, s + 2, 1⟩ =
      T.C + ofComplex o (toComplex o (T.B - T.C) *
        ((1 - (Circle.exp (2 * T.beta - labelAngle s) : ℂ) * (omega : ℂ)) /
          (1 - (Circle.exp (2 * T.gamma) : ℂ) * (Circle.exp (2 * T.beta - labelAngle s) : ℂ)))) := by
  show rotationFixedPoint o T.C T.B (2 * T.gamma - labelAngle (1 : TrisectorLabel))
      (2 * T.beta - labelAngle (s + 2)) = _
  rw [rotationFixedPoint, m3p_exp_lab1 (2 * T.gamma), m3p_exp_add_two (2 * T.beta) s]
  have hAB : ((Circle.exp (2 * T.gamma) : ℂ) * (omega : ℂ) ^ 2) *
      ((Circle.exp (2 * T.beta - labelAngle s) : ℂ) * (omega : ℂ)) =
      (Circle.exp (2 * T.gamma) : ℂ) * (Circle.exp (2 * T.beta - labelAngle s) : ℂ) := by
    linear_combination ((Circle.exp (2 * T.gamma) : ℂ) *
      (Circle.exp (2 * T.beta - labelAngle s) : ℂ)) * m3p_omega_cubed
  rw [hAB]


/-- Difference of the `s`-th red monochrome side: the `0 -> 1` side. -/
theorem m3p_red_diff12 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, s + 1, 2⟩ - T.constellationPoint ⟨.red, s, 0⟩) =
      toComplex o (T.B - T.C) *
        ((Circle.exp (2 * T.beta - labelAngle s) : ℂ) * (1 - (omega : ℂ) ^ 2) /
          (1 - (Circle.exp (2 * T.gamma) : ℂ) * (Circle.exp (2 * T.beta - labelAngle s) : ℂ))) := by
  rw [m3p_red_form1, m3p_red_form0, toComplex_sub, toComplex_add, toComplex_add,
    toComplex_ofComplex, toComplex_ofComplex]
  ring

/-- Difference of the `s`-th red monochrome side: the `1 -> 2` side. -/
theorem m3p_red_diff23 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, s + 2, 1⟩ - T.constellationPoint ⟨.red, s + 1, 2⟩) =
      toComplex o (T.B - T.C) *
        ((Circle.exp (2 * T.beta - labelAngle s) : ℂ) * ((omega : ℂ) ^ 2 - (omega : ℂ)) /
          (1 - (Circle.exp (2 * T.gamma) : ℂ) * (Circle.exp (2 * T.beta - labelAngle s) : ℂ))) := by
  rw [m3p_red_form2, m3p_red_form1, toComplex_sub, toComplex_add, toComplex_add,
    toComplex_ofComplex, toComplex_ofComplex]
  ring

/-- Difference of the `s`-th red monochrome side: the `2 -> 0` side. -/
theorem m3p_red_diff31 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, s, 0⟩ - T.constellationPoint ⟨.red, s + 2, 1⟩) =
      toComplex o (T.B - T.C) *
        ((Circle.exp (2 * T.beta - labelAngle s) : ℂ) * ((omega : ℂ) - 1) /
          (1 - (Circle.exp (2 * T.gamma) : ℂ) * (Circle.exp (2 * T.beta - labelAngle s) : ℂ))) := by
  rw [m3p_red_form0, m3p_red_form2, toComplex_sub, toComplex_add, toComplex_add,
    toComplex_ofComplex, toComplex_ofComplex]
  ring

/-- The basic complex identity behind the direction classification of the nine joins
(multiplied form: no division). -/
theorem m3p_key (b g ls : ℝ) :
    (Circle.exp (2 * b - ls) : ℂ) * (1 - (omega : ℂ) ^ 2) * (2 * (Real.sin (b + g - ls / 2) : ℂ)) =
      ((Real.sqrt 3 : ℝ) : ℂ) *
        ((1 - (Circle.exp (2 * g) : ℂ) * (Circle.exp (2 * b - ls) : ℂ)) *
          (Circle.exp (b - g - ls / 2) : ℂ) * (omega : ℂ)) := by
  have hX : (1 - (Circle.exp (2 * g) : ℂ) * (Circle.exp (2 * b - ls) : ℂ) : ℂ) =
      (1 : ℂ) - (Circle.exp (2 * g + (2 * b - ls)) : ℂ) := by
    rw [m6_circle_exp_mul]
  rw [hX, m6_one_sub_exp]
  rw [show 2 * g + (2 * b - ls) = 2 * (b + g - ls / 2) by ring,
    show (2 * (b + g - ls / 2)) / 2 = b + g - ls / 2 by ring]
  have hsplit_exp : (Circle.exp (2 * b - ls) : ℂ) =
      (Circle.exp (b + g - ls / 2) : ℂ) * (Circle.exp (b - g - ls / 2) : ℂ) := by
    rw [show 2 * b - ls = (b + g - ls / 2) + (b - g - ls / 2) by ring, Circle.exp_add,
      Circle.coe_mul]
  rw [hsplit_exp, m3p_one_sub_omega_sq]
  ring

/-- `aStar` scaled by the side length is minus the side vector `B - C`. -/
theorem m3p_aStar_scaled (T : OrientedTriangle E o) :
    toComplex o T.aStar * ((T.aLength : ℝ) : ℂ) = -(toComplex o (T.B - T.C)) := by
  have ha : T.aStar = T.aLength⁻¹ • T.a := rfl
  rw [ha, toComplex_smul]
  have hTa : T.a = T.C - T.B := rfl
  rw [hTa, show toComplex o (T.C - T.B) = -toComplex o (T.B - T.C) by
    rw [← toComplex_neg]; congr 1; abel]
  have hinv : ((T.aLength⁻¹ : ℝ) : ℂ) * ((T.aLength : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt T.aLength_pos), Complex.ofReal_one]
  calc ((T.aLength⁻¹ : ℝ) : ℂ) * -(toComplex o (T.B - T.C)) * ((T.aLength : ℝ) : ℂ)
      = -toComplex o (T.B - T.C) * (((T.aLength⁻¹ : ℝ) : ℂ) * ((T.aLength : ℝ) : ℂ)) := by ring
    _ = -toComplex o (T.B - T.C) := by rw [hinv, mul_one]

/-- `cStar` in terms of `aStar`: the two differ by the exponential of `3β`. -/
theorem m3p_cStar_form (T : OrientedTriangle E o) :
    toComplex o T.cStar = -((Circle.exp (3 * T.beta) : ℂ) * toComplex o T.aStar) := by
  set Zc : ℂ := toComplex o T.cStar with hZc
  set Za : ℂ := toComplex o T.aStar with hZa
  set W : ℂ := toComplex o (T.B - T.C) with hW
  set X : ℂ := (T.delta : ℂ) * (Real.sin (3 * T.alpha) : ℂ) with hX
  set e3 : ℂ := (Circle.exp (3 * T.beta) : ℂ) with he3
  set em3 : ℂ := (Circle.exp (-3 * T.beta) : ℂ) with hem3
  have hXa : X = ((T.aLength : ℝ) : ℂ) := by
    rw [hX, ← Complex.ofReal_mul, T.side_lengths_sine.1]
  have hXne : X ≠ 0 := by
    rw [hXa]
    exact_mod_cast (ne_of_gt T.aLength_pos)
  have hem3' : em3 ≠ 0 := by rw [hem3]; exact m4_circle_exp_ne_zero _
  have hexp : em3 * e3 = 1 := by
    rw [hem3, he3, m6_circle_exp_mul, show -3 * T.beta + 3 * T.beta = 0 by ring]
    simp
  have h1 : W = X * em3 * Zc := by
    rw [hW, hZc, hX, hem3]
    exact toComplex_B_sub_C (T := T)
  have h2 : W = -(Za * X) := by
    have hh := m3p_aStar_scaled (T := T)
    rw [hW, hZa, hXa]
    rw [hh]
    ring
  calc Zc = W / (X * em3) := by
        rw [h1]
        field_simp
    _ = (-(Za * X)) / (X * em3) := by rw [h2]
    _ = -(e3 * Za) := by
        have hXne' : X * em3 ≠ 0 := mul_ne_zero hXne hem3'
        field_simp
        rw [mul_assoc, hexp, mul_one]

/-- `bStar` in terms of `aStar`: the two differ by the exponential of `3(α+β)`. -/
theorem m3p_bStar_form (T : OrientedTriangle E o) :
    toComplex o T.bStar = (Circle.exp (3 * (T.alpha + T.beta)) : ℂ) * toComplex o T.aStar := by
  have hc := m3p_cStar_form (T := T)
  have hCA := toComplex_C_sub_A (T := T)
  rw [hc] at hCA
  have hYb : ((T.bLength : ℝ) : ℂ) = (T.delta : ℂ) * (Real.sin (3 * T.beta) : ℂ) := by
    rw [← Complex.ofReal_mul, T.side_lengths_sine.2.1]
  have hb : toComplex o T.bStar * ((T.bLength : ℝ) : ℂ) = -(toComplex o (T.C - T.A)) := by
    have hstar : T.bStar = T.bLength⁻¹ • T.b := rfl
    rw [hstar, toComplex_smul]
    have hTb : T.b = T.A - T.C := rfl
    rw [hTb, show toComplex o (T.A - T.C) = -toComplex o (T.C - T.A) by
      rw [← toComplex_neg]; congr 1; abel]
    have hinv : ((T.bLength⁻¹ : ℝ) : ℂ) * ((T.bLength : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt T.bLength_pos), Complex.ofReal_one]
    calc ((T.bLength⁻¹ : ℝ) : ℂ) * -(toComplex o (T.C - T.A)) * ((T.bLength : ℝ) : ℂ)
        = -toComplex o (T.C - T.A) * (((T.bLength⁻¹ : ℝ) : ℂ) * ((T.bLength : ℝ) : ℂ)) := by
          ring
      _ = -toComplex o (T.C - T.A) := by rw [hinv, mul_one]
  have hL : -(toComplex o (T.C - T.A)) =
      (Circle.exp (3 * (T.alpha + T.beta)) : ℂ) * toComplex o T.aStar * ((T.bLength : ℝ) : ℂ) := by
    rw [hCA, hYb,
      show (Circle.exp (3 * (T.alpha + T.beta)) : ℂ) =
        (Circle.exp (3 * T.alpha) : ℂ) * (Circle.exp (3 * T.beta) : ℂ) from by
        rw [show 3 * (T.alpha + T.beta) = 3 * T.alpha + 3 * T.beta by ring, Circle.exp_add,
          Circle.coe_mul]]
    ring
  exact mul_right_cancel₀ (by exact_mod_cast (ne_of_gt T.bLength_pos)) (hb.trans hL)

/-- `e^{iπ} = -1` on the circle. -/
theorem m3p_exp_pi : (Circle.exp Real.pi : ℂ) = -1 := by
  simpa using exp_nat_pi 1

/-- `2π` is a period of the circle exponential. -/
theorem m3p_exp_two_pi (θ : ℝ) : (Circle.exp (θ + 2 * Real.pi) : ℂ) = (Circle.exp θ : ℂ) := by
  have h2pi : (Circle.exp (2 * Real.pi) : ℂ) = 1 := by
    simpa using exp_nat_pi 2
  rw [(m6_circle_exp_mul θ (2 * Real.pi)).symm, h2pi, mul_one]

/-- `ω ^ 2` as an exponential. -/
theorem m3p_omega_sq_exp : ((omega : ℂ)) ^ 2 = (Circle.exp (4 * Real.pi / 3) : ℂ) := by
  rw [pow_two, show (omega : ℂ) = (Circle.exp (2 * Real.pi / 3) : ℂ) from rfl, m6_circle_exp_mul,
    show 2 * Real.pi / 3 + 2 * Real.pi / 3 = 4 * Real.pi / 3 by ring]

/-- `e^{iπ/3} = -ω²`. -/
theorem m3p_exp_pi_div_three : (Circle.exp (Real.pi / 3) : ℂ) = -(omega : ℂ) ^ 2 := by
  have h : (Circle.exp (Real.pi / 3) : ℂ) * (-1) = (omega : ℂ) ^ 2 := by
    rw [← m3p_exp_pi, m6_circle_exp_mul,
      show Real.pi / 3 + Real.pi = 4 * Real.pi / 3 by ring, m3p_omega_sq_exp]
  linear_combination -h

/-- `e^{-iπ/3} = -ω`. -/
theorem m3p_exp_neg_pi_div_three : (Circle.exp (-(Real.pi / 3)) : ℂ) = -(omega : ℂ) := by
  have hw : (omega : ℂ) = (Circle.exp (2 * Real.pi / 3) : ℂ) := rfl
  rw [hw, show 2 * Real.pi / 3 = -(Real.pi / 3) + Real.pi by ring, Circle.exp_add,
    Circle.coe_mul, m3p_exp_pi]
  ring

/-- The half-label phase, `s = 0`. -/
theorem m3p_phase0 :
    (Circle.exp (-(labelAngle (0 : TrisectorLabel)) / 2) : ℂ) = 1 := by
  rw [labelAngle_zero, neg_zero, zero_div, Circle.exp_zero]
  simp

/-- The half-label phase, `s = 1`. -/
theorem m3p_phase1 :
    (Circle.exp (-(labelAngle (1 : TrisectorLabel)) / 2) : ℂ) = -(omega : ℂ) := by
  rw [labelAngle_one, show -(2 * Real.pi / 3) / 2 = -(Real.pi / 3) by ring,
    m3p_exp_neg_pi_div_three]

/-- The half-label phase, `s = 2`. -/
theorem m3p_phase2 :
    (Circle.exp (-(labelAngle (2 : TrisectorLabel)) / 2) : ℂ) = (omega : ℂ) ^ 2 := by
  rw [labelAngle_two, show -(2 * (2 * Real.pi / 3)) / 2 = -(2 * Real.pi / 3) by ring]
  rw [← m3p_exp_two_pi (-(2 * Real.pi / 3)),
    show -(2 * Real.pi / 3) + 2 * Real.pi = 4 * Real.pi / 3 by ring, ← m3p_omega_sq_exp]

/-- The common scalar of the three Morley side direction formulas. -/
noncomputable def m3pRho (T : OrientedTriangle E o) : ℝ :=
  4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma

theorem m3p_rho_pos (T : OrientedTriangle E o) : 0 < m3pRho T := by
  rw [m3pRho]
  have h1 := m7_delta_pos T
  have h2 := m7_sin_alpha_pos T
  have h3 := m7_sin_beta_pos T
  have h4 := m7_sin_gamma_pos T
  positivity

/-- The coefficient of the three join direction formulas. -/
noncomputable def m3pJoinCoef (T : OrientedTriangle E o) (s : TrisectorLabel) : ℝ :=
  -(T.aLength * (Real.sqrt 3 / (2 * Real.sin (T.beta + T.gamma - labelAngle s / 2))))

/-- The complex frame in which all nine joins have directions among three values. -/
noncomputable def m3pFrame (T : OrientedTriangle E o) : ℂ :=
  toComplex o T.aStar * (Circle.exp (T.beta - T.gamma) : ℂ)

theorem m3p_Frame_ne (T : OrientedTriangle E o) : m3pFrame T ≠ 0 := by
  rw [m3pFrame]
  have h1 : toComplex o T.aStar ≠ 0 := by
    intro h
    have hn := m7_norm_aStar T
    rw [← toComplex_norm (o := o) T.aStar, h] at hn
    simp at hn
  exact mul_ne_zero h1 (m4_circle_exp_ne_zero _)

/-- The direction of `Y - X` in the frame. -/
theorem m3p_Z_YX (T : OrientedTriangle E o) :
    toComplex o (T.Y - T.X) =
      (((-(m3pRho T)) : ℝ) : ℂ) *
        (m3pFrame T * (omega : ℂ) ^ 2) := by
  rw [Y_sub_X, toComplex_smul, toComplex_rotateVector]
  have hexp : (Circle.exp (T.alpha + 2 * T.beta) : ℂ) =
      -((Circle.exp (T.beta - T.gamma) : ℂ) * (omega : ℂ) ^ 2) := by
    rw [show T.alpha + 2 * T.beta = (T.beta - T.gamma) + Real.pi / 3 by
      have h := m4_angles_sum T; linarith]
    rw [← m6_circle_exp_mul, m3p_exp_pi_div_three]
    ring
  rw [hexp, m3pFrame, m3pRho]
  push_cast
  ring

/-- The direction of `Z - Y` in the frame. -/
theorem m3p_Z_ZY (T : OrientedTriangle E o) :
    toComplex o (T.Z - T.Y) =
      (((-(m3pRho T)) : ℝ) : ℂ) *
        (m3pFrame T * 1) := by
  rw [Z_sub_Y, toComplex_smul, toComplex_rotateVector, m3p_bStar_form, m3pFrame]
  have hA : (Circle.exp (3 * (T.alpha + T.beta)) : ℂ) * (Circle.exp (T.beta + 2 * T.gamma) : ℂ) =
      -(Circle.exp (T.beta - T.gamma) : ℂ) := by
    rw [m6_circle_exp_mul,
      show 3 * (T.alpha + T.beta) + (T.beta + 2 * T.gamma) = (T.beta - T.gamma) + Real.pi by
        have h := m4_angles_sum T; linarith,
      ← m6_circle_exp_mul, m3p_exp_pi]
    ring
  have hkey : (Circle.exp (3 * (T.alpha + T.beta)) : ℂ) * toComplex o T.aStar *
      (Circle.exp (T.beta + 2 * T.gamma) : ℂ) =
      -(toComplex o T.aStar * (Circle.exp (T.beta - T.gamma) : ℂ) * 1) := by
    calc (Circle.exp (3 * (T.alpha + T.beta)) : ℂ) * toComplex o T.aStar *
          (Circle.exp (T.beta + 2 * T.gamma) : ℂ)
        = ((Circle.exp (3 * (T.alpha + T.beta)) : ℂ) * (Circle.exp (T.beta + 2 * T.gamma) : ℂ)) *
            toComplex o T.aStar := by ring
      _ = -(toComplex o T.aStar * (Circle.exp (T.beta - T.gamma) : ℂ) * 1) := by rw [hA]; ring
  rw [hkey, m3pRho]
  push_cast
  ring

/-- The direction of `X - Z` in the frame. -/
theorem m3p_Z_XZ (T : OrientedTriangle E o) :
    toComplex o (T.X - T.Z) =
      (((-(m3pRho T)) : ℝ) : ℂ) *
        (m3pFrame T * (omega : ℂ)) := by
  rw [X_sub_Z, toComplex_smul, toComplex_rotateVector, m3p_cStar_form, m3pFrame]
  have hA : (Circle.exp (3 * T.beta) : ℂ) * (Circle.exp (T.gamma + 2 * T.alpha) : ℂ) =
      (Circle.exp (T.beta - T.gamma) : ℂ) * (omega : ℂ) := by
    rw [show (omega : ℂ) = (Circle.exp (2 * Real.pi / 3) : ℂ) from rfl, m6_circle_exp_mul,
      m6_circle_exp_mul,
      show 3 * T.beta + (T.gamma + 2 * T.alpha) = (T.beta - T.gamma) + 2 * Real.pi / 3 by
        have h := m4_angles_sum T; linarith]
  have hkey : -((Circle.exp (3 * T.beta) : ℂ) * toComplex o T.aStar) *
      (Circle.exp (T.gamma + 2 * T.alpha) : ℂ) =
      -(toComplex o T.aStar * (Circle.exp (T.beta - T.gamma) : ℂ) * (omega : ℂ)) := by
    calc -((Circle.exp (3 * T.beta) : ℂ) * toComplex o T.aStar) *
          (Circle.exp (T.gamma + 2 * T.alpha) : ℂ)
        = -(((Circle.exp (3 * T.beta) : ℂ) * (Circle.exp (T.gamma + 2 * T.alpha) : ℂ)) *
            toComplex o T.aStar) := by ring
      _ = -(toComplex o T.aStar * (Circle.exp (T.beta - T.gamma) : ℂ) * (omega : ℂ)) := by
          rw [hA]; push_cast; ring
  rw [hkey, m3pRho]
  push_cast
  ring

/-- `1 - e^{iθ} ≠ 0` when `sin (θ/2) ≠ 0`. -/
theorem m3p_one_sub_exp_ne (θ : ℝ) (h : Real.sin (θ / 2) ≠ 0) :
    (1 : ℂ) - (Circle.exp θ : ℂ) ≠ 0 := by
  have hI : (-2 * Complex.I : ℂ) ≠ 0 := by
    intro hc
    have him := congrArg Complex.im hc
    simp at him
  have hs : ((Real.sin (θ / 2) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact h
  rw [m6_one_sub_exp]
  exact mul_ne_zero (mul_ne_zero hI hs) (m4_circle_exp_ne_zero _)

theorem m3p_sin_bg_ne (T : OrientedTriangle E o) (s : TrisectorLabel) :
    Real.sin (T.beta + T.gamma - labelAngle s / 2) ≠ 0 := by
  have h := m6_sin_shift_sub_ne_zero T.m6_beta_add_gamma_bounds_lt.1
    T.m6_beta_add_gamma_bounds_lt.2 s 0
  rwa [labelAngle_zero, add_zero] at h

theorem m3p_den_ne (T : OrientedTriangle E o) (s : TrisectorLabel) :
    (1 - (Circle.exp (2 * T.gamma) : ℂ) * (Circle.exp (2 * T.beta - labelAngle s) : ℂ)) ≠ 0 := by
  have hprod : (Circle.exp (2 * T.gamma) : ℂ) * (Circle.exp (2 * T.beta - labelAngle s) : ℂ) =
      (Circle.exp (2 * T.gamma + (2 * T.beta - labelAngle s)) : ℂ) := m6_circle_exp_mul _ _
  have harg : 2 * T.gamma + (2 * T.beta - labelAngle s) = 2 * (T.beta + T.gamma - labelAngle s / 2) := by
    ring
  rw [hprod, harg]
  exact m3p_one_sub_exp_ne _ (by rw [show 2 * (T.beta + T.gamma - labelAngle s / 2) / 2 =
    T.beta + T.gamma - labelAngle s / 2 by ring]; exact m3p_sin_bg_ne T s)

/-- The divided form of the key identity. -/
theorem m3p_key_div (T : OrientedTriangle E o) (s : TrisectorLabel) :
    (Circle.exp (2 * T.beta - labelAngle s) : ℂ) * (1 - (omega : ℂ) ^ 2) =
      ((Real.sqrt 3 / (2 * Real.sin (T.beta + T.gamma - labelAngle s / 2)) : ℝ) : ℂ) *
        ((1 - (Circle.exp (2 * T.gamma) : ℂ) * (Circle.exp (2 * T.beta - labelAngle s) : ℂ)) *
          (Circle.exp (T.beta - T.gamma - labelAngle s / 2) : ℂ) * (omega : ℂ)) := by
  have hs := m3p_sin_bg_ne T s
  have h2s : ((2 * Real.sin (T.beta + T.gamma - labelAngle s / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero two_ne_zero hs)
  have hcast : ((Real.sqrt 3 / (2 * Real.sin (T.beta + T.gamma - labelAngle s / 2)) : ℝ) : ℂ)
      = ((Real.sqrt 3 : ℝ) : ℂ) /
        ((2 * Real.sin (T.beta + T.gamma - labelAngle s / 2) : ℝ) : ℂ) := by
    push_cast
    ring
  have hk := m3p_key (T.beta) (T.gamma) (labelAngle s)
  rw [hcast, div_mul_eq_mul_div, eq_div_iff h2s]
  push_cast at hk ⊢
  exact hk

/-- The frame relation: `B - C = -|a| · aStar`. -/
theorem m3p_W_eq (T : OrientedTriangle E o) :
    toComplex o (T.B - T.C) = -(toComplex o T.aStar * ((T.aLength : ℝ) : ℂ)) := by
  have h := m3p_aStar_scaled (T := T)
  rw [h]
  ring

theorem m3p_exp_beta_gamma_split (T : OrientedTriangle E o) (s : TrisectorLabel) :
    (Circle.exp (T.beta - T.gamma - labelAngle s / 2) : ℂ) =
      (Circle.exp (T.beta - T.gamma) : ℂ) * (Circle.exp (-(labelAngle s) / 2) : ℂ) := by
  rw [show T.beta - T.gamma - labelAngle s / 2 = (T.beta - T.gamma) + (-(labelAngle s) / 2) by ring,
    ← m6_circle_exp_mul]

/-- The direction of the `0 -> 1` side of the `s`-th red monochrome triangle, in the frame. -/
theorem m3p_Z_join12 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, s + 1, 2⟩ - T.constellationPoint ⟨.red, s, 0⟩) =
      (((m3pJoinCoef T s) : ℝ) : ℂ) *
        (m3pFrame T * ((Circle.exp (-(labelAngle s) / 2) : ℂ) * (omega : ℂ))) := by
  have hden := m3p_den_ne T s
  have hs := m3p_sin_bg_ne T s
  rw [m3p_red_diff12, m3p_W_eq, m3p_key_div, m3p_exp_beta_gamma_split, m3pFrame]
  have hc : ((Real.sqrt 3 /
        (2 * Real.sin (T.beta + T.gamma - labelAngle s / 2)) : ℝ) : ℂ) *
      ((1 - (Circle.exp (2 * T.gamma) : ℂ) * (Circle.exp (2 * T.beta - labelAngle s) : ℂ)) *
          ((Circle.exp (T.beta - T.gamma) : ℂ) * (Circle.exp (-(labelAngle s) / 2) : ℂ)) *
        (omega : ℂ)) /
      (1 - (Circle.exp (2 * T.gamma) : ℂ) * (Circle.exp (2 * T.beta - labelAngle s) : ℂ)) =
      ((Real.sqrt 3 /
        (2 * Real.sin (T.beta + T.gamma - labelAngle s / 2)) : ℝ) : ℂ) *
        ((Circle.exp (T.beta - T.gamma) : ℂ) * (Circle.exp (-(labelAngle s) / 2) : ℂ) *
          (omega : ℂ)) := by
    field_simp
  rw [hc, m3pJoinCoef]
  push_cast
  ring

theorem m3p_omega_half : (-(omega : ℂ)) * (omega : ℂ) = -((omega : ℂ) ^ 2) := by ring

/-- The direction of the `1 -> 2` side of the `s`-th red monochrome triangle, in the frame. -/
theorem m3p_Z_join23 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, s + 2, 1⟩ - T.constellationPoint ⟨.red, s + 1, 2⟩) =
      (((m3pJoinCoef T s) : ℝ) : ℂ) *
        (m3pFrame T * ((Circle.exp (-(labelAngle s) / 2) : ℂ) * 1)) := by
  have hden := m3p_den_ne T s
  have hw0 : (omega : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hrel : (Circle.exp (2 * T.beta - labelAngle s) : ℂ) * ((omega : ℂ) ^ 2 - (omega : ℂ)) =
      ((Circle.exp (2 * T.beta - labelAngle s) : ℂ) * (1 - (omega : ℂ) ^ 2)) / (omega : ℂ) := by
    rw [eq_div_iff hw0]
    ring_nf
    rw [omega_cubed]
    ring
  rw [m3p_red_diff23, m3p_W_eq, hrel, m3p_key_div, m3p_exp_beta_gamma_split, m3pFrame]
  field_simp
  rw [m3pJoinCoef]
  push_cast
  ring

/-- The direction of the `2 -> 0` side of the `s`-th red monochrome triangle, in the frame. -/
theorem m3p_Z_join31 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, s, 0⟩ - T.constellationPoint ⟨.red, s + 2, 1⟩) =
      (((m3pJoinCoef T s) : ℝ) : ℂ) *
        (m3pFrame T * ((Circle.exp (-(labelAngle s) / 2) : ℂ) * (omega : ℂ) ^ 2)) := by
  have hden := m3p_den_ne T s
  have hrel : (Circle.exp (2 * T.beta - labelAngle s) : ℂ) * ((omega : ℂ) - 1) =
      (omega : ℂ) * ((Circle.exp (2 * T.beta - labelAngle s) : ℂ) * (1 - (omega : ℂ) ^ 2)) := by
    ring_nf
    rw [omega_cubed]
    ring
  rw [m3p_red_diff31, m3p_W_eq, hrel, m3p_key_div, m3p_exp_beta_gamma_split, m3pFrame]
  field_simp
  rw [m3pJoinCoef]
  push_cast
  ring

/-- The three Morley side vectors, indexed by `0 = Y - X`, `1 = Z - Y`, `2 = X - Z`. -/
noncomputable def m3pSide (T : OrientedTriangle E o) (d : TrisectorLabel) : E :=
  if d = 0 then T.Y - T.X else if d = 1 then T.Z - T.Y else T.X - T.Z

theorem m3p_side_zero (T : OrientedTriangle E o) : m3pSide T 0 = T.Y - T.X := by
  rw [m3pSide, if_pos rfl]

theorem m3p_side_one (T : OrientedTriangle E o) : m3pSide T 1 = T.Z - T.Y := by
  rw [m3pSide, if_neg (by decide), if_pos rfl]

theorem m3p_side_two (T : OrientedTriangle E o) : m3pSide T 2 = T.X - T.Z := by
  rw [m3pSide, if_neg (by decide), if_neg (by decide)]

theorem m3p_parallel_of_toComplex {v w : E}
    (h : ∃ r : ℝ, toComplex o w = (r : ℂ) * toComplex o v) : Parallel v w := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  apply toComplex_injective o
  rw [toComplex_smul, hr]

theorem m3p_omega4 : (omega : ℂ) ^ 4 = (omega : ℂ) := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, omega_cubed, one_mul, pow_one]

/-- Frame cancellation, `u = v` case. -/
theorem m3p_par_step1 (T : OrientedTriangle E o) {X S : E} {u v : ℂ} {c1 : ℝ}
    (hX : toComplex o X = (c1 : ℂ) * (m3pFrame T * u))
    (hS : toComplex o S = (((-(m3pRho T)) : ℝ) : ℂ) * (m3pFrame T * v))
    (huv : u = v) : Parallel S X := by
  have hρ := ne_of_gt (m3p_rho_pos T)
  have hcoe : ((-(c1 / m3pRho T) : ℝ) : ℂ) * (((-(m3pRho T)) : ℝ) : ℂ) = (c1 : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [show (-(c1 / m3pRho T)) * (-(m3pRho T)) = (c1 / m3pRho T) * (m3pRho T) from by ring,
      div_mul_cancel₀ _ hρ]
  refine m3p_parallel_of_toComplex (o := o) (v := S) ⟨-(c1 / m3pRho T), ?_⟩
  rw [hX, hS, huv]
  rw [← hcoe]
  ring

/-- Frame cancellation, `u = -v` case. -/
theorem m3p_par_step2 (T : OrientedTriangle E o) {X S : E} {u v : ℂ} {c1 : ℝ}
    (hX : toComplex o X = (c1 : ℂ) * (m3pFrame T * u))
    (hS : toComplex o S = (((-(m3pRho T)) : ℝ) : ℂ) * (m3pFrame T * v))
    (huv : u = -v) : Parallel S X := by
  have hρ := ne_of_gt (m3p_rho_pos T)
  have hcoe : ((c1 / m3pRho T : ℝ) : ℂ) * (((-(m3pRho T)) : ℝ) : ℂ) = (-c1 : ℂ) := by
    rw [← Complex.ofReal_mul,
      show (c1 / m3pRho T) * (-(m3pRho T)) = -c1 from by
        rw [show (c1 / m3pRho T) * (-(m3pRho T)) = -((c1 / m3pRho T) * (m3pRho T)) from by ring,
          div_mul_cancel₀ _ hρ]]
    exact Complex.ofReal_neg c1
  refine m3p_parallel_of_toComplex (o := o) (v := S) ⟨c1 / m3pRho T, ?_⟩
  rw [hX, hS, huv]
  have hc1 : (c1 : ℂ) = -(((c1 / m3pRho T : ℝ) : ℂ) * (((-(m3pRho T)) : ℝ) : ℂ)) := by
    rw [hcoe]
    ring
  rw [hc1]
  ring

/-- **The `0 -> 1` side of the `s`-th red monochrome triangle is parallel to the Morley side
of index `s + 2`** (`0 = Y - X`, `1 = Z - Y`, `2 = X - Z`). -/
theorem m3p_red_par12 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    Parallel (m3pSide T (s + 2))
      (T.constellationPoint ⟨.red, s + 1, 2⟩ - T.constellationPoint ⟨.red, s, 0⟩) := by
  rcases zmod3_cases s with rfl | rfl | rfl
  · rw [show ((0 : ZMod 3) + 2) = 2 from by decide, m3p_side_two]
    refine m3p_par_step1 T (m3p_Z_join12 T 0) (m3p_Z_XZ T) ?_
    rw [m3p_phase0]
    ring
  · rw [show ((1 : ZMod 3) + 2) = 0 from by decide, m3p_side_zero]
    refine m3p_par_step2 T (m3p_Z_join12 T 1) (m3p_Z_YX T) ?_
    rw [m3p_phase1]
    ring
  · rw [show ((2 : ZMod 3) + 2) = 1 from by decide, m3p_side_one]
    refine m3p_par_step1 T (m3p_Z_join12 T 2) (m3p_Z_ZY T) ?_
    rw [m3p_phase2]
    ring_nf
    rw [omega_cubed]

/-- **The `1 -> 2` side of the `s`-th red monochrome triangle is parallel to the Morley side
of index `s + 1`.** -/
theorem m3p_red_par23 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    Parallel (m3pSide T (s + 1))
      (T.constellationPoint ⟨.red, s + 2, 1⟩ - T.constellationPoint ⟨.red, s + 1, 2⟩) := by
  rcases zmod3_cases s with rfl | rfl | rfl
  · rw [show ((0 : ZMod 3) + 1) = 1 from by decide, m3p_side_one]
    refine m3p_par_step1 T (m3p_Z_join23 T 0) (m3p_Z_ZY T) ?_
    rw [m3p_phase0]
    ring
  · rw [show ((1 : ZMod 3) + 1) = 2 from by decide, m3p_side_two]
    refine m3p_par_step2 T (m3p_Z_join23 T 1) (m3p_Z_XZ T) ?_
    rw [m3p_phase1]
    ring
  · rw [show ((2 : ZMod 3) + 1) = 0 from by decide, m3p_side_zero]
    refine m3p_par_step1 T (m3p_Z_join23 T 2) (m3p_Z_YX T) ?_
    rw [m3p_phase2]
    ring

/-- **The `2 -> 0` side of the `s`-th red monochrome triangle is parallel to the Morley side
of index `s`.** -/
theorem m3p_red_par31 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    Parallel (m3pSide T s)
      (T.constellationPoint ⟨.red, s, 0⟩ - T.constellationPoint ⟨.red, s + 2, 1⟩) := by
  rcases zmod3_cases s with rfl | rfl | rfl
  · rw [m3p_side_zero]
    refine m3p_par_step1 T (m3p_Z_join31 T 0) (m3p_Z_YX T) ?_
    rw [m3p_phase0]
    ring
  · rw [m3p_side_one]
    refine m3p_par_step2 T (m3p_Z_join31 T 1) (m3p_Z_ZY T) ?_
    rw [m3p_phase1]
    ring_nf
    rw [omega_cubed]
  · rw [m3p_side_two]
    refine m3p_par_step1 T (m3p_Z_join31 T 2) (m3p_Z_XZ T) ?_
    rw [m3p_phase2]
    ring_nf
    rw [m3p_omega4]

/-- The side index shifts by one under the cyclic relabelling `m7_cyclic`. -/
theorem m3p_side_cyclic (T : OrientedTriangle E o) (d : TrisectorLabel) :
    m3pSide (m7_cyclic T) d = m3pSide T (d + 1) := by
  rcases zmod3_cases d with rfl | rfl | rfl
  · rw [show ((0 : ZMod 3) + 1) = 1 from by decide, m3p_side_zero, m3p_side_one,
      m7_cyclic_Y, m7_cyclic_X]
  · rw [show ((1 : ZMod 3) + 1) = 2 from by decide, m3p_side_one, m3p_side_two,
      m7_cyclic_Z, m7_cyclic_Y]
  · rw [show ((2 : ZMod 3) + 1) = 0 from by decide, m3p_side_two, m3p_side_zero,
      m7_cyclic_X, m7_cyclic_Z]

theorem m3p_side_ptM (T : OrientedTriangle E o) {v : E} (d : TrisectorLabel)
    (h : Parallel (m3pSide T d) v) : T.parallelToMorleySide v := by
  rcases zmod3_cases d with rfl | rfl | rfl
  · rw [m3p_side_zero] at h
    exact Or.inl h
  · rw [m3p_side_one] at h
    exact Or.inr (Or.inl h)
  · rw [m3p_side_two] at h
    exact Or.inr (Or.inr h)

/-- **Green version of `m3p_red_par12`.** -/
theorem m3p_green_par12 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    Parallel (m3pSide T s)
      (T.constellationPoint ⟨.green, s + 1, 2⟩ - T.constellationPoint ⟨.green, s, 0⟩) := by
  have h := m3p_red_par12 (m7_cyclic T) s
  rw [m3p_side_cyclic] at h
  rw [show s + 2 + 1 = s from by
      rw [add_assoc, show (2 + 1 : ZMod 3) = 0 from by decide, add_zero]] at h
  rwa [m3_cp_cyclic_red, m3_cp_cyclic_red] at h

/-- **Green version of `m3p_red_par23`.** -/
theorem m3p_green_par23 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    Parallel (m3pSide T (s + 2))
      (T.constellationPoint ⟨.green, s + 2, 1⟩ - T.constellationPoint ⟨.green, s + 1, 2⟩) := by
  have h := m3p_red_par23 (m7_cyclic T) s
  rw [m3p_side_cyclic] at h
  rw [show s + 1 + 1 = s + 2 from by
      rw [add_assoc, show (1 + 1 : ZMod 3) = 2 from by decide]] at h
  rwa [m3_cp_cyclic_red, m3_cp_cyclic_red] at h

/-- **Green version of `m3p_red_par31`.** -/
theorem m3p_green_par31 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    Parallel (m3pSide T (s + 1))
      (T.constellationPoint ⟨.green, s, 0⟩ - T.constellationPoint ⟨.green, s + 2, 1⟩) := by
  have h := m3p_red_par31 (m7_cyclic T) s
  rw [m3p_side_cyclic] at h
  skip
  rwa [m3_cp_cyclic_red, m3_cp_cyclic_red] at h

/-- **Blue version of `m3p_red_par12`.** -/
theorem m3p_blue_par12 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    Parallel (m3pSide T (s + 1))
      (T.constellationPoint ⟨.blue, s + 1, 2⟩ - T.constellationPoint ⟨.blue, s, 0⟩) := by
  have h := m3p_red_par12 (m7_cyclic (m7_cyclic T)) s
  rw [m3p_side_cyclic, m3p_side_cyclic] at h
  rw [show s + 2 + 1 + 1 = s + 1 from by
    rw [add_assoc (s + 2) 1 1, add_assoc s 2 (1 + 1),
      show (2 + (1 + 1) : ZMod 3) = 1 from by decide]] at h
  rwa [m3_cp_cyclic_red, m3_cp_cyclic_green] at h

/-- **Blue version of `m3p_red_par23`.** -/
theorem m3p_blue_par23 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    Parallel (m3pSide T s)
      (T.constellationPoint ⟨.blue, s + 2, 1⟩ - T.constellationPoint ⟨.blue, s + 1, 2⟩) := by
  have h := m3p_red_par23 (m7_cyclic (m7_cyclic T)) s
  rw [m3p_side_cyclic, m3p_side_cyclic] at h
  rw [show s + 1 + 1 + 1 = s from by
    rw [add_assoc (s + 1) 1 1, add_assoc s 1 (1 + 1),
      show (1 + (1 + 1) : ZMod 3) = 0 from by decide, add_zero]] at h
  rwa [m3_cp_cyclic_red, m3_cp_cyclic_green] at h

/-- **Blue version of `m3p_red_par31`.** -/
theorem m3p_blue_par31 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    Parallel (m3pSide T (s + 2))
      (T.constellationPoint ⟨.blue, s, 0⟩ - T.constellationPoint ⟨.blue, s + 2, 1⟩) := by
  have h := m3p_red_par31 (m7_cyclic (m7_cyclic T)) s
  rw [m3p_side_cyclic, m3p_side_cyclic] at h
  rw [show s + 1 + 1 = s + 2 from by
      rw [add_assoc, show (1 + 1 : ZMod 3) = 2 from by decide]] at h
  rwa [m3_cp_cyclic_red, m3_cp_cyclic_green] at h

/-- **Every monochrome Morley triangle has its three sides parallel to the Morley triangle.**
This is the root's `monochrome_sides_parallel`, proved here together with the exact direction
index of each side. -/
theorem m3p_monochrome_sides_parallel (T : OrientedTriangle E o) (c : TrisectorColor)
    (s : TrisectorLabel) :
    let t := T.monochromeTriangle c s
    T.parallelToMorleySide (t.second - t.first) ∧
      T.parallelToMorleySide (t.third - t.second) ∧
        T.parallelToMorleySide (t.first - t.third) := by
  refine ⟨?_, ?_, ?_⟩ <;> cases c
  · exact m3p_side_ptM T (s + 2) (m3p_red_par12 T s)
  · exact m3p_side_ptM T s (m3p_green_par12 T s)
  · exact m3p_side_ptM T (s + 1) (m3p_blue_par12 T s)
  · exact m3p_side_ptM T (s + 1) (m3p_red_par23 T s)
  · exact m3p_side_ptM T (s + 2) (m3p_green_par23 T s)
  · exact m3p_side_ptM T s (m3p_blue_par23 T s)
  · exact m3p_side_ptM T s (m3p_red_par31 T s)
  · exact m3p_side_ptM T (s + 1) (m3p_green_par31 T s)
  · exact m3p_side_ptM T (s + 2) (m3p_blue_par31 T s)

end OrientedTriangle

namespace OrientedTriangle

/-- The nine monochrome triangles have the same three side directions. -/
theorem _root_.XamboMorley.OrientedTriangle.monochrome_sides_parallel (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (c : TrisectorColor) (s : TrisectorLabel) :
    let t := T.monochromeTriangle c s
    T.parallelToMorleySide (t.second - t.first) ∧
      T.parallelToMorleySide (t.third - t.second) ∧
      T.parallelToMorleySide (t.first - t.third) := by
  exact _root_.XamboMorley.OrientedTriangle.OrientedTriangle.m3p_monochrome_sides_parallel T c s

end OrientedTriangle


theorem m4d_exp_three_label (t : TrisectorLabel) :
    (Circle.exp (3 * labelAngle t) : ℂ) = 1 := by
  have h3 : (3 : ℝ) * labelAngle t = ((3 : ℕ) : ℝ) * labelAngle t := by norm_num
  rw [h3, Circle.exp_natCast_mul, Circle.coe_pow, labelAngle_exp, ← pow_mul,
    show t.val * 3 = 3 * t.val from by ring, pow_mul, omega_cubed, one_pow]

theorem m4d_shift_cube (a : ℝ) (t : TrisectorLabel) :
    (Circle.exp (2 * a - labelAngle t) : ℂ) ^ 3 = (Circle.exp (6 * a) : ℂ) := by
  rw [← Circle.coe_pow, ← Circle.exp_natCast_mul]
  rw [show ((3 : ℕ) : ℝ) * (2 * a - labelAngle t) = 6 * a - 3 * labelAngle t by
    push_cast; ring]
  rw [Circle.exp_sub, Circle.coe_div, m4d_exp_three_label, div_one]

theorem m4d_sin_three_beta_ne (T : OrientedTriangle E o) : Real.sin (3 * T.beta) ≠ 0 :=
  ne_of_gt (m3_sin_three_beta_pos T)

theorem m4d_sin_three_alpha_ne (T : OrientedTriangle E o) : Real.sin (3 * T.alpha) ≠ 0 :=
  ne_of_gt (m3_sin_three_alpha_pos T)

theorem m4d_five_ne (T : OrientedTriangle E o) :
    (Circle.exp (6 * T.beta) : ℂ) - 1 ≠ 0 := by
  have h : (1 - (Circle.exp (6 * T.beta) : ℂ)) ≠ 0 := by
    refine OrientedTriangle.m7b_one_sub_exp_ne (6 * T.beta) ?_
    rw [show 6 * T.beta / 2 = 3 * T.beta by ring]
    exact m4d_sin_three_beta_ne T
  intro h0
  rw [sub_eq_zero] at h0
  exact h (by rw [h0, sub_self])

theorem m4d_six_alpha_sub_one_ne (T : OrientedTriangle E o) :
    (Circle.exp (6 * T.alpha) : ℂ) - 1 ≠ 0 := by
  have h : (1 - (Circle.exp (6 * T.alpha) : ℂ)) ≠ 0 := by
    refine OrientedTriangle.m7b_one_sub_exp_ne (6 * T.alpha) ?_
    rw [show 6 * T.alpha / 2 = 3 * T.alpha by ring]
    exact m4d_sin_three_alpha_ne T
  intro h0
  rw [sub_eq_zero] at h0
  exact h (by rw [h0, sub_self])

theorem m4d_exp_pi_div_two : (Circle.exp (Real.pi / 2) : ℂ) = Complex.I := by
  have h1 : (Circle.exp (-(Real.pi / 2)) : ℂ) = -Complex.I := m6_exp_neg_pi_div_two
  have hmul : ((Circle.exp (-(Real.pi / 2)) : ℂ)) * (Circle.exp (Real.pi / 2) : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← Circle.exp_add, show -(Real.pi / 2) + Real.pi / 2 = 0 by ring]
    simp
  rw [h1] at hmul
  have hne : (-Complex.I : ℂ) ≠ 0 := by
    intro h
    have h2 : (-Complex.I : ℂ) * Complex.I = 0 := by rw [h, zero_mul]
    rw [neg_mul, Complex.I_mul_I] at h2
    norm_num at h2
  refine mul_left_cancel₀ hne ?_
  rw [hmul, neg_mul, Complex.I_mul_I]
  norm_num

theorem m4d_six_alpha (T : OrientedTriangle E o) :
    (Circle.exp (6 * T.alpha) : ℂ) - 1 =
      2 * Complex.I * ((Real.sin (3 * T.alpha) : ℂ) * (Circle.exp (3 * T.alpha) : ℂ)) := by
  have h := one_sub_unit_eq (6 * T.alpha)
  rw [show 6 * T.alpha / 2 = 3 * T.alpha by ring] at h
  have h2 : (Circle.exp (3 * T.alpha - Real.pi / 2) : ℂ) =
      (Circle.exp (3 * T.alpha) : ℂ) * (-Complex.I) := by
    rw [show 3 * T.alpha - Real.pi / 2 = 3 * T.alpha + -(Real.pi / 2) by ring,
      Circle.exp_add, Circle.coe_mul, m6_exp_neg_pi_div_two]
  rw [h2] at h
  linear_combination -h

theorem m4d_six_beta (T : OrientedTriangle E o) :
    (Circle.exp (6 * T.beta) : ℂ) - 1 =
      2 * Complex.I * ((Real.sin (3 * T.beta) : ℂ) * (Circle.exp (3 * T.beta) : ℂ)) := by
  have h := one_sub_unit_eq (6 * T.beta)
  rw [show 6 * T.beta / 2 = 3 * T.beta by ring] at h
  have h2 : (Circle.exp (3 * T.beta - Real.pi / 2) : ℂ) =
      (Circle.exp (3 * T.beta) : ℂ) * (-Complex.I) := by
    rw [show 3 * T.beta - Real.pi / 2 = 3 * T.beta + -(Real.pi / 2) by ring,
      Circle.exp_add, Circle.coe_mul, m6_exp_neg_pi_div_two]
  rw [h2] at h
  linear_combination -h

theorem m4d_exp_pi : (Circle.exp Real.pi : ℂ) = -1 := by
  rw [show Real.pi = Real.pi / 2 + Real.pi / 2 by ring, Circle.exp_add, Circle.coe_mul,
    m4d_exp_pi_div_two, Complex.I_mul_I]

theorem m4d_three_gamma (T : OrientedTriangle E o) :
    (Circle.exp (3 * T.gamma) : ℂ) =
      -((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ)) := by
  have hsum := T.angle_sum
  have harg : 3 * T.gamma = -(3 * (T.alpha + T.beta)) + Real.pi := by linarith
  rw [harg, Circle.exp_add, Circle.coe_mul]
  rw [m4d_exp_pi]
  ring

theorem m4d_rho (T : OrientedTriangle E o) :
    ‖T.B - T.C‖ / ‖T.A - T.C‖ = Real.sin (3 * T.alpha) / Real.sin (3 * T.beta) := by
  have ha : ‖T.B - T.C‖ = T.aLength := by
    rw [aLength, show T.a = T.C - T.B from rfl, norm_sub_rev]
  have hb : ‖T.A - T.C‖ = T.bLength := by
    rw [bLength, show T.b = T.A - T.C from rfl]
  rw [ha, hb, T.side_lengths_sine.1, T.side_lengths_sine.2.1]
  have h1 : T.delta ≠ 0 := ne_of_gt (m7_delta_pos T)
  field_simp

theorem m4d_p_rel (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    toComplex o (T.B - T.C) *
        ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) ^ 3 *
          ((Circle.exp (2 * T.beta - labelAngle i) : ℂ) ^ 3 - 1))
      = ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) ^ 3 - 1) *
          toComplex o (T.C - T.A) := by
  have hP : toComplex o (T.B - T.C) =
      -(((‖T.B - T.C‖ / ‖T.A - T.C‖ : ℝ) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ)) *
        toComplex o (T.C - T.A) := by
    have h := congrArg (toComplex o) T.m6_trisector_C
    rw [h, toComplex_smul, toComplex_rotateVector]
    rw [show T.A - T.C = -(T.C - T.A) from by abel, toComplex_neg]
    ring
  have hXYZ : ((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ) * (Circle.exp (6 * T.alpha) : ℂ)) *
      (Circle.exp (3 * T.beta) : ℂ) = (Circle.exp (3 * T.alpha) : ℂ) := by
    rw [Circle.coe_exp, Circle.coe_exp, Circle.coe_exp, Circle.coe_exp,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hK : -(((‖T.B - T.C‖ / ‖T.A - T.C‖ : ℝ) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ)) *
        ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) ^ 3 *
          ((Circle.exp (2 * T.beta - labelAngle i) : ℂ) ^ 3 - 1))
      = ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) ^ 3 - 1) := by
    rw [m4d_shift_cube T.alpha k, m4d_shift_cube T.beta i, m4d_six_alpha T, m4d_six_beta T,
      m4d_three_gamma T, m4d_rho T]
    have hs : (Real.sin (3 * T.beta) : ℂ) ≠ 0 := by
      exact_mod_cast m4d_sin_three_beta_ne T
    have hcancel : ((Real.sin (3 * T.alpha) / Real.sin (3 * T.beta) : ℝ) : ℂ) *
        (Real.sin (3 * T.beta) : ℂ) = (Real.sin (3 * T.alpha) : ℂ) := by
      rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (m4d_sin_three_beta_ne T)]
    have h1 : (-((((Real.sin (3 * T.alpha) / Real.sin (3 * T.beta) : ℝ) : ℂ) *
          (-((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ)))))) *
        ((Circle.exp (6 * T.alpha) : ℂ) *
          (2 * Complex.I * ((Real.sin (3 * T.beta) : ℂ) * (Circle.exp (3 * T.beta) : ℂ))))
        = 2 * Complex.I * ((Real.sin (3 * T.alpha) : ℂ) *
            (((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ) * (Circle.exp (6 * T.alpha) : ℂ)) *
              (Circle.exp (3 * T.beta) : ℂ))) := by
      linear_combination (2 * Complex.I *
        (((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ) * (Circle.exp (6 * T.alpha) : ℂ)) *
          (Circle.exp (3 * T.beta) : ℂ))) * hcancel
    rw [h1, hXYZ]
  rw [hP]
  linear_combination (toComplex o (T.C - T.A)) * hK

theorem m4d_sin_ne (i j k : TrisectorLabel) (hq : i + j + k ≠ 1) :
    Real.sin ((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * Real.pi / 3) ≠ 0 := by
  intro hsin
  rw [Real.sin_eq_zero_iff] at hsin
  obtain ⟨m, hm⟩ := hsin
  have hreal : ((1 : ℝ) - ((i.val + j.val + k.val : ℕ) : ℝ)) = 3 * (m : ℝ) := by
    have h4 : (m : ℝ) * 3 = 1 - ((i.val + j.val + k.val : ℕ) : ℝ) := by
      nlinarith [hm, Real.pi_pos]
    linarith
  have hint : ((1 : ℤ) - ((i.val + j.val + k.val : ℕ) : ℤ)) = 3 * m := by
    exact_mod_cast hreal
  have hN : ((i.val + j.val + k.val : ℕ) : ZMod 3) = 1 := by
    have h6 : (((i.val + j.val + k.val : ℕ) : ℤ)) = 1 - 3 * m := by linarith
    rw [← Int.cast_natCast, h6]
    push_cast
    have h3z : ((3 : ZMod 3)) = 0 := by decide
    rw [h3z]
    ring
  rw [show ((i.val + j.val + k.val : ℕ) : ZMod 3) = i + j + k from by
    push_cast
    rw [ZMod.natCast_zmod_val i, ZMod.natCast_zmod_val j, ZMod.natCast_zmod_val k]] at hN
  exact hq hN

theorem m4d_T_cube (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
      (Circle.exp (2 * T.gamma - labelAngle j) : ℂ)) ^ 3 = 1 := by
  rw [mul_pow, mul_pow, m4d_shift_cube T.alpha k, m4d_shift_cube T.beta i,
    m4d_shift_cube T.gamma j]
  rw [← Circle.coe_mul, ← Circle.coe_mul, ← Circle.exp_add, ← Circle.exp_add]
  rw [show 6 * T.alpha + 6 * T.beta + 6 * T.gamma = 2 * Real.pi by
    rw [← T.angle_sum]; ring]
  rw [show (2 * Real.pi : ℝ) = Real.pi + Real.pi by ring, Circle.exp_add, Circle.coe_mul,
    m4d_exp_pi]
  norm_num

theorem m4d_T_form (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
      (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) =
      (Circle.exp ((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3)) : ℂ) := by
  rw [← Circle.coe_mul, ← Circle.coe_mul, ← Circle.exp_add, ← Circle.exp_add]
  congr 1
  congr 1
  push_cast [labelAngle]
  linear_combination (2 / 3) * T.angle_sum

theorem m4d_T_ne_one (T : OrientedTriangle E o) (i j k : TrisectorLabel)
    (hq : i + j + k ≠ 1) :
    (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
      (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) ≠ 1 := by
  rw [m4d_T_form T i j k]
  intro h1
  have h0 : (1 - (Circle.exp ((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3)) : ℂ)) = 0 := by
    rw [h1]; ring
  rw [one_sub_unit_eq] at h0
  have hsin : Real.sin (((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3)) / 2) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · have h2 : (2 * Real.sin (((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3)) / 2) : ℝ) = 0 := by
        exact_mod_cast h
      linarith
    · exact absurd h (OrientedTriangle.m7b_exp_ne_zero _)
  exact m4d_sin_ne i j k hq (by
    rwa [show (1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3) / 2
      = (1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * Real.pi / 3 by ring] at hsin)

theorem m4d_T_quad (T : OrientedTriangle E o) (i j k : TrisectorLabel)
    (hq : i + j + k ≠ 1) :
    1 + (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
        (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) +
      ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
        (Circle.exp (2 * T.gamma - labelAngle j) : ℂ)) ^ 2 = 0 := by
  set Tt : ℂ := (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) *
    (Circle.exp (2 * T.beta - labelAngle i) : ℂ) * (Circle.exp (2 * T.gamma - labelAngle j) : ℂ)
    with hTt
  have h3 : Tt ^ 3 = 1 := m4d_T_cube T i j k
  have hne : Tt ≠ 1 := m4d_T_ne_one T i j k hq
  have hfac : (Tt - 1) * (Tt ^ 2 + Tt + 1) = 0 := by
    linear_combination h3
  have h2 : Tt ^ 2 + Tt + 1 = 0 := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
  linear_combination h2

theorem m4d_cmv_norm {z : ℂ} {v : E} :
    ‖complexMulVector o z v‖ = ‖z‖ * ‖v‖ := by
  rw [← toComplex_norm (o := o) (complexMulVector o z v), w9_toComplex_complexMulVector,
    norm_mul, toComplex_norm, mul_comm]

theorem m4d_circle_norm (θ : ℝ) : ‖(Circle.exp θ : ℂ)‖ = 1 := Circle.norm_coe _

theorem m4d_rot_C (T : OrientedTriangle E o) (i j k : TrisectorLabel)
    (hq : i + j + k ≠ 1) :
    toComplex o (T.constellationPoint ⟨.green, j, k⟩) -
        toComplex o (T.constellationPoint ⟨.red, i, j⟩)
      = (-((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) *
          (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
          (Circle.exp (2 * T.gamma - labelAngle j) : ℂ))) *
        (toComplex o (T.constellationPoint ⟨.blue, k, i⟩) -
          toComplex o (T.constellationPoint ⟨.red, i, j⟩)) := by
  rw [OrientedTriangle.m7b_red_form T i j, OrientedTriangle.m7b_green_form T j k, OrientedTriangle.m7b_blue_form T k i]
  set Eu : ℂ := (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) with hEu
  set Ev : ℂ := (Circle.exp (2 * T.beta - labelAngle i) : ℂ) with hEv
  set Ew : ℂ := (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) with hEw
  set B1 : ℂ := 1 - Ew * Ev with hB1
  set B2 : ℂ := 1 - Eu * Ew with hB2
  set B3 : ℂ := 1 - Ev * Eu with hB3
  have hn1 : B1 ≠ 0 := by
    rw [hB1, hEw, hEv]
    refine OrientedTriangle.m7b_one_sub_exp_mul_ne (φ := 2 * T.gamma - labelAngle j)
      (ψ := 2 * T.beta - labelAngle i) ?_
    obtain ⟨hb0, hb1⟩ := m6_beta_add_gamma_bounds_lt (o := o) T
    convert m6_sin_shift_sub_ne_zero hb0 hb1 i j using 2
    ring
  have hn2 : B2 ≠ 0 := by
    rw [hB2, hEu, hEw]
    refine OrientedTriangle.m7b_one_sub_exp_mul_ne (φ := 2 * T.alpha - labelAngle k)
      (ψ := 2 * T.gamma - labelAngle j) ?_
    obtain ⟨hb0, hb1⟩ := m6_gamma_add_alpha_bounds_lt (o := o) T
    convert m6_sin_shift_sub_ne_zero hb0 hb1 k j using 2
    ring
  have hn3 : B3 ≠ 0 := by
    rw [hB3, hEv, hEu]
    refine OrientedTriangle.m7b_one_sub_exp_mul_ne (φ := 2 * T.beta - labelAngle i)
      (ψ := 2 * T.alpha - labelAngle k) ?_
    obtain ⟨hb0, hb1⟩ := m6_alpha_add_beta_bounds_lt (o := o) T
    convert m6_sin_shift_sub_ne_zero hb0 hb1 i k using 2
    ring
  have hKnz : Eu ^ 3 * (Ev ^ 3 - 1) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero 3 ?_) ?_
    · rw [hEu]; exact OrientedTriangle.m7b_exp_ne_zero _
    · rw [hEv, m4d_shift_cube (a := T.beta) (t := i)]
      exact m4d_five_ne T
  have hp'' : toComplex o (T.B - T.C) * (Eu ^ 3 * (Ev ^ 3 - 1))
      = (Eu ^ 3 - 1) * toComplex o (T.C - T.A) := by
    have h := m4d_p_rel T i j k
    rw [← hEu, ← hEv] at h
    exact h
  have hT'' : 1 + Eu * Ev * Ew + (Eu * Ev * Ew) ^ 2 = 0 := by
    have h := m4d_T_quad T i j k hq
    rw [← hEu, ← hEv, ← hEw] at h
    exact h
  have hkey := OrientedTriangle.m7b_affine_key Eu Ev Ew (-(Eu * Ev * Ew))
    (toComplex o (T.B - T.C)) (toComplex o (T.C - T.A)) B1 B2 B3
    (Eu ^ 3 * (Ev ^ 3 - 1)) (Eu * Ev * Ew)
    ((1 - Ev) / B1) ((1 - Ew) / B2) ((1 - Eu) / B3)
    (by rw [hB1]; ring) (by rw [hB2]; ring) (by rw [hB3]; ring) rfl rfl
    (by field_simp) (by field_simp) (by field_simp)
    hn1 hn2 hn3 hKnz hp'' hT'' rfl
  have e1 : toComplex o T.A - toComplex o T.C + toComplex o (T.C - T.A) = 0 := by
    rw [← toComplex_sub, show T.A - T.C = -(T.C - T.A) from by abel, toComplex_neg]
    ring
  have e2 : toComplex o T.B - toComplex o T.C - toComplex o (T.B - T.C) = 0 := by
    rw [← toComplex_sub]
    ring
  have e3 : toComplex o (T.A - T.B) + toComplex o (T.B - T.C) + toComplex o (T.C - T.A) = 0 := by
    rw [← toComplex_add, ← toComplex_add]
    congr 1
    abel
    simp
  linear_combination hkey + e1 - (-(Eu * Ev * Ew)) * e2 -
    (-(Eu * Ev * Ew)) * ((1 - Eu) / B3) * e3


/-! ### The diagonal case: `Eu Ev Ew = ω` and the rotation angle -/

/-- `exp (2πi) = 1`, coerced to `ℂ`. -/
theorem m4d_exp_two_pi : (Circle.exp (2 * Real.pi) : ℂ) = 1 := by
  have h : (Circle.exp (Real.pi + Real.pi) : ℂ) =
      (Circle.exp Real.pi : ℂ) * (Circle.exp Real.pi : ℂ) := by
    rw [Circle.exp_add, Circle.coe_mul]
  rw [show (2 * Real.pi : ℝ) = Real.pi + Real.pi by ring, h, m2_exp_pi]
  norm_num

/-- `exp (-n·2πi) = 1` for every natural `n`. -/
theorem m4d_exp_neg_nat_two_pi (n : ℕ) :
    (Circle.exp (-((n : ℝ) * (2 * Real.pi))) : ℂ) = 1 := by
  have hmul : (Circle.exp ((n : ℝ) * (2 * Real.pi)) : ℂ) *
      (Circle.exp (-((n : ℝ) * (2 * Real.pi))) : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← Circle.exp_add,
      show (n : ℝ) * (2 * Real.pi) + -((n : ℝ) * (2 * Real.pi)) = 0 by ring,
      Circle.exp_zero, Circle.coe_one]
  have hpos : (Circle.exp ((n : ℝ) * (2 * Real.pi)) : ℂ) = 1 := by
    rw [show (n : ℝ) * (2 * Real.pi) = (n : ℕ) * (2 * Real.pi) by push_cast; ring,
      Circle.exp_natCast_mul, Circle.coe_pow, m4d_exp_two_pi, one_pow]
  rw [hpos, one_mul] at hmul
  exact hmul

/-- On the diagonal, the product of the three label exponentials is `ω`. -/
theorem m4d_diag_T (T : OrientedTriangle E o) (i : TrisectorLabel) :
    (Circle.exp (2 * T.alpha - labelAngle i) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
      (Circle.exp (2 * T.gamma - labelAngle i) : ℂ) = (omega : ℂ) := by
  have hsum := T.angle_sum
  have harg : (2 * T.alpha - labelAngle i) + (2 * T.beta - labelAngle i) +
      (2 * T.gamma - labelAngle i)
      = 2 * Real.pi / 3 + (-(((i.val : ℝ)) * (2 * Real.pi))) := by
    have hl : labelAngle i = ((i.val : ℝ)) * (2 * Real.pi / 3) := rfl
    rw [hl]
    linarith
  rw [← Circle.coe_mul, ← Circle.coe_mul, ← Circle.exp_add, ← Circle.exp_add, harg,
    Circle.exp_add, Circle.coe_mul, m4d_exp_neg_nat_two_pi, mul_one]
  rfl

/-- `i + i + i ≠ 1` in `ZMod 3`. -/
theorem m4d_diag_three_ne_one (i : TrisectorLabel) : i + i + i ≠ 1 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  have hzero : i + i + i = 0 := by
    calc i + i + i = 3 * i := by ring
      _ = 0 := by rw [h3, zero_mul]
  rw [hzero]
  exact (by decide : (0 : ZMod 3) ≠ 1)

/-- The rotation identity on the diagonal: `g - r = exp(-π/3)·(b - r)`. -/
theorem m4d_rot_omega_diag (T : OrientedTriangle E o) (i : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.green, i, i⟩) -
        toComplex o (T.constellationPoint ⟨.red, i, i⟩)
      = (Circle.exp (-(Real.pi / 3)) : ℂ) *
        (toComplex o (T.constellationPoint ⟨.blue, i, i⟩) -
          toComplex o (T.constellationPoint ⟨.red, i, i⟩)) := by
  have h := m4d_rot_C T i i i (m4d_diag_three_ne_one i)
  rw [m4d_diag_T T i] at h
  rw [h, m2_exp_neg_pi_third]

/-- The diagonal triangle is non-degenerate: `b ≠ r`.  This uses the injectivity
hypothesis of the target statement. -/
theorem m4d_diag_blue_ne_red (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (i : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.blue, i, i⟩) -
        toComplex o (T.constellationPoint ⟨.red, i, i⟩) ≠ 0 := by
  intro h0
  have h1 : toComplex o (T.constellationPoint ⟨.blue, i, i⟩) =
      toComplex o (T.constellationPoint ⟨.red, i, i⟩) := sub_eq_zero.mp h0
  have h2 : T.constellationPoint ⟨.blue, i, i⟩ = T.constellationPoint ⟨.red, i, i⟩ :=
    toComplex_injective o h1
  have h3 : (⟨TrisectorColor.blue, i, i⟩ : ConstellationIndex) =
      ⟨TrisectorColor.red, i, i⟩ := h h2
  exact absurd (congrArg ConstellationIndex.color h3)
    (by decide : TrisectorColor.blue ≠ TrisectorColor.red)

/-- Positivity of the oriented area of the diagonal tricolor triangle. -/
theorem m4d_area_diag_pos (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (i : TrisectorLabel) :
    0 < orientedArea o (T.constellationPoint ⟨.green, i, i⟩ - T.constellationPoint ⟨.red, i, i⟩)
      (T.constellationPoint ⟨.blue, i, i⟩ - T.constellationPoint ⟨.red, i, i⟩) := by
  have hrw := m4d_rot_omega_diag T i
  have hw : toComplex o (T.constellationPoint ⟨.blue, i, i⟩) -
      toComplex o (T.constellationPoint ⟨.red, i, i⟩) ≠ 0 := m4d_diag_blue_ne_red T h i
  rw [orientedArea, areaForm_complex, toComplex_sub, toComplex_sub, hrw, map_mul,
    m6_conj_circle_exp, neg_neg]
  have hassoc : (Circle.exp (Real.pi / 3) : ℂ) *
        (starRingEnd ℂ) (toComplex o (T.constellationPoint ⟨.blue, i, i⟩) -
          toComplex o (T.constellationPoint ⟨.red, i, i⟩)) *
        (toComplex o (T.constellationPoint ⟨.blue, i, i⟩) -
          toComplex o (T.constellationPoint ⟨.red, i, i⟩))
      = (Circle.exp (Real.pi / 3) : ℂ) *
        (((starRingEnd ℂ) (toComplex o (T.constellationPoint ⟨.blue, i, i⟩) -
          toComplex o (T.constellationPoint ⟨.red, i, i⟩))) *
          (toComplex o (T.constellationPoint ⟨.blue, i, i⟩) -
            toComplex o (T.constellationPoint ⟨.red, i, i⟩))) := by ring
  rw [hassoc, ← Complex.normSq_eq_conj_mul_self]
  have hval : ((Circle.exp (Real.pi / 3) : ℂ) *
      ((Complex.normSq (toComplex o (T.constellationPoint ⟨.blue, i, i⟩) -
        toComplex o (T.constellationPoint ⟨.red, i, i⟩)) : ℝ) : ℂ)).im
      = Real.sin (Real.pi / 3) *
        Complex.normSq (toComplex o (T.constellationPoint ⟨.blue, i, i⟩) -
          toComplex o (T.constellationPoint ⟨.red, i, i⟩)) := by
    rw [m6_circle_exp_eq]
    simp [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im]
  rw [hval]
  refine mul_pos ?_ (Complex.normSq_pos.mpr hw)
  exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])

/-! ### The general orientation formula for the tricolor triangles

For any labels with `i+j+k ≠ 1` the oriented area of the tricolor triangle is
`‖b-r‖² · Im(Eu Ev Ew)`.  Since `Eu Ev Ew = exp(i(1-N)·2π/3)` with `N = i.val+j.val+k.val`,
the sign is decided by the residue of `i+j+k` in `ZMod 3`: `0 ↦ +`, `2 ↦ -`. -/

/-- `exp(i n 2π/3) = ω^n`. -/
theorem m4d_exp_N_eq (n : ℕ) :
    (Circle.exp ((n : ℝ) * (2 * Real.pi / 3)) : ℂ) = (omega : ℂ) ^ n := by
  rw [Circle.exp_natCast_mul, Circle.coe_pow]
  rfl

/-- `exp(-x) = (exp x)⁻¹`, coerced to `ℂ`. -/
theorem m4d_exp_neg (x : ℝ) :
    (Circle.exp (-x) : ℂ) = ((Circle.exp x : ℂ))⁻¹ := by
  rw [Circle.exp_neg, Circle.coe_inv]

/-- `Im ω = √3/2`. -/
theorem m4d_im_omega : (omega : ℂ).im = Real.sqrt 3 / 2 := by
  show (Circle.exp (2 * Real.pi / 3) : ℂ).im = Real.sqrt 3 / 2
  rw [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.mk_eq_add_mul_I]
  exact m3_sin_two_pi_div_three

/-- `Im ω² = -√3/2`. -/
theorem m4d_im_omega_sq : ((omega : ℂ) ^ 2).im = -(Real.sqrt 3 / 2) := by
  have hsq : ((omega : ℂ)) ^ 2 = (Circle.exp (4 * Real.pi / 3) : ℂ) := by
    rw [show ((omega : ℂ)) ^ 2 = ((Circle.exp (2 * Real.pi / 3) : ℂ)) ^ 2 from rfl,
      show ((Circle.exp (2 * Real.pi / 3) : ℂ)) ^ 2
        = (Circle.exp ((2 : ℕ) * (2 * Real.pi / 3)) : ℂ) from by
        rw [Circle.exp_natCast_mul, Circle.coe_pow]]
    congr 1
    push_cast
    ring
  rw [hsq]
  show (Circle.exp (4 * Real.pi / 3) : ℂ).im = -(Real.sqrt 3 / 2)
  rw [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.mk_eq_add_mul_I]
  exact m3_sin_four_pi_div_three

/-- `Im ω > 0`. -/
theorem m4d_im_omega_pos : 0 < (omega : ℂ).im := by
  rw [m4d_im_omega]
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- `Im ω² < 0`. -/
theorem m4d_im_omega_sq_neg : ((omega : ℂ) ^ 2).im < 0 := by
  rw [m4d_im_omega_sq]
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- `Eu Ev Ew = ω` on the sum-zero class. -/
theorem m4d_T_of_sum_zero (T : OrientedTriangle E o) (i j k : TrisectorLabel)
    (h : i + j + k = 0) :
    (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
      (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) = (omega : ℂ) := by
  have hN : ((i.val + j.val + k.val : ℕ) : ZMod 3) = 0 := by
    rw [show ((i.val + j.val + k.val : ℕ) : ZMod 3) = i + j + k from by
      push_cast
      rw [ZMod.natCast_zmod_val i, ZMod.natCast_zmod_val j, ZMod.natCast_zmod_val k]]
    exact h
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff (i.val + j.val + k.val) 3).mp hN
  rw [m4d_T_form T i j k, hq]
  have harg : (1 - (((3 * q : ℕ)) : ℝ)) * (2 * Real.pi / 3)
      = 2 * Real.pi / 3 + (-(((q : ℝ)) * (2 * Real.pi))) := by
    push_cast
    ring
  rw [harg, Circle.exp_add, Circle.coe_mul, m4d_exp_neg_nat_two_pi, mul_one]
  rfl

/-- `Eu Ev Ew = ω²` on the sum-two class. -/
theorem m4d_T_of_sum_two (T : OrientedTriangle E o) (i j k : TrisectorLabel)
    (h : i + j + k = 2) :
    (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
      (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) = (omega : ℂ) ^ 2 := by
  have hN : ((i.val + j.val + k.val + 1 : ℕ) : ZMod 3) = 0 := by
    rw [show ((i.val + j.val + k.val + 1 : ℕ) : ZMod 3) = i + j + k + 1 from by
      push_cast
      rw [ZMod.natCast_zmod_val i, ZMod.natCast_zmod_val j, ZMod.natCast_zmod_val k]]
    rw [h, show (2 : ZMod 3) + 1 = 0 from by decide]
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff (i.val + j.val + k.val + 1) 3).mp hN
  have hpow : (omega : ℂ) ^ (i.val + j.val + k.val) = (omega : ℂ) ^ 2 := by
    have h1 : (omega : ℂ) ^ (i.val + j.val + k.val + 1) = 1 := by
      rw [hq, pow_mul, omega_cubed, one_pow]
    have h2 : (omega : ℂ) ^ (i.val + j.val + k.val) * (omega : ℂ) = 1 := by
      rw [← pow_succ]
      exact h1
    calc (omega : ℂ) ^ (i.val + j.val + k.val)
        = (omega : ℂ) ^ (i.val + j.val + k.val) * 1 := by ring
      _ = (omega : ℂ) ^ (i.val + j.val + k.val) * ((omega : ℂ) * (omega : ℂ) ^ 2) := by
            rw [omega_mul_sq]
      _ = ((omega : ℂ) ^ (i.val + j.val + k.val) * (omega : ℂ)) * (omega : ℂ) ^ 2 := by ring
      _ = 1 * (omega : ℂ) ^ 2 := by rw [h2]
      _ = (omega : ℂ) ^ 2 := by ring
  rw [m4d_T_form T i j k]
  have harg : (1 - (((i.val + j.val + k.val : ℕ)) : ℝ)) * (2 * Real.pi / 3)
      = 2 * Real.pi / 3 + (-(((i.val + j.val + k.val : ℕ) : ℝ) * (2 * Real.pi / 3))) := by
    push_cast
    ring
  rw [harg, Circle.exp_add, Circle.coe_mul, m4d_exp_neg, m4d_exp_N_eq,
    show (Circle.exp (2 * Real.pi / 3) : ℂ) = (omega : ℂ) from rfl, hpow]
  have hsqne : ((omega : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (Circle.coe_ne_zero omega)
  have hinv : (((omega : ℂ) ^ 2))⁻¹ = (omega : ℂ) := by
    calc (((omega : ℂ) ^ 2))⁻¹ = (((omega : ℂ) ^ 2))⁻¹ * 1 := by ring
      _ = (((omega : ℂ) ^ 2))⁻¹ * (((omega : ℂ) ^ 2) * (omega : ℂ)) := by rw [omega_sq_mul]
      _ = (omega : ℂ) := by
            field_simp
  rw [hinv]
  ring

/-- Constellation points of different colours are distinct, by injectivity. -/
theorem m4d_cp_ne (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {a b : ConstellationIndex} (hab : a.color ≠ b.color) :
    T.constellationPoint a ≠ T.constellationPoint b :=
  fun he => hab (congrArg ConstellationIndex.color (h he))

/-- **The general oriented-area formula** for a tricolor triangle with labels
`i+j+k ≠ 1`: the sign of the area is the sign of `Im(Eu Ev Ew)`. -/
theorem m4d_area_eq (T : OrientedTriangle E o) (i j k : TrisectorLabel) (h : i + j + k ≠ 1) :
    orientedArea o (T.constellationPoint ⟨.green, j, k⟩ - T.constellationPoint ⟨.red, i, j⟩)
        (T.constellationPoint ⟨.blue, k, i⟩ - T.constellationPoint ⟨.red, i, j⟩)
      = Complex.normSq (toComplex o (T.constellationPoint ⟨.blue, k, i⟩) -
            toComplex o (T.constellationPoint ⟨.red, i, j⟩)) *
          ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) *
            (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
            (Circle.exp (2 * T.gamma - labelAngle j) : ℂ)).im := by
  set Tp : ℂ := (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) *
    (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
    (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) with hTp
  set w : ℂ := toComplex o (T.constellationPoint ⟨.blue, k, i⟩) -
    toComplex o (T.constellationPoint ⟨.red, i, j⟩) with hw
  have hgr : toComplex o (T.constellationPoint ⟨.green, j, k⟩) -
      toComplex o (T.constellationPoint ⟨.red, i, j⟩) = (-Tp) * w := m4d_rot_C T i j k h
  rw [orientedArea, areaForm_complex, toComplex_sub, toComplex_sub, hgr, map_mul, map_neg]
  have hassoc : ((-(starRingEnd ℂ) Tp) * (starRingEnd ℂ) w) * w =
      (-(starRingEnd ℂ) Tp) * ((starRingEnd ℂ) w * w) := by ring
  rw [hassoc, ← Complex.normSq_eq_conj_mul_self]
  have h2 : ((-(starRingEnd ℂ) Tp) * ((Complex.normSq w : ℝ) : ℂ)).im =
      Tp.im * Complex.normSq w := by
    rw [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h2]
  ring

/-- **Sum-zero labels give positive orientation** (clause 1 of `tricolor_orientation`,
for all labels). -/
theorem m4d_area_pos_of_sum_zero (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (i j k : TrisectorLabel) (hs : i + j + k = 0) :
    0 < orientedArea o (T.constellationPoint ⟨.green, j, k⟩ - T.constellationPoint ⟨.red, i, j⟩)
      (T.constellationPoint ⟨.blue, k, i⟩ - T.constellationPoint ⟨.red, i, j⟩) := by
  have hne : i + j + k ≠ 1 := by rw [hs]; exact (by decide : (0 : ZMod 3) ≠ 1)
  rw [m4d_area_eq T i j k hne, m4d_T_of_sum_zero T i j k hs]
  refine mul_pos (Complex.normSq_pos.mpr ?_) m4d_im_omega_pos
  intro h0
  have h1 : toComplex o (T.constellationPoint ⟨.blue, k, i⟩) =
      toComplex o (T.constellationPoint ⟨.red, i, j⟩) := sub_eq_zero.mp h0
  have h2 : T.constellationPoint ⟨.blue, k, i⟩ = T.constellationPoint ⟨.red, i, j⟩ :=
    toComplex_injective o h1
  exact (m4d_cp_ne T h (by decide : TrisectorColor.blue ≠ TrisectorColor.red)) h2

/-- **Sum-two labels give negative orientation** (clause 2 of `tricolor_orientation`,
for all labels). -/
theorem m4d_area_neg_of_sum_two (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (i j k : TrisectorLabel) (hs : i + j + k = 2) :
    orientedArea o (T.constellationPoint ⟨.green, j, k⟩ - T.constellationPoint ⟨.red, i, j⟩)
      (T.constellationPoint ⟨.blue, k, i⟩ - T.constellationPoint ⟨.red, i, j⟩) < 0 := by
  have hne : i + j + k ≠ 1 := by rw [hs]; exact (by decide : (2 : ZMod 3) ≠ 1)
  rw [m4d_area_eq T i j k hne, m4d_T_of_sum_two T i j k hs]
  refine mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr ?_) m4d_im_omega_sq_neg
  intro h0
  have h1 : toComplex o (T.constellationPoint ⟨.blue, k, i⟩) =
      toComplex o (T.constellationPoint ⟨.red, i, j⟩) := sub_eq_zero.mp h0
  have h2 : T.constellationPoint ⟨.blue, k, i⟩ = T.constellationPoint ⟨.red, i, j⟩ :=
    toComplex_injective o h1
  exact (m4d_cp_ne T h (by decide : TrisectorColor.blue ≠ TrisectorColor.red)) h2


/-! ### The target statement

`tricolor_diagonal_positive` of the root file, proved here for every
`i : TrisectorLabel` and every oriented triangle, with the injectivity premise
used (it rules out the degenerate collapse `b = r`). -/

theorem m4d_tricolor_diagonal_positive (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (i : TrisectorLabel) :
    PositivelyOriented (o := o) (T.tricolorTriangle ⟨i, i, i⟩) := by
  have hpos := OrientedTriangle.m4d_area_diag_pos (o := o) T h i
  show 0 < orientedArea o
    ((T.tricolorTriangle ⟨i, i, i⟩).second - (T.tricolorTriangle ⟨i, i, i⟩).first)
    ((T.tricolorTriangle ⟨i, i, i⟩).third - (T.tricolorTriangle ⟨i, i, i⟩).first)
  exact hpos

/-- The `⟨0,0,0⟩` case of the root file, recovered from the uniform argument
(it agrees with `m1_diagonal_zero_pos`, which is the `XYZ` route). -/
theorem m4d_tricolor_diagonal_zero_pos (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) :
    PositivelyOriented (o := o) (T.tricolorTriangle ⟨0, 0, 0⟩) :=
  m4d_tricolor_diagonal_positive T h 0

/-! ### The sum-zero and sum-two clauses of `tricolor_orientation`

`PositivelyOriented` of a `TricolorIndex` is exactly the oriented area computed above, so
these are the first two clauses of the root's `tricolor_orientation` for *all* labels
(the sum-one clause, which needs the exceptional index analysis, is untouched). -/

theorem m4d_tricolor_pos_of_sum_zero (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (q : TricolorIndex) (hq : q.i + q.j + q.k = 0) :
    PositivelyOriented (o := o) (T.tricolorTriangle q) :=
  OrientedTriangle.m4d_area_pos_of_sum_zero T h q.i q.j q.k hq

theorem m4d_tricolor_neg_of_sum_two (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (q : TricolorIndex) (hq : q.i + q.j + q.k = 2) :
    NegativelyOriented (o := o) (T.tricolorTriangle q) :=
  OrientedTriangle.m4d_area_neg_of_sum_two T h q.i q.j q.k hq

/-- The first two clauses of `tricolor_orientation`, proved for every label. -/
theorem m4d_tricolor_orientation_zero_two (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) :
    (∀ q : TricolorIndex, q.i + q.j + q.k = 0 →
        PositivelyOriented (o := o) (T.tricolorTriangle q)) ∧
      (∀ q : TricolorIndex, q.i + q.j + q.k = 2 →
        NegativelyOriented (o := o) (T.tricolorTriangle q)) :=
  ⟨fun q hq => m4d_tricolor_pos_of_sum_zero T h q hq,
    fun q hq => m4d_tricolor_neg_of_sum_two T h q hq⟩

/-- The diagonal `⟨i,i,i⟩` case, as a corollary of the sum-zero clause
(independent of the direct proof `m4d_tricolor_diagonal_positive`). -/
theorem m4d_tricolor_diagonal_positive' (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (i : TrisectorLabel) :
    PositivelyOriented (o := o) (T.tricolorTriangle ⟨i, i, i⟩) := by
  have hsum : (⟨i, i, i⟩ : TricolorIndex).i + (⟨i, i, i⟩ : TricolorIndex).j +
      (⟨i, i, i⟩ : TricolorIndex).k = 0 := by
    have h3 : (3 : ZMod 3) = 0 := by decide
    show i + i + i = 0
    calc i + i + i = 3 * i := by ring
      _ = 0 := by rw [h3, zero_mul]
  exact m4d_tricolor_pos_of_sum_zero T h ⟨i, i, i⟩ hsum


/-- The special gallery labels from Figures A4–A6. -/
theorem _root_.XamboMorley.OrientedTriangle.tricolor_diagonal_positive
    (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (i : TrisectorLabel) :
    PositivelyOriented (o := o) (T.tricolorTriangle ⟨i, i, i⟩) := by
  exact m4d_tricolor_diagonal_positive T h i



/-- The key scalar identity behind the tricolor equilateral theorem, stated with the
three affine coefficients `lam, mu, nu` as abstract numbers satisfying the multiplicative
relations that define them. -/
lemma m7c_base_affine_key (eu ev ew ζ P Q B1 B2 B3 K T lam mu nu : ℂ)
    (hB1 : B1 = 1 - ev * ew) (hB2 : B2 = 1 - ew * eu) (hB3 : B3 = 1 - eu * ev)
    (hK : K = eu ^ 3 * (ev ^ 3 - 1)) (hTdef : T = eu * ev * ew)
    (hlam : lam * B1 = 1 - ev) (hmu : mu * B2 = 1 - ew) (hnu : nu * B3 = 1 - eu)
    (h1 : B1 ≠ 0) (h2 : B2 ≠ 0) (h3 : B3 ≠ 0) (hK' : K ≠ 0)
    (hp : P * K = (eu ^ 3 - 1) * Q)
    (hT : 1 + T + T ^ 2 = 0) (hζ : ζ = -T) :
    (mu - 1) * Q - lam * P = ζ * ((1 - lam - nu) * P - nu * Q) := by
  obtain rfl : K = eu ^ 3 * (ev ^ 3 - 1) := hK
  obtain rfl : T = eu * ev * ew := hTdef
  obtain rfl : ζ = -(eu * ev * ew) := hζ
  have hPi : B1 * B2 * B3 ≠ 0 := mul_ne_zero (mul_ne_zero h1 h2) h3
  have e1 : B1 * B2 * B3 * mu = (1 - ew) * B1 * B3 := by
    rw [show B1 * B2 * B3 * mu = (mu * B2) * (B1 * B3) from by ring, hmu]
    ring
  have e2 : B1 * B2 * B3 * lam = (1 - ev) * B2 * B3 := by
    rw [show B1 * B2 * B3 * lam = (lam * B1) * (B2 * B3) from by ring, hlam]
    ring
  have e3 : B1 * B2 * B3 * nu = (1 - eu) * B1 * B2 := by
    rw [show B1 * B2 * B3 * nu = (nu * B3) * (B1 * B2) from by ring, hnu]
    ring
  have hexpand : B1 * B2 * B3 * ((mu - 1) * Q - lam * P + (eu * ev * ew) * ((1 - lam - nu) * P - nu * Q))
      = ((B1 * B2 * B3 * mu - B1 * B2 * B3) * Q - (B1 * B2 * B3 * lam) * P)
        + (eu * ev * ew) * (((B1 * B2 * B3 - B1 * B2 * B3 * lam - B1 * B2 * B3 * nu) * P)
            - (B1 * B2 * B3 * nu) * Q) := by
    ring
  have hcert : (eu ^ 3 * (ev ^ 3 - 1)) * ((1 - ew) * B1 * B3 - B1 * B2 * B3 + (-(eu * ev * ew)) * (1 - eu) * B1 * B2)
      - (eu ^ 3 - 1) * ((1 - ev) * B2 * B3
          + (-(eu * ev * ew)) * (B1 * B2 * B3 - (1 - ev) * B2 * B3 - (1 - eu) * B1 * B2))
      = (1 + (eu * ev * ew) + (eu * ev * ew) ^ 2) *
        (eu ^ 4 * ev ^ 3 * ew - eu ^ 4 * ev ^ 2 - eu ^ 4 * ev * ew + eu ^ 4 * ev
          - eu ^ 3 * ev ^ 3 * ew + eu ^ 3 * ev + eu ^ 3 * ew - eu ^ 3 + eu * ev ^ 2
          + eu * ev * ew - eu * ev - eu * ew - ev + 1) := by
    rw [hB1, hB2, hB3]
    ring
  have hp' : (eu ^ 3 * (ev ^ 3 - 1)) * P = (eu ^ 3 - 1) * Q := by
    rw [mul_comm]
    exact hp
  have hXform : (eu ^ 3 * (ev ^ 3 - 1)) *
      (((1 - ew) * B1 * B3 - B1 * B2 * B3) * Q - (1 - ev) * B2 * B3 * P
        + (eu * ev * ew) * ((B1 * B2 * B3 - (1 - ev) * B2 * B3 - (1 - eu) * B1 * B2) * P
            - (1 - eu) * B1 * B2 * Q))
      = ((1 - ew) * B1 * B3 - B1 * B2 * B3 + (-(eu * ev * ew)) * (1 - eu) * B1 * B2)
          * ((eu ^ 3 * (ev ^ 3 - 1)) * Q)
        - ((1 - ev) * B2 * B3 + (-(eu * ev * ew)) * (B1 * B2 * B3 - (1 - ev) * B2 * B3
            - (1 - eu) * B1 * B2)) * ((eu ^ 3 * (ev ^ 3 - 1)) * P) := by
    ring
  have hcleared : B1 * B2 * B3 *
      ((mu - 1) * Q - lam * P + (eu * ev * ew) * ((1 - lam - nu) * P - nu * Q)) = 0 := by
    rw [hexpand, e1, e2, e3]
    have hmain : (eu ^ 3 * (ev ^ 3 - 1)) *
        (((1 - ew) * B1 * B3 - B1 * B2 * B3) * Q - (1 - ev) * B2 * B3 * P
          + (eu * ev * ew) * ((B1 * B2 * B3 - (1 - ev) * B2 * B3 - (1 - eu) * B1 * B2) * P
              - (1 - eu) * B1 * B2 * Q)) = 0 := by
      rw [hXform, hp']
      rw [show
        ((1 - ew) * B1 * B3 - B1 * B2 * B3 + (-(eu * ev * ew)) * (1 - eu) * B1 * B2)
            * ((eu ^ 3 * (ev ^ 3 - 1)) * Q)
          - ((1 - ev) * B2 * B3 + (-(eu * ev * ew)) * (B1 * B2 * B3 - (1 - ev) * B2 * B3
              - (1 - eu) * B1 * B2)) * ((eu ^ 3 - 1) * Q)
        = ((eu ^ 3 * (ev ^ 3 - 1)) *
              ((1 - ew) * B1 * B3 - B1 * B2 * B3 + (-(eu * ev * ew)) * (1 - eu) * B1 * B2)
            - (eu ^ 3 - 1) * ((1 - ev) * B2 * B3 + (-(eu * ev * ew)) * (B1 * B2 * B3
                - (1 - ev) * B2 * B3 - (1 - eu) * B1 * B2))) * Q from by ring]
      rw [hcert, hT]
      ring
    exact (mul_eq_zero.mp hmain).resolve_left hK'
  have hcube : (mu - 1) * Q - lam * P + (eu * ev * ew) * ((1 - lam - nu) * P - nu * Q) = 0 :=
    (mul_eq_zero.mp hcleared).resolve_left hPi
  linear_combination hcube


/-! ### Geometric support for the tricolor theorem -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable {o : Orientation ℝ E (Fin 2)}


theorem m7c_base_exp_ne_zero (θ : ℝ) : (Circle.exp θ : ℂ) ≠ 0 := by
  intro h
  have h1 : ‖(Circle.exp θ : ℂ)‖ = 1 := Circle.norm_coe _
  rw [h, norm_zero] at h1
  norm_num at h1

theorem m7c_base_one_sub_exp_ne (θ : ℝ) (h : Real.sin (θ / 2) ≠ 0) :
    (1 - (Circle.exp θ : ℂ)) ≠ 0 := by
  rw [one_sub_unit_eq]
  refine mul_ne_zero ?_ (m7c_base_exp_ne_zero _)
  intro h0
  apply h
  have h4 : (2 * Real.sin (θ / 2) : ℝ) = 0 := by exact_mod_cast h0
  linarith

theorem m7c_base_one_sub_exp_mul_ne {φ ψ : ℝ} (h : Real.sin ((φ + ψ) / 2) ≠ 0) :
    (1 - (Circle.exp φ : ℂ) * Circle.exp ψ) ≠ 0 := by
  rw [← Circle.coe_mul, ← Circle.exp_add]
  exact m7c_base_one_sub_exp_ne (φ + ψ) h

theorem m7c_base_red_form (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, i, j⟩) =
      toComplex o T.C + toComplex o (T.B - T.C) *
        ((1 - (Circle.exp (2 * T.beta - labelAngle i) : ℂ)) /
          (1 - (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) *
            (Circle.exp (2 * T.beta - labelAngle i) : ℂ))) := by
  simp only [constellationPoint, toComplex_rotationFixedPoint]

theorem m7c_base_green_form (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.green, i, j⟩) =
      toComplex o T.A + toComplex o (T.C - T.A) *
        ((1 - (Circle.exp (2 * T.gamma - labelAngle i) : ℂ)) /
          (1 - (Circle.exp (2 * T.alpha - labelAngle j) : ℂ) *
            (Circle.exp (2 * T.gamma - labelAngle i) : ℂ))) := by
  simp only [constellationPoint, toComplex_rotationFixedPoint]

theorem m7c_base_blue_form (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.blue, i, j⟩) =
      toComplex o T.B + toComplex o (T.A - T.B) *
        ((1 - (Circle.exp (2 * T.alpha - labelAngle i) : ℂ)) /
          (1 - (Circle.exp (2 * T.beta - labelAngle j) : ℂ) *
            (Circle.exp (2 * T.alpha - labelAngle i) : ℂ))) := by
  simp only [constellationPoint, toComplex_rotationFixedPoint]




theorem m7c_base_exp_three_label (t : TrisectorLabel) :
    (Circle.exp (3 * labelAngle t) : ℂ) = 1 := by
  have h3 : (3 : ℝ) * labelAngle t = ((3 : ℕ) : ℝ) * labelAngle t := by norm_num
  rw [h3, Circle.exp_natCast_mul, Circle.coe_pow, labelAngle_exp, ← pow_mul,
    show t.val * 3 = 3 * t.val from by ring, pow_mul, omega_cubed, one_pow]

theorem m7c_base_shift_cube (a : ℝ) (t : TrisectorLabel) :
    (Circle.exp (2 * a - labelAngle t) : ℂ) ^ 3 = (Circle.exp (6 * a) : ℂ) := by
  rw [← Circle.coe_pow, ← Circle.exp_natCast_mul]
  rw [show ((3 : ℕ) : ℝ) * (2 * a - labelAngle t) = 6 * a - 3 * labelAngle t by
    push_cast; ring]
  rw [Circle.exp_sub, Circle.coe_div, m7c_base_exp_three_label, div_one]

theorem m7c_base_sin_three_beta_ne (T : OrientedTriangle E o) : Real.sin (3 * T.beta) ≠ 0 :=
  ne_of_gt (m3_sin_three_beta_pos T)

theorem m7c_base_sin_three_alpha_ne (T : OrientedTriangle E o) : Real.sin (3 * T.alpha) ≠ 0 :=
  ne_of_gt (m3_sin_three_alpha_pos T)

theorem m7c_base_five_ne (T : OrientedTriangle E o) :
    (Circle.exp (6 * T.beta) : ℂ) - 1 ≠ 0 := by
  have h : (1 - (Circle.exp (6 * T.beta) : ℂ)) ≠ 0 := by
    refine m7c_base_one_sub_exp_ne (6 * T.beta) ?_
    rw [show 6 * T.beta / 2 = 3 * T.beta by ring]
    exact m7c_base_sin_three_beta_ne T
  intro h0
  rw [sub_eq_zero] at h0
  exact h (by rw [h0, sub_self])

theorem m7c_base_six_alpha_sub_one_ne (T : OrientedTriangle E o) :
    (Circle.exp (6 * T.alpha) : ℂ) - 1 ≠ 0 := by
  have h : (1 - (Circle.exp (6 * T.alpha) : ℂ)) ≠ 0 := by
    refine m7c_base_one_sub_exp_ne (6 * T.alpha) ?_
    rw [show 6 * T.alpha / 2 = 3 * T.alpha by ring]
    exact m7c_base_sin_three_alpha_ne T
  intro h0
  rw [sub_eq_zero] at h0
  exact h (by rw [h0, sub_self])

theorem m7c_base_exp_pi_div_two : (Circle.exp (Real.pi / 2) : ℂ) = Complex.I := by
  have h1 : (Circle.exp (-(Real.pi / 2)) : ℂ) = -Complex.I := m6_exp_neg_pi_div_two
  have hmul : ((Circle.exp (-(Real.pi / 2)) : ℂ)) * (Circle.exp (Real.pi / 2) : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← Circle.exp_add, show -(Real.pi / 2) + Real.pi / 2 = 0 by ring]
    simp
  rw [h1] at hmul
  have hne : (-Complex.I : ℂ) ≠ 0 := by
    intro h
    have h2 : (-Complex.I : ℂ) * Complex.I = 0 := by rw [h, zero_mul]
    rw [neg_mul, Complex.I_mul_I] at h2
    norm_num at h2
  refine mul_left_cancel₀ hne ?_
  rw [hmul, neg_mul, Complex.I_mul_I]
  norm_num

theorem m7c_base_six_alpha (T : OrientedTriangle E o) :
    (Circle.exp (6 * T.alpha) : ℂ) - 1 =
      2 * Complex.I * ((Real.sin (3 * T.alpha) : ℂ) * (Circle.exp (3 * T.alpha) : ℂ)) := by
  have h := one_sub_unit_eq (6 * T.alpha)
  rw [show 6 * T.alpha / 2 = 3 * T.alpha by ring] at h
  have h2 : (Circle.exp (3 * T.alpha - Real.pi / 2) : ℂ) =
      (Circle.exp (3 * T.alpha) : ℂ) * (-Complex.I) := by
    rw [show 3 * T.alpha - Real.pi / 2 = 3 * T.alpha + -(Real.pi / 2) by ring,
      Circle.exp_add, Circle.coe_mul, m6_exp_neg_pi_div_two]
  rw [h2] at h
  linear_combination -h

theorem m7c_base_six_beta (T : OrientedTriangle E o) :
    (Circle.exp (6 * T.beta) : ℂ) - 1 =
      2 * Complex.I * ((Real.sin (3 * T.beta) : ℂ) * (Circle.exp (3 * T.beta) : ℂ)) := by
  have h := one_sub_unit_eq (6 * T.beta)
  rw [show 6 * T.beta / 2 = 3 * T.beta by ring] at h
  have h2 : (Circle.exp (3 * T.beta - Real.pi / 2) : ℂ) =
      (Circle.exp (3 * T.beta) : ℂ) * (-Complex.I) := by
    rw [show 3 * T.beta - Real.pi / 2 = 3 * T.beta + -(Real.pi / 2) by ring,
      Circle.exp_add, Circle.coe_mul, m6_exp_neg_pi_div_two]
  rw [h2] at h
  linear_combination -h

theorem m7c_base_exp_pi : (Circle.exp Real.pi : ℂ) = -1 := by
  rw [show Real.pi = Real.pi / 2 + Real.pi / 2 by ring, Circle.exp_add, Circle.coe_mul,
    m7c_base_exp_pi_div_two, Complex.I_mul_I]

theorem m7c_base_three_gamma (T : OrientedTriangle E o) :
    (Circle.exp (3 * T.gamma) : ℂ) =
      -((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ)) := by
  have hsum := T.angle_sum
  have harg : 3 * T.gamma = -(3 * (T.alpha + T.beta)) + Real.pi := by linarith
  rw [harg, Circle.exp_add, Circle.coe_mul]
  rw [m7c_base_exp_pi]
  ring

theorem m7c_base_rho (T : OrientedTriangle E o) :
    ‖T.B - T.C‖ / ‖T.A - T.C‖ = Real.sin (3 * T.alpha) / Real.sin (3 * T.beta) := by
  have ha : ‖T.B - T.C‖ = T.aLength := by
    rw [aLength, show T.a = T.C - T.B from rfl, norm_sub_rev]
  have hb : ‖T.A - T.C‖ = T.bLength := by
    rw [bLength, show T.b = T.A - T.C from rfl]
  rw [ha, hb, T.side_lengths_sine.1, T.side_lengths_sine.2.1]
  have h1 : T.delta ≠ 0 := ne_of_gt (m7_delta_pos T)
  field_simp

theorem m7c_base_p_rel (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    toComplex o (T.B - T.C) *
        ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) ^ 3 *
          ((Circle.exp (2 * T.beta - labelAngle i) : ℂ) ^ 3 - 1))
      = ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) ^ 3 - 1) *
          toComplex o (T.C - T.A) := by
  have hP : toComplex o (T.B - T.C) =
      -(((‖T.B - T.C‖ / ‖T.A - T.C‖ : ℝ) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ)) *
        toComplex o (T.C - T.A) := by
    have h := congrArg (toComplex o) T.m6_trisector_C
    rw [h, toComplex_smul, toComplex_rotateVector]
    rw [show T.A - T.C = -(T.C - T.A) from by abel, toComplex_neg]
    ring
  have hXYZ : ((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ) * (Circle.exp (6 * T.alpha) : ℂ)) *
      (Circle.exp (3 * T.beta) : ℂ) = (Circle.exp (3 * T.alpha) : ℂ) := by
    rw [Circle.coe_exp, Circle.coe_exp, Circle.coe_exp, Circle.coe_exp,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hK : -(((‖T.B - T.C‖ / ‖T.A - T.C‖ : ℝ) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ)) *
        ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) ^ 3 *
          ((Circle.exp (2 * T.beta - labelAngle i) : ℂ) ^ 3 - 1))
      = ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) ^ 3 - 1) := by
    rw [m7c_base_shift_cube T.alpha k, m7c_base_shift_cube T.beta i, m7c_base_six_alpha T, m7c_base_six_beta T,
      m7c_base_three_gamma T, m7c_base_rho T]
    have hs : (Real.sin (3 * T.beta) : ℂ) ≠ 0 := by
      exact_mod_cast m7c_base_sin_three_beta_ne T
    have hcancel : ((Real.sin (3 * T.alpha) / Real.sin (3 * T.beta) : ℝ) : ℂ) *
        (Real.sin (3 * T.beta) : ℂ) = (Real.sin (3 * T.alpha) : ℂ) := by
      rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (m7c_base_sin_three_beta_ne T)]
    have h1 : (-((((Real.sin (3 * T.alpha) / Real.sin (3 * T.beta) : ℝ) : ℂ) *
          (-((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ)))))) *
        ((Circle.exp (6 * T.alpha) : ℂ) *
          (2 * Complex.I * ((Real.sin (3 * T.beta) : ℂ) * (Circle.exp (3 * T.beta) : ℂ))))
        = 2 * Complex.I * ((Real.sin (3 * T.alpha) : ℂ) *
            (((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ) * (Circle.exp (6 * T.alpha) : ℂ)) *
              (Circle.exp (3 * T.beta) : ℂ))) := by
      linear_combination (2 * Complex.I *
        (((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ) * (Circle.exp (6 * T.alpha) : ℂ)) *
          (Circle.exp (3 * T.beta) : ℂ))) * hcancel
    rw [h1, hXYZ]
  rw [hP]
  linear_combination (toComplex o (T.C - T.A)) * hK

theorem m7c_base_sin_ne (i j k : TrisectorLabel) (hq : i + j + k ≠ 1) :
    Real.sin ((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * Real.pi / 3) ≠ 0 := by
  intro hsin
  rw [Real.sin_eq_zero_iff] at hsin
  obtain ⟨m, hm⟩ := hsin
  have hreal : ((1 : ℝ) - ((i.val + j.val + k.val : ℕ) : ℝ)) = 3 * (m : ℝ) := by
    have h4 : (m : ℝ) * 3 = 1 - ((i.val + j.val + k.val : ℕ) : ℝ) := by
      nlinarith [hm, Real.pi_pos]
    linarith
  have hint : ((1 : ℤ) - ((i.val + j.val + k.val : ℕ) : ℤ)) = 3 * m := by
    exact_mod_cast hreal
  have hN : ((i.val + j.val + k.val : ℕ) : ZMod 3) = 1 := by
    have h6 : (((i.val + j.val + k.val : ℕ) : ℤ)) = 1 - 3 * m := by linarith
    rw [← Int.cast_natCast, h6]
    push_cast
    have h3z : ((3 : ZMod 3)) = 0 := by decide
    rw [h3z]
    ring
  rw [show ((i.val + j.val + k.val : ℕ) : ZMod 3) = i + j + k from by
    push_cast
    rw [ZMod.natCast_zmod_val i, ZMod.natCast_zmod_val j, ZMod.natCast_zmod_val k]] at hN
  exact hq hN

theorem m7c_base_T_cube (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
      (Circle.exp (2 * T.gamma - labelAngle j) : ℂ)) ^ 3 = 1 := by
  rw [mul_pow, mul_pow, m7c_base_shift_cube T.alpha k, m7c_base_shift_cube T.beta i,
    m7c_base_shift_cube T.gamma j]
  rw [← Circle.coe_mul, ← Circle.coe_mul, ← Circle.exp_add, ← Circle.exp_add]
  rw [show 6 * T.alpha + 6 * T.beta + 6 * T.gamma = 2 * Real.pi by
    rw [← T.angle_sum]; ring]
  rw [show (2 * Real.pi : ℝ) = Real.pi + Real.pi by ring, Circle.exp_add, Circle.coe_mul,
    m7c_base_exp_pi]
  norm_num

theorem m7c_base_T_form (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
      (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) =
      (Circle.exp ((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3)) : ℂ) := by
  rw [← Circle.coe_mul, ← Circle.coe_mul, ← Circle.exp_add, ← Circle.exp_add]
  congr 1
  congr 1
  push_cast [labelAngle]
  linear_combination (2 / 3) * T.angle_sum

theorem m7c_base_T_ne_one (T : OrientedTriangle E o) (i j k : TrisectorLabel)
    (hq : i + j + k ≠ 1) :
    (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
      (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) ≠ 1 := by
  rw [m7c_base_T_form T i j k]
  intro h1
  have h0 : (1 - (Circle.exp ((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3)) : ℂ)) = 0 := by
    rw [h1]; ring
  rw [one_sub_unit_eq] at h0
  have hsin : Real.sin (((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3)) / 2) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · have h2 : (2 * Real.sin (((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3)) / 2) : ℝ) = 0 := by
        exact_mod_cast h
      linarith
    · exact absurd h (m7c_base_exp_ne_zero _)
  exact m7c_base_sin_ne i j k hq (by
    rwa [show (1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3) / 2
      = (1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * Real.pi / 3 by ring] at hsin)

theorem m7c_base_T_quad (T : OrientedTriangle E o) (i j k : TrisectorLabel)
    (hq : i + j + k ≠ 1) :
    1 + (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
        (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) +
      ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
        (Circle.exp (2 * T.gamma - labelAngle j) : ℂ)) ^ 2 = 0 := by
  set Tt : ℂ := (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) *
    (Circle.exp (2 * T.beta - labelAngle i) : ℂ) * (Circle.exp (2 * T.gamma - labelAngle j) : ℂ)
    with hTt
  have h3 : Tt ^ 3 = 1 := m7c_base_T_cube T i j k
  have hne : Tt ≠ 1 := m7c_base_T_ne_one T i j k hq
  have hfac : (Tt - 1) * (Tt ^ 2 + Tt + 1) = 0 := by
    linear_combination h3
  have h2 : Tt ^ 2 + Tt + 1 = 0 := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
  linear_combination h2

theorem m7c_base_cmv_norm {z : ℂ} {v : E} :
    ‖complexMulVector o z v‖ = ‖z‖ * ‖v‖ := by
  rw [← toComplex_norm (o := o) (complexMulVector o z v), w9_toComplex_complexMulVector,
    norm_mul, toComplex_norm, mul_comm]

theorem m7c_base_circle_norm (θ : ℝ) : ‖(Circle.exp θ : ℂ)‖ = 1 := Circle.norm_coe _

theorem m7c_base_rot_C (T : OrientedTriangle E o) (i j k : TrisectorLabel)
    (hq : i + j + k ≠ 1) :
    toComplex o (T.constellationPoint ⟨.green, j, k⟩) -
        toComplex o (T.constellationPoint ⟨.red, i, j⟩)
      = (-((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) *
          (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
          (Circle.exp (2 * T.gamma - labelAngle j) : ℂ))) *
        (toComplex o (T.constellationPoint ⟨.blue, k, i⟩) -
          toComplex o (T.constellationPoint ⟨.red, i, j⟩)) := by
  rw [m7c_base_red_form T i j, m7c_base_green_form T j k, m7c_base_blue_form T k i]
  set Eu : ℂ := (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) with hEu
  set Ev : ℂ := (Circle.exp (2 * T.beta - labelAngle i) : ℂ) with hEv
  set Ew : ℂ := (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) with hEw
  set B1 : ℂ := 1 - Ew * Ev with hB1
  set B2 : ℂ := 1 - Eu * Ew with hB2
  set B3 : ℂ := 1 - Ev * Eu with hB3
  have hn1 : B1 ≠ 0 := by
    rw [hB1, hEw, hEv]
    refine m7c_base_one_sub_exp_mul_ne (φ := 2 * T.gamma - labelAngle j)
      (ψ := 2 * T.beta - labelAngle i) ?_
    obtain ⟨hb0, hb1⟩ := m6_beta_add_gamma_bounds_lt (o := o) T
    convert m6_sin_shift_sub_ne_zero hb0 hb1 i j using 2
    ring
  have hn2 : B2 ≠ 0 := by
    rw [hB2, hEu, hEw]
    refine m7c_base_one_sub_exp_mul_ne (φ := 2 * T.alpha - labelAngle k)
      (ψ := 2 * T.gamma - labelAngle j) ?_
    obtain ⟨hb0, hb1⟩ := m6_gamma_add_alpha_bounds_lt (o := o) T
    convert m6_sin_shift_sub_ne_zero hb0 hb1 k j using 2
    ring
  have hn3 : B3 ≠ 0 := by
    rw [hB3, hEv, hEu]
    refine m7c_base_one_sub_exp_mul_ne (φ := 2 * T.beta - labelAngle i)
      (ψ := 2 * T.alpha - labelAngle k) ?_
    obtain ⟨hb0, hb1⟩ := m6_alpha_add_beta_bounds_lt (o := o) T
    convert m6_sin_shift_sub_ne_zero hb0 hb1 i k using 2
    ring
  have hKnz : Eu ^ 3 * (Ev ^ 3 - 1) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero 3 ?_) ?_
    · rw [hEu]; exact m7c_base_exp_ne_zero _
    · rw [hEv, m7c_base_shift_cube (a := T.beta) (t := i)]
      exact m7c_base_five_ne T
  have hp'' : toComplex o (T.B - T.C) * (Eu ^ 3 * (Ev ^ 3 - 1))
      = (Eu ^ 3 - 1) * toComplex o (T.C - T.A) := by
    have h := m7c_base_p_rel T i j k
    rw [← hEu, ← hEv] at h
    exact h
  have hT'' : 1 + Eu * Ev * Ew + (Eu * Ev * Ew) ^ 2 = 0 := by
    have h := m7c_base_T_quad T i j k hq
    rw [← hEu, ← hEv, ← hEw] at h
    exact h
  have hkey := m7c_base_affine_key Eu Ev Ew (-(Eu * Ev * Ew))
    (toComplex o (T.B - T.C)) (toComplex o (T.C - T.A)) B1 B2 B3
    (Eu ^ 3 * (Ev ^ 3 - 1)) (Eu * Ev * Ew)
    ((1 - Ev) / B1) ((1 - Ew) / B2) ((1 - Eu) / B3)
    (by rw [hB1]; ring) (by rw [hB2]; ring) (by rw [hB3]; ring) rfl rfl
    (by field_simp) (by field_simp) (by field_simp)
    hn1 hn2 hn3 hKnz hp'' hT'' rfl
  have e1 : toComplex o T.A - toComplex o T.C + toComplex o (T.C - T.A) = 0 := by
    rw [← toComplex_sub, show T.A - T.C = -(T.C - T.A) from by abel, toComplex_neg]
    ring
  have e2 : toComplex o T.B - toComplex o T.C - toComplex o (T.B - T.C) = 0 := by
    rw [← toComplex_sub]
    ring
  have e3 : toComplex o (T.A - T.B) + toComplex o (T.B - T.C) + toComplex o (T.C - T.A) = 0 := by
    rw [← toComplex_add, ← toComplex_add]
    congr 1
    abel
    simp
  linear_combination hkey + e1 - (-(Eu * Ev * Ew)) * e2 -
    (-(Eu * Ev * Ew)) * ((1 - Eu) / B3) * e3

theorem m7c_base_cmv_one (v : E) : complexMulVector o (1 : ℂ) v = v := by
  apply toComplex_injective o
  rw [w9_toComplex_complexMulVector]
  ring

theorem m7c_base_tricolor_equilateral_of_ne_one (T : OrientedTriangle E o) (q : TricolorIndex)
    (hq : q.i + q.j + q.k ≠ 1) :
    Equilateral (T.tricolorTriangle q).first (T.tricolorTriangle q).second
      (T.tricolorTriangle q).third := by
  set Eu : ℂ := (Circle.exp (2 * T.alpha - labelAngle q.k) : ℂ) with hEu
  set Ev : ℂ := (Circle.exp (2 * T.beta - labelAngle q.i) : ℂ) with hEv
  set Ew : ℂ := (Circle.exp (2 * T.gamma - labelAngle q.j) : ℂ) with hEw
  have hC := m7c_base_rot_C T q.i q.j q.k hq
  rw [← hEu, ← hEv, ← hEw] at hC
  have hE : T.constellationPoint ⟨.green, q.j, q.k⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩
      = complexMulVector o (-(Eu * Ev * Ew))
          (T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩) := by
    apply toComplex_injective o
    rw [toComplex_sub, w9_toComplex_complexMulVector, toComplex_sub, mul_comm]
    exact hC
  have hT'' : 1 + Eu * Ev * Ew + (Eu * Ev * Ew) ^ 2 = 0 := by
    have h := m7c_base_T_quad T q.i q.j q.k hq
    rw [← hEu, ← hEv, ← hEw] at h
    exact h
  have hnorm : ‖Eu‖ = 1 := by rw [hEu]; exact m7c_base_circle_norm _
  have hnorm' : ‖Ev‖ = 1 := by rw [hEv]; exact m7c_base_circle_norm _
  have hnorm'' : ‖Ew‖ = 1 := by rw [hEw]; exact m7c_base_circle_norm _
  have hTnorm : ‖Eu * Ev * Ew‖ = 1 := by rw [norm_mul, norm_mul, hnorm, hnorm', hnorm'']; norm_num
  have hζ : ‖(-(Eu * Ev * Ew))‖ = 1 := by rw [norm_neg, hTnorm]
  have hζ1 : ‖(-(Eu * Ev * Ew)) - 1‖ = 1 := by
    have hsq : -(Eu * Ev * Ew) - 1 = (Eu * Ev * Ew) ^ 2 := by
      linear_combination -hT''
    rw [hsq, norm_pow, hTnorm, one_pow]
  have hbg : T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.green, q.j, q.k⟩
      = complexMulVector o (1 - (-(Eu * Ev * Ew)))
          (T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩) := by
    apply toComplex_injective o
    rw [toComplex_sub, w9_toComplex_complexMulVector, toComplex_sub]
    linear_combination -hC
  have h1 : dist (T.tricolorTriangle q).first (T.tricolorTriangle q).second
      = ‖T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩‖ := by
    show dist (T.constellationPoint ⟨.red, q.i, q.j⟩) (T.constellationPoint ⟨.green, q.j, q.k⟩) = _
    rw [dist_eq_norm, norm_sub_rev,
      show T.constellationPoint ⟨.green, q.j, q.k⟩ -
        T.constellationPoint ⟨.red, q.i, q.j⟩ = complexMulVector o (-(Eu * Ev * Ew))
          (T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩) from hE,
      m7c_base_cmv_norm, hζ, one_mul]
  have h2 : dist (T.tricolorTriangle q).second (T.tricolorTriangle q).third
      = ‖T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩‖ := by
    show dist (T.constellationPoint ⟨.green, q.j, q.k⟩) (T.constellationPoint ⟨.blue, q.k, q.i⟩) = _
    rw [dist_eq_norm, norm_sub_rev,
      show T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.green, q.j, q.k⟩ =
        complexMulVector o (1 - (-(Eu * Ev * Ew)))
          (T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩) from hbg,
      m7c_base_cmv_norm, show ‖1 - (-(Eu * Ev * Ew))‖ = 1 from by rw [norm_sub_rev]; exact hζ1,
      one_mul]
  have h3 : dist (T.tricolorTriangle q).third (T.tricolorTriangle q).first
      = ‖T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩‖ := by
    show dist (T.constellationPoint ⟨.blue, q.k, q.i⟩) (T.constellationPoint ⟨.red, q.i, q.j⟩) = _
    rw [dist_eq_norm]
  exact ⟨h1.trans h2.symm, h2.trans h3.symm⟩




variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable {o : Orientation ℝ E (Fin 2)}

/-! ### Rotating a pair of parallel vectors -/

theorem m7c_parallel_rot {u w : E} (φ : ℝ) (h : Parallel u w) :
    Parallel (rotateVector o u φ) (rotateVector o w φ) := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨r, by rw [rotateVector_smul]⟩

/-- A nonzero rotated area forbids parallelism. -/
theorem m7c_notParallel_of_area {u w : E}
    (h : (conj (toComplex o u) * toComplex o w).im ≠ 0) : ¬ Parallel u w := by
  rintro ⟨r, rfl⟩
  apply h
  rw [toComplex_smul, mul_left_comm, mul_comm (conj (toComplex o u)) (toComplex o u),
    Complex.mul_conj]
  simp

/-! ### Uniqueness of a rotated preimage on a second line -/

theorem m7c_unique_hit {V : E} {l₁ l₂ : Line E} {φ : ℝ}
    (hpar : ¬ Parallel (rotateVector o l₁.direction φ) l₂.direction)
    {P P' : E} (h1 : l₁.mem P) (h2 : l₁.mem P')
    (g1 : l₂.mem (V + rotateVector o (P - V) φ))
    (g2 : l₂.mem (V + rotateVector o (P' - V) φ)) : P = P' := by
  by_contra hne
  have hd : P' - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hP : Parallel l₁.direction (P' - P) := l₁.parallel_of_mem_sub h1 h2
  have hP' : Parallel (rotateVector o l₁.direction φ) (rotateVector o (P' - P) φ) :=
    m7c_parallel_rot φ hP
  have hsub : (V + rotateVector o (P' - V) φ) - (V + rotateVector o (P - V) φ)
      = rotateVector o (P' - P) φ := by
    rw [add_sub_add_left_eq_sub, ← rotateVector_sub]
    congr 1
    abel
  have hQ : Parallel l₂.direction ((V + rotateVector o (P' - V) φ) - (V + rotateVector o (P - V) φ)) :=
    l₂.parallel_of_mem_sub g1 g2
  rw [hsub] at hQ
  obtain ⟨r, hr⟩ := hQ
  obtain ⟨s, hs⟩ := hP'
  have hne0 : rotateVector o (P' - P) φ ≠ 0 := by
    intro h0
    have hv := rotateVector_norm o (P' - P) φ
    rw [h0, norm_zero] at hv
    exact hd (norm_eq_zero.mp hv.symm)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hr
    exact hne0 hr
  apply hpar
  have hkey : r • l₂.direction = s • rotateVector o l₁.direction φ := by rw [← hr, ← hs]
  refine ⟨r⁻¹ * s, ?_⟩
  calc l₂.direction = r⁻¹ • (r • l₂.direction) := by
        rw [smul_smul, inv_mul_cancel₀ hr0, one_smul]
    _ = r⁻¹ • (s • rotateVector o l₁.direction φ) := by rw [hkey]
    _ = (r⁻¹ * s) • rotateVector o l₁.direction φ := by rw [smul_smul]

/-! ### The complex form of the sides in the frame `C - B` -/

theorem m7c_exp_cancel3 (a : ℝ) :
    (Circle.exp (3 * a) : ℂ) * (Circle.exp (-3 * a) : ℂ) = 1 := by
  rw [m6_circle_exp_mul, show 3 * a + -3 * a = 0 from by ring]
  simp

theorem m7c_exp_neg_pi : (Circle.exp (-Real.pi) : ℂ) = -1 := by
  rw [m6_circle_exp_eq, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]
  norm_num

theorem m7c_exp_neg_pi_add3 (b : ℝ) :
    (Circle.exp (-Real.pi + 3 * b) : ℂ) = -((Circle.exp (3 * b) : ℂ)) := by
  rw [← m6_circle_exp_mul, m7c_exp_neg_pi]
  ring

theorem m7c_star_conj_mul (T : OrientedTriangle E o) :
    conj (toComplex o T.aStar) * toComplex o T.aStar = 1 := by
  rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm, toComplex_norm, m7_norm_aStar]
  norm_num

theorem m7c_AC_form (T : OrientedTriangle E o) :
    toComplex o (T.A - T.C) =
      -((T.bLength : ℝ) : ℂ) * (Circle.exp (-3 * T.gamma) : ℂ) * toComplex o T.aStar := by
  have hCA := toComplex_C_sub_A (T := T)
  have hbb : toComplex o T.bStar =
      -((Circle.exp (-3 * T.gamma) : ℂ)) * toComplex o T.aStar := by
    rw [T.bStar_relation, toComplex_neg, toComplex_rotateVector]
    ring
  have hcc : toComplex o T.cStar =
      -((Circle.exp (-3 * T.alpha) : ℂ)) * toComplex o T.bStar := by
    rw [T.cStar_relation, toComplex_neg, toComplex_rotateVector]
    ring
  have hAC : T.A - T.C = -(T.C - T.A) := by abel
  have hbL := T.side_lengths_sine.2.1
  rw [hAC, toComplex_neg, hCA, hcc, hbb, hbL, ← Complex.ofReal_mul]
  linear_combination (-(((T.delta * Real.sin (3 * T.beta) : ℝ)) : ℂ) *
    (Circle.exp (-3 * T.gamma) : ℂ) * toComplex o T.aStar) * m7c_exp_cancel3 T.alpha

theorem m7c_BA_form (T : OrientedTriangle E o) :
    toComplex o (T.B - T.A) =
      -((T.cLength : ℝ) : ℂ) * (Circle.exp (3 * T.beta) : ℂ) * toComplex o T.aStar := by
  have hAB := toComplex_A_sub_B (T := T)
  have hbb : toComplex o T.bStar =
      -((Circle.exp (-3 * T.gamma) : ℂ)) * toComplex o T.aStar := by
    rw [T.bStar_relation, toComplex_neg, toComplex_rotateVector]
    ring
  have hcc : toComplex o T.cStar =
      -((Circle.exp (-3 * T.alpha) : ℂ)) * toComplex o T.bStar := by
    rw [T.cStar_relation, toComplex_neg, toComplex_rotateVector]
    ring
  have hBA : T.B - T.A = -(T.A - T.B) := by abel
  have hsum := T.angle_sum
  have hkey : (Circle.exp (-3 * T.alpha) : ℂ) * (Circle.exp (-3 * T.gamma) : ℂ) =
      -((Circle.exp (3 * T.beta) : ℂ)) := by
    rw [m6_circle_exp_mul,
      show -3 * T.alpha + -3 * T.gamma = -Real.pi + 3 * T.beta from by linarith,
      m7c_exp_neg_pi_add3]
  have hcL := T.side_lengths_sine.2.2
  rw [hBA, toComplex_neg, hAB, hcc, hbb, hcL, ← Complex.ofReal_mul]
  linear_combination ((((T.delta * Real.sin (3 * T.gamma) : ℝ)) : ℂ) *
    toComplex o T.aStar) * hkey

/-- `conj (A - C) * (C - B) = -(|A-C| |C-B|) exp(3 i gamma)`. -/
theorem m7c_conj_AC_mul_CB (T : OrientedTriangle E o) :
    conj (toComplex o (T.A - T.C)) * toComplex o (T.C - T.B) =
      -((T.aLength : ℝ) : ℂ) * ((T.bLength : ℝ) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ) := by
  have hAC := m7c_AC_form T
  have hCB : toComplex o (T.C - T.B) = ((T.aLength : ℝ) : ℂ) * toComplex o T.aStar := by
    have h := m1_toComplex_B_sub_C T
    have hh : T.C - T.B = -(T.B - T.C) := by abel
    rw [hh, toComplex_neg, h]; ring
  have hconj : conj (toComplex o (T.A - T.C)) =
      -((T.bLength : ℝ) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ) * conj (toComplex o T.aStar) := by
    rw [hAC]
    simp only [map_mul, map_neg, Complex.conj_ofReal, m6_conj_circle_exp]
    have harg : -(-3 * T.gamma) = 3 * T.gamma := by ring
    rw [harg]
  rw [hconj, hCB]
  have hstar := m7c_star_conj_mul T
  linear_combination (-((T.aLength : ℝ) : ℂ) * ((T.bLength : ℝ) : ℂ) *
    (Circle.exp (3 * T.gamma) : ℂ)) * hstar

/-- `conj (C - B) * (B - A) = -(|C-B| |B-A|) exp(3 i beta)`. -/
theorem m7c_conj_CB_mul_BA (T : OrientedTriangle E o) :
    conj (toComplex o (T.C - T.B)) * toComplex o (T.B - T.A) =
      -((T.aLength : ℝ) : ℂ) * ((T.cLength : ℝ) : ℂ) * (Circle.exp (3 * T.beta) : ℂ) := by
  have hBA := m7c_BA_form T
  have hCB : toComplex o (T.C - T.B) = ((T.aLength : ℝ) : ℂ) * toComplex o T.aStar := by
    have h := m1_toComplex_B_sub_C T
    have hh : T.C - T.B = -(T.B - T.C) := by abel
    rw [hh, toComplex_neg, h]; ring
  have hconj : conj (toComplex o (T.C - T.B)) =
      ((T.aLength : ℝ) : ℂ) * conj (toComplex o T.aStar) := by
    rw [hCB]
    simp only [map_mul, Complex.conj_ofReal]
  rw [hconj, hBA]
  have hstar := m7c_star_conj_mul T
  linear_combination (-((T.aLength : ℝ) : ℂ) * ((T.cLength : ℝ) : ℂ) *
    (Circle.exp (3 * T.beta) : ℂ)) * hstar


/-! ### The rotated area of a pair of triangle sides -/

theorem m7c_area1 (T : OrientedTriangle E o) (θ φ : ℝ) :
    (conj (toComplex o (rotateVector o (T.A - T.C) θ)) *
      toComplex o (rotateVector o (T.C - T.B) φ)).im
      = -((T.aLength : ℝ) * (T.bLength : ℝ)) * Real.sin (3 * T.gamma + φ - θ) := by
  rw [← areaForm_complex]
  have hkey : conj (toComplex o (T.A - T.C)) * toComplex o (T.C - T.B) =
      (Circle.exp (-(-3 * T.gamma)) : ℂ) * ((-(T.aLength * T.bLength) : ℝ) : ℂ) := by
    rw [m7c_conj_AC_mul_CB]
    have harg : -(-3 * T.gamma) = 3 * T.gamma := by ring
    rw [harg, Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  have harg : φ - θ + 3 * T.gamma = 3 * T.gamma + φ - θ := by ring
  simpa [orientedArea, harg] using m3_area_rot_general (T.A - T.C) (T.C - T.B) (-3 * T.gamma)
    (-(T.aLength * T.bLength)) hkey 1 θ φ

theorem m7c_area2 (T : OrientedTriangle E o) (θ φ : ℝ) :
    (conj (toComplex o (rotateVector o (T.C - T.B) θ)) *
      toComplex o (rotateVector o (T.B - T.A) φ)).im
      = -((T.aLength : ℝ) * (T.cLength : ℝ)) * Real.sin (3 * T.beta + φ - θ) := by
  rw [← areaForm_complex]
  have hkey : conj (toComplex o (T.C - T.B)) * toComplex o (T.B - T.A) =
      (Circle.exp (-(-3 * T.beta)) : ℂ) * ((-(T.aLength * T.cLength) : ℝ) : ℂ) := by
    rw [m7c_conj_CB_mul_BA]
    have harg : -(-3 * T.beta) = 3 * T.beta := by ring
    rw [harg, Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  have harg : φ - θ + 3 * T.beta = 3 * T.beta + φ - θ := by ring
  simpa [orientedArea, harg] using m3_area_rot_general (T.C - T.B) (T.B - T.A) (-3 * T.beta)
    (-(T.aLength * T.cLength)) hkey 1 θ φ

theorem m7c_notParallel_AC_CB (T : OrientedTriangle E o) (θ φ : ℝ)
    (h : Real.sin (3 * T.gamma + φ - θ) ≠ 0) :
    ¬ Parallel (rotateVector o (T.A - T.C) θ) (rotateVector o (T.C - T.B) φ) := by
  apply m7c_notParallel_of_area
  rw [m7c_area1]
  exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (ne_of_gt T.aLength_pos)
    (ne_of_gt T.bLength_pos))) h

theorem m7c_notParallel_CB_BA (T : OrientedTriangle E o) (θ φ : ℝ)
    (h : Real.sin (3 * T.beta + φ - θ) ≠ 0) :
    ¬ Parallel (rotateVector o (T.C - T.B) θ) (rotateVector o (T.B - T.A) φ) := by
  apply m7c_notParallel_of_area
  rw [m7c_area2]
  exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (ne_of_gt T.aLength_pos)
    (ne_of_gt T.cLength_pos))) h


/-! ### Three distinct points cannot all produce an equilateral triangle -/

theorem m7c_no_three {V : E} {l₁ l₂ : Line E}
    (h₁ : ¬ Parallel (rotateVector o l₁.direction (Real.pi / 3)) l₂.direction)
    (h₂ : ¬ Parallel (rotateVector o l₁.direction (-(Real.pi / 3))) l₂.direction)
    {P₀ P₁ P₂ : E} (hm₀ : l₁.mem P₀) (hm₁ : l₁.mem P₁) (hm₂ : l₁.mem P₂)
    (hd₀₁ : P₀ ≠ P₁) (hd₁₂ : P₁ ≠ P₂) (hd₀₂ : P₀ ≠ P₂)
    (e₀ : l₂.mem (V + rotateVector o (P₀ - V) (Real.pi / 3)) ∨
          l₂.mem (V + rotateVector o (P₀ - V) (-(Real.pi / 3))))
    (e₁ : l₂.mem (V + rotateVector o (P₁ - V) (Real.pi / 3)) ∨
          l₂.mem (V + rotateVector o (P₁ - V) (-(Real.pi / 3))))
    (e₂ : l₂.mem (V + rotateVector o (P₂ - V) (Real.pi / 3)) ∨
          l₂.mem (V + rotateVector o (P₂ - V) (-(Real.pi / 3)))) : False := by
  rcases e₀ with e₀ | e₀ <;> rcases e₁ with e₁ | e₁ <;> rcases e₂ with e₂ | e₂
  · exact hd₀₁ (m7c_unique_hit h₁ hm₀ hm₁ e₀ e₁)
  · exact hd₀₁ (m7c_unique_hit h₁ hm₀ hm₁ e₀ e₁)
  · exact hd₀₂ (m7c_unique_hit h₁ hm₀ hm₂ e₀ e₂)
  · exact hd₁₂ (m7c_unique_hit h₂ hm₁ hm₂ e₁ e₂)
  · exact hd₁₂ (m7c_unique_hit h₁ hm₁ hm₂ e₁ e₂)
  · exact hd₀₂ (m7c_unique_hit h₂ hm₀ hm₂ e₀ e₂)
  · exact hd₀₁ (m7c_unique_hit h₂ hm₀ hm₁ e₀ e₁)
  · exact hd₀₁ (m7c_unique_hit h₂ hm₀ hm₁ e₀ e₁)

/-! ### Distinctness of constellation points -/

theorem m7c_cp_ne_color (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {c c' : TrisectorColor} (hc : c ≠ c') (a b a' b' : TrisectorLabel) :
    T.constellationPoint ⟨c, a, b⟩ ≠ T.constellationPoint ⟨c', a', b'⟩ := by
  intro hh
  exact hc (congrArg ConstellationIndex.color (h hh))

theorem m7c_cp_ne_second (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (c : TrisectorColor) (a : TrisectorLabel) {b b' : TrisectorLabel} (hb : b ≠ b') :
    T.constellationPoint ⟨c, a, b⟩ ≠ T.constellationPoint ⟨c, a, b'⟩ := by
  intro hh
  exact hb (by simpa using congrArg ConstellationIndex.second (h hh))

theorem m7c_cp_ne_first (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (c : TrisectorColor) (b : TrisectorLabel) {a a' : TrisectorLabel} (ha : a ≠ a') :
    T.constellationPoint ⟨c, a, b⟩ ≠ T.constellationPoint ⟨c, a', b⟩ := by
  intro hh
  exact ha (by simpa using congrArg ConstellationIndex.first (h hh))

/-! ### The equilateral-to-membership step -/

theorem m7c_equilateral_swap23 {P Q R : E} (h : Equilateral P Q R) : Equilateral P R Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [dist_comm P R, ← h2, dist_comm]
  · rw [dist_comm R Q, ← h1, dist_comm]

theorem m7c_mem_of_equilateral {V P Q : E} {l₂ : Line E}
    (hV : V ≠ P) (hQ : l₂.mem Q)
    (he : Equilateral V P Q) :
    l₂.mem (V + rotateVector o (P - V) (Real.pi / 3)) ∨
      l₂.mem (V + rotateVector o (P - V) (-(Real.pi / 3))) := by
  have he' : Equilateral V Q P := m7c_equilateral_swap23 he
  have hrot := (m5_equilateral_iff_rotate (o := o) V Q P hV).mp he'
  rcases hrot with hr | hr
  · left
    have hh : V + rotateVector o (P - V) (Real.pi / 3) = Q := by rw [← hr]; abel
    rw [hh]
    exact hQ
  · right
    have hh : V + rotateVector o (P - V) (-(Real.pi / 3)) = Q := by rw [← hr]; abel
    rw [hh]
    exact hQ


/-! ### The two family arrangements -/

theorem m7c_familyA (T : OrientedTriangle E o) (i j : TrisectorLabel)
    (h : Injective T.constellationPoint)
    (h₁ : ¬ Parallel (rotateVector o (T.greenC j).direction (Real.pi / 3)) (T.blueB i).direction)
    (h₂ : ¬ Parallel (rotateVector o (T.greenC j).direction (-(Real.pi / 3))) (T.blueB i).direction) :
    ¬ (Equilateral (T.constellationPoint ⟨.red, i, j⟩) (T.constellationPoint ⟨.green, j, 0⟩)
          (T.constellationPoint ⟨.blue, 0, i⟩) ∧
       Equilateral (T.constellationPoint ⟨.red, i, j⟩) (T.constellationPoint ⟨.green, j, 1⟩)
          (T.constellationPoint ⟨.blue, 1, i⟩) ∧
       Equilateral (T.constellationPoint ⟨.red, i, j⟩) (T.constellationPoint ⟨.green, j, 2⟩)
          (T.constellationPoint ⟨.blue, 2, i⟩)) := by
  rintro ⟨he₀, he₁, he₂⟩
  exact m7c_no_three (V := T.constellationPoint ⟨.red, i, j⟩) h₁ h₂
    (m6_constellation_mem_greenC T j 0) (m6_constellation_mem_greenC T j 1)
    (m6_constellation_mem_greenC T j 2)
    (m7c_cp_ne_second T h .green j (by decide : (0 : TrisectorLabel) ≠ 1))
    (m7c_cp_ne_second T h .green j (by decide : (1 : TrisectorLabel) ≠ 2))
    (m7c_cp_ne_second T h .green j (by decide : (0 : TrisectorLabel) ≠ 2))
    (m7c_mem_of_equilateral (m7c_cp_ne_color T h (by decide : TrisectorColor.red ≠ TrisectorColor.green)
      i j j 0) (m6_constellation_mem_blueB T 0 i) he₀)
    (m7c_mem_of_equilateral (m7c_cp_ne_color T h (by decide : TrisectorColor.red ≠ TrisectorColor.green)
      i j j 1) (m6_constellation_mem_blueB T 1 i) he₁)
    (m7c_mem_of_equilateral (m7c_cp_ne_color T h (by decide : TrisectorColor.red ≠ TrisectorColor.green)
      i j j 2) (m6_constellation_mem_blueB T 2 i) he₂)

theorem m7c_familyB (T : OrientedTriangle E o) (i k : TrisectorLabel)
    (h : Injective T.constellationPoint)
    (h₁ : ¬ Parallel (rotateVector o (T.redB i).direction (Real.pi / 3)) (T.greenA k).direction)
    (h₂ : ¬ Parallel (rotateVector o (T.redB i).direction (-(Real.pi / 3))) (T.greenA k).direction) :
    ¬ (Equilateral (T.constellationPoint ⟨.red, i, 0⟩) (T.constellationPoint ⟨.green, 0, k⟩)
          (T.constellationPoint ⟨.blue, k, i⟩) ∧
       Equilateral (T.constellationPoint ⟨.red, i, 1⟩) (T.constellationPoint ⟨.green, 1, k⟩)
          (T.constellationPoint ⟨.blue, k, i⟩) ∧
       Equilateral (T.constellationPoint ⟨.red, i, 2⟩) (T.constellationPoint ⟨.green, 2, k⟩)
          (T.constellationPoint ⟨.blue, k, i⟩)) := by
  rintro ⟨he₀, he₁, he₂⟩
  have e₀ : Equilateral (T.constellationPoint ⟨.blue, k, i⟩) (T.constellationPoint ⟨.red, i, 0⟩)
      (T.constellationPoint ⟨.green, 0, k⟩) :=
    m1_equilateral_cycle (m1_equilateral_cycle he₀)
  have e₁ : Equilateral (T.constellationPoint ⟨.blue, k, i⟩) (T.constellationPoint ⟨.red, i, 1⟩)
      (T.constellationPoint ⟨.green, 1, k⟩) :=
    m1_equilateral_cycle (m1_equilateral_cycle he₁)
  have e₂ : Equilateral (T.constellationPoint ⟨.blue, k, i⟩) (T.constellationPoint ⟨.red, i, 2⟩)
      (T.constellationPoint ⟨.green, 2, k⟩) :=
    m1_equilateral_cycle (m1_equilateral_cycle he₂)
  exact m7c_no_three (V := T.constellationPoint ⟨.blue, k, i⟩) h₁ h₂
    (m6_constellation_mem_redB T i 0) (m6_constellation_mem_redB T i 1)
    (m6_constellation_mem_redB T i 2)
    (m7c_cp_ne_second T h .red i (by decide : (0 : TrisectorLabel) ≠ 1))
    (m7c_cp_ne_second T h .red i (by decide : (1 : TrisectorLabel) ≠ 2))
    (m7c_cp_ne_second T h .red i (by decide : (0 : TrisectorLabel) ≠ 2))
    (m7c_mem_of_equilateral (m7c_cp_ne_color T h (by decide : TrisectorColor.blue ≠ TrisectorColor.red)
      k i i 0) (m6_constellation_mem_greenA T 0 k) e₀)
    (m7c_mem_of_equilateral (m7c_cp_ne_color T h (by decide : TrisectorColor.blue ≠ TrisectorColor.red)
      k i i 1) (m6_constellation_mem_greenA T 1 k) e₁)
    (m7c_mem_of_equilateral (m7c_cp_ne_color T h (by decide : TrisectorColor.blue ≠ TrisectorColor.red)
      k i i 2) (m6_constellation_mem_greenA T 2 k) e₂)


/-! ### The trisector directions -/

theorem m7c_greenC_dir (T : OrientedTriangle E o) (j : TrisectorLabel) :
    (T.greenC j).direction = rotateVector o (T.A - T.C) (labelAngle j + T.gamma) := by
  show rotateVector o T.CY.direction (labelAngle j) = _
  rw [show T.CY.direction = rotateVector o (T.A - T.C) T.gamma from rfl, ← rotateVector_add_angle]

theorem m7c_blueB_dir (T : OrientedTriangle E o) (i : TrisectorLabel) :
    (T.blueB i).direction = rotateVector o (T.C - T.B) (2 * T.beta - labelAngle i) := by
  show rotateVector o T.BZ.direction (-labelAngle i) = _
  rw [show T.BZ.direction = rotateVector o (T.C - T.B) (2 * T.beta) from rfl,
    ← rotateVector_add_angle,
    show -labelAngle i + 2 * T.beta = 2 * T.beta - labelAngle i from by ring]

theorem m7c_redB_dir (T : OrientedTriangle E o) (i : TrisectorLabel) :
    (T.redB i).direction = rotateVector o (T.C - T.B) (labelAngle i + T.beta) := by
  show rotateVector o T.BX.direction (labelAngle i) = _
  rw [show T.BX.direction = rotateVector o (T.C - T.B) T.beta from rfl, ← rotateVector_add_angle]

theorem m7c_greenA_dir (T : OrientedTriangle E o) (k : TrisectorLabel) :
    (T.greenA k).direction = rotateVector o (T.B - T.A) (2 * T.alpha - labelAngle k) := by
  show rotateVector o T.AY.direction (-labelAngle k) = _
  rw [show T.AY.direction = rotateVector o (T.B - T.A) (2 * T.alpha) from rfl,
    ← rotateVector_add_angle,
    show -labelAngle k + 2 * T.alpha = 2 * T.alpha - labelAngle k from by ring]


/-! ### Elementary sine facts on the open interval `(-π/3, π/3)` -/

theorem m7c_int_eq_zero_of_mul_lt {n : ℤ} (h : |(n : ℝ)| * Real.pi < Real.pi / 3) : n = 0 := by
  have h2 : 3 * |(n : ℝ)| < 1 := by nlinarith [h, Real.pi_pos]
  have h4 : |(n : ℝ)| < 1 := by linarith
  rcases abs_lt.mp h4 with ⟨h5, h6⟩
  have h7 : (-1 : ℤ) < n := by exact_mod_cast h5
  have h8 : n < 1 := by exact_mod_cast h6
  have h9 : n = 0 := by omega
  exact h9

theorem m7c_eq_zero_of_sin_eq_zero {x : ℝ} (hx : |x| < Real.pi / 3)
    (h : Real.sin x = 0) : x = 0 := by
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
  have h1 : |x| = |(n : ℝ)| * Real.pi := by
    rw [← hn, abs_mul, abs_of_pos Real.pi_pos]
  have h2 : |(n : ℝ)| * Real.pi < Real.pi / 3 := by rw [← h1]; exact hx
  have h3 : n = 0 := m7c_int_eq_zero_of_mul_lt h2
  rw [← hn, h3]
  ring

theorem m7c_sin_ne_zero_of_abs_lt {x : ℝ} (hx : |x| < Real.pi / 3) (hx0 : x ≠ 0) :
    Real.sin x ≠ 0 := by
  intro h
  exact hx0 (m7c_eq_zero_of_sin_eq_zero hx h)

theorem m7c_area_eq_zero_of_parallel {u w : E} (h : Parallel u w) :
    orientedArea o u w = 0 := by
  obtain ⟨r, rfl⟩ := h
  rw [m1_orientedArea_smul_right, m1_orientedArea_self, mul_zero]

/-! ### The non-parallelism conditions for the two arrangements -/

theorem m7c_ni_A_plus (T : OrientedTriangle E o) (i j : TrisectorLabel)
    (hij : labelAngle i + labelAngle j = 4 * Real.pi / 3) :
    ¬ Parallel (rotateVector o (T.greenC j).direction (Real.pi / 3)) (T.blueB i).direction := by
  rw [m7c_greenC_dir, m7c_blueB_dir, ← rotateVector_add_angle]
  apply m7c_notParallel_AC_CB
  have hsum := T.angle_sum
  have harg : 3 * T.gamma + (2 * T.beta - labelAngle i) - (Real.pi / 3 + (labelAngle j + T.gamma))
      = -2 * T.alpha - Real.pi := by linarith
  rw [harg]
  have h2 : (0 : ℝ) < 2 * T.alpha := by linarith [m3_alpha_pos T]
  have h3 : 2 * T.alpha < Real.pi := by linarith [m3_three_alpha_lt_pi T]
  have hs : 0 < Real.sin (2 * T.alpha) := Real.sin_pos_of_pos_of_lt_pi h2 h3
  have he : Real.sin (-2 * T.alpha - Real.pi) = Real.sin (2 * T.alpha) := by
    rw [show -2 * T.alpha - Real.pi = -(2 * T.alpha + Real.pi) from by ring, Real.sin_neg,
      Real.sin_add_pi]
    ring
  rw [he]
  exact ne_of_gt hs

theorem m7c_ni_A_minus (T : OrientedTriangle E o) (i j : TrisectorLabel)
    (hij : labelAngle i + labelAngle j = 4 * Real.pi / 3) :
    ¬ Parallel (rotateVector o (T.greenC j).direction (-(Real.pi / 3))) (T.blueB i).direction := by
  rw [m7c_greenC_dir, m7c_blueB_dir, ← rotateVector_add_angle]
  apply m7c_notParallel_AC_CB
  have hsum := T.angle_sum
  have harg : 3 * T.gamma + (2 * T.beta - labelAngle i) - (-(Real.pi / 3) + (labelAngle j + T.gamma))
      = -2 * T.alpha - Real.pi / 3 := by linarith
  rw [harg]
  have hs : 0 < Real.sin (2 * T.alpha + Real.pi / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [m3_alpha_pos T, Real.pi_pos])
      (by linarith [m3_three_alpha_lt_pi T, m3_alpha_pos T])
  have he : Real.sin (-2 * T.alpha - Real.pi / 3) = -Real.sin (2 * T.alpha + Real.pi / 3) := by
    rw [show -2 * T.alpha - Real.pi / 3 = -(2 * T.alpha + Real.pi / 3) from by ring, Real.sin_neg]
  rw [he]
  exact neg_ne_zero.mpr (ne_of_gt hs)

theorem m7c_ni_B_plus (T : OrientedTriangle E o) (i k : TrisectorLabel)
    (hik : labelAngle i + labelAngle k = 2 * Real.pi / 3) :
    ¬ Parallel (rotateVector o (T.redB i).direction (Real.pi / 3)) (T.greenA k).direction := by
  rw [m7c_redB_dir, m7c_greenA_dir, ← rotateVector_add_angle]
  apply m7c_notParallel_CB_BA
  have hsum := T.angle_sum
  have harg : 3 * T.beta + (2 * T.alpha - labelAngle k) - (Real.pi / 3 + (labelAngle i + T.beta))
      = -2 * T.gamma - Real.pi / 3 := by linarith
  rw [harg]
  have hs : 0 < Real.sin (2 * T.gamma + Real.pi / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [m3_gamma_pos T, Real.pi_pos])
      (by linarith [m3_three_gamma_lt_pi T, m3_gamma_pos T])
  have he : Real.sin (-2 * T.gamma - Real.pi / 3) = -Real.sin (2 * T.gamma + Real.pi / 3) := by
    rw [show -2 * T.gamma - Real.pi / 3 = -(2 * T.gamma + Real.pi / 3) from by ring, Real.sin_neg]
  rw [he]
  exact neg_ne_zero.mpr (ne_of_gt hs)

theorem m7c_ni_B_minus (T : OrientedTriangle E o) (i k : TrisectorLabel)
    (hik : labelAngle i + labelAngle k = 2 * Real.pi / 3) (hg : T.gamma ≠ Real.pi / 6) :
    ¬ Parallel (rotateVector o (T.redB i).direction (-(Real.pi / 3))) (T.greenA k).direction := by
  rw [m7c_redB_dir, m7c_greenA_dir, ← rotateVector_add_angle]
  apply m7c_notParallel_CB_BA
  have hsum := T.angle_sum
  have harg : 3 * T.beta + (2 * T.alpha - labelAngle k) - (-(Real.pi / 3) + (labelAngle i + T.beta))
      = Real.pi / 3 - 2 * T.gamma := by linarith
  rw [harg]
  have hx : |Real.pi / 3 - 2 * T.gamma| < Real.pi / 3 := by
    rw [abs_lt]
    constructor
    · linarith [m3_three_gamma_lt_pi T, m3_gamma_pos T]
    · linarith [m3_gamma_pos T, Real.pi_pos]
  have hx0 : Real.pi / 3 - 2 * T.gamma ≠ 0 := by
    intro h; apply hg; linarith
  exact m7c_sin_ne_zero_of_abs_lt hx hx0


theorem m7c_ni_A_minus_00 (T : OrientedTriangle E o) :
    ¬ Parallel (rotateVector o (T.greenC 0).direction (-(Real.pi / 3))) (T.blueB 0).direction := by
  rw [m7c_greenC_dir, m7c_blueB_dir, ← rotateVector_add_angle]
  apply m7c_notParallel_AC_CB
  rw [m4_labelAngle_zero]
  have hsum := T.angle_sum
  have harg : 3 * T.gamma + (2 * T.beta - 0) - (-(Real.pi / 3) + (0 + T.gamma)) =
      Real.pi - 2 * T.alpha := by linarith
  rw [harg, Real.sin_pi_sub]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [m3_alpha_pos T])
    (by linarith [m3_three_alpha_lt_pi T, m3_alpha_pos T]))

/-! ### The converse: a parallelism forces a distinguished angle -/

theorem m7c_par_A00_plus (T : OrientedTriangle E o)
    (hpar : Parallel (rotateVector o (T.greenC 0).direction (Real.pi / 3))
      (T.blueB 0).direction) : T.alpha = Real.pi / 6 := by
  have h0 := m7c_area_eq_zero_of_parallel (o := o) hpar
  rw [m7c_greenC_dir, m7c_blueB_dir, ← rotateVector_add_angle] at h0
  have h1 : (conj (toComplex o (rotateVector o (T.A - T.C)
        (Real.pi / 3 + (labelAngle (0 : TrisectorLabel) + T.gamma)))) *
      toComplex o (rotateVector o (T.C - T.B) (2 * T.beta - labelAngle (0 : TrisectorLabel)))).im
      = 0 := by
    rw [← areaForm_complex]
    exact h0
  rw [m7c_area1] at h1
  have hsin : Real.sin (3 * T.gamma + (2 * T.beta - labelAngle (0 : TrisectorLabel)) -
      (Real.pi / 3 + (labelAngle (0 : TrisectorLabel) + T.gamma))) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (neg_ne_zero.mpr (mul_ne_zero (ne_of_gt T.aLength_pos)
        (ne_of_gt T.bLength_pos)))
    · exact h
  rw [m4_labelAngle_zero] at hsin
  have hsum := T.angle_sum
  have harg : 3 * T.gamma + (2 * T.beta - 0) - (Real.pi / 3 + (0 + T.gamma))
      = Real.pi / 3 - 2 * T.alpha := by linarith
  rw [harg] at hsin
  have hx : |Real.pi / 3 - 2 * T.alpha| < Real.pi / 3 := by
    rw [abs_lt]
    constructor
    · linarith [m3_three_alpha_lt_pi T, m3_alpha_pos T]
    · linarith [m3_alpha_pos T, Real.pi_pos]
  have := m7c_eq_zero_of_sin_eq_zero hx hsin
  linarith

theorem m7c_par_B01_minus (T : OrientedTriangle E o)
    (hpar : Parallel (rotateVector o (T.redB 0).direction (-(Real.pi / 3)))
      (T.greenA 1).direction) : T.gamma = Real.pi / 6 := by
  have h0 := m7c_area_eq_zero_of_parallel (o := o) hpar
  rw [m7c_redB_dir, m7c_greenA_dir, ← rotateVector_add_angle] at h0
  have h1 : (conj (toComplex o (rotateVector o (T.C - T.B)
        (-(Real.pi / 3) + (labelAngle (0 : TrisectorLabel) + T.beta)))) *
      toComplex o (rotateVector o (T.B - T.A) (2 * T.alpha - labelAngle (1 : TrisectorLabel)))).im
      = 0 := by
    rw [← areaForm_complex]
    exact h0
  rw [m7c_area2] at h1
  have hsin : Real.sin (3 * T.beta + (2 * T.alpha - labelAngle (1 : TrisectorLabel)) -
      (-(Real.pi / 3) + (labelAngle (0 : TrisectorLabel) + T.beta))) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (neg_ne_zero.mpr (mul_ne_zero (ne_of_gt T.aLength_pos)
        (ne_of_gt T.cLength_pos)))
    · exact h
  have hl1 : labelAngle (1 : TrisectorLabel) = 2 * Real.pi / 3 := m4_labelAngle_one
  rw [m4_labelAngle_zero, hl1] at hsin
  have hsum := T.angle_sum
  have harg : 3 * T.beta + (2 * T.alpha - 2 * Real.pi / 3) -
      (-(Real.pi / 3) + (0 + T.beta)) = Real.pi / 3 - 2 * T.gamma := by linarith
  rw [harg] at hsin
  have hx : |Real.pi / 3 - 2 * T.gamma| < Real.pi / 3 := by
    rw [abs_lt]
    constructor
    · linarith [m3_three_gamma_lt_pi T, m3_gamma_pos T]
    · linarith [m3_gamma_pos T, Real.pi_pos]
  have := m7c_eq_zero_of_sin_eq_zero hx hsin
  linarith


/-! ### The three orbit representatives are not equilateral -/

theorem m7c_not_equil_022 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    ¬ Equilateral (T.tricolorTriangle ⟨0, 2, 2⟩).first (T.tricolorTriangle ⟨0, 2, 2⟩).second
      (T.tricolorTriangle ⟨0, 2, 2⟩).third := by
  intro he
  have h02 : labelAngle (0 : TrisectorLabel) + labelAngle (2 : TrisectorLabel) =
      4 * Real.pi / 3 := by
    rw [m4_labelAngle_zero, m4_labelAngle_two, zero_add]
  exact m7c_familyA T 0 2 h (m7c_ni_A_plus T 0 2 h02) (m7c_ni_A_minus T 0 2 h02)
    ⟨m7c_base_tricolor_equilateral_of_ne_one T ⟨0, 2, 0⟩ (by decide),
      m7c_base_tricolor_equilateral_of_ne_one T ⟨0, 2, 1⟩ (by decide), he⟩

theorem m7c_not_equil_112 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    ¬ Equilateral (T.tricolorTriangle ⟨1, 1, 2⟩).first (T.tricolorTriangle ⟨1, 1, 2⟩).second
      (T.tricolorTriangle ⟨1, 1, 2⟩).third := by
  intro he
  have h11 : labelAngle (1 : TrisectorLabel) + labelAngle (1 : TrisectorLabel) =
      4 * Real.pi / 3 := by
    rw [m4_labelAngle_one]
    ring
  exact m7c_familyA T 1 1 h (m7c_ni_A_plus T 1 1 h11) (m7c_ni_A_minus T 1 1 h11)
    ⟨m7c_base_tricolor_equilateral_of_ne_one T ⟨1, 1, 0⟩ (by decide),
      m7c_base_tricolor_equilateral_of_ne_one T ⟨1, 1, 1⟩ (by decide), he⟩

theorem m7c_not_equil_001 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    ¬ Equilateral (T.tricolorTriangle ⟨0, 0, 1⟩).first (T.tricolorTriangle ⟨0, 0, 1⟩).second
      (T.tricolorTriangle ⟨0, 0, 1⟩).third := by
  intro he
  have h01 : labelAngle (0 : TrisectorLabel) + labelAngle (1 : TrisectorLabel) =
      2 * Real.pi / 3 := by
    rw [m4_labelAngle_zero, m4_labelAngle_one, zero_add]
  by_cases hA : Parallel (rotateVector o (T.greenC 0).direction (Real.pi / 3)) (T.blueB 0).direction
  · have ha := m7c_par_A00_plus T hA
    by_cases hB : Parallel (rotateVector o (T.redB 0).direction (-(Real.pi / 3)))
        (T.greenA 1).direction
    · have hg := m7c_par_B01_minus T hB
      have hsum := T.angle_sum
      linarith [m3_beta_pos T]
    · exact m7c_familyB T 0 1 h (m7c_ni_B_plus T 0 1 h01) hB
        ⟨he, m7c_base_tricolor_equilateral_of_ne_one T ⟨0, 1, 1⟩ (by decide),
          m7c_base_tricolor_equilateral_of_ne_one T ⟨0, 2, 1⟩ (by decide)⟩
  · exact m7c_familyA T 0 0 h hA (m7c_ni_A_minus_00 T)
      ⟨m7c_base_tricolor_equilateral_of_ne_one T ⟨0, 0, 0⟩ (by decide), he,
        m7c_base_tricolor_equilateral_of_ne_one T ⟨0, 0, 2⟩ (by decide)⟩


/-! ### Injectivity is inherited by the cyclically relabelled triangle -/

def m7cColorShift (c : TrisectorColor) : TrisectorColor :=
  match c with
  | .red => .green
  | .green => .blue
  | .blue => .red

theorem m7c_shift_inj : Injective (fun q : ConstellationIndex =>
    (⟨m7cColorShift q.color, q.first, q.second⟩ : ConstellationIndex)) := by
  intro a b hab
  revert a b
  decide

theorem m7c_injective_cyclic (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Injective (T.m7_cyclic).constellationPoint := by
  have heq : (T.m7_cyclic).constellationPoint = fun q : ConstellationIndex =>
      T.constellationPoint ⟨m7cColorShift q.color, q.first, q.second⟩ := by
    funext q
    rcases q with ⟨c, a, b⟩
    rcases c with _ | _ | _ <;> rfl
  rw [heq]
  exact h.comp m7c_shift_inj

theorem m7c_not_equil_100 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    ¬ Equilateral (T.tricolorTriangle ⟨1, 0, 0⟩).first (T.tricolorTriangle ⟨1, 0, 0⟩).second
      (T.tricolorTriangle ⟨1, 0, 0⟩).third := by
  intro he
  have h2 : Equilateral ((T.m7_cyclic).tricolorTriangle ⟨0, 0, 1⟩).first
      ((T.m7_cyclic).tricolorTriangle ⟨0, 0, 1⟩).second
      ((T.m7_cyclic).tricolorTriangle ⟨0, 0, 1⟩).third :=
    (m6_tricolor_cyclic T 0 0 1).mpr he
  exact m7c_not_equil_001 (T.m7_cyclic) (m7c_injective_cyclic T h) h2

theorem m7c_not_equil_010 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    ¬ Equilateral (T.tricolorTriangle ⟨0, 1, 0⟩).first (T.tricolorTriangle ⟨0, 1, 0⟩).second
      (T.tricolorTriangle ⟨0, 1, 0⟩).third := by
  intro he
  have h2 : Equilateral ((T.m7_cyclic).tricolorTriangle ⟨1, 0, 0⟩).first
      ((T.m7_cyclic).tricolorTriangle ⟨1, 0, 0⟩).second
      ((T.m7_cyclic).tricolorTriangle ⟨1, 0, 0⟩).third :=
    (m6_tricolor_cyclic T 1 0 0).mpr he
  exact m7c_not_equil_100 (T.m7_cyclic) (m7c_injective_cyclic T h) h2

theorem m7c_not_equil_202 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    ¬ Equilateral (T.tricolorTriangle ⟨2, 0, 2⟩).first (T.tricolorTriangle ⟨2, 0, 2⟩).second
      (T.tricolorTriangle ⟨2, 0, 2⟩).third := by
  intro he
  have h2 : Equilateral ((T.m7_cyclic).tricolorTriangle ⟨0, 2, 2⟩).first
      ((T.m7_cyclic).tricolorTriangle ⟨0, 2, 2⟩).second
      ((T.m7_cyclic).tricolorTriangle ⟨0, 2, 2⟩).third :=
    (m6_tricolor_cyclic T 0 2 2).mpr he
  exact m7c_not_equil_022 (T.m7_cyclic) (m7c_injective_cyclic T h) h2

theorem m7c_not_equil_220 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    ¬ Equilateral (T.tricolorTriangle ⟨2, 2, 0⟩).first (T.tricolorTriangle ⟨2, 2, 0⟩).second
      (T.tricolorTriangle ⟨2, 2, 0⟩).third := by
  intro he
  have h2 : Equilateral ((T.m7_cyclic).tricolorTriangle ⟨2, 0, 2⟩).first
      ((T.m7_cyclic).tricolorTriangle ⟨2, 0, 2⟩).second
      ((T.m7_cyclic).tricolorTriangle ⟨2, 0, 2⟩).third :=
    (m6_tricolor_cyclic T 2 0 2).mpr he
  exact m7c_not_equil_202 (T.m7_cyclic) (m7c_injective_cyclic T h) h2

theorem m7c_not_equil_211 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    ¬ Equilateral (T.tricolorTriangle ⟨2, 1, 1⟩).first (T.tricolorTriangle ⟨2, 1, 1⟩).second
      (T.tricolorTriangle ⟨2, 1, 1⟩).third := by
  intro he
  have h2 : Equilateral ((T.m7_cyclic).tricolorTriangle ⟨1, 1, 2⟩).first
      ((T.m7_cyclic).tricolorTriangle ⟨1, 1, 2⟩).second
      ((T.m7_cyclic).tricolorTriangle ⟨1, 1, 2⟩).third :=
    (m6_tricolor_cyclic T 1 1 2).mpr he
  exact m7c_not_equil_112 (T.m7_cyclic) (m7c_injective_cyclic T h) h2

theorem m7c_not_equil_121 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    ¬ Equilateral (T.tricolorTriangle ⟨1, 2, 1⟩).first (T.tricolorTriangle ⟨1, 2, 1⟩).second
      (T.tricolorTriangle ⟨1, 2, 1⟩).third := by
  intro he
  have h2 : Equilateral ((T.m7_cyclic).tricolorTriangle ⟨2, 1, 1⟩).first
      ((T.m7_cyclic).tricolorTriangle ⟨2, 1, 1⟩).second
      ((T.m7_cyclic).tricolorTriangle ⟨2, 1, 1⟩).third :=
    (m6_tricolor_cyclic T 2 1 1).mpr he
  exact m7c_not_equil_211 (T.m7_cyclic) (m7c_injective_cyclic T h) h2


/-! ### All nine sum-one labels are not equilateral -/

theorem m7c_sum_one_cases (q : TricolorIndex) (hq : q.i + q.j + q.k = 1) :
    (q.i = 0 ∧ q.j = 0 ∧ q.k = 1) ∨ (q.i = 1 ∧ q.j = 0 ∧ q.k = 0) ∨
    (q.i = 0 ∧ q.j = 1 ∧ q.k = 0) ∨ (q.i = 0 ∧ q.j = 2 ∧ q.k = 2) ∨
    (q.i = 2 ∧ q.j = 0 ∧ q.k = 2) ∨ (q.i = 2 ∧ q.j = 2 ∧ q.k = 0) ∨
    (q.i = 1 ∧ q.j = 1 ∧ q.k = 2) ∨ (q.i = 2 ∧ q.j = 1 ∧ q.k = 1) ∨
    (q.i = 1 ∧ q.j = 2 ∧ q.k = 1) := by
  revert hq
  revert q
  decide

theorem m7c_not_equilateral_of_sum_one (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (q : TricolorIndex)
    (hq : q.i + q.j + q.k = 1) :
    ¬ Equilateral (T.tricolorTriangle q).first (T.tricolorTriangle q).second
      (T.tricolorTriangle q).third := by
  obtain ⟨qi, qj, qk⟩ := q
  rcases m7c_sum_one_cases ⟨qi, qj, qk⟩ hq with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  · exact m7c_not_equil_001 T h
  · exact m7c_not_equil_100 T h
  · exact m7c_not_equil_010 T h
  · exact m7c_not_equil_022 T h
  · exact m7c_not_equil_202 T h
  · exact m7c_not_equil_220 T h
  · exact m7c_not_equil_112 T h
  · exact m7c_not_equil_211 T h
  · exact m7c_not_equil_121 T h

/-- **`tricolor_equilateral_iff`**, complete. -/
theorem m7c_tricolor_equilateral_iff (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (q : TricolorIndex) :
    Equilateral (T.tricolorTriangle q).first (T.tricolorTriangle q).second
      (T.tricolorTriangle q).third ↔ q.i + q.j + q.k ≠ 1 := by
  constructor
  · intro he hq
    exact m7c_not_equilateral_of_sum_one T h q hq he
  · exact m7c_base_tricolor_equilateral_of_ne_one T q

/-- All 18 tricolor equilateral triangles; the exceptional nine have
`i+j+k=1` in `ZMod 3`. -/
theorem _root_.XamboMorley.OrientedTriangle.tricolor_equilateral_iff
    (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (q : TricolorIndex) :
    Equilateral (T.tricolorTriangle q).first (T.tricolorTriangle q).second
      (T.tricolorTriangle q).third ↔ q.i + q.j + q.k ≠ 1 := by
  exact m7c_tricolor_equilateral_iff T h q


theorem tricolor_not_equilateral_iff (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (q : TricolorIndex) :
    ¬Equilateral (T.tricolorTriangle q).first (T.tricolorTriangle q).second
      (T.tricolorTriangle q).third ↔ q.i + q.j + q.k = 1 := by
  rw [← not_iff_not]
  push_neg
  exact T.tricolor_equilateral_iff h q



/-- `gallery_equilateral_card`, derived from `tricolor_equilateral_iff` and
`monochrome_equilateral` (both outside this direction's assignment). -/
theorem gallery_equilateral_card_proof (T : OrientedTriangle E o)
    (hPoints : Injective T.constellationPoint) (h : Injective T.galleryTriangle) :
    {t ∈ Set.range T.galleryTriangle | Equilateral t.first t.second t.third}.ncard = 27 :=
  T.gallery_equilateral_card_of_criteria h
    (fun q => T.tricolor_equilateral_iff hPoints q)
    (fun c s => T.monochrome_equilateral hPoints c s)
theorem gallery_equilateral_card (T : OrientedTriangle E o)
    (hPoints : Injective T.constellationPoint) (h : Injective T.galleryTriangle) :
    {t ∈ Set.range T.galleryTriangle | Equilateral t.first t.second t.third}.ncard = 27 := by
  exact gallery_equilateral_card_proof T hPoints h





noncomputable section
open scoped Real RealInnerProductSpace ComplexConjugate Matrix
open Function Set


/-- The key scalar identity behind the tricolor equilateral theorem, stated with the
three affine coefficients `lam, mu, nu` as abstract numbers satisfying the multiplicative
relations that define them. -/
lemma m3c7_affine_key (eu ev ew ζ P Q B1 B2 B3 K T lam mu nu : ℂ)
    (hB1 : B1 = 1 - ev * ew) (hB2 : B2 = 1 - ew * eu) (hB3 : B3 = 1 - eu * ev)
    (hK : K = eu ^ 3 * (ev ^ 3 - 1)) (hTdef : T = eu * ev * ew)
    (hlam : lam * B1 = 1 - ev) (hmu : mu * B2 = 1 - ew) (hnu : nu * B3 = 1 - eu)
    (h1 : B1 ≠ 0) (h2 : B2 ≠ 0) (h3 : B3 ≠ 0) (hK' : K ≠ 0)
    (hp : P * K = (eu ^ 3 - 1) * Q)
    (hT : 1 + T + T ^ 2 = 0) (hζ : ζ = -T) :
    (mu - 1) * Q - lam * P = ζ * ((1 - lam - nu) * P - nu * Q) := by
  obtain rfl : K = eu ^ 3 * (ev ^ 3 - 1) := hK
  obtain rfl : T = eu * ev * ew := hTdef
  obtain rfl : ζ = -(eu * ev * ew) := hζ
  have hPi : B1 * B2 * B3 ≠ 0 := mul_ne_zero (mul_ne_zero h1 h2) h3
  have e1 : B1 * B2 * B3 * mu = (1 - ew) * B1 * B3 := by
    rw [show B1 * B2 * B3 * mu = (mu * B2) * (B1 * B3) from by ring, hmu]
    ring
  have e2 : B1 * B2 * B3 * lam = (1 - ev) * B2 * B3 := by
    rw [show B1 * B2 * B3 * lam = (lam * B1) * (B2 * B3) from by ring, hlam]
    ring
  have e3 : B1 * B2 * B3 * nu = (1 - eu) * B1 * B2 := by
    rw [show B1 * B2 * B3 * nu = (nu * B3) * (B1 * B2) from by ring, hnu]
    ring
  have hexpand : B1 * B2 * B3 * ((mu - 1) * Q - lam * P + (eu * ev * ew) * ((1 - lam - nu) * P - nu * Q))
      = ((B1 * B2 * B3 * mu - B1 * B2 * B3) * Q - (B1 * B2 * B3 * lam) * P)
        + (eu * ev * ew) * (((B1 * B2 * B3 - B1 * B2 * B3 * lam - B1 * B2 * B3 * nu) * P)
            - (B1 * B2 * B3 * nu) * Q) := by
    ring
  have hcert : (eu ^ 3 * (ev ^ 3 - 1)) * ((1 - ew) * B1 * B3 - B1 * B2 * B3 + (-(eu * ev * ew)) * (1 - eu) * B1 * B2)
      - (eu ^ 3 - 1) * ((1 - ev) * B2 * B3
          + (-(eu * ev * ew)) * (B1 * B2 * B3 - (1 - ev) * B2 * B3 - (1 - eu) * B1 * B2))
      = (1 + (eu * ev * ew) + (eu * ev * ew) ^ 2) *
        (eu ^ 4 * ev ^ 3 * ew - eu ^ 4 * ev ^ 2 - eu ^ 4 * ev * ew + eu ^ 4 * ev
          - eu ^ 3 * ev ^ 3 * ew + eu ^ 3 * ev + eu ^ 3 * ew - eu ^ 3 + eu * ev ^ 2
          + eu * ev * ew - eu * ev - eu * ew - ev + 1) := by
    rw [hB1, hB2, hB3]
    ring
  have hp' : (eu ^ 3 * (ev ^ 3 - 1)) * P = (eu ^ 3 - 1) * Q := by
    rw [mul_comm]
    exact hp
  have hXform : (eu ^ 3 * (ev ^ 3 - 1)) *
      (((1 - ew) * B1 * B3 - B1 * B2 * B3) * Q - (1 - ev) * B2 * B3 * P
        + (eu * ev * ew) * ((B1 * B2 * B3 - (1 - ev) * B2 * B3 - (1 - eu) * B1 * B2) * P
            - (1 - eu) * B1 * B2 * Q))
      = ((1 - ew) * B1 * B3 - B1 * B2 * B3 + (-(eu * ev * ew)) * (1 - eu) * B1 * B2)
          * ((eu ^ 3 * (ev ^ 3 - 1)) * Q)
        - ((1 - ev) * B2 * B3 + (-(eu * ev * ew)) * (B1 * B2 * B3 - (1 - ev) * B2 * B3
            - (1 - eu) * B1 * B2)) * ((eu ^ 3 * (ev ^ 3 - 1)) * P) := by
    ring
  have hcleared : B1 * B2 * B3 *
      ((mu - 1) * Q - lam * P + (eu * ev * ew) * ((1 - lam - nu) * P - nu * Q)) = 0 := by
    rw [hexpand, e1, e2, e3]
    have hmain : (eu ^ 3 * (ev ^ 3 - 1)) *
        (((1 - ew) * B1 * B3 - B1 * B2 * B3) * Q - (1 - ev) * B2 * B3 * P
          + (eu * ev * ew) * ((B1 * B2 * B3 - (1 - ev) * B2 * B3 - (1 - eu) * B1 * B2) * P
              - (1 - eu) * B1 * B2 * Q)) = 0 := by
      rw [hXform, hp']
      rw [show
        ((1 - ew) * B1 * B3 - B1 * B2 * B3 + (-(eu * ev * ew)) * (1 - eu) * B1 * B2)
            * ((eu ^ 3 * (ev ^ 3 - 1)) * Q)
          - ((1 - ev) * B2 * B3 + (-(eu * ev * ew)) * (B1 * B2 * B3 - (1 - ev) * B2 * B3
              - (1 - eu) * B1 * B2)) * ((eu ^ 3 - 1) * Q)
        = ((eu ^ 3 * (ev ^ 3 - 1)) *
              ((1 - ew) * B1 * B3 - B1 * B2 * B3 + (-(eu * ev * ew)) * (1 - eu) * B1 * B2)
            - (eu ^ 3 - 1) * ((1 - ev) * B2 * B3 + (-(eu * ev * ew)) * (B1 * B2 * B3
                - (1 - ev) * B2 * B3 - (1 - eu) * B1 * B2))) * Q from by ring]
      rw [hcert, hT]
      ring
    exact (mul_eq_zero.mp hmain).resolve_left hK'
  have hcube : (mu - 1) * Q - lam * P + (eu * ev * ew) * ((1 - lam - nu) * P - nu * Q) = 0 :=
    (mul_eq_zero.mp hcleared).resolve_left hPi
  linear_combination hcube


/-! ### Geometric support for the tricolor theorem -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable {o : Orientation ℝ E (Fin 2)}


theorem m3c7_exp_ne_zero (θ : ℝ) : (Circle.exp θ : ℂ) ≠ 0 := by
  intro h
  have h1 : ‖(Circle.exp θ : ℂ)‖ = 1 := Circle.norm_coe _
  rw [h, norm_zero] at h1
  norm_num at h1

theorem m3c7_one_sub_exp_ne (θ : ℝ) (h : Real.sin (θ / 2) ≠ 0) :
    (1 - (Circle.exp θ : ℂ)) ≠ 0 := by
  rw [one_sub_unit_eq]
  refine mul_ne_zero ?_ (m3c7_exp_ne_zero _)
  intro h0
  apply h
  have h4 : (2 * Real.sin (θ / 2) : ℝ) = 0 := by exact_mod_cast h0
  linarith

theorem m3c7_one_sub_exp_mul_ne {φ ψ : ℝ} (h : Real.sin ((φ + ψ) / 2) ≠ 0) :
    (1 - (Circle.exp φ : ℂ) * Circle.exp ψ) ≠ 0 := by
  rw [← Circle.coe_mul, ← Circle.exp_add]
  exact m3c7_one_sub_exp_ne (φ + ψ) h

theorem m3c7_red_form (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, i, j⟩) =
      toComplex o T.C + toComplex o (T.B - T.C) *
        ((1 - (Circle.exp (2 * T.beta - labelAngle i) : ℂ)) /
          (1 - (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) *
            (Circle.exp (2 * T.beta - labelAngle i) : ℂ))) := by
  simp only [constellationPoint, toComplex_rotationFixedPoint]

theorem m3c7_green_form (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.green, i, j⟩) =
      toComplex o T.A + toComplex o (T.C - T.A) *
        ((1 - (Circle.exp (2 * T.gamma - labelAngle i) : ℂ)) /
          (1 - (Circle.exp (2 * T.alpha - labelAngle j) : ℂ) *
            (Circle.exp (2 * T.gamma - labelAngle i) : ℂ))) := by
  simp only [constellationPoint, toComplex_rotationFixedPoint]

theorem m3c7_blue_form (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.blue, i, j⟩) =
      toComplex o T.B + toComplex o (T.A - T.B) *
        ((1 - (Circle.exp (2 * T.alpha - labelAngle i) : ℂ)) /
          (1 - (Circle.exp (2 * T.beta - labelAngle j) : ℂ) *
            (Circle.exp (2 * T.alpha - labelAngle i) : ℂ))) := by
  simp only [constellationPoint, toComplex_rotationFixedPoint]




theorem m3c7_exp_three_label (t : TrisectorLabel) :
    (Circle.exp (3 * labelAngle t) : ℂ) = 1 := by
  have h3 : (3 : ℝ) * labelAngle t = ((3 : ℕ) : ℝ) * labelAngle t := by norm_num
  rw [h3, Circle.exp_natCast_mul, Circle.coe_pow, labelAngle_exp, ← pow_mul,
    show t.val * 3 = 3 * t.val from by ring, pow_mul, omega_cubed, one_pow]

theorem m3c7_shift_cube (a : ℝ) (t : TrisectorLabel) :
    (Circle.exp (2 * a - labelAngle t) : ℂ) ^ 3 = (Circle.exp (6 * a) : ℂ) := by
  rw [← Circle.coe_pow, ← Circle.exp_natCast_mul]
  rw [show ((3 : ℕ) : ℝ) * (2 * a - labelAngle t) = 6 * a - 3 * labelAngle t by
    push_cast; ring]
  rw [Circle.exp_sub, Circle.coe_div, m3c7_exp_three_label, div_one]

theorem m3c7_sin_three_beta_ne (T : OrientedTriangle E o) : Real.sin (3 * T.beta) ≠ 0 :=
  ne_of_gt (m3_sin_three_beta_pos T)

theorem m3c7_sin_three_alpha_ne (T : OrientedTriangle E o) : Real.sin (3 * T.alpha) ≠ 0 :=
  ne_of_gt (m3_sin_three_alpha_pos T)

theorem m3c7_five_ne (T : OrientedTriangle E o) :
    (Circle.exp (6 * T.beta) : ℂ) - 1 ≠ 0 := by
  have h : (1 - (Circle.exp (6 * T.beta) : ℂ)) ≠ 0 := by
    refine m3c7_one_sub_exp_ne (6 * T.beta) ?_
    rw [show 6 * T.beta / 2 = 3 * T.beta by ring]
    exact m3c7_sin_three_beta_ne T
  intro h0
  rw [sub_eq_zero] at h0
  exact h (by rw [h0, sub_self])

theorem m3c7_six_alpha_sub_one_ne (T : OrientedTriangle E o) :
    (Circle.exp (6 * T.alpha) : ℂ) - 1 ≠ 0 := by
  have h : (1 - (Circle.exp (6 * T.alpha) : ℂ)) ≠ 0 := by
    refine m3c7_one_sub_exp_ne (6 * T.alpha) ?_
    rw [show 6 * T.alpha / 2 = 3 * T.alpha by ring]
    exact m3c7_sin_three_alpha_ne T
  intro h0
  rw [sub_eq_zero] at h0
  exact h (by rw [h0, sub_self])

theorem m3c7_exp_pi_div_two : (Circle.exp (Real.pi / 2) : ℂ) = Complex.I := by
  have h1 : (Circle.exp (-(Real.pi / 2)) : ℂ) = -Complex.I := m6_exp_neg_pi_div_two
  have hmul : ((Circle.exp (-(Real.pi / 2)) : ℂ)) * (Circle.exp (Real.pi / 2) : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← Circle.exp_add, show -(Real.pi / 2) + Real.pi / 2 = 0 by ring]
    simp
  rw [h1] at hmul
  have hne : (-Complex.I : ℂ) ≠ 0 := by
    intro h
    have h2 : (-Complex.I : ℂ) * Complex.I = 0 := by rw [h, zero_mul]
    rw [neg_mul, Complex.I_mul_I] at h2
    norm_num at h2
  refine mul_left_cancel₀ hne ?_
  rw [hmul, neg_mul, Complex.I_mul_I]
  norm_num

theorem m3c7_six_alpha (T : OrientedTriangle E o) :
    (Circle.exp (6 * T.alpha) : ℂ) - 1 =
      2 * Complex.I * ((Real.sin (3 * T.alpha) : ℂ) * (Circle.exp (3 * T.alpha) : ℂ)) := by
  have h := one_sub_unit_eq (6 * T.alpha)
  rw [show 6 * T.alpha / 2 = 3 * T.alpha by ring] at h
  have h2 : (Circle.exp (3 * T.alpha - Real.pi / 2) : ℂ) =
      (Circle.exp (3 * T.alpha) : ℂ) * (-Complex.I) := by
    rw [show 3 * T.alpha - Real.pi / 2 = 3 * T.alpha + -(Real.pi / 2) by ring,
      Circle.exp_add, Circle.coe_mul, m6_exp_neg_pi_div_two]
  rw [h2] at h
  linear_combination -h

theorem m3c7_six_beta (T : OrientedTriangle E o) :
    (Circle.exp (6 * T.beta) : ℂ) - 1 =
      2 * Complex.I * ((Real.sin (3 * T.beta) : ℂ) * (Circle.exp (3 * T.beta) : ℂ)) := by
  have h := one_sub_unit_eq (6 * T.beta)
  rw [show 6 * T.beta / 2 = 3 * T.beta by ring] at h
  have h2 : (Circle.exp (3 * T.beta - Real.pi / 2) : ℂ) =
      (Circle.exp (3 * T.beta) : ℂ) * (-Complex.I) := by
    rw [show 3 * T.beta - Real.pi / 2 = 3 * T.beta + -(Real.pi / 2) by ring,
      Circle.exp_add, Circle.coe_mul, m6_exp_neg_pi_div_two]
  rw [h2] at h
  linear_combination -h

theorem m3c7_exp_pi : (Circle.exp Real.pi : ℂ) = -1 := by
  rw [show Real.pi = Real.pi / 2 + Real.pi / 2 by ring, Circle.exp_add, Circle.coe_mul,
    m3c7_exp_pi_div_two, Complex.I_mul_I]

theorem m3c7_three_gamma (T : OrientedTriangle E o) :
    (Circle.exp (3 * T.gamma) : ℂ) =
      -((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ)) := by
  have hsum := T.angle_sum
  have harg : 3 * T.gamma = -(3 * (T.alpha + T.beta)) + Real.pi := by linarith
  rw [harg, Circle.exp_add, Circle.coe_mul]
  rw [m3c7_exp_pi]
  ring

theorem m3c7_rho (T : OrientedTriangle E o) :
    ‖T.B - T.C‖ / ‖T.A - T.C‖ = Real.sin (3 * T.alpha) / Real.sin (3 * T.beta) := by
  have ha : ‖T.B - T.C‖ = T.aLength := by
    rw [aLength, show T.a = T.C - T.B from rfl, norm_sub_rev]
  have hb : ‖T.A - T.C‖ = T.bLength := by
    rw [bLength, show T.b = T.A - T.C from rfl]
  rw [ha, hb, T.side_lengths_sine.1, T.side_lengths_sine.2.1]
  have h1 : T.delta ≠ 0 := ne_of_gt (m7_delta_pos T)
  field_simp

theorem m3c7_p_rel (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    toComplex o (T.B - T.C) *
        ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) ^ 3 *
          ((Circle.exp (2 * T.beta - labelAngle i) : ℂ) ^ 3 - 1))
      = ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) ^ 3 - 1) *
          toComplex o (T.C - T.A) := by
  have hP : toComplex o (T.B - T.C) =
      -(((‖T.B - T.C‖ / ‖T.A - T.C‖ : ℝ) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ)) *
        toComplex o (T.C - T.A) := by
    have h := congrArg (toComplex o) T.m6_trisector_C
    rw [h, toComplex_smul, toComplex_rotateVector]
    rw [show T.A - T.C = -(T.C - T.A) from by abel, toComplex_neg]
    ring
  have hXYZ : ((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ) * (Circle.exp (6 * T.alpha) : ℂ)) *
      (Circle.exp (3 * T.beta) : ℂ) = (Circle.exp (3 * T.alpha) : ℂ) := by
    rw [Circle.coe_exp, Circle.coe_exp, Circle.coe_exp, Circle.coe_exp,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hK : -(((‖T.B - T.C‖ / ‖T.A - T.C‖ : ℝ) : ℂ) * (Circle.exp (3 * T.gamma) : ℂ)) *
        ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) ^ 3 *
          ((Circle.exp (2 * T.beta - labelAngle i) : ℂ) ^ 3 - 1))
      = ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) ^ 3 - 1) := by
    rw [m3c7_shift_cube T.alpha k, m3c7_shift_cube T.beta i, m3c7_six_alpha T, m3c7_six_beta T,
      m3c7_three_gamma T, m3c7_rho T]
    have hs : (Real.sin (3 * T.beta) : ℂ) ≠ 0 := by
      exact_mod_cast m3c7_sin_three_beta_ne T
    have hcancel : ((Real.sin (3 * T.alpha) / Real.sin (3 * T.beta) : ℝ) : ℂ) *
        (Real.sin (3 * T.beta) : ℂ) = (Real.sin (3 * T.alpha) : ℂ) := by
      rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (m3c7_sin_three_beta_ne T)]
    have h1 : (-((((Real.sin (3 * T.alpha) / Real.sin (3 * T.beta) : ℝ) : ℂ) *
          (-((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ)))))) *
        ((Circle.exp (6 * T.alpha) : ℂ) *
          (2 * Complex.I * ((Real.sin (3 * T.beta) : ℂ) * (Circle.exp (3 * T.beta) : ℂ))))
        = 2 * Complex.I * ((Real.sin (3 * T.alpha) : ℂ) *
            (((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ) * (Circle.exp (6 * T.alpha) : ℂ)) *
              (Circle.exp (3 * T.beta) : ℂ))) := by
      linear_combination (2 * Complex.I *
        (((Circle.exp (-(3 * (T.alpha + T.beta))) : ℂ) * (Circle.exp (6 * T.alpha) : ℂ)) *
          (Circle.exp (3 * T.beta) : ℂ))) * hcancel
    rw [h1, hXYZ]
  rw [hP]
  linear_combination (toComplex o (T.C - T.A)) * hK

theorem m3c7_sin_ne (i j k : TrisectorLabel) (hq : i + j + k ≠ 1) :
    Real.sin ((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * Real.pi / 3) ≠ 0 := by
  intro hsin
  rw [Real.sin_eq_zero_iff] at hsin
  obtain ⟨m, hm⟩ := hsin
  have hreal : ((1 : ℝ) - ((i.val + j.val + k.val : ℕ) : ℝ)) = 3 * (m : ℝ) := by
    have h4 : (m : ℝ) * 3 = 1 - ((i.val + j.val + k.val : ℕ) : ℝ) := by
      nlinarith [hm, Real.pi_pos]
    linarith
  have hint : ((1 : ℤ) - ((i.val + j.val + k.val : ℕ) : ℤ)) = 3 * m := by
    exact_mod_cast hreal
  have hN : ((i.val + j.val + k.val : ℕ) : ZMod 3) = 1 := by
    have h6 : (((i.val + j.val + k.val : ℕ) : ℤ)) = 1 - 3 * m := by linarith
    rw [← Int.cast_natCast, h6]
    push_cast
    have h3z : ((3 : ZMod 3)) = 0 := by decide
    rw [h3z]
    ring
  rw [show ((i.val + j.val + k.val : ℕ) : ZMod 3) = i + j + k from by
    push_cast
    rw [ZMod.natCast_zmod_val i, ZMod.natCast_zmod_val j, ZMod.natCast_zmod_val k]] at hN
  exact hq hN

theorem m3c7_T_cube (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
      (Circle.exp (2 * T.gamma - labelAngle j) : ℂ)) ^ 3 = 1 := by
  rw [mul_pow, mul_pow, m3c7_shift_cube T.alpha k, m3c7_shift_cube T.beta i,
    m3c7_shift_cube T.gamma j]
  rw [← Circle.coe_mul, ← Circle.coe_mul, ← Circle.exp_add, ← Circle.exp_add]
  rw [show 6 * T.alpha + 6 * T.beta + 6 * T.gamma = 2 * Real.pi by
    rw [← T.angle_sum]; ring]
  rw [show (2 * Real.pi : ℝ) = Real.pi + Real.pi by ring, Circle.exp_add, Circle.coe_mul,
    m3c7_exp_pi]
  norm_num

theorem m3c7_T_form (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
      (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) =
      (Circle.exp ((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3)) : ℂ) := by
  rw [← Circle.coe_mul, ← Circle.coe_mul, ← Circle.exp_add, ← Circle.exp_add]
  congr 1
  congr 1
  push_cast [labelAngle]
  linear_combination (2 / 3) * T.angle_sum

theorem m3c7_T_ne_one (T : OrientedTriangle E o) (i j k : TrisectorLabel)
    (hq : i + j + k ≠ 1) :
    (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
      (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) ≠ 1 := by
  rw [m3c7_T_form T i j k]
  intro h1
  have h0 : (1 - (Circle.exp ((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3)) : ℂ)) = 0 := by
    rw [h1]; ring
  rw [one_sub_unit_eq] at h0
  have hsin : Real.sin (((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3)) / 2) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · have h2 : (2 * Real.sin (((1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3)) / 2) : ℝ) = 0 := by
        exact_mod_cast h
      linarith
    · exact absurd h (m3c7_exp_ne_zero _)
  exact m3c7_sin_ne i j k hq (by
    rwa [show (1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * (2 * Real.pi / 3) / 2
      = (1 - ((i.val + j.val + k.val : ℕ) : ℝ)) * Real.pi / 3 by ring] at hsin)

theorem m3c7_T_quad (T : OrientedTriangle E o) (i j k : TrisectorLabel)
    (hq : i + j + k ≠ 1) :
    1 + (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
        (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) +
      ((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) * (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
        (Circle.exp (2 * T.gamma - labelAngle j) : ℂ)) ^ 2 = 0 := by
  set Tt : ℂ := (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) *
    (Circle.exp (2 * T.beta - labelAngle i) : ℂ) * (Circle.exp (2 * T.gamma - labelAngle j) : ℂ)
    with hTt
  have h3 : Tt ^ 3 = 1 := m3c7_T_cube T i j k
  have hne : Tt ≠ 1 := m3c7_T_ne_one T i j k hq
  have hfac : (Tt - 1) * (Tt ^ 2 + Tt + 1) = 0 := by
    linear_combination h3
  have h2 : Tt ^ 2 + Tt + 1 = 0 := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
  linear_combination h2

theorem m3c7_cmv_norm {z : ℂ} {v : E} :
    ‖complexMulVector o z v‖ = ‖z‖ * ‖v‖ := by
  rw [← toComplex_norm (o := o) (complexMulVector o z v), w9_toComplex_complexMulVector,
    norm_mul, toComplex_norm, mul_comm]

theorem m3c7_circle_norm (θ : ℝ) : ‖(Circle.exp θ : ℂ)‖ = 1 := Circle.norm_coe _

theorem m3c7_rot_C (T : OrientedTriangle E o) (i j k : TrisectorLabel)
    (hq : i + j + k ≠ 1) :
    toComplex o (T.constellationPoint ⟨.green, j, k⟩) -
        toComplex o (T.constellationPoint ⟨.red, i, j⟩)
      = (-((Circle.exp (2 * T.alpha - labelAngle k) : ℂ) *
          (Circle.exp (2 * T.beta - labelAngle i) : ℂ) *
          (Circle.exp (2 * T.gamma - labelAngle j) : ℂ))) *
        (toComplex o (T.constellationPoint ⟨.blue, k, i⟩) -
          toComplex o (T.constellationPoint ⟨.red, i, j⟩)) := by
  rw [m3c7_red_form T i j, m3c7_green_form T j k, m3c7_blue_form T k i]
  set Eu : ℂ := (Circle.exp (2 * T.alpha - labelAngle k) : ℂ) with hEu
  set Ev : ℂ := (Circle.exp (2 * T.beta - labelAngle i) : ℂ) with hEv
  set Ew : ℂ := (Circle.exp (2 * T.gamma - labelAngle j) : ℂ) with hEw
  set B1 : ℂ := 1 - Ew * Ev with hB1
  set B2 : ℂ := 1 - Eu * Ew with hB2
  set B3 : ℂ := 1 - Ev * Eu with hB3
  have hn1 : B1 ≠ 0 := by
    rw [hB1, hEw, hEv]
    refine m3c7_one_sub_exp_mul_ne (φ := 2 * T.gamma - labelAngle j)
      (ψ := 2 * T.beta - labelAngle i) ?_
    obtain ⟨hb0, hb1⟩ := m6_beta_add_gamma_bounds_lt (o := o) T
    convert m6_sin_shift_sub_ne_zero hb0 hb1 i j using 2
    ring
  have hn2 : B2 ≠ 0 := by
    rw [hB2, hEu, hEw]
    refine m3c7_one_sub_exp_mul_ne (φ := 2 * T.alpha - labelAngle k)
      (ψ := 2 * T.gamma - labelAngle j) ?_
    obtain ⟨hb0, hb1⟩ := m6_gamma_add_alpha_bounds_lt (o := o) T
    convert m6_sin_shift_sub_ne_zero hb0 hb1 k j using 2
    ring
  have hn3 : B3 ≠ 0 := by
    rw [hB3, hEv, hEu]
    refine m3c7_one_sub_exp_mul_ne (φ := 2 * T.beta - labelAngle i)
      (ψ := 2 * T.alpha - labelAngle k) ?_
    obtain ⟨hb0, hb1⟩ := m6_alpha_add_beta_bounds_lt (o := o) T
    convert m6_sin_shift_sub_ne_zero hb0 hb1 i k using 2
    ring
  have hKnz : Eu ^ 3 * (Ev ^ 3 - 1) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero 3 ?_) ?_
    · rw [hEu]; exact m3c7_exp_ne_zero _
    · rw [hEv, m3c7_shift_cube (a := T.beta) (t := i)]
      exact m3c7_five_ne T
  have hp'' : toComplex o (T.B - T.C) * (Eu ^ 3 * (Ev ^ 3 - 1))
      = (Eu ^ 3 - 1) * toComplex o (T.C - T.A) := by
    have h := m3c7_p_rel T i j k
    rw [← hEu, ← hEv] at h
    exact h
  have hT'' : 1 + Eu * Ev * Ew + (Eu * Ev * Ew) ^ 2 = 0 := by
    have h := m3c7_T_quad T i j k hq
    rw [← hEu, ← hEv, ← hEw] at h
    exact h
  have hkey := m3c7_affine_key Eu Ev Ew (-(Eu * Ev * Ew))
    (toComplex o (T.B - T.C)) (toComplex o (T.C - T.A)) B1 B2 B3
    (Eu ^ 3 * (Ev ^ 3 - 1)) (Eu * Ev * Ew)
    ((1 - Ev) / B1) ((1 - Ew) / B2) ((1 - Eu) / B3)
    (by rw [hB1]; ring) (by rw [hB2]; ring) (by rw [hB3]; ring) rfl rfl
    (by field_simp) (by field_simp) (by field_simp)
    hn1 hn2 hn3 hKnz hp'' hT'' rfl
  have e1 : toComplex o T.A - toComplex o T.C + toComplex o (T.C - T.A) = 0 := by
    rw [← toComplex_sub, show T.A - T.C = -(T.C - T.A) from by abel, toComplex_neg]
    ring
  have e2 : toComplex o T.B - toComplex o T.C - toComplex o (T.B - T.C) = 0 := by
    rw [← toComplex_sub]
    ring
  have e3 : toComplex o (T.A - T.B) + toComplex o (T.B - T.C) + toComplex o (T.C - T.A) = 0 := by
    rw [← toComplex_add, ← toComplex_add]
    congr 1
    abel
    simp
  linear_combination hkey + e1 - (-(Eu * Ev * Ew)) * e2 -
    (-(Eu * Ev * Ew)) * ((1 - Eu) / B3) * e3

theorem m3c7_cmv_one (v : E) : complexMulVector o (1 : ℂ) v = v := by
  apply toComplex_injective o
  rw [w9_toComplex_complexMulVector]
  ring

theorem m3c7_tricolor_equilateral_of_ne_one (T : OrientedTriangle E o) (q : TricolorIndex)
    (hq : q.i + q.j + q.k ≠ 1) :
    Equilateral (T.tricolorTriangle q).first (T.tricolorTriangle q).second
      (T.tricolorTriangle q).third := by
  set Eu : ℂ := (Circle.exp (2 * T.alpha - labelAngle q.k) : ℂ) with hEu
  set Ev : ℂ := (Circle.exp (2 * T.beta - labelAngle q.i) : ℂ) with hEv
  set Ew : ℂ := (Circle.exp (2 * T.gamma - labelAngle q.j) : ℂ) with hEw
  have hC := m3c7_rot_C T q.i q.j q.k hq
  rw [← hEu, ← hEv, ← hEw] at hC
  have hE : T.constellationPoint ⟨.green, q.j, q.k⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩
      = complexMulVector o (-(Eu * Ev * Ew))
          (T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩) := by
    apply toComplex_injective o
    rw [toComplex_sub, w9_toComplex_complexMulVector, toComplex_sub, mul_comm]
    exact hC
  have hT'' : 1 + Eu * Ev * Ew + (Eu * Ev * Ew) ^ 2 = 0 := by
    have h := m3c7_T_quad T q.i q.j q.k hq
    rw [← hEu, ← hEv, ← hEw] at h
    exact h
  have hnorm : ‖Eu‖ = 1 := by rw [hEu]; exact m3c7_circle_norm _
  have hnorm' : ‖Ev‖ = 1 := by rw [hEv]; exact m3c7_circle_norm _
  have hnorm'' : ‖Ew‖ = 1 := by rw [hEw]; exact m3c7_circle_norm _
  have hTnorm : ‖Eu * Ev * Ew‖ = 1 := by rw [norm_mul, norm_mul, hnorm, hnorm', hnorm'']; norm_num
  have hζ : ‖(-(Eu * Ev * Ew))‖ = 1 := by rw [norm_neg, hTnorm]
  have hζ1 : ‖(-(Eu * Ev * Ew)) - 1‖ = 1 := by
    have hsq : -(Eu * Ev * Ew) - 1 = (Eu * Ev * Ew) ^ 2 := by
      linear_combination -hT''
    rw [hsq, norm_pow, hTnorm, one_pow]
  have hbg : T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.green, q.j, q.k⟩
      = complexMulVector o (1 - (-(Eu * Ev * Ew)))
          (T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩) := by
    apply toComplex_injective o
    rw [toComplex_sub, w9_toComplex_complexMulVector, toComplex_sub]
    linear_combination -hC
  have h1 : dist (T.tricolorTriangle q).first (T.tricolorTriangle q).second
      = ‖T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩‖ := by
    show dist (T.constellationPoint ⟨.red, q.i, q.j⟩) (T.constellationPoint ⟨.green, q.j, q.k⟩) = _
    rw [dist_eq_norm, norm_sub_rev,
      show T.constellationPoint ⟨.green, q.j, q.k⟩ -
        T.constellationPoint ⟨.red, q.i, q.j⟩ = complexMulVector o (-(Eu * Ev * Ew))
          (T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩) from hE,
      m3c7_cmv_norm, hζ, one_mul]
  have h2 : dist (T.tricolorTriangle q).second (T.tricolorTriangle q).third
      = ‖T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩‖ := by
    show dist (T.constellationPoint ⟨.green, q.j, q.k⟩) (T.constellationPoint ⟨.blue, q.k, q.i⟩) = _
    rw [dist_eq_norm, norm_sub_rev,
      show T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.green, q.j, q.k⟩ =
        complexMulVector o (1 - (-(Eu * Ev * Ew)))
          (T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩) from hbg,
      m3c7_cmv_norm, show ‖1 - (-(Eu * Ev * Ew))‖ = 1 from by rw [norm_sub_rev]; exact hζ1,
      one_mul]
  have h3 : dist (T.tricolorTriangle q).third (T.tricolorTriangle q).first
      = ‖T.constellationPoint ⟨.blue, q.k, q.i⟩ - T.constellationPoint ⟨.red, q.i, q.j⟩‖ := by
    show dist (T.constellationPoint ⟨.blue, q.k, q.i⟩) (T.constellationPoint ⟨.red, q.i, q.j⟩) = _
    rw [dist_eq_norm]
  exact ⟨h1.trans h2.symm, h2.trans h3.symm⟩

/-! ## m3c — reducing `tricolor_sides_parallel` to one side per label -/

theorem m3c_one_add_omega : (1 : ℂ) + (omega : ℂ) = -((omega : ℂ) ^ 2) := by
  linear_combination omega_sum

theorem m3c_one_add_omega_sq : (1 : ℂ) + (omega : ℂ) ^ 2 = -((omega : ℂ)) := by
  linear_combination omega_sum

theorem m3c_omega_pow_four : (omega : ℂ) ^ 4 = (omega : ℂ) := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, omega_cubed, one_mul, pow_one]

/-- Rotation of a side: `r - q = ω (q - p)` for a positively weighted equilateral triple. -/
theorem m3c_complex_ratio1 {p q r : ℂ}
    (h : p + (omega : ℂ) * q + (omega : ℂ) ^ 2 * r = 0) :
    r - q = (omega : ℂ) * (q - p) := by
  have h1 : (omega : ℂ) ^ 2 * r = -(p + (omega : ℂ) * q) := by linear_combination h
  have h2 : r = -((omega : ℂ) * p) - (omega : ℂ) ^ 2 * q := by
    calc r = (omega : ℂ) ^ 3 * r := by rw [omega_cubed, one_mul]
      _ = (omega : ℂ) * ((omega : ℂ) ^ 2 * r) := by ring
      _ = (omega : ℂ) * (-(p + (omega : ℂ) * q)) := by rw [h1]
      _ = -((omega : ℂ) * p) - (omega : ℂ) ^ 2 * q := by ring
  have h3 : (omega : ℂ) ^ 2 + 1 = -(omega : ℂ) := by linear_combination m3c_one_add_omega_sq
  rw [h2]
  linear_combination (-q) * h3

/-- Rotation of a side: `r - q = ω² (q - p)` for a negatively weighted equilateral triple. -/
theorem m3c_complex_ratio2 {p q r : ℂ}
    (h : p + (omega : ℂ) ^ 2 * q + (omega : ℂ) * r = 0) :
    r - q = (omega : ℂ) ^ 2 * (q - p) := by
  have h1 : (omega : ℂ) * r = -(p + (omega : ℂ) ^ 2 * q) := by linear_combination h
  have h2 : r = -((omega : ℂ) ^ 2 * p) - (omega : ℂ) * q := by
    calc r = (omega : ℂ) ^ 3 * r := by rw [omega_cubed, one_mul]
      _ = (omega : ℂ) ^ 2 * ((omega : ℂ) * r) := by ring
      _ = (omega : ℂ) ^ 2 * (-(p + (omega : ℂ) ^ 2 * q)) := by rw [h1]
      _ = -((omega : ℂ) ^ 2 * p) - (omega : ℂ) * q := by
        linear_combination (-((omega : ℂ) * q)) * omega_cubed
  have h3 : (omega : ℂ) + 1 = -((omega : ℂ) ^ 2) := by linear_combination m3c_one_add_omega
  rw [h2]
  linear_combination (-q) * h3

/-- Multiplication of a vector by a complex number. -/
noncomputable def m3cRot (μ : ℂ) (v : E) : E := ofComplex o (μ * toComplex o v)

theorem m3c_toComplex_rot (μ : ℂ) (v : E) :
    toComplex o (m3cRot (o := o) μ v) = μ * toComplex o v := by
  simp [m3cRot]

theorem m3c_rot_smul (μ : ℂ) (r : ℝ) (v : E) :
    m3cRot (o := o) μ (r • v) = r • m3cRot (o := o) μ v := by
  apply toComplex_injective o
  rw [m3c_toComplex_rot, toComplex_smul, toComplex_smul, m3c_toComplex_rot]
  push_cast
  ring

/-- **The `120°` relation between the sides of an equilateral triangle.** -/
theorem m3c_equilateral_sub_ratio (P Q R : E) (h : Equilateral P Q R) :
    toComplex o (R - Q) = (omega : ℂ) * toComplex o (Q - P) ∨
      toComplex o (R - Q) = (omega : ℂ) ^ 2 * toComplex o (Q - P) := by
  have hnap := (m6_equilateral_iff_napoleon (o := o) P Q R).mp h
  rcases hnap with hh | hh
  · left
    have := m3c_complex_ratio1 hh
    rw [← toComplex_sub, ← toComplex_sub] at this
    exact this
  · right
    have := m3c_complex_ratio2 hh
    rw [← toComplex_sub, ← toComplex_sub] at this
    exact this

/-- A closed equilateral triple of complex numbers is `{a, ωa, ω²a}`, hence `ω`-stable. -/
theorem m3c_omega_triple {a b c : ℂ} (hsum : a + b + c = 0)
    (hab : b = (omega : ℂ) * a ∨ b = (omega : ℂ) ^ 2 * a) :
    ((omega : ℂ) * a = a ∨ (omega : ℂ) * a = b ∨ (omega : ℂ) * a = c) ∧
      ((omega : ℂ) * b = a ∨ (omega : ℂ) * b = b ∨ (omega : ℂ) * b = c) ∧
        ((omega : ℂ) * c = a ∨ (omega : ℂ) * c = b ∨ (omega : ℂ) * c = c) := by
  have h1w : (1 : ℂ) + (omega : ℂ) = -((omega : ℂ) ^ 2) := m3c_one_add_omega
  have h1w2 : (1 : ℂ) + (omega : ℂ) ^ 2 = -((omega : ℂ)) := m3c_one_add_omega_sq
  rcases hab with hab | hab
  · have hc : c = (omega : ℂ) ^ 2 * a := by
      have hh : c = -(a + b) := by linear_combination hsum
      rw [hab] at hh
      rw [hh, show a + (omega : ℂ) * a = (1 + (omega : ℂ)) * a from by ring, h1w]
      ring
    have hb : (omega : ℂ) * b = c := by
      rw [hab, show (omega : ℂ) * ((omega : ℂ) * a) = (omega : ℂ) ^ 2 * a from by ring, hc]
    have hcc : (omega : ℂ) * c = a := by
      rw [hc, show (omega : ℂ) * ((omega : ℂ) ^ 2 * a) = (omega : ℂ) ^ 3 * a from by ring,
        omega_cubed, one_mul]
    exact ⟨Or.inr (Or.inl hab.symm), Or.inr (Or.inr hb), Or.inl hcc⟩
  · have hc : c = (omega : ℂ) * a := by
      have hh : c = -(a + b) := by linear_combination hsum
      rw [hab] at hh
      rw [hh, show a + (omega : ℂ) ^ 2 * a = (1 + (omega : ℂ) ^ 2) * a from by ring, h1w2]
      ring
    have hb : (omega : ℂ) * b = a := by
      rw [hab, show (omega : ℂ) * ((omega : ℂ) ^ 2 * a) = (omega : ℂ) ^ 3 * a from by ring,
        omega_cubed, one_mul]
    have hcc : (omega : ℂ) * c = b := by
      rw [hc, show (omega : ℂ) * ((omega : ℂ) * a) = (omega : ℂ) ^ 2 * a from by ring, hab]
    exact ⟨Or.inr (Or.inr hc.symm), Or.inl hb, Or.inr (Or.inl hcc)⟩

/-- The Morley side triple is `ω`-stable. -/
theorem m3c_omega_morley_complex (T : OrientedTriangle E o) :
    ((omega : ℂ) * toComplex o (T.Y - T.X) = toComplex o (T.Y - T.X) ∨
        (omega : ℂ) * toComplex o (T.Y - T.X) = toComplex o (T.Z - T.Y) ∨
          (omega : ℂ) * toComplex o (T.Y - T.X) = toComplex o (T.X - T.Z)) ∧
      ((omega : ℂ) * toComplex o (T.Z - T.Y) = toComplex o (T.Y - T.X) ∨
          (omega : ℂ) * toComplex o (T.Z - T.Y) = toComplex o (T.Z - T.Y) ∨
            (omega : ℂ) * toComplex o (T.Z - T.Y) = toComplex o (T.X - T.Z)) ∧
        ((omega : ℂ) * toComplex o (T.X - T.Z) = toComplex o (T.Y - T.X) ∨
            (omega : ℂ) * toComplex o (T.X - T.Z) = toComplex o (T.Z - T.Y) ∨
              (omega : ℂ) * toComplex o (T.X - T.Z) = toComplex o (T.X - T.Z)) := by
  have hcl : toComplex o (T.Y - T.X) + toComplex o (T.Z - T.Y) + toComplex o (T.X - T.Z) = 0 := by
    simp only [toComplex_sub]; ring
  exact m3c_omega_triple hcl (m3c_equilateral_sub_ratio (o := o) T.X T.Y T.Z T.morley)

/-- Transfer of a complex `ω`-relation to the vector level. -/
theorem m3c_rot_eq_of_complex {f g : E}
    (h : (omega : ℂ) * toComplex o f = toComplex o g) :
    m3cRot (o := o) (omega : ℂ) f = g := by
  apply toComplex_injective o
  rw [m3c_toComplex_rot]
  exact h

theorem m3c_omega_side1 (T : OrientedTriangle E o) :
    m3cRot (o := o) (omega : ℂ) (T.Y - T.X) = T.Y - T.X ∨
      m3cRot (o := o) (omega : ℂ) (T.Y - T.X) = T.Z - T.Y ∨
        m3cRot (o := o) (omega : ℂ) (T.Y - T.X) = T.X - T.Z := by
  obtain ⟨k1, -, -⟩ := m3c_omega_morley_complex T
  rcases k1 with k | k | k
  · exact Or.inl (m3c_rot_eq_of_complex k)
  · exact Or.inr (Or.inl (m3c_rot_eq_of_complex k))
  · exact Or.inr (Or.inr (m3c_rot_eq_of_complex k))

theorem m3c_omega_side2 (T : OrientedTriangle E o) :
    m3cRot (o := o) (omega : ℂ) (T.Z - T.Y) = T.Y - T.X ∨
      m3cRot (o := o) (omega : ℂ) (T.Z - T.Y) = T.Z - T.Y ∨
        m3cRot (o := o) (omega : ℂ) (T.Z - T.Y) = T.X - T.Z := by
  obtain ⟨-, k2, -⟩ := m3c_omega_morley_complex T
  rcases k2 with k | k | k
  · exact Or.inl (m3c_rot_eq_of_complex k)
  · exact Or.inr (Or.inl (m3c_rot_eq_of_complex k))
  · exact Or.inr (Or.inr (m3c_rot_eq_of_complex k))

theorem m3c_omega_side3 (T : OrientedTriangle E o) :
    m3cRot (o := o) (omega : ℂ) (T.X - T.Z) = T.Y - T.X ∨
      m3cRot (o := o) (omega : ℂ) (T.X - T.Z) = T.Z - T.Y ∨
        m3cRot (o := o) (omega : ℂ) (T.X - T.Z) = T.X - T.Z := by
  obtain ⟨-, -, k3⟩ := m3c_omega_morley_complex T
  rcases k3 with k | k | k
  · exact Or.inl (m3c_rot_eq_of_complex k)
  · exact Or.inr (Or.inl (m3c_rot_eq_of_complex k))
  · exact Or.inr (Or.inr (m3c_rot_eq_of_complex k))

theorem m3c_pMS_of_rot_eq (T : OrientedTriangle E o) {f : E}
    (hk : m3cRot (o := o) (omega : ℂ) f = T.Y - T.X ∨
      m3cRot (o := o) (omega : ℂ) f = T.Z - T.Y ∨
        m3cRot (o := o) (omega : ℂ) f = T.X - T.Z) :
    T.parallelToMorleySide (m3cRot (o := o) (omega : ℂ) f) := by
  rcases hk with hk | hk | hk
  · exact Or.inl ⟨1, by rw [hk]; simp⟩
  · exact Or.inr (Or.inl ⟨1, by rw [hk]; simp⟩)
  · exact Or.inr (Or.inr ⟨1, by rw [hk]; simp⟩)

theorem m3c_pMS_smul (T : OrientedTriangle E o) (c : ℝ) {v : E}
    (h : T.parallelToMorleySide v) : T.parallelToMorleySide (c • v) := by
  rcases h with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩
  · exact Or.inl ⟨c * r, by rw [hr, smul_smul]⟩
  · exact Or.inr (Or.inl ⟨c * r, by rw [hr, smul_smul]⟩)
  · exact Or.inr (Or.inr ⟨c * r, by rw [hr, smul_smul]⟩)

/-- Multiplying a vector parallel to a Morley side by `ω` again gives one. -/
theorem m3c_pMS_rot (T : OrientedTriangle E o) {v : E}
    (h : T.parallelToMorleySide v) :
    T.parallelToMorleySide (m3cRot (o := o) (omega : ℂ) v) := by
  rcases h with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩
  · rw [hr, m3c_rot_smul]
    exact m3c_pMS_smul T r (m3c_pMS_of_rot_eq T (m3c_omega_side1 T))
  · rw [hr, m3c_rot_smul]
    exact m3c_pMS_smul T r (m3c_pMS_of_rot_eq T (m3c_omega_side2 T))
  · rw [hr, m3c_rot_smul]
    exact m3c_pMS_smul T r (m3c_pMS_of_rot_eq T (m3c_omega_side3 T))

/-- **The reduction.** In an equilateral triangle `P Q R`, one side parallel to a Morley
side forces the other two. -/
theorem m3c_pMS_of_equilateral_of_pMS (T : OrientedTriangle E o) {P Q R : E}
    (heq : Equilateral P Q R) (h : T.parallelToMorleySide (Q - P)) :
    T.parallelToMorleySide (R - Q) ∧ T.parallelToMorleySide (P - R) := by
  have heq' : Equilateral Q R P := (m6_equilateral_cyclic P Q R).mpr heq
  have h1 := m3c_equilateral_sub_ratio (o := o) P Q R heq
  have h2 := m3c_equilateral_sub_ratio (o := o) Q R P heq'
  have hRQ : T.parallelToMorleySide (R - Q) := by
    rcases h1 with h1 | h1
    · have e : m3cRot (o := o) (omega : ℂ) (Q - P) = R - Q := by
        apply toComplex_injective o
        rw [m3c_toComplex_rot]
        exact h1.symm
      rw [← e]
      exact m3c_pMS_rot T h
    · have e : m3cRot (o := o) (omega : ℂ) (m3cRot (o := o) (omega : ℂ) (Q - P)) = R - Q := by
        apply toComplex_injective o
        rw [m3c_toComplex_rot, m3c_toComplex_rot]
        rw [show (omega : ℂ) * ((omega : ℂ) * toComplex o (Q - P))
          = (omega : ℂ) ^ 2 * toComplex o (Q - P) from by ring]
        exact h1.symm
      rw [← e]
      exact m3c_pMS_rot T (m3c_pMS_rot T h)
  refine ⟨hRQ, ?_⟩
  rcases h2 with h2 | h2
  · have e : m3cRot (o := o) (omega : ℂ) (R - Q) = P - R := by
      apply toComplex_injective o
      rw [m3c_toComplex_rot]
      exact h2.symm
    rw [← e]
    exact m3c_pMS_rot T hRQ
  · have e : m3cRot (o := o) (omega : ℂ) (m3cRot (o := o) (omega : ℂ) (R - Q)) = P - R := by
      apply toComplex_injective o
      rw [m3c_toComplex_rot, m3c_toComplex_rot]
      rw [show (omega : ℂ) * ((omega : ℂ) * toComplex o (R - Q))
        = (omega : ℂ) ^ 2 * toComplex o (R - Q) from by ring]
      exact h2.symm
    rw [← e]
    exact m3c_pMS_rot T (m3c_pMS_rot T hRQ)

/-! ### The `⟨0,0,0⟩` label: closed outright -/

theorem m3c_tricolor_zero_eq (T : OrientedTriangle E o) :
    (T.tricolorTriangle (⟨0, 0, 0⟩ : TricolorIndex)).first = T.X ∧
      (T.tricolorTriangle (⟨0, 0, 0⟩ : TricolorIndex)).second = T.Y ∧
        (T.tricolorTriangle (⟨0, 0, 0⟩ : TricolorIndex)).third = T.Z := by
  have hl : labelAngle (0 : TrisectorLabel) = 0 := by simp [labelAngle]
  refine ⟨?_, ?_, ?_⟩
  · show T.constellationPoint ⟨.red, 0, 0⟩ = _
    simp only [OrientedTriangle.constellationPoint, hl, sub_zero]
    rfl
  · show T.constellationPoint ⟨.green, 0, 0⟩ = _
    simp only [OrientedTriangle.constellationPoint, hl, sub_zero]
    rfl
  · show T.constellationPoint ⟨.blue, 0, 0⟩ = _
    simp only [OrientedTriangle.constellationPoint, hl, sub_zero]
    rfl

theorem m3c_tricolor_sides_zero (T : OrientedTriangle E o) :
    (let t := T.tricolorTriangle (⟨0, 0, 0⟩ : TricolorIndex)
     T.parallelToMorleySide (t.second - t.first) ∧
       T.parallelToMorleySide (t.third - t.second) ∧
         T.parallelToMorleySide (t.first - t.third)) := by
  obtain ⟨h1, h2, h3⟩ := m3c_tricolor_zero_eq T
  refine ⟨?_, ?_, ?_⟩
  · show T.parallelToMorleySide
      ((T.tricolorTriangle (⟨0, 0, 0⟩ : TricolorIndex)).second -
        (T.tricolorTriangle (⟨0, 0, 0⟩ : TricolorIndex)).first)
    rw [h1, h2]
    exact Or.inl ⟨1, by simp⟩
  · show T.parallelToMorleySide
      ((T.tricolorTriangle (⟨0, 0, 0⟩ : TricolorIndex)).third -
        (T.tricolorTriangle (⟨0, 0, 0⟩ : TricolorIndex)).second)
    rw [h2, h3]
    exact Or.inr (Or.inl ⟨1, by simp⟩)
  · show T.parallelToMorleySide
      ((T.tricolorTriangle (⟨0, 0, 0⟩ : TricolorIndex)).first -
        (T.tricolorTriangle (⟨0, 0, 0⟩ : TricolorIndex)).third)
    rw [h1, h3]
    exact Or.inr (Or.inr ⟨1, by simp⟩)

/-! ### The reduction, applied to the root's target -/

/-- **`tricolor_sides_parallel` follows from its first conjunct alone.**  The eighteen
non-exceptional tricolour triangles are equilateral, and in an equilateral triangle one
side parallel to a Morley side forces the other two. -/
theorem m3c_tricolor_sides_parallel_of_first (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint)
    (hfirst : ∀ q : TricolorIndex, q.i + q.j + q.k ≠ 1 →
      T.parallelToMorleySide ((T.tricolorTriangle q).second - (T.tricolorTriangle q).first)) :
    ∀ q : TricolorIndex, q.i + q.j + q.k ≠ 1 →
      (let t := T.tricolorTriangle q
       T.parallelToMorleySide (t.second - t.first) ∧
         T.parallelToMorleySide (t.third - t.second) ∧
           T.parallelToMorleySide (t.first - t.third)) := by
  intro q hq
  have heq := m3c7_tricolor_equilateral_of_ne_one T q hq
  obtain ⟨h2, h3⟩ := m3c_pMS_of_equilateral_of_pMS (T := T) heq (hfirst q hq)
  exact ⟨hfirst q hq, h2, h3⟩

/-- The root's `tricolor_sides_parallel`, in the exact form of the root statement, given
the first conjunct for each label. -/
theorem m3c_tricolor_sides_parallel (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint)
    (hfirst : ∀ q : TricolorIndex, q.i + q.j + q.k ≠ 1 →
      (let t := T.tricolorTriangle q
       T.parallelToMorleySide (t.second - t.first))) :
    ∀ q : TricolorIndex, q.i + q.j + q.k ≠ 1 →
      (let t := T.tricolorTriangle q
       T.parallelToMorleySide (t.second - t.first) ∧
         T.parallelToMorleySide (t.third - t.second) ∧
           T.parallelToMorleySide (t.first - t.third)) :=
  m3c_tricolor_sides_parallel_of_first T h fun q hq => hfirst q hq

/-! ### Cyclic transport: the open labels fall into eight orbits -/

/-- **Cyclic transport of the first conjunct.**  The first conjunct for the label
`(i,j,k)` of `m7_cyclic T` is the *third-to-second* side of the label `(k,i,j)` at `T`;
since that side is parallel to a Morley side as soon as the first is (the triangle being
equilateral), the first conjunct propagates along the cyclic action
`(i,j,k) ↦ (k,i,j)`.  Hence the eighteen labels reduce to eight orbit representatives. -/
theorem m3c_hfirst_cyclic (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (i j k : TrisectorLabel) (hq : i + j + k ≠ 1)
    (hrep : T.parallelToMorleySide
      ((T.tricolorTriangle ⟨k, i, j⟩).second - (T.tricolorTriangle ⟨k, i, j⟩).first)) :
    (m7_cyclic T).parallelToMorleySide
      (((m7_cyclic T).tricolorTriangle ⟨i, j, k⟩).second -
        ((m7_cyclic T).tricolorTriangle ⟨i, j, k⟩).first) := by
  have hsum : k + i + j ≠ 1 := by
    intro hc
    apply hq
    rw [← hc]
    abel
  have heq := m3c7_tricolor_equilateral_of_ne_one T (⟨k, i, j⟩ : TricolorIndex) hsum
  obtain ⟨h3, -⟩ := m3c_pMS_of_equilateral_of_pMS (T := T) heq hrep
  have hpt : ((m7_cyclic T).tricolorTriangle ⟨i, j, k⟩).second -
        ((m7_cyclic T).tricolorTriangle ⟨i, j, k⟩).first
      = (T.tricolorTriangle ⟨k, i, j⟩).third - (T.tricolorTriangle ⟨k, i, j⟩).second := by
    show (m7_cyclic T).constellationPoint ⟨.green, j, k⟩ -
        (m7_cyclic T).constellationPoint ⟨.red, i, j⟩ = _
    rw [m3_cp_cyclic_green, m3_cp_cyclic_red]
    rfl
  rw [hpt, m3_parallelToMorleySide_cyclic]
  exact h3

/-- Transitivity helper: a vector parallel to a Morley side, in the same direction as
another, is itself parallel to a Morley side.  This is the link between the guide-line
(incidence) description of the tricolour sides and the m3p direction table. -/
theorem m3c_pMS_of_parallel_trans (T : OrientedTriangle E o) {u v : E}
    (h1 : T.parallelToMorleySide u) (h2 : Parallel u v) : T.parallelToMorleySide v := by
  rcases h1 with h1 | h1 | h1
  · exact Or.inl (h1.trans h2)
  · exact Or.inr (Or.inl (h1.trans h2))
  · exact Or.inr (Or.inr (h1.trans h2))

/-- **The collinearity-to-direction bridge.**  If the first side of a tricolour triangle
lies on a red equal-sum join whose direction is a Morley direction, then the first conjunct
of `tricolor_sides_parallel` holds for that label. -/
theorem m3c_hfirst_of_collinear (T : OrientedTriangle E o) (i j k i' j' : TrisectorLabel)
    (hR : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, i, j⟩ - T.constellationPoint ⟨.red, i', j'⟩))
    (hcol : Parallel (T.constellationPoint ⟨.red, i, j⟩ - T.constellationPoint ⟨.red, i', j'⟩)
      (T.constellationPoint ⟨.green, j, k⟩ - T.constellationPoint ⟨.red, i, j⟩)) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, j, k⟩ - T.constellationPoint ⟨.red, i, j⟩) :=
  m3c_pMS_of_parallel_trans T hR hcol

/-! ### The explicit real-ratio machinery for the tricolour first conjunct -/

theorem m3c_star_eq_inv {z : ℂ} (h : ‖z‖ = 1) : star z = z⁻¹ := by
  have h2 : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, h]; norm_num
  rw [Complex.inv_def, h2]
  simp

theorem m3c_norm_P (T : OrientedTriangle E o) : ‖m1P T‖ = 1 := by
  rw [m1P]; exact Circle.norm_coe _
theorem m3c_norm_Q (T : OrientedTriangle E o) : ‖m1Q T‖ = 1 := by
  rw [m1Q]; exact Circle.norm_coe _
theorem m3c_norm_R (T : OrientedTriangle E o) : ‖m1R T‖ = 1 := by
  rw [m1R]; exact Circle.norm_coe _
theorem m3c_norm_sigma (l : TrisectorLabel) : ‖m1sigma l‖ = 1 := by
  rw [m1sigma]; exact Circle.norm_coe _

theorem m3c_P_ne (T : OrientedTriangle E o) : m1P T ≠ 0 := by
  rw [m1P]; exact Circle.coe_ne_zero _
theorem m3c_Q_ne (T : OrientedTriangle E o) : m1Q T ≠ 0 := by
  rw [m1Q]; exact Circle.coe_ne_zero _
theorem m3c_R_ne (T : OrientedTriangle E o) : m1R T ≠ 0 := by
  rw [m1R]; exact Circle.coe_ne_zero _

theorem m3c_P_cube_sub_one_ne (T : OrientedTriangle E o) : m1P T ^ 3 - 1 ≠ 0 := by
  have h : m1P T ^ 3 = (Circle.exp (6 * T.beta) : ℂ) := by
    rw [m1P, ← Circle.coe_pow, ← Circle.exp_natCast_mul]
    congr 2
    push_cast; ring
  rw [h]
  exact m3c7_five_ne T

theorem m3c_R_cube_sub_one_ne (T : OrientedTriangle E o) : m1R T ^ 3 - 1 ≠ 0 := by
  have h : m1R T ^ 3 = (Circle.exp (6 * T.alpha) : ℂ) := by
    rw [m1R, ← Circle.coe_pow, ← Circle.exp_natCast_mul]
    congr 2
    push_cast; ring
  rw [h]
  exact m3c7_six_alpha_sub_one_ne T

/-- The coefficient `λ = U / W`, `U = toComplex(B-C)`, `W = toComplex(C-A)`. -/
noncomputable def m3cLam (T : OrientedTriangle E o) : ℂ :=
  ((m1R T) ^ 3 - 1) / ((m1R T) ^ 3 * ((m1P T) ^ 3 - 1))

noncomputable def m3cRho (T : OrientedTriangle E o) (i j : TrisectorLabel) : ℂ :=
  (1 - m1P T * m1sigma i) / (1 - m1P T * m1Q T * m1sigma (i + j))

noncomputable def m3cGam (T : OrientedTriangle E o) (i j : TrisectorLabel) : ℂ :=
  (1 - m1Q T * m1sigma i) / (1 - m1Q T * m1R T * m1sigma (i + j))

noncomputable def m3cA (T : OrientedTriangle E o) (i j k : TrisectorLabel) : ℂ :=
  (1 - m3cGam T j k) + m3cLam T * m3cRho T i j

noncomputable def m3cB (T : OrientedTriangle E o) (i j i' j' : TrisectorLabel) : ℂ :=
  m3cLam T * (m3cRho T i' j' - m3cRho T i j)

/-- `U = λ · W`, the algebraic relation between the two side vectors. -/
theorem m3c_U_eq (T : OrientedTriangle E o) :
    toComplex o (T.B - T.C) = m3cLam T * toComplex o (T.C - T.A) := by
  have h := m3c7_p_rel T 0 0 0
  have hl0 : labelAngle (0 : TrisectorLabel) = 0 := labelAngle_zero
  rw [hl0] at h
  simp only [sub_zero] at h
  have e0 : (Circle.exp (2 * T.alpha) : ℂ) = m1R T := rfl
  have e1 : (Circle.exp (2 * T.beta) : ℂ) = m1P T := rfl
  rw [e0, e1] at h
  have hP3 : (m1P T) ^ 3 - 1 ≠ 0 := m3c_P_cube_sub_one_ne T
  have hR3 : (m1R T) ^ 3 ≠ 0 := pow_ne_zero 3 (m3c_R_ne T)
  rw [m3cLam, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hR3 hP3)]
  exact h

theorem m3c_star_P (T : OrientedTriangle E o) : star (m1P T) = (m1P T)⁻¹ :=
  m3c_star_eq_inv (m3c_norm_P T)
theorem m3c_star_Q (T : OrientedTriangle E o) : star (m1Q T) = (m1Q T)⁻¹ :=
  m3c_star_eq_inv (m3c_norm_Q T)
theorem m3c_star_R (T : OrientedTriangle E o) : star (m1R T) = (m1R T)⁻¹ :=
  m3c_star_eq_inv (m3c_norm_R T)
theorem m3c_star_sigma (l : TrisectorLabel) : star (m1sigma l) = (m1sigma l)⁻¹ :=
  m3c_star_eq_inv (m3c_norm_sigma l)

/-- Realness extraction: a ratio whose cross-conjugate product is symmetric is real. -/
theorem m3c_real_div {A B : ℂ} (hB : B ≠ 0) (h : star A * B = A * star B) :
    ∃ r : ℝ, A = (r : ℂ) * B := by
  have hstarB : star B ≠ 0 := by simpa using hB
  have hw : star A / star B = A / B := by
    rw [div_eq_div_iff hstarB hB]; exact h
  have hreal : star (A / B) = A / B := by
    rw [show star (A / B) = star A / star B from by simp, hw]
  have him : (A / B).im = 0 := by
    have h2 := congrArg Complex.im hreal
    simp only [Complex.star_def, Complex.conj_im] at h2
    linarith
  refine ⟨(A / B).re, ?_⟩
  have hwre : A / B = (((A / B).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  rw [← hwre]
  field_simp

/-- The nonvanishing inputs for `field_simp`. -/
theorem m3c_red_den (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    (1 - m1P T * m1Q T * m1sigma (i + j)) ≠ 0 := m1_red_den_ne T (i + j)
theorem m3c_green_den (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    (1 - m1Q T * m1R T * m1sigma (i + j)) ≠ 0 := m1_green_den_ne T (i + j)

/-! ### Nonvanishing in the `ω = P·Q·R` normal form -/

theorem m3c_d_red (T : OrientedTriangle E o) :
    (1 - m1P T * m1Q T * (m1P T * m1Q T * m1R T)) ≠ 0 := by
  rw [m1_PQR T, ← m1sigma_two]
  exact m1_red_den_ne T 2

theorem m3c_d_green (T : OrientedTriangle E o) :
    (1 - m1Q T * m1R T * (m1P T * m1Q T * m1R T)) ≠ 0 := by
  rw [m1_PQR T, ← m1sigma_two]
  exact m1_green_den_ne T 2

theorem m3c_d_red_conj (T : OrientedTriangle E o) :
    (1 - (m1P T)⁻¹ * (m1Q T)⁻¹ * ((m1P T) * (m1Q T) * (m1R T))⁻¹) ≠ 0 := by
  have hx1 : (m1P T * m1Q T * (m1P T * m1Q T * m1R T)) ≠ 1 := by
    intro h
    exact m3c_d_red T (by rw [h]; ring)
  have hrew : (1 : ℂ) - (m1P T)⁻¹ * (m1Q T)⁻¹ * ((m1P T) * (m1Q T) * (m1R T))⁻¹
      = 1 - (m1P T * m1Q T * (m1P T * m1Q T * m1R T))⁻¹ := by
    rw [mul_inv]
    ring
  rw [hrew]
  intro h0
  exact hx1 (inv_eq_one.mp (by linear_combination -h0))

theorem m3c_d_green_conj (T : OrientedTriangle E o) :
    (1 - (m1Q T)⁻¹ * (m1R T)⁻¹ * ((m1P T) * (m1Q T) * (m1R T))⁻¹) ≠ 0 := by
  have hx1 : (m1Q T * m1R T * (m1P T * m1Q T * m1R T)) ≠ 1 := by
    intro h
    exact m3c_d_green T (by rw [h]; ring)
  have hrew : (1 : ℂ) - (m1Q T)⁻¹ * (m1R T)⁻¹ * ((m1P T) * (m1Q T) * (m1R T))⁻¹
      = 1 - (m1Q T * m1R T * (m1P T * m1Q T * m1R T))⁻¹ := by
    rw [mul_inv]
    ring
  rw [hrew]
  intro h0
  exact hx1 (inv_eq_one.mp (by linear_combination -h0))

theorem m3c_d1 (T : OrientedTriangle E o) :
    (1 - m1R T * m1Q T ^ 2 * m1P T ^ 2) ≠ 0 := by
  have h := m3c_d_red T
  rw [show (1 - m1R T * m1Q T ^ 2 * m1P T ^ 2)
      = (1 - m1P T * m1Q T * (m1P T * m1Q T * m1R T)) from by ring]
  exact h

theorem m3c_e2 (T : OrientedTriangle E o) :
    (-1 + m1R T ^ 2 * m1Q T ^ 2 * m1P T) ≠ 0 := by
  have h := m3c_d_green T
  rw [show (-1 + m1R T ^ 2 * m1Q T ^ 2 * m1P T)
      = -(1 - m1Q T * m1R T * (m1P T * m1Q T * m1R T)) from by ring]
  exact neg_ne_zero.mpr h

theorem m3c_e1 (T : OrientedTriangle E o) : (-1 + m1P T ^ 3) ≠ 0 := by
  have h := m3c_P_cube_sub_one_ne T
  rw [show (-1 + m1P T ^ 3) = -(1 - m1P T ^ 3) from by ring]
  exact neg_ne_zero.mpr (by
    intro h0; exact h (by linear_combination -h0))

theorem m3c_e3 (T : OrientedTriangle E o) : (m1R T ^ 3 - 1) ≠ 0 := m3c_R_cube_sub_one_ne T

theorem m3c_e4 (T : OrientedTriangle E o) :
    (-1 + m1R T * m1Q T ^ 2 * m1P T ^ 2 - m1R T * m1Q T ^ 2 * m1P T ^ 5 + m1P T ^ 3) ≠ 0 := by
  have h1 : (1 - m1R T * m1Q T ^ 2 * m1P T ^ 2) ≠ 0 := m3c_d1 T
  have h2 : (1 - m1P T ^ 3) ≠ 0 := by
    intro h0; exact m3c_P_cube_sub_one_ne T (by linear_combination -h0)
  rw [show (-1 + m1R T * m1Q T ^ 2 * m1P T ^ 2 - m1R T * m1Q T ^ 2 * m1P T ^ 5 + m1P T ^ 3)
      = (-(1 - m1R T * m1Q T ^ 2 * m1P T ^ 2)) * (1 - m1P T ^ 3) from by ring]
  exact mul_ne_zero (neg_ne_zero.mpr h1) h2

theorem m3c_e2b (T : OrientedTriangle E o) :
    (1 - m1R T ^ 2 * m1Q T ^ 2 * m1P T) ≠ 0 := by
  have h := m3c_e2 T
  rwa [show (1 - m1R T ^ 2 * m1Q T ^ 2 * m1P T)
      = -(-1 + m1R T ^ 2 * m1Q T ^ 2 * m1P T) from by ring, neg_ne_zero]

theorem m3c_d1b (T : OrientedTriangle E o) :
    (m1R T * m1Q T ^ 2 * m1P T ^ 2 - 1) ≠ 0 := by
  have h := m3c_d1 T
  rwa [show (m1R T * m1Q T ^ 2 * m1P T ^ 2 - 1)
      = -(1 - m1R T * m1Q T ^ 2 * m1P T ^ 2) from by ring, neg_ne_zero]

theorem m3c_e1b (T : OrientedTriangle E o) : (1 - m1P T ^ 3) ≠ 0 := by
  have h := m3c_P_cube_sub_one_ne T
  rwa [show (1 - m1P T ^ 3) = -(m1P T ^ 3 - 1) from by ring, neg_ne_zero]

theorem m3c_e3b (T : OrientedTriangle E o) : (1 - m1R T ^ 3) ≠ 0 := by
  have h := m3c_R_cube_sub_one_ne T
  rwa [show (1 - m1R T ^ 3) = -(m1R T ^ 3 - 1) from by ring, neg_ne_zero]

theorem m3c_e4b (T : OrientedTriangle E o) :
    (1 - m1R T * m1Q T ^ 2 * m1P T ^ 2 + m1R T * m1Q T ^ 2 * m1P T ^ 5 - m1P T ^ 3) ≠ 0 := by
  have h := m3c_e4 T
  rw [show (1 - m1R T * m1Q T ^ 2 * m1P T ^ 2 + m1R T * m1Q T ^ 2 * m1P T ^ 5 - m1P T ^ 3)
      = -(-1 + m1R T * m1Q T ^ 2 * m1P T ^ 2 - m1R T * m1Q T ^ 2 * m1P T ^ 5 + m1P T ^ 3)
      from by ring]
  exact neg_ne_zero.mpr h





noncomputable section
open scoped Real RealInnerProductSpace ComplexConjugate Matrix
open Function Set


variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable {o : Orientation ℝ E (Fin 2)}


/-! ### Common-denominator form of the tricolour coefficient `A` and the join coefficient `B` -/

/-- Denominator of `m3cRho`. -/
noncomputable def m1mDrho (T : OrientedTriangle E o) (i j : TrisectorLabel) : ℂ :=
  1 - m1P T * m1Q T * m1sigma (i + j)

/-- Denominator of `m3cGam`. -/
noncomputable def m1mDgam (T : OrientedTriangle E o) (j k : TrisectorLabel) : ℂ :=
  1 - m1Q T * m1R T * m1sigma (j + k)

/-- Numerator of `m3cLam`. -/
noncomputable def m1mLamNum (T : OrientedTriangle E o) : ℂ := (m1R T) ^ 3 - 1

/-- Denominator of `m3cLam`. -/
noncomputable def m1mLamDen (T : OrientedTriangle E o) : ℂ := (m1R T) ^ 3 * ((m1P T) ^ 3 - 1)

/-- Denominator of `m3cA T i j k` in its unenlarged form. -/
noncomputable def m1mDA (T : OrientedTriangle E o) (i j k : TrisectorLabel) : ℂ :=
  m1mDgam T j k * m1mLamDen T * m1mDrho T i j

/-- Numerator of `m3cA T i j k` over `m1mDA`. -/
noncomputable def m1mNAb (T : OrientedTriangle E o) (i j k : TrisectorLabel) : ℂ :=
  (m1Q T * m1sigma j * (1 - m1R T * m1sigma k)) * m1mLamDen T * m1mDrho T i j
    + m1mLamNum T * (1 - m1P T * m1sigma i) * m1mDgam T j k

/-- The common denominator of `m3cA T i j k` and `m3cB T i j i' j'`. -/
noncomputable def m1mD (T : OrientedTriangle E o) (i j k i' j' : TrisectorLabel) : ℂ :=
  m1mDgam T j k * m1mLamDen T * m1mDrho T i j * m1mDrho T i' j'

/-- Numerator of `m3cA T i j k` over the common denominator `m1mD`. -/
noncomputable def m1mNA (T : OrientedTriangle E o) (i j k i' j' : TrisectorLabel) : ℂ :=
  m1mNAb T i j k * m1mDrho T i' j'

/-- Numerator of `m3cB T i j i' j'` over the common denominator `m1mD`. -/
noncomputable def m1mNB (T : OrientedTriangle E o) (i j k i' j' : TrisectorLabel) : ℂ :=
  m1mLamNum T * ((1 - m1P T * m1sigma i') * m1mDrho T i j
      - (1 - m1P T * m1sigma i) * m1mDrho T i' j') * m1mDgam T j k

/-! ### Nonvanishing -/

theorem m1m_Drho_ne (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    m1mDrho T i j ≠ 0 :=
  m1_red_den_ne T (i + j)

theorem m1m_Dgam_ne (T : OrientedTriangle E o) (j k : TrisectorLabel) :
    m1mDgam T j k ≠ 0 :=
  m1_green_den_ne T (j + k)

theorem m1m_LamDen_ne (T : OrientedTriangle E o) : m1mLamDen T ≠ 0 := by
  unfold m1mLamDen
  exact mul_ne_zero (pow_ne_zero 3 (m3c_R_ne T)) (m3c_P_cube_sub_one_ne T)

theorem m1m_DA_ne (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    m1mDA T i j k ≠ 0 := by
  unfold m1mDA
  exact mul_ne_zero (mul_ne_zero (m1m_Dgam_ne T j k) (m1m_LamDen_ne T)) (m1m_Drho_ne T i j)

theorem m1m_D_ne (T : OrientedTriangle E o) (i j k i' j' : TrisectorLabel) :
    m1mD T i j k i' j' ≠ 0 := by
  unfold m1mD
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (m1m_Dgam_ne T j k) (m1m_LamDen_ne T))
    (m1m_Drho_ne T i j)) (m1m_Drho_ne T i' j')

theorem m1m_three (T : OrientedTriangle E o) : (m1P T * m1Q T * m1R T) ^ 3 = 1 := by
  rw [m1_PQR T]
  exact omega_cubed

/-! ### The two abstract division-clearing keys -/

/-- Clearing the denominators of `m3cA` against `m1mDA`. -/
theorem m1m_A_key (P Q R si sj sk sijk sjpk : ℂ) (hP : P ^ 3 - 1 ≠ 0) (hR : R ≠ 0)
    (hA : 1 - P * Q * sijk ≠ 0) (hB : 1 - Q * R * sjpk ≠ 0) (hs : sjpk = sj * sk) :
    (1 - (1 - Q * sj) / (1 - Q * R * sjpk)) + ((R ^ 3 - 1) / (R ^ 3 * (P ^ 3 - 1))) *
        ((1 - P * si) / (1 - P * Q * sijk))
    = ((Q * sj * (1 - R * sk)) * (R ^ 3 * (P ^ 3 - 1)) * (1 - P * Q * sijk)
        + (R ^ 3 - 1) * (1 - P * si) * (1 - Q * R * sjpk))
      / ((1 - Q * R * sjpk) * (R ^ 3 * (P ^ 3 - 1)) * (1 - P * Q * sijk)) := by
  set a := 1 - Q * R * sjpk with ha
  set b := R ^ 3 * (P ^ 3 - 1) with hb
  set c := 1 - P * Q * sijk with hc
  have ha' : a ≠ 0 := by rw [ha]; exact hB
  have hb' : b ≠ 0 := by rw [hb]; exact mul_ne_zero (pow_ne_zero 3 hR) hP
  have hc' : c ≠ 0 := by rw [hc]; exact hA
  field_simp
  rw [ha, hs]
  ring

/-- Clearing the denominators of `m3cB` against `m1mD`. -/
theorem m1m_B_key (P Q R si sip sjp sijk sijp sjpk : ℂ) (hP : P ^ 3 - 1 ≠ 0) (hR : R ≠ 0)
    (hA : 1 - P * Q * sijk ≠ 0) (hB : 1 - Q * R * sjpk ≠ 0) (hC : 1 - P * Q * sijp ≠ 0) :
    ((R ^ 3 - 1) / (R ^ 3 * (P ^ 3 - 1))) *
        (((1 - P * sip) / (1 - P * Q * sijp)) - ((1 - P * si) / (1 - P * Q * sijk)))
    = ((R ^ 3 - 1) * ((1 - P * sip) * (1 - P * Q * sijk) - (1 - P * si) * (1 - P * Q * sijp))
        * (1 - Q * R * sjpk))
      / ((1 - Q * R * sjpk) * (R ^ 3 * (P ^ 3 - 1)) * (1 - P * Q * sijk) * (1 - P * Q * sijp)) := by
  set a := 1 - Q * R * sjpk with ha
  set b := R ^ 3 * (P ^ 3 - 1) with hb
  set c := 1 - P * Q * sijk with hc
  set d := 1 - P * Q * sijp with hd
  have ha' : a ≠ 0 := by rw [ha]; exact hB
  have hb' : b ≠ 0 := by rw [hb]; exact mul_ne_zero (pow_ne_zero 3 hR) hP
  have hc' : c ≠ 0 := by rw [hc]; exact hA
  have hd' : d ≠ 0 := by rw [hd]; exact hC
  field_simp

/-! ### Fraction forms -/

/-- `m3cA T i j k = m1mNAb/m1mDA`. -/
theorem m1m_A_frac' (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    m3cA T i j k = m1mNAb T i j k / m1mDA T i j k := by
  unfold m3cA m3cRho m3cGam m3cLam m1mNAb m1mDA m1mDgam m1mDrho m1mLamNum m1mLamDen
  exact m1m_A_key (m1P T) (m1Q T) (m1R T) (m1sigma i) (m1sigma j) (m1sigma k)
    (m1sigma (i + j)) (m1sigma (j + k)) (m3c_P_cube_sub_one_ne T) (m3c_R_ne T)
    (m1_red_den_ne T (i + j)) (m1_green_den_ne T (j + k)) (m1sigma_mul j k)

/-- `m3cA T i j k = NA/D`. -/
theorem m1m_A_frac (T : OrientedTriangle E o) (i j k i' j' : TrisectorLabel) :
    m3cA T i j k = m1mNA T i j k i' j' / m1mD T i j k i' j' := by
  rw [m1m_A_frac']
  have h1 : m1mNA T i j k i' j' = m1mNAb T i j k * m1mDrho T i' j' := rfl
  have h2 : m1mD T i j k i' j' = m1mDA T i j k * m1mDrho T i' j' := by
    unfold m1mD m1mDA
    ring
  rw [h1, h2, mul_div_mul_right _ _ (m1m_Drho_ne T i' j')]

/-- `m3cB T i j i' j' = NB/D`. -/
theorem m1m_B_frac (T : OrientedTriangle E o) (i j k i' j' : TrisectorLabel) :
    m3cB T i j i' j' = m1mNB T i j k i' j' / m1mD T i j k i' j' := by
  unfold m3cB m3cRho m3cLam m1mNB m1mD m1mDgam m1mDrho m1mLamNum m1mLamDen
  exact m1m_B_key (m1P T) (m1Q T) (m1R T) (m1sigma i) (m1sigma i') (m1sigma j')
    (m1sigma (i + j)) (m1sigma (i' + j')) (m1sigma (j + k))
    (m3c_P_cube_sub_one_ne T) (m3c_R_ne T) (m1_red_den_ne T (i + j))
    (m1_green_den_ne T (j + k)) (m1_red_den_ne T (i' + j'))

/-! ### The realness criterion -/

/-- **Realness criterion**, common-denominator form. -/
theorem m1m_real_key (T : OrientedTriangle E o) {A B NA NB : ℂ} {i j k i' j' : TrisectorLabel}
    (hA : A = NA / m1mD T i j k i' j') (hB : B = NB / m1mD T i j k i' j')
    (h : star NA * NB = NA * star NB) :
    star A * B = A * star B := by
  have hD := m1m_D_ne T i j k i' j'
  have hD' : star (m1mD T i j k i' j') ≠ 0 := by simpa using hD
  have e1 : star A * B
      = star NA * NB / (star (m1mD T i j k i' j') * m1mD T i j k i' j') := by
    rw [hA, hB, star_div₀]
    ring
  have e2 : A * star B
      = NA * star NB / (star (m1mD T i j k i' j') * m1mD T i j k i' j') := by
    rw [hA, hB, star_div₀]
    ring
  rw [e1, e2, h]

/-! ### The monomial values of `m1sigma` -/

theorem m1m_sigma_zero (T : OrientedTriangle E o) : m1sigma (0 : TrisectorLabel) = 1 :=
  m1sigma_zero

theorem m1m_sigma_one (T : OrientedTriangle E o) :
    m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := by
  rw [m1sigma_one, m1_PQR]

theorem m1m_sigma_two (T : OrientedTriangle E o) :
    m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := by
  rw [m1sigma_two, m1_PQR]

/-- Cancellation lemma: a common factor in the two numerators is harmless. -/
theorem m1m_poly_cancel {g NA NB : ℂ} (h : star NA * NB = NA * star NB) :
    star (g * NA) * (g * NB) = (g * NA) * star (g * NB) := by
  rw [star_mul, star_mul]
  calc star NA * star g * (g * NB) = (star g * g) * (star NA * NB) := by ring
    _ = (star g * g) * (NA * star NB) := by rw [h]
    _ = g * NA * (star NB * star g) := by ring





noncomputable section
open scoped Real RealInnerProductSpace ComplexConjugate Matrix
open Function Set


variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable {o : Orientation ℝ E (Fin 2)}


/-! ### Representative `⟨1,1,1⟩`, red join pair `⟨0,2⟩` -/

set_option maxRecDepth 100000 in
noncomputable def m1mNAc_111_02 (T : OrientedTriangle E o) : ℂ :=
  (-m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 11) + m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 8 + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 9 + (-m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 6) + m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 10 + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 7) + (-m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 6) + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 9 + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 6) + (-m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 8) + m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 5 + (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 7) + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 4 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 5 + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 3 + m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 6 + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 8) + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 5 + m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 6 + (-m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 3) + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 4) + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 2) + (-(2 : ℂ) * m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 5) + (-m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 3) + m1P T ^ 3 * m1Q T ^ 2 * m1R T + m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 4 + (2 : ℂ) * m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 2 + (-m1Q T ^ 2 * m1R T)

set_option maxRecDepth 100000 in
noncomputable def m1mNBc_111_02 (T : OrientedTriangle E o) : ℂ :=
  m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 11 + (-m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 8) + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 9) + m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 6 + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 10) + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 9) + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 7 + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 6 + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 8 + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 7 + (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 5) + (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 4) + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 8 + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 5) + (-m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 6) + m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 3

set_option maxRecDepth 100000 in
theorem m1m_hNAc_111_02 (T : OrientedTriangle E o) :
    (m1P T * m1Q T * m1R T) ^ 11 * star (m1mNA T 1 1 1 0 2) = m1mNAc_111_02 T := by
  have hP := m3c_P_ne T
  have hQ := m3c_Q_ne T
  have hR := m3c_R_ne T
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((1 : TrisectorLabel) + 1) = m1P T * m1Q T * m1R T := by
    rw [show ((1 : TrisectorLabel) + 1) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s2 : m1sigma ((1 : TrisectorLabel) + 1) = m1P T * m1Q T * m1R T := by
    rw [show ((1 : TrisectorLabel) + 1) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s3 : m1sigma ((0 : TrisectorLabel) + 2) = m1P T * m1Q T * m1R T := by
    rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide]
    exact m1m_sigma_two T
  unfold m1mNA m1mNAb m1mDrho m1mDgam m1mLamNum m1mLamDen m1mNAc_111_02
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  simp only [
    star_add, star_mul', star_sub, star_neg, star_pow, star_one, star_zero, star_natCast,
    star_ofNat, star_intCast, star_inv, m3c_star_P, m3c_star_Q, m3c_star_R]
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem m1m_hNBc_111_02 (T : OrientedTriangle E o) :
    (m1P T * m1Q T * m1R T) ^ 11 * star (m1mNB T 1 1 1 0 2) = m1mNBc_111_02 T := by
  have hP := m3c_P_ne T
  have hQ := m3c_Q_ne T
  have hR := m3c_R_ne T
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((1 : TrisectorLabel) + 1) = m1P T * m1Q T * m1R T := by
    rw [show ((1 : TrisectorLabel) + 1) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s2 : m1sigma ((1 : TrisectorLabel) + 1) = m1P T * m1Q T * m1R T := by
    rw [show ((1 : TrisectorLabel) + 1) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s3 : m1sigma ((0 : TrisectorLabel) + 2) = m1P T * m1Q T * m1R T := by
    rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide]
    exact m1m_sigma_two T
  unfold m1mNB m1mDrho m1mDgam m1mLamNum m1mNBc_111_02
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  simp only [
    star_add, star_mul', star_sub, star_neg, star_pow, star_one, star_zero, star_natCast,
    star_ofNat, star_intCast, star_inv, m3c_star_P, m3c_star_Q, m3c_star_R]
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem m1m_cert_111_02 (T : OrientedTriangle E o) :
    m1mNAc_111_02 T * m1mNB T 1 1 1 0 2 = m1mNA T 1 1 1 0 2 * m1mNBc_111_02 T := by
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((1 : TrisectorLabel) + 1) = m1P T * m1Q T * m1R T := by
    rw [show ((1 : TrisectorLabel) + 1) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s2 : m1sigma ((1 : TrisectorLabel) + 1) = m1P T * m1Q T * m1R T := by
    rw [show ((1 : TrisectorLabel) + 1) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s3 : m1sigma ((0 : TrisectorLabel) + 2) = m1P T * m1Q T * m1R T := by
    rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide]
    exact m1m_sigma_two T
  unfold m1mNAc_111_02 m1mNBc_111_02 m1mNA m1mNAb m1mNB m1mDrho m1mDgam m1mLamNum m1mLamDen
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  linear_combination (m1P T ^ 18 * m1Q T ^ 17 * m1R T ^ 18 + (-m1P T ^ 18 * m1Q T ^ 17 * m1R T ^ 15) + (-m1P T ^ 17 * m1Q T ^ 15 * m1R T ^ 16) + m1P T ^ 17 * m1Q T ^ 15 * m1R T ^ 13 + (-(3 : ℂ) * m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 17) + (-m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 16) + (-m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 15) + (3 : ℂ) * m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 14 + m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 13 + m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 12 + (-m1P T ^ 15 * m1Q T ^ 17 * m1R T ^ 18) + m1P T ^ 15 * m1Q T ^ 17 * m1R T ^ 15 + m1P T ^ 15 * m1Q T ^ 14 * m1R T ^ 15 + (-m1P T ^ 15 * m1Q T ^ 14 * m1R T ^ 12) + (3 : ℂ) * m1P T ^ 15 * m1Q T ^ 13 * m1R T ^ 15 + m1P T ^ 15 * m1Q T ^ 13 * m1R T ^ 14 + m1P T ^ 15 * m1Q T ^ 13 * m1R T ^ 13 + (-(3 : ℂ) * m1P T ^ 15 * m1Q T ^ 13 * m1R T ^ 12) + (-m1P T ^ 15 * m1Q T ^ 13 * m1R T ^ 11) + (-m1P T ^ 15 * m1Q T ^ 13 * m1R T ^ 10) + m1P T ^ 14 * m1Q T ^ 15 * m1R T ^ 16 + (-m1P T ^ 14 * m1Q T ^ 15 * m1R T ^ 13) + (-m1P T ^ 14 * m1Q T ^ 14 * m1R T ^ 16) + (2 : ℂ) * m1P T ^ 14 * m1Q T ^ 14 * m1R T ^ 13 + (-m1P T ^ 14 * m1Q T ^ 14 * m1R T ^ 10) + (3 : ℂ) * m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 16 + (3 : ℂ) * m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 15 + (3 : ℂ) * m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 14 + (-(2 : ℂ) * m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 13) + (-(3 : ℂ) * m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 12) + (-(3 : ℂ) * m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 11) + (-m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 10) + (-m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 13) + m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 10 + (3 : ℂ) * m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 17 + m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 16 + m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 15 + (-(3 : ℂ) * m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 14) + (-m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 13) + (-m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 12) + m1P T ^ 13 * m1Q T ^ 14 * m1R T ^ 16 + (-(2 : ℂ) * m1P T ^ 13 * m1Q T ^ 14 * m1R T ^ 13) + m1P T ^ 13 * m1Q T ^ 14 * m1R T ^ 10 + (-m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 14) + (-m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 13) + (-m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 12) + (-m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 11) + m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 10 + m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 9 + (2 : ℂ) * m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 8 + (-(3 : ℂ) * m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 14) + (-(3 : ℂ) * m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 13) + (-(3 : ℂ) * m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 12) + (2 : ℂ) * m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 11 + (3 : ℂ) * m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 10 + (3 : ℂ) * m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 9 + m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 8 + (-m1P T ^ 12 * m1Q T ^ 14 * m1R T ^ 15) + m1P T ^ 12 * m1Q T ^ 14 * m1R T ^ 12 + (-(3 : ℂ) * m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 15) + (-m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 14) + (-m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 13) + (3 : ℂ) * m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 12 + m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 11 + m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 15 + (-m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 14) + (-(4 : ℂ) * m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 12) + (2 : ℂ) * m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 11 + (2 : ℂ) * m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 9 + (-m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 8) + (-m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 15) + (-(3 : ℂ) * m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 14) + (-(3 : ℂ) * m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 13) + (-m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 12) + (2 : ℂ) * m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 11 + (3 : ℂ) * m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 9 + m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 8 + (2 : ℂ) * m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 12 + m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 11 + m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 10 + (-m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 9) + (-m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 8) + (-m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 7) + (-m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 6) + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 16) + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 15) + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 14) + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 13 + (3 : ℂ) * m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 12 + (3 : ℂ) * m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 11 + m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 10 + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 15) + m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 13 + (4 : ℂ) * m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 12 + (-m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 10) + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 9) + (-m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 13) + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 10 + (-m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 7) + (-m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 13) + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 12 + (3 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 11 + (6 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 10 + (-m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 9) + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 8) + (-(5 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 7) + (-m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 6) + m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 13 + (3 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 12 + (3 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 11 + m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 10 + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 9) + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 8) + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 7) + (-m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 6) + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 14 + m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 13 + m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 12 + (-m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 11) + (-m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 10) + (-m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 9) + (-m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 8) + (3 : ℂ) * m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 14 + (4 : ℂ) * m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 13 + (3 : ℂ) * m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 12 + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 11) + (-(5 : ℂ) * m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 10) + (-(3 : ℂ) * m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 9) + (-m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 8) + m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 7 + (-m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 14) + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 13 + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 11 + (-(4 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 10) + (-m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 8) + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 7 + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 13 + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 12 + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 11 + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 10 + (-m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 9) + (-(3 : ℂ) * m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 8) + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 7) + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 5 + (-m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 11) + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 10) + (-(3 : ℂ) * m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 9) + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 8) + m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 7 + (3 : ℂ) * m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 6 + (3 : ℂ) * m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 5 + m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 4 + m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 15 + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 14 + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 13 + m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 12 + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 11) + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 10) + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 9) + (-m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 8) + m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 14 + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 12) + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 11) + (-m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 10) + m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 9 + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 8 + m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 7 + m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 6 + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 12 + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 11) + (-(4 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 9) + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 8 + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 6 + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 5) + m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 12 + (-m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 11) + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 10) + (-(5 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 9) + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 8) + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 7 + (4 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 6 + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 5 + (-m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 11) + (-m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 10) + (-m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 9) + (-m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 8) + m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 7 + m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 6 + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 5 + (-m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 13) + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 12) + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 11) + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 10) + m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 9 + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 8 + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 7 + m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 6 + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 13) + (-(5 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 12) + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 11) + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 10) + (6 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 9 + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 8 + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 7 + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 6) + (-m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 12) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 9 + (-m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 6) + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 10) + (-m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 9) + (4 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 7 + m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 6 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 4) + m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 9 + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 8 + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 7 + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 6 + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 5) + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 4) + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 3) + (-m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 13) + (-m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 12) + (-m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 11) + (-m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 10) + m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 9 + m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 8 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 7 + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 11 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 10 + (3 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 9 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 8 + (-m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 7) + (-(3 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 6) + (-(3 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 5) + (-m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 4) + (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 11) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 8 + (-(4 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 7) + (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 5) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 4 + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 9 + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 8 + (3 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 7 + (-m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 6) + (-m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 5) + (-(3 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 4) + m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 7 + (-m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 4) + m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 11 + (3 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 10 + (3 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 9 + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 8 + (-(3 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 7) + (-(3 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 6) + (-(3 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 5) + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 11 + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 10 + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 9 + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 8) + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 7) + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 6) + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 5) + m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 9 + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 6) + m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 3 + (-m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 7) + (-m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 6) + (-(3 : ℂ) * m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 5) + m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 4 + m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 3 + (3 : ℂ) * m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 2 + m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 9 + (-m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 6) + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 9) + (-(3 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 8) + (-(3 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 7) + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 6) + (3 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 5 + (3 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 4 + (3 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 3 + (-m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 9) + (2 : ℂ) * m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 6 + (-m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 3) + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 6) + m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 3 + (-m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 9) + (-m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 8) + (-(3 : ℂ) * m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 7) + m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 6 + m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 5 + (3 : ℂ) * m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 4 + (-m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 7) + m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 4 + m1P T ^ 4 * m1Q T ^ 2 * m1R T ^ 4 + (-m1P T ^ 4 * m1Q T ^ 2 * m1R T) + m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 7 + m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 6 + (3 : ℂ) * m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 5 + (-m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 4) + (-m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 3) + (-(3 : ℂ) * m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 2) + m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 6 + (-m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 3) + (-m1P T * m1Q T ^ 2 * m1R T ^ 4) + m1P T * m1Q T ^ 2 * m1R T) * (m1m_three T)

set_option maxRecDepth 100000 in
theorem m1m_poly_111_02 (T : OrientedTriangle E o) :
    star (m1mNA T 1 1 1 0 2) * m1mNB T 1 1 1 0 2 = m1mNA T 1 1 1 0 2 * star (m1mNB T 1 1 1 0 2) := by
  have hK : (m1P T * m1Q T * m1R T) ^ 11 ≠ 0 :=
    pow_ne_zero 11 (mul_ne_zero (mul_ne_zero (m3c_P_ne T) (m3c_Q_ne T)) (m3c_R_ne T))
  refine mul_left_cancel₀ hK ?_
  calc (m1P T * m1Q T * m1R T) ^ 11 * (star (m1mNA T 1 1 1 0 2) * m1mNB T 1 1 1 0 2)
      = ((m1P T * m1Q T * m1R T) ^ 11 * star (m1mNA T 1 1 1 0 2)) * m1mNB T 1 1 1 0 2 := by ring
    _ = m1mNAc_111_02 T * m1mNB T 1 1 1 0 2 := by rw [m1m_hNAc_111_02 T]
    _ = m1mNA T 1 1 1 0 2 * m1mNBc_111_02 T := m1m_cert_111_02 T
    _ = m1mNA T 1 1 1 0 2 * ((m1P T * m1Q T * m1R T) ^ 11 * star (m1mNB T 1 1 1 0 2)) := by rw [m1m_hNBc_111_02 T]
    _ = (m1P T * m1Q T * m1R T) ^ 11 * (m1mNA T 1 1 1 0 2 * star (m1mNB T 1 1 1 0 2)) := by ring

theorem m1m_real_111_02 (T : OrientedTriangle E o) :
    star (m3cA T 1 1 1) * m3cB T 1 1 0 2
      = m3cA T 1 1 1 * star (m3cB T 1 1 0 2) :=
  m1m_real_key T (m1m_A_frac T 1 1 1 0 2) (m1m_B_frac T 1 1 1 0 2) (m1m_poly_111_02 T)

/-! ### Representative `⟨2,2,2⟩`, red join pair `⟨1,0⟩` -/

set_option maxRecDepth 100000 in
noncomputable def m1mNAc_222_10 (T : OrientedTriangle E o) : ℂ :=
  (-m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 11) + m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 8 + (-m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 7) + m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 10 + (-m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 7) + m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 8 + m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 9 + (-m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 6) + m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 7 + (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 7) + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 4 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 5 + (-m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 5) + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 8) + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 5 + (-m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 6) + (-m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 3) + (-(2 : ℂ) * m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 5) + m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 5 + (-m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 2) + (-m1P T ^ 4 * m1Q T ^ 3 * m1R T ^ 3) + (2 : ℂ) * m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 3 + m1P T ^ 3 * m1Q T ^ 2 * m1R T + m1P T * m1Q T ^ 3 * m1R T ^ 3 + (-m1Q T ^ 2 * m1R T)

set_option maxRecDepth 100000 in
noncomputable def m1mNBc_222_10 (T : OrientedTriangle E o) : ℂ :=
  (-m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 10) + m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 7 + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 9 + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 6) + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 7 + (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 4) + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 8 + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 5) + (-m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 6) + m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 3 + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 7) + m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 4 + (-m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 5) + m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 2 + m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 4 + (-m1P T ^ 3 * m1Q T ^ 3 * m1R T)

set_option maxRecDepth 100000 in
theorem m1m_hNAc_222_10 (T : OrientedTriangle E o) :
    (m1P T * m1Q T * m1R T) ^ 11 * star (m1mNA T 2 2 2 1 0) = m1mNAc_222_10 T := by
  have hP := m3c_P_ne T
  have hQ := m3c_Q_ne T
  have hR := m3c_R_ne T
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((2 : TrisectorLabel) + 2) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s2 : m1sigma ((2 : TrisectorLabel) + 2) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s3 : m1sigma ((1 : TrisectorLabel) + 0) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((1 : TrisectorLabel) + 0) = 1 from by decide]
    exact m1m_sigma_one T
  unfold m1mNA m1mNAb m1mDrho m1mDgam m1mLamNum m1mLamDen m1mNAc_222_10
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  simp only [
    star_add, star_mul', star_sub, star_neg, star_pow, star_one, star_zero, star_natCast,
    star_ofNat, star_intCast, star_inv, m3c_star_P, m3c_star_Q, m3c_star_R]
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem m1m_hNBc_222_10 (T : OrientedTriangle E o) :
    (m1P T * m1Q T * m1R T) ^ 11 * star (m1mNB T 2 2 2 1 0) = m1mNBc_222_10 T := by
  have hP := m3c_P_ne T
  have hQ := m3c_Q_ne T
  have hR := m3c_R_ne T
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((2 : TrisectorLabel) + 2) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s2 : m1sigma ((2 : TrisectorLabel) + 2) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s3 : m1sigma ((1 : TrisectorLabel) + 0) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((1 : TrisectorLabel) + 0) = 1 from by decide]
    exact m1m_sigma_one T
  unfold m1mNB m1mDrho m1mDgam m1mLamNum m1mNBc_222_10
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  simp only [
    star_add, star_mul', star_sub, star_neg, star_pow, star_one, star_zero, star_natCast,
    star_ofNat, star_intCast, star_inv, m3c_star_P, m3c_star_Q, m3c_star_R]
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem m1m_cert_222_10 (T : OrientedTriangle E o) :
    m1mNAc_222_10 T * m1mNB T 2 2 2 1 0 = m1mNA T 2 2 2 1 0 * m1mNBc_222_10 T := by
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((2 : TrisectorLabel) + 2) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s2 : m1sigma ((2 : TrisectorLabel) + 2) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s3 : m1sigma ((1 : TrisectorLabel) + 0) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((1 : TrisectorLabel) + 0) = 1 from by decide]
    exact m1m_sigma_one T
  unfold m1mNAc_222_10 m1mNBc_222_10 m1mNA m1mNAb m1mNB m1mDrho m1mDgam m1mLamNum m1mLamDen
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  linear_combination ((-m1P T ^ 17 * m1Q T ^ 16 * m1R T ^ 17) + m1P T ^ 17 * m1Q T ^ 16 * m1R T ^ 14 + m1P T ^ 16 * m1Q T ^ 16 * m1R T ^ 18 + (-(2 : ℂ) * m1P T ^ 16 * m1Q T ^ 16 * m1R T ^ 15) + m1P T ^ 16 * m1Q T ^ 16 * m1R T ^ 12 + m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 16 + m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 15 + (-m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 13) + (-m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 12) + (-m1P T ^ 15 * m1Q T ^ 15 * m1R T ^ 17) + (2 : ℂ) * m1P T ^ 15 * m1Q T ^ 15 * m1R T ^ 14 + (-m1P T ^ 15 * m1Q T ^ 15 * m1R T ^ 11) + m1P T ^ 15 * m1Q T ^ 13 * m1R T ^ 14 + (-m1P T ^ 15 * m1Q T ^ 13 * m1R T ^ 11) + m1P T ^ 14 * m1Q T ^ 16 * m1R T ^ 17 + (-m1P T ^ 14 * m1Q T ^ 16 * m1R T ^ 14) + (-m1P T ^ 14 * m1Q T ^ 15 * m1R T ^ 17) + (2 : ℂ) * m1P T ^ 14 * m1Q T ^ 15 * m1R T ^ 14 + (-m1P T ^ 14 * m1Q T ^ 15 * m1R T ^ 11) + m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 15 + (-m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 14) + (-m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 13) + m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 11 + m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 10 + (-m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 9) + (-m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 13) + (-m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 12) + m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 10 + m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 9 + (-m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 16) + (-m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 15) + m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 13 + m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 12 + (-(2 : ℂ) * m1P T ^ 13 * m1Q T ^ 13 * m1R T ^ 16) + m1P T ^ 13 * m1Q T ^ 13 * m1R T ^ 15 + (4 : ℂ) * m1P T ^ 13 * m1Q T ^ 13 * m1R T ^ 13 + (-(2 : ℂ) * m1P T ^ 13 * m1Q T ^ 13 * m1R T ^ 12) + (-(2 : ℂ) * m1P T ^ 13 * m1Q T ^ 13 * m1R T ^ 10) + m1P T ^ 13 * m1Q T ^ 13 * m1R T ^ 9 + (-m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 14) + (-(2 : ℂ) * m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 13) + m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 12 + (2 : ℂ) * m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 10 + (-m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 9) + m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 8 + m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 15 + (-m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 14) + (-(2 : ℂ) * m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 12) + m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 11 + m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 9 + (2 : ℂ) * m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 15 + m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 14 + (-(4 : ℂ) * m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 12) + (-(2 : ℂ) * m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 11) + (2 : ℂ) * m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 9 + m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 8 + (-(2 : ℂ) * m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 12) + m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 11 + m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 9 + (-m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 8) + (-m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 7) + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 15) + m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 14 + m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 13 + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 12 + (-m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 11) + (-m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 10) + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 15 + (-m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 14) + m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 13 + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 12) + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 11 + (-m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 10) + m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 9 + (-m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 8) + m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 13 + m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 12 + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 11 + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 10) + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 8) + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 7 + (-m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 6) + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 11 + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 10 + (-m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 9) + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 8) + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 7) + m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 6 + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 14 + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 13 + (-m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 12) + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 11) + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 10) + m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 9 + m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 14 + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 13) + (-m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 12) + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 11) + (4 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 9 + m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 8 + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 7) + (-m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 6) + (-m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 12) + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 11 + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 10) + (3 : ℂ) * m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 9 + (-m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 8) + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 7 + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 6) + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 13) + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 12 + (-m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 11) + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 10 + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 9) + m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 8 + (-m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 7) + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 13) + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 12) + m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 11 + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 10 + (4 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 9 + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 8) + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 7) + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 6) + m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 5 + m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 10 + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 9) + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 8) + (-m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 7) + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 6 + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 5 + m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 13 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 12) + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 11) + (-m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 10) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 9 + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 8 + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 13) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 12 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 11) + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 9) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 8 + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 7 + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 6 + (-m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 11) + m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 10 + (-m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 9) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 8 + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 7) + m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 6 + (-m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 5) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 4 + (-m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 9) + (-m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 8) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 7 + m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 6 + m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 5 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 4) + (-m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 12) + (-m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 11) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 10 + m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 9 + m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 8 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 7) + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 11 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 10 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 8) + (-(4 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 7) + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 5 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 4 + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 10 + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 8 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 7) + (-m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 5) + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 4 + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 11 + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 10) + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 9 + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 7 + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 6) + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 5) + m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 10 + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 9) + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 7) + (4 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 6 + m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 4 + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 3) + m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 7 + m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 6 + (-m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 4) + (-m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 3) + m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 10 + m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 9 + (-m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 7) + (-m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 6) + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 10) + m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 9 + m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 8 + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 6) + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 5) + m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 4 + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 8) + (2 : ℂ) * m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 5 + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 2) + (-m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 5) + m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 2 + (-m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 8) + m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 5 + (-m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 8) + (2 : ℂ) * m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 5 + (-m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 2) + (-m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 7) + (-m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 6) + m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 4 + m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 3 + m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 7 + (-(2 : ℂ) * m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 4) + m1P T ^ 3 * m1Q T ^ 3 * m1R T + m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 5 + (-m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 2)) * (m1m_three T)

set_option maxRecDepth 100000 in
theorem m1m_poly_222_10 (T : OrientedTriangle E o) :
    star (m1mNA T 2 2 2 1 0) * m1mNB T 2 2 2 1 0 = m1mNA T 2 2 2 1 0 * star (m1mNB T 2 2 2 1 0) := by
  have hK : (m1P T * m1Q T * m1R T) ^ 11 ≠ 0 :=
    pow_ne_zero 11 (mul_ne_zero (mul_ne_zero (m3c_P_ne T) (m3c_Q_ne T)) (m3c_R_ne T))
  refine mul_left_cancel₀ hK ?_
  calc (m1P T * m1Q T * m1R T) ^ 11 * (star (m1mNA T 2 2 2 1 0) * m1mNB T 2 2 2 1 0)
      = ((m1P T * m1Q T * m1R T) ^ 11 * star (m1mNA T 2 2 2 1 0)) * m1mNB T 2 2 2 1 0 := by ring
    _ = m1mNAc_222_10 T * m1mNB T 2 2 2 1 0 := by rw [m1m_hNAc_222_10 T]
    _ = m1mNA T 2 2 2 1 0 * m1mNBc_222_10 T := m1m_cert_222_10 T
    _ = m1mNA T 2 2 2 1 0 * ((m1P T * m1Q T * m1R T) ^ 11 * star (m1mNB T 2 2 2 1 0)) := by rw [m1m_hNBc_222_10 T]
    _ = (m1P T * m1Q T * m1R T) ^ 11 * (m1mNA T 2 2 2 1 0 * star (m1mNB T 2 2 2 1 0)) := by ring

theorem m1m_real_222_10 (T : OrientedTriangle E o) :
    star (m3cA T 2 2 2) * m3cB T 2 2 1 0
      = m3cA T 2 2 2 * star (m3cB T 2 2 1 0) :=
  m1m_real_key T (m1m_A_frac T 2 2 2 1 0) (m1m_B_frac T 2 2 2 1 0) (m1m_poly_222_10 T)

/-! ### Representative `⟨0,1,2⟩`, red join pair `⟨2,2⟩` -/

set_option maxRecDepth 100000 in
noncomputable def m1mNAc_012_22 (T : OrientedTriangle E o) : ℂ :=
  (-m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 12) + m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 9 + m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 11 + (-m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 8) + m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 12 + (-m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 9) + (-m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 11) + m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 8 + (-m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 7) + m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 10 + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 7) + (-m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 9) + m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 6 + m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 5 + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 10) + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 7 + m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 9 + (-m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 6) + m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 7 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 5 + (-m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 5) + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 3) + (-(2 : ℂ) * m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 5) + (-m1P T ^ 4 * m1Q T ^ 3 * m1R T ^ 3) + (2 : ℂ) * m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 3 + m1P T ^ 3 * m1Q T ^ 2 * m1R T + m1P T * m1Q T ^ 3 * m1R T ^ 3 + (-m1Q T ^ 2 * m1R T)

set_option maxRecDepth 100000 in
noncomputable def m1mNBc_012_22 (T : OrientedTriangle E o) : ℂ :=
  (-m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 12) + m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 9 + m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 11 + (-m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 8) + m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 11 + (-m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 8) + (-m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 10) + m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 7 + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 10 + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 7) + (-m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 9) + m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 6 + (-m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 9) + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 6 + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 8 + (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 5)

set_option maxRecDepth 100000 in
theorem m1m_hNAc_012_22 (T : OrientedTriangle E o) :
    (m1P T * m1Q T * m1R T) ^ 12 * star (m1mNA T 0 1 2 2 2) = m1mNAc_012_22 T := by
  have hP := m3c_P_ne T
  have hQ := m3c_Q_ne T
  have hR := m3c_R_ne T
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((0 : TrisectorLabel) + 1) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((0 : TrisectorLabel) + 1) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s2 : m1sigma ((1 : TrisectorLabel) + 2) = 1 := by
    rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide]
    exact m1m_sigma_zero T
  have h_s3 : m1sigma ((2 : TrisectorLabel) + 2) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide]
    exact m1m_sigma_one T
  unfold m1mNA m1mNAb m1mDrho m1mDgam m1mLamNum m1mLamDen m1mNAc_012_22
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  simp only [
    star_add, star_mul', star_sub, star_neg, star_pow, star_one, star_zero, star_natCast,
    star_ofNat, star_intCast, star_inv, m3c_star_P, m3c_star_Q, m3c_star_R]
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem m1m_hNBc_012_22 (T : OrientedTriangle E o) :
    (m1P T * m1Q T * m1R T) ^ 12 * star (m1mNB T 0 1 2 2 2) = m1mNBc_012_22 T := by
  have hP := m3c_P_ne T
  have hQ := m3c_Q_ne T
  have hR := m3c_R_ne T
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((0 : TrisectorLabel) + 1) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((0 : TrisectorLabel) + 1) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s2 : m1sigma ((1 : TrisectorLabel) + 2) = 1 := by
    rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide]
    exact m1m_sigma_zero T
  have h_s3 : m1sigma ((2 : TrisectorLabel) + 2) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide]
    exact m1m_sigma_one T
  unfold m1mNB m1mDrho m1mDgam m1mLamNum m1mNBc_012_22
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  simp only [
    star_add, star_mul', star_sub, star_neg, star_pow, star_one, star_zero, star_natCast,
    star_ofNat, star_intCast, star_inv, m3c_star_P, m3c_star_Q, m3c_star_R]
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem m1m_cert_012_22 (T : OrientedTriangle E o) :
    m1mNAc_012_22 T * m1mNB T 0 1 2 2 2 = m1mNA T 0 1 2 2 2 * m1mNBc_012_22 T := by
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((0 : TrisectorLabel) + 1) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((0 : TrisectorLabel) + 1) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s2 : m1sigma ((1 : TrisectorLabel) + 2) = 1 := by
    rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide]
    exact m1m_sigma_zero T
  have h_s3 : m1sigma ((2 : TrisectorLabel) + 2) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide]
    exact m1m_sigma_one T
  unfold m1mNAc_012_22 m1mNBc_012_22 m1mNA m1mNAb m1mNB m1mDrho m1mDgam m1mLamNum m1mLamDen
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  linear_combination ((-m1P T ^ 20 * m1Q T ^ 19 * m1R T ^ 20) + m1P T ^ 20 * m1Q T ^ 19 * m1R T ^ 17 + m1P T ^ 20 * m1Q T ^ 18 * m1R T ^ 19 + (-m1P T ^ 20 * m1Q T ^ 18 * m1R T ^ 16) + m1P T ^ 19 * m1Q T ^ 18 * m1R T ^ 19 + m1P T ^ 19 * m1Q T ^ 18 * m1R T ^ 18 + (-m1P T ^ 19 * m1Q T ^ 18 * m1R T ^ 16) + (-m1P T ^ 19 * m1Q T ^ 18 * m1R T ^ 15) + (-m1P T ^ 19 * m1Q T ^ 17 * m1R T ^ 18) + (-m1P T ^ 19 * m1Q T ^ 17 * m1R T ^ 17) + m1P T ^ 19 * m1Q T ^ 17 * m1R T ^ 15 + m1P T ^ 19 * m1Q T ^ 17 * m1R T ^ 14 + (-m1P T ^ 18 * m1Q T ^ 17 * m1R T ^ 17) + m1P T ^ 18 * m1Q T ^ 17 * m1R T ^ 14 + m1P T ^ 18 * m1Q T ^ 16 * m1R T ^ 16 + (-m1P T ^ 18 * m1Q T ^ 16 * m1R T ^ 13) + m1P T ^ 17 * m1Q T ^ 19 * m1R T ^ 20 + (-m1P T ^ 17 * m1Q T ^ 19 * m1R T ^ 17) + (-m1P T ^ 17 * m1Q T ^ 18 * m1R T ^ 19) + m1P T ^ 17 * m1Q T ^ 18 * m1R T ^ 16 + (3 : ℂ) * m1P T ^ 17 * m1Q T ^ 16 * m1R T ^ 18 + (-m1P T ^ 17 * m1Q T ^ 16 * m1R T ^ 17) + (-(3 : ℂ) * m1P T ^ 17 * m1Q T ^ 16 * m1R T ^ 15) + m1P T ^ 17 * m1Q T ^ 16 * m1R T ^ 14 + (-(3 : ℂ) * m1P T ^ 17 * m1Q T ^ 15 * m1R T ^ 17) + m1P T ^ 17 * m1Q T ^ 15 * m1R T ^ 16 + (3 : ℂ) * m1P T ^ 17 * m1Q T ^ 15 * m1R T ^ 14 + (-m1P T ^ 17 * m1Q T ^ 15 * m1R T ^ 13) + (-m1P T ^ 16 * m1Q T ^ 18 * m1R T ^ 19) + (-m1P T ^ 16 * m1Q T ^ 18 * m1R T ^ 18) + m1P T ^ 16 * m1Q T ^ 18 * m1R T ^ 16 + m1P T ^ 16 * m1Q T ^ 18 * m1R T ^ 15 + m1P T ^ 16 * m1Q T ^ 17 * m1R T ^ 18 + m1P T ^ 16 * m1Q T ^ 17 * m1R T ^ 17 + (-m1P T ^ 16 * m1Q T ^ 17 * m1R T ^ 15) + (-m1P T ^ 16 * m1Q T ^ 17 * m1R T ^ 14) + (-(3 : ℂ) * m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 17) + (-(2 : ℂ) * m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 16) + m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 15 + (3 : ℂ) * m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 14 + (2 : ℂ) * m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 13 + (-m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 12) + (3 : ℂ) * m1P T ^ 16 * m1Q T ^ 14 * m1R T ^ 16 + (2 : ℂ) * m1P T ^ 16 * m1Q T ^ 14 * m1R T ^ 15 + (-m1P T ^ 16 * m1Q T ^ 14 * m1R T ^ 14) + (-(3 : ℂ) * m1P T ^ 16 * m1Q T ^ 14 * m1R T ^ 13) + (-(2 : ℂ) * m1P T ^ 16 * m1Q T ^ 14 * m1R T ^ 12) + m1P T ^ 16 * m1Q T ^ 14 * m1R T ^ 11 + m1P T ^ 15 * m1Q T ^ 17 * m1R T ^ 17 + (-m1P T ^ 15 * m1Q T ^ 17 * m1R T ^ 14) + (-m1P T ^ 15 * m1Q T ^ 16 * m1R T ^ 16) + m1P T ^ 15 * m1Q T ^ 16 * m1R T ^ 13 + (3 : ℂ) * m1P T ^ 15 * m1Q T ^ 14 * m1R T ^ 15 + (-m1P T ^ 15 * m1Q T ^ 14 * m1R T ^ 14) + (-(3 : ℂ) * m1P T ^ 15 * m1Q T ^ 14 * m1R T ^ 12) + m1P T ^ 15 * m1Q T ^ 14 * m1R T ^ 11 + (-(3 : ℂ) * m1P T ^ 15 * m1Q T ^ 13 * m1R T ^ 14) + m1P T ^ 15 * m1Q T ^ 13 * m1R T ^ 13 + (3 : ℂ) * m1P T ^ 15 * m1Q T ^ 13 * m1R T ^ 11 + (-m1P T ^ 15 * m1Q T ^ 13 * m1R T ^ 10) + (-(3 : ℂ) * m1P T ^ 14 * m1Q T ^ 16 * m1R T ^ 18) + m1P T ^ 14 * m1Q T ^ 16 * m1R T ^ 17 + (3 : ℂ) * m1P T ^ 14 * m1Q T ^ 16 * m1R T ^ 15 + (-m1P T ^ 14 * m1Q T ^ 16 * m1R T ^ 14) + (3 : ℂ) * m1P T ^ 14 * m1Q T ^ 15 * m1R T ^ 17 + (-m1P T ^ 14 * m1Q T ^ 15 * m1R T ^ 16) + (-(3 : ℂ) * m1P T ^ 14 * m1Q T ^ 15 * m1R T ^ 14) + m1P T ^ 14 * m1Q T ^ 15 * m1R T ^ 13 + m1P T ^ 14 * m1Q T ^ 14 * m1R T ^ 16 + (-(2 : ℂ) * m1P T ^ 14 * m1Q T ^ 14 * m1R T ^ 13) + m1P T ^ 14 * m1Q T ^ 14 * m1R T ^ 10 + (-(3 : ℂ) * m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 16) + m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 15 + (-m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 14) + (3 : ℂ) * m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 13 + m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 12 + m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 11 + (-(2 : ℂ) * m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 9) + (3 : ℂ) * m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 15 + (-(2 : ℂ) * m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 14) + m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 13 + (-(3 : ℂ) * m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 12) + m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 11 + (-m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 10) + m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 8 + (3 : ℂ) * m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 17 + (2 : ℂ) * m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 16 + (-m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 15) + (-(3 : ℂ) * m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 14) + (-(2 : ℂ) * m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 13) + m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 12 + (-(4 : ℂ) * m1P T ^ 13 * m1Q T ^ 14 * m1R T ^ 16) + (-(2 : ℂ) * m1P T ^ 13 * m1Q T ^ 14 * m1R T ^ 15) + m1P T ^ 13 * m1Q T ^ 14 * m1R T ^ 14 + (5 : ℂ) * m1P T ^ 13 * m1Q T ^ 14 * m1R T ^ 13 + (2 : ℂ) * m1P T ^ 13 * m1Q T ^ 14 * m1R T ^ 12 + (-m1P T ^ 13 * m1Q T ^ 14 * m1R T ^ 11) + (-m1P T ^ 13 * m1Q T ^ 14 * m1R T ^ 10) + m1P T ^ 13 * m1Q T ^ 13 * m1R T ^ 15 + (-(2 : ℂ) * m1P T ^ 13 * m1Q T ^ 13 * m1R T ^ 12) + m1P T ^ 13 * m1Q T ^ 13 * m1R T ^ 9 + (3 : ℂ) * m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 15 + m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 14 + (-(2 : ℂ) * m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 13) + (-(2 : ℂ) * m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 12) + (-(2 : ℂ) * m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 11) + (2 : ℂ) * m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 10 + (-m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 9) + m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 8 + (-(3 : ℂ) * m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 14) + (-m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 13) + (2 : ℂ) * m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 12 + (2 : ℂ) * m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 11 + (2 : ℂ) * m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 10 + (-(2 : ℂ) * m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 9) + m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 8 + (-m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 7) + (-(3 : ℂ) * m1P T ^ 12 * m1Q T ^ 14 * m1R T ^ 15) + m1P T ^ 12 * m1Q T ^ 14 * m1R T ^ 14 + (3 : ℂ) * m1P T ^ 12 * m1Q T ^ 14 * m1R T ^ 12 + (-m1P T ^ 12 * m1Q T ^ 14 * m1R T ^ 11) + (3 : ℂ) * m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 14 + (-m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 13) + (-(3 : ℂ) * m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 11) + m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 10 + (-(3 : ℂ) * m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 13) + (3 : ℂ) * m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 12 + (3 : ℂ) * m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 10 + (-(3 : ℂ) * m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 9) + (3 : ℂ) * m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 12 + (-(3 : ℂ) * m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 11) + (-(3 : ℂ) * m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 9) + (3 : ℂ) * m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 8 + (3 : ℂ) * m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 16 + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 15) + m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 14 + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 13) + m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 12 + (-m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 11) + m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 9 + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 15) + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 14 + (-m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 13) + (3 : ℂ) * m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 12 + (-m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 11) + m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 10 + (-m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 8) + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 14) + (4 : ℂ) * m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 11 + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 8) + m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 14 + m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 13 + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 12 + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 11) + (-(6 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 10) + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 9) + m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 8 + (5 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 7 + (-m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 13) + m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 12 + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 11) + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 9 + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 8 + (-m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 7) + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 6) + (-(3 : ℂ) * m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 15) + (-m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 14) + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 13 + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 12 + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 11 + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 10) + m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 9 + (-m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 8) + (5 : ℂ) * m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 14 + m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 13 + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 12) + (-(6 : ℂ) * m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 11) + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 10) + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 9 + m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 8 + m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 7 + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 13) + (4 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 10 + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 7) + (-m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 13) + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 11 + (-m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 10) + (3 : ℂ) * m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 9 + (-m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 8) + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 7 + (-(3 : ℂ) * m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 6) + m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 12 + (-m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 10) + m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 9 + (-(3 : ℂ) * m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 8) + m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 7 + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 6) + (3 : ℂ) * m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 5 + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 13 + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 12) + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 10) + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 9 + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 12) + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 11 + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 9 + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 8) + m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 11 + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 10) + (-m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 8) + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 7 + (-m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 10) + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 9 + m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 7 + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 6) + (-m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 14) + m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 13 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 12) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 11 + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 9 + (-m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 8) + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 7) + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 13 + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 12) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 11 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 10) + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 9) + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 8) + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 7 + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 6 + m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 12 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 9) + m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 6 + (-m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 11) + (-m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 10) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 9 + (5 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 8 + m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 7 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 6) + (-(4 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 5) + m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 9 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 8) + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 7) + (-m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 6) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 5 + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 4 + m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 13 + (-m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 11) + m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 10 + (-(3 : ℂ) * m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 9) + m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 8 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 7) + (3 : ℂ) * m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 6 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 12) + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 10 + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 9 + (3 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 8 + (-m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 7) + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 6 + (-(3 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 5) + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 11 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 8) + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 5 + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 8 + (-(3 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 7) + (-m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 5) + (3 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 4 + (-m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 7) + (3 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 6 + m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 4 + (-(3 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 3) + (-m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 11) + (3 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 10 + m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 8 + (-(3 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 7) + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 10 + (-(3 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 9) + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 7) + (3 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 6 + m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 8 + (-m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 5) + (-m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 7) + m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 4 + m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 10 + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 9) + (-(3 : ℂ) * m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 8) + (-m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 7) + (2 : ℂ) * m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 6 + (3 : ℂ) * m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 5 + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 9) + (2 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 8 + (3 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 7 + m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 6 + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 5) + (-(3 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 4) + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 7) + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 6) + m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 4 + m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 3 + m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 6 + m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 5 + (-m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 3) + (-m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 2) + (-m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 8) + (3 : ℂ) * m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 7 + m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 5 + (-(3 : ℂ) * m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 4) + m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 7 + (-(3 : ℂ) * m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 6) + (-m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 4) + (3 : ℂ) * m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 3 + m1P T ^ 4 * m1Q T ^ 3 * m1R T ^ 5 + (-m1P T ^ 4 * m1Q T ^ 3 * m1R T ^ 2) + (-m1P T ^ 4 * m1Q T ^ 2 * m1R T ^ 4) + m1P T ^ 4 * m1Q T ^ 2 * m1R T + (-m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 8) + m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 5 + m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 7 + (-m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 4) + m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 7 + m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 6 + (-m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 4) + (-m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 3) + (-m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 6) + (-m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 5) + m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 3 + m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 2 + (-m1P T * m1Q T ^ 3 * m1R T ^ 5) + m1P T * m1Q T ^ 3 * m1R T ^ 2 + m1P T * m1Q T ^ 2 * m1R T ^ 4 + (-m1P T * m1Q T ^ 2 * m1R T)) * (m1m_three T)

set_option maxRecDepth 100000 in
theorem m1m_poly_012_22 (T : OrientedTriangle E o) :
    star (m1mNA T 0 1 2 2 2) * m1mNB T 0 1 2 2 2 = m1mNA T 0 1 2 2 2 * star (m1mNB T 0 1 2 2 2) := by
  have hK : (m1P T * m1Q T * m1R T) ^ 12 ≠ 0 :=
    pow_ne_zero 12 (mul_ne_zero (mul_ne_zero (m3c_P_ne T) (m3c_Q_ne T)) (m3c_R_ne T))
  refine mul_left_cancel₀ hK ?_
  calc (m1P T * m1Q T * m1R T) ^ 12 * (star (m1mNA T 0 1 2 2 2) * m1mNB T 0 1 2 2 2)
      = ((m1P T * m1Q T * m1R T) ^ 12 * star (m1mNA T 0 1 2 2 2)) * m1mNB T 0 1 2 2 2 := by ring
    _ = m1mNAc_012_22 T * m1mNB T 0 1 2 2 2 := by rw [m1m_hNAc_012_22 T]
    _ = m1mNA T 0 1 2 2 2 * m1mNBc_012_22 T := m1m_cert_012_22 T
    _ = m1mNA T 0 1 2 2 2 * ((m1P T * m1Q T * m1R T) ^ 12 * star (m1mNB T 0 1 2 2 2)) := by rw [m1m_hNBc_012_22 T]
    _ = (m1P T * m1Q T * m1R T) ^ 12 * (m1mNA T 0 1 2 2 2 * star (m1mNB T 0 1 2 2 2)) := by ring

theorem m1m_real_012_22 (T : OrientedTriangle E o) :
    star (m3cA T 0 1 2) * m3cB T 0 1 2 2
      = m3cA T 0 1 2 * star (m3cB T 0 1 2 2) :=
  m1m_real_key T (m1m_A_frac T 0 1 2 2 2) (m1m_B_frac T 0 1 2 2 2) (m1m_poly_012_22 T)

/-! ### Representative `⟨0,2,1⟩`, red join pair `⟨2,0⟩` -/

set_option maxRecDepth 100000 in
noncomputable def m1mNAc_021_20 (T : OrientedTriangle E o) : ℂ :=
  (-m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 10) + m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 7 + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 9 + (-m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 6) + m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 10 + (-m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 7) + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 9) + m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 6 + (-m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 6) + m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 9 + (-m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 6) + (-m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 8) + m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 5 + (-m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 9) + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 6 + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 8 + (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 5) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 5 + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 3 + m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 6 + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 4) + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 2) + (-(2 : ℂ) * m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 5) + (-m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 3) + m1P T ^ 3 * m1Q T ^ 2 * m1R T + m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 4 + (2 : ℂ) * m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 2 + (-m1Q T ^ 2 * m1R T)

set_option maxRecDepth 100000 in
noncomputable def m1mNBc_021_20 (T : OrientedTriangle E o) : ℂ :=
  (-m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 10) + m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 7 + m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 9 + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 6) + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 9 + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 6) + (-m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 8) + m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 5 + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 9 + (-m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 6) + (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 8) + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 5 + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 8) + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 5 + m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 7 + (-m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 4)

set_option maxRecDepth 100000 in
theorem m1m_hNAc_021_20 (T : OrientedTriangle E o) :
    (m1P T * m1Q T * m1R T) ^ 10 * star (m1mNA T 0 2 1 2 0) = m1mNAc_021_20 T := by
  have hP := m3c_P_ne T
  have hQ := m3c_Q_ne T
  have hR := m3c_R_ne T
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((0 : TrisectorLabel) + 2) = m1P T * m1Q T * m1R T := by
    rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s2 : m1sigma ((2 : TrisectorLabel) + 1) = 1 := by
    rw [show ((2 : TrisectorLabel) + 1) = 0 from by decide]
    exact m1m_sigma_zero T
  have h_s3 : m1sigma ((2 : TrisectorLabel) + 0) = m1P T * m1Q T * m1R T := by
    rw [show ((2 : TrisectorLabel) + 0) = 2 from by decide]
    exact m1m_sigma_two T
  unfold m1mNA m1mNAb m1mDrho m1mDgam m1mLamNum m1mLamDen m1mNAc_021_20
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  simp only [
    star_add, star_mul', star_sub, star_neg, star_pow, star_one, star_zero, star_natCast,
    star_ofNat, star_intCast, star_inv, m3c_star_P, m3c_star_Q, m3c_star_R]
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem m1m_hNBc_021_20 (T : OrientedTriangle E o) :
    (m1P T * m1Q T * m1R T) ^ 10 * star (m1mNB T 0 2 1 2 0) = m1mNBc_021_20 T := by
  have hP := m3c_P_ne T
  have hQ := m3c_Q_ne T
  have hR := m3c_R_ne T
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((0 : TrisectorLabel) + 2) = m1P T * m1Q T * m1R T := by
    rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s2 : m1sigma ((2 : TrisectorLabel) + 1) = 1 := by
    rw [show ((2 : TrisectorLabel) + 1) = 0 from by decide]
    exact m1m_sigma_zero T
  have h_s3 : m1sigma ((2 : TrisectorLabel) + 0) = m1P T * m1Q T * m1R T := by
    rw [show ((2 : TrisectorLabel) + 0) = 2 from by decide]
    exact m1m_sigma_two T
  unfold m1mNB m1mDrho m1mDgam m1mLamNum m1mNBc_021_20
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  simp only [
    star_add, star_mul', star_sub, star_neg, star_pow, star_one, star_zero, star_natCast,
    star_ofNat, star_intCast, star_inv, m3c_star_P, m3c_star_Q, m3c_star_R]
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem m1m_cert_021_20 (T : OrientedTriangle E o) :
    m1mNAc_021_20 T * m1mNB T 0 2 1 2 0 = m1mNA T 0 2 1 2 0 * m1mNBc_021_20 T := by
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((0 : TrisectorLabel) + 2) = m1P T * m1Q T * m1R T := by
    rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s2 : m1sigma ((2 : TrisectorLabel) + 1) = 1 := by
    rw [show ((2 : TrisectorLabel) + 1) = 0 from by decide]
    exact m1m_sigma_zero T
  have h_s3 : m1sigma ((2 : TrisectorLabel) + 0) = m1P T * m1Q T * m1R T := by
    rw [show ((2 : TrisectorLabel) + 0) = 2 from by decide]
    exact m1m_sigma_two T
  unfold m1mNAc_021_20 m1mNBc_021_20 m1mNA m1mNAb m1mNB m1mDrho m1mDgam m1mLamNum m1mLamDen
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  linear_combination ((-m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 16) + m1P T ^ 16 * m1Q T ^ 15 * m1R T ^ 13 + m1P T ^ 16 * m1Q T ^ 14 * m1R T ^ 15 + (-m1P T ^ 16 * m1Q T ^ 14 * m1R T ^ 12) + m1P T ^ 15 * m1Q T ^ 14 * m1R T ^ 15 + (-m1P T ^ 15 * m1Q T ^ 14 * m1R T ^ 12) + (-m1P T ^ 15 * m1Q T ^ 13 * m1R T ^ 14) + m1P T ^ 15 * m1Q T ^ 13 * m1R T ^ 11 + (3 : ℂ) * m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 15 + m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 13 + (-(3 : ℂ) * m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 12) + (-m1P T ^ 14 * m1Q T ^ 13 * m1R T ^ 10) + (-(3 : ℂ) * m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 14) + (-m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 12) + (3 : ℂ) * m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 11 + m1P T ^ 14 * m1Q T ^ 12 * m1R T ^ 9 + m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 16 + (-m1P T ^ 13 * m1Q T ^ 15 * m1R T ^ 13) + (-m1P T ^ 13 * m1Q T ^ 14 * m1R T ^ 15) + m1P T ^ 13 * m1Q T ^ 14 * m1R T ^ 12 + (-(3 : ℂ) * m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 14) + (-m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 13) + (-m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 12) + (3 : ℂ) * m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 11 + m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 10 + m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 9 + (3 : ℂ) * m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 13 + m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 12 + m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 11 + (-(3 : ℂ) * m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 10) + (-m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 9) + (-m1P T ^ 13 * m1Q T ^ 11 * m1R T ^ 8) + (-m1P T ^ 12 * m1Q T ^ 14 * m1R T ^ 15) + m1P T ^ 12 * m1Q T ^ 14 * m1R T ^ 12 + m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 14 + (-m1P T ^ 12 * m1Q T ^ 13 * m1R T ^ 11) + (-(3 : ℂ) * m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 14) + (-(2 : ℂ) * m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 12) + (3 : ℂ) * m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 11 + (2 : ℂ) * m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 9 + (3 : ℂ) * m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 13 + (2 : ℂ) * m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 11 + (-(3 : ℂ) * m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 10) + (-(2 : ℂ) * m1P T ^ 12 * m1Q T ^ 10 * m1R T ^ 8) + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 15) + (-m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 13) + (3 : ℂ) * m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 12 + m1P T ^ 11 * m1Q T ^ 13 * m1R T ^ 10 + (3 : ℂ) * m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 14 + m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 12 + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 11) + (-m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 9) + m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 13 + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 10) + m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 7 + (3 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 13 + m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 12 + (3 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 11 + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 10) + m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 9 + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 8) + (-m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 7) + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 6) + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 12) + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 11) + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 10) + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 9 + m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 8 + (3 : ℂ) * m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 7 + m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 6 + m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 5 + (3 : ℂ) * m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 14 + m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 13 + m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 12 + (-(3 : ℂ) * m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 11) + (-m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 10) + (-m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 9) + (-(4 : ℂ) * m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 13) + (-m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 12) + (-m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 11) + (5 : ℂ) * m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 10 + m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 9 + m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 8 + (-m1P T ^ 10 * m1Q T ^ 11 * m1R T ^ 7) + m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 12 + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 9) + m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 6 + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 13 + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 11 + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 10) + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 8) + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 7 + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 5 + (-m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 12) + (-m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 10) + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 9 + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 7 + (-m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 6) + (-m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 4) + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 14 + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 12 + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 11) + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 9) + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 13) + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 11) + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 8 + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 12) + (4 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 9 + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 6) + (-m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 12) + m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 11 + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 10) + (-m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 9) + (-(6 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 8) + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 7 + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 6 + (5 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 5 + m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 11 + m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 10 + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 9 + m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 8 + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 7 + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 6) + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 5) + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 4) + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 13) + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 12) + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 11) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 10 + m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 9 + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 8 + m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 7 + m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 6 + (5 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 12 + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 11 + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 10 + (-(6 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 9) + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 8) + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 7) + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 6 + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 5) + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 11) + (4 : ℂ) * m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 8 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 5) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 9 + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 7 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 6) + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 4) + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 8) + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 6) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 5 + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 3 + (-m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 13) + (-m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 11) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 8 + (-m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 7) + (-m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 5) + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 12 + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 10 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 9) + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 7) + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 6 + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 4 + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 11 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 8) + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 5 + (-m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 10) + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 9 + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 8 + (5 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 7 + (-m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 6) + (-m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 5) + (-(4 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 4) + (-m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 8) + (-m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 7) + (-(3 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 6) + m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 5 + m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 4 + (3 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 3 + m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 12 + m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 11 + (3 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 10 + m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 9 + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 8 + (-(3 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 7) + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 6) + (-(3 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 5) + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 11) + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 10) + (-(3 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 9) + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 8 + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 7) + (3 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 6 + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 5 + (3 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 4 + m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 10 + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 7) + m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 4 + (-m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 8) + (-(3 : ℂ) * m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 6) + m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 5 + (3 : ℂ) * m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 3 + m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 7 + (3 : ℂ) * m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 5 + (-m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 4) + (-(3 : ℂ) * m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 2) + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 9) + (-(3 : ℂ) * m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 7) + (2 : ℂ) * m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 6 + (3 : ℂ) * m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 4 + (2 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 8 + (3 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 6 + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 5) + (-(3 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 3) + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 6) + m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 3 + m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 5 + (-m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 2) + (-m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 9) + (-m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 8) + (-(3 : ℂ) * m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 7) + m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 6 + m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 5 + (3 : ℂ) * m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 4 + m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 8 + m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 7 + (3 : ℂ) * m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 6 + (-m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 5) + (-m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 4) + (-(3 : ℂ) * m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 3) + m1P T ^ 4 * m1Q T ^ 3 * m1R T ^ 5 + (-m1P T ^ 4 * m1Q T ^ 3 * m1R T ^ 2) + (-m1P T ^ 4 * m1Q T ^ 2 * m1R T ^ 4) + m1P T ^ 4 * m1Q T ^ 2 * m1R T + m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 8 + (3 : ℂ) * m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 6 + (-m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 5) + (-(3 : ℂ) * m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 3) + (-m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 7) + (-(3 : ℂ) * m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 5) + m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 4 + (3 : ℂ) * m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 2 + m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 6 + (-m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 3) + (-m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 5) + m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 2 + (-m1P T * m1Q T ^ 3 * m1R T ^ 5) + m1P T * m1Q T ^ 3 * m1R T ^ 2 + m1P T * m1Q T ^ 2 * m1R T ^ 4 + (-m1P T * m1Q T ^ 2 * m1R T)) * (m1m_three T)

set_option maxRecDepth 100000 in
theorem m1m_poly_021_20 (T : OrientedTriangle E o) :
    star (m1mNA T 0 2 1 2 0) * m1mNB T 0 2 1 2 0 = m1mNA T 0 2 1 2 0 * star (m1mNB T 0 2 1 2 0) := by
  have hK : (m1P T * m1Q T * m1R T) ^ 10 ≠ 0 :=
    pow_ne_zero 10 (mul_ne_zero (mul_ne_zero (m3c_P_ne T) (m3c_Q_ne T)) (m3c_R_ne T))
  refine mul_left_cancel₀ hK ?_
  calc (m1P T * m1Q T * m1R T) ^ 10 * (star (m1mNA T 0 2 1 2 0) * m1mNB T 0 2 1 2 0)
      = ((m1P T * m1Q T * m1R T) ^ 10 * star (m1mNA T 0 2 1 2 0)) * m1mNB T 0 2 1 2 0 := by ring
    _ = m1mNAc_021_20 T * m1mNB T 0 2 1 2 0 := by rw [m1m_hNAc_021_20 T]
    _ = m1mNA T 0 2 1 2 0 * m1mNBc_021_20 T := m1m_cert_021_20 T
    _ = m1mNA T 0 2 1 2 0 * ((m1P T * m1Q T * m1R T) ^ 10 * star (m1mNB T 0 2 1 2 0)) := by rw [m1m_hNBc_021_20 T]
    _ = (m1P T * m1Q T * m1R T) ^ 10 * (m1mNA T 0 2 1 2 0 * star (m1mNB T 0 2 1 2 0)) := by ring

theorem m1m_real_021_20 (T : OrientedTriangle E o) :
    star (m3cA T 0 2 1) * m3cB T 0 2 2 0
      = m3cA T 0 2 1 * star (m3cB T 0 2 2 0) :=
  m1m_real_key T (m1m_A_frac T 0 2 1 2 0) (m1m_B_frac T 0 2 1 2 0) (m1m_poly_021_20 T)

/-! ### Representative `⟨0,0,2⟩`, red join pair `⟨1,2⟩` -/

set_option maxRecDepth 100000 in
noncomputable def m1mNAc_002_12 (T : OrientedTriangle E o) : ℂ :=
  (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 7) + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 4 + (-m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 4) + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 7 + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 4) + m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 7 + (-m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 4) + m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 5 + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 4 + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 7) + m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 4 + (-m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 5) + m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 2 + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 5) + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 4) + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 2) + m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 4 + m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 5 + (-m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 2) + m1P T ^ 4 * m1Q T ^ 3 * m1R T ^ 2 + (-(2 : ℂ) * m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 4) + (-m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 2) + m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 4 + (2 : ℂ) * m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 2 + (-m1P T * m1Q T ^ 3 * m1R T ^ 2)

set_option maxRecDepth 100000 in
noncomputable def m1mNBc_002_12 (T : OrientedTriangle E o) : ℂ :=
  (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 7) + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 4 + m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 7 + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 4) + m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 5 + (-m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 2) + m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 5 + (-m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 2) + (-m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 5) + m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 2 + (-m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 5) + m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 2 + (-m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 3) + m1P T ^ 3 * m1Q T ^ 3 + m1P T ^ 2 * m1Q T ^ 2 * m1R T ^ 3 + (-m1P T ^ 2 * m1Q T ^ 2)

set_option maxRecDepth 100000 in
theorem m1m_hNAc_002_12 (T : OrientedTriangle E o) :
    (m1P T * m1Q T * m1R T) ^ 7 * star (m1mNA T 0 0 2 1 2) = m1mNAc_002_12 T := by
  have hP := m3c_P_ne T
  have hQ := m3c_Q_ne T
  have hR := m3c_R_ne T
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((0 : TrisectorLabel) + 0) = 1 := by
    rw [show ((0 : TrisectorLabel) + 0) = 0 from by decide]
    exact m1m_sigma_zero T
  have h_s2 : m1sigma ((0 : TrisectorLabel) + 2) = m1P T * m1Q T * m1R T := by
    rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s3 : m1sigma ((1 : TrisectorLabel) + 2) = 1 := by
    rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide]
    exact m1m_sigma_zero T
  unfold m1mNA m1mNAb m1mDrho m1mDgam m1mLamNum m1mLamDen m1mNAc_002_12
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  simp only [
    star_add, star_mul', star_sub, star_neg, star_pow, star_one, star_zero, star_natCast,
    star_ofNat, star_intCast, star_inv, m3c_star_P, m3c_star_Q, m3c_star_R]
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem m1m_hNBc_002_12 (T : OrientedTriangle E o) :
    (m1P T * m1Q T * m1R T) ^ 7 * star (m1mNB T 0 0 2 1 2) = m1mNBc_002_12 T := by
  have hP := m3c_P_ne T
  have hQ := m3c_Q_ne T
  have hR := m3c_R_ne T
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((0 : TrisectorLabel) + 0) = 1 := by
    rw [show ((0 : TrisectorLabel) + 0) = 0 from by decide]
    exact m1m_sigma_zero T
  have h_s2 : m1sigma ((0 : TrisectorLabel) + 2) = m1P T * m1Q T * m1R T := by
    rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s3 : m1sigma ((1 : TrisectorLabel) + 2) = 1 := by
    rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide]
    exact m1m_sigma_zero T
  unfold m1mNB m1mDrho m1mDgam m1mLamNum m1mNBc_002_12
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  simp only [
    star_add, star_mul', star_sub, star_neg, star_pow, star_one, star_zero, star_natCast,
    star_ofNat, star_intCast, star_inv, m3c_star_P, m3c_star_Q, m3c_star_R]
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem m1m_cert_002_12 (T : OrientedTriangle E o) :
    m1mNAc_002_12 T * m1mNB T 0 0 2 1 2 = m1mNA T 0 0 2 1 2 * m1mNBc_002_12 T := by
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((0 : TrisectorLabel) + 0) = 1 := by
    rw [show ((0 : TrisectorLabel) + 0) = 0 from by decide]
    exact m1m_sigma_zero T
  have h_s2 : m1sigma ((0 : TrisectorLabel) + 2) = m1P T * m1Q T * m1R T := by
    rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s3 : m1sigma ((1 : TrisectorLabel) + 2) = 1 := by
    rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide]
    exact m1m_sigma_zero T
  unfold m1mNAc_002_12 m1mNBc_002_12 m1mNA m1mNAb m1mNB m1mDrho m1mDgam m1mLamNum m1mLamDen
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  linear_combination (m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 11 + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 8) + m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 5 + (-m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 9) + m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 8 + m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 6 + (-m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 5) + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 11) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 8 + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 5) + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 11) + (4 : ℂ) * m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 8 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 5) + m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 9 + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 8) + m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 7 + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 5 + (-m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 4) + (-m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 3) + m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 7 + (-m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 6) + (-m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 4) + m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 3 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 11 + (-(4 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 8) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 5 + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 11 + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 9 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 8) + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 6) + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 5 + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 3 + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 9 + (3 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 8 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 7) + (-(3 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 6) + (-(3 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 5) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 4 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 3 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 7) + (3 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 6 + (-m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 5) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 4 + (-(3 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 3) + m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 2 + m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 9 + (-m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 8) + (-m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 6) + m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 5 + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 11) + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 8 + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 5) + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 9) + m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 8 + (4 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 6 + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 5) + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 3) + m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 2 + (-m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 9) + (-m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 8) + m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 7 + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 6 + m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 5 + (-m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 4) + (-m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 3) + m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 7 + (-(3 : ℂ) * m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 6) + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 5 + (-m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 4) + (3 : ℂ) * m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 3 + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 2) + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 9) + (3 : ℂ) * m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 8 + (-m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 7) + (2 : ℂ) * m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 6 + (-(3 : ℂ) * m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 5) + m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 4 + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 8) + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 7) + m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 6 + (2 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 5 + m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 4 + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 3) + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 2) + m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 9 + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 8) + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 6) + (4 : ℂ) * m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 5 + m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 3 + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 2) + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 6) + (2 : ℂ) * m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 3 + (-m1P T ^ 5 * m1Q T ^ 4) + m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 6 + (-m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 5) + (-m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 3) + m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 2 + m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 9 + (-(3 : ℂ) * m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 8) + (2 : ℂ) * m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 7 + (-m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 6) + (3 : ℂ) * m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 5 + (-(2 : ℂ) * m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 4) + (2 : ℂ) * m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 8 + (2 : ℂ) * m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 7 + (-(3 : ℂ) * m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 6) + (-(3 : ℂ) * m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 5) + (-(2 : ℂ) * m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 4) + (3 : ℂ) * m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 3 + m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 2 + m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 8 + m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 6 + (-(2 : ℂ) * m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 5) + (-(2 : ℂ) * m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 3) + m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 2 + m1P T ^ 4 * m1Q T ^ 4 + (2 : ℂ) * m1P T ^ 4 * m1Q T ^ 3 * m1R T ^ 6 + (-(4 : ℂ) * m1P T ^ 4 * m1Q T ^ 3 * m1R T ^ 3) + (2 : ℂ) * m1P T ^ 4 * m1Q T ^ 3 + m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 8 + (-m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 7) + (-m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 5) + m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 4 + (-m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 8) + (-m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 7) + (3 : ℂ) * m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 6 + m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 4 + (-(3 : ℂ) * m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 3) + m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 2 + (-(2 : ℂ) * m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 6) + (4 : ℂ) * m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 3 + (-(2 : ℂ) * m1P T ^ 3 * m1Q T ^ 3) + (-m1P T ^ 3 * m1Q T ^ 2 * m1R T ^ 6) + (2 : ℂ) * m1P T ^ 3 * m1Q T ^ 2 * m1R T ^ 3 + (-m1P T ^ 3 * m1Q T ^ 2) + (-m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 6) + m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 5 + m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 3 + (-m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 2) + m1P T ^ 2 * m1Q T ^ 2 * m1R T ^ 6 + (-(2 : ℂ) * m1P T ^ 2 * m1Q T ^ 2 * m1R T ^ 3) + m1P T ^ 2 * m1Q T ^ 2) * (m1m_three T)

set_option maxRecDepth 100000 in
theorem m1m_poly_002_12 (T : OrientedTriangle E o) :
    star (m1mNA T 0 0 2 1 2) * m1mNB T 0 0 2 1 2 = m1mNA T 0 0 2 1 2 * star (m1mNB T 0 0 2 1 2) := by
  have hK : (m1P T * m1Q T * m1R T) ^ 7 ≠ 0 :=
    pow_ne_zero 7 (mul_ne_zero (mul_ne_zero (m3c_P_ne T) (m3c_Q_ne T)) (m3c_R_ne T))
  refine mul_left_cancel₀ hK ?_
  calc (m1P T * m1Q T * m1R T) ^ 7 * (star (m1mNA T 0 0 2 1 2) * m1mNB T 0 0 2 1 2)
      = ((m1P T * m1Q T * m1R T) ^ 7 * star (m1mNA T 0 0 2 1 2)) * m1mNB T 0 0 2 1 2 := by ring
    _ = m1mNAc_002_12 T * m1mNB T 0 0 2 1 2 := by rw [m1m_hNAc_002_12 T]
    _ = m1mNA T 0 0 2 1 2 * m1mNBc_002_12 T := m1m_cert_002_12 T
    _ = m1mNA T 0 0 2 1 2 * ((m1P T * m1Q T * m1R T) ^ 7 * star (m1mNB T 0 0 2 1 2)) := by rw [m1m_hNBc_002_12 T]
    _ = (m1P T * m1Q T * m1R T) ^ 7 * (m1mNA T 0 0 2 1 2 * star (m1mNB T 0 0 2 1 2)) := by ring

theorem m1m_real_002_12 (T : OrientedTriangle E o) :
    star (m3cA T 0 0 2) * m3cB T 0 0 1 2
      = m3cA T 0 0 2 * star (m3cB T 0 0 1 2) :=
  m1m_real_key T (m1m_A_frac T 0 0 2 1 2) (m1m_B_frac T 0 0 2 1 2) (m1m_poly_002_12 T)

/-! ### Representative `⟨1,1,0⟩`, red join pair `⟨2,0⟩` -/

set_option maxRecDepth 100000 in
noncomputable def m1mNAc_110_20 (T : OrientedTriangle E o) : ℂ :=
  (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 9) + m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 6 + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 8 + (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 5) + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 6 + (-m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 4) + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 7 + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 4) + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 5) + (2 : ℂ) * m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 3 + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 2) + m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 4 + (-m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 3) + (-m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 6) + m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 3 + (-m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 4) + m1P T ^ 4 * m1Q T ^ 4 * m1R T + (-m1P T ^ 3 * m1Q T ^ 2 * m1R T ^ 2) + m1P T ^ 3 * m1Q T ^ 2 * m1R T + (-(2 : ℂ) * m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 3) + (2 : ℂ) * m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 2 + m1P T ^ 2 * m1Q T ^ 2 * m1R T ^ 3 + (-m1P T ^ 2 * m1Q T ^ 2) + m1Q T ^ 2 * m1R T ^ 2 + (-m1Q T ^ 2 * m1R T)

set_option maxRecDepth 100000 in
noncomputable def m1mNBc_110_20 (T : OrientedTriangle E o) : ℂ :=
  m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 8 + (-m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 5) + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 7) + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 4 + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 7) + m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 4 + (-m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 5) + m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 2 + m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 6 + (-m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 3) + m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 4 + (-m1P T ^ 4 * m1Q T ^ 4 * m1R T) + m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 4 + (-m1P T ^ 3 * m1Q T ^ 3 * m1R T) + (-m1P T ^ 2 * m1Q T ^ 2 * m1R T ^ 3) + m1P T ^ 2 * m1Q T ^ 2

set_option maxRecDepth 100000 in
theorem m1m_hNAc_110_20 (T : OrientedTriangle E o) :
    (m1P T * m1Q T * m1R T) ^ 9 * star (m1mNA T 1 1 0 2 0) = m1mNAc_110_20 T := by
  have hP := m3c_P_ne T
  have hQ := m3c_Q_ne T
  have hR := m3c_R_ne T
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((1 : TrisectorLabel) + 1) = m1P T * m1Q T * m1R T := by
    rw [show ((1 : TrisectorLabel) + 1) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s2 : m1sigma ((1 : TrisectorLabel) + 0) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((1 : TrisectorLabel) + 0) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s3 : m1sigma ((2 : TrisectorLabel) + 0) = m1P T * m1Q T * m1R T := by
    rw [show ((2 : TrisectorLabel) + 0) = 2 from by decide]
    exact m1m_sigma_two T
  unfold m1mNA m1mNAb m1mDrho m1mDgam m1mLamNum m1mLamDen m1mNAc_110_20
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  simp only [
    star_add, star_mul', star_sub, star_neg, star_pow, star_one, star_zero, star_natCast,
    star_ofNat, star_intCast, star_inv, m3c_star_P, m3c_star_Q, m3c_star_R]
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem m1m_hNBc_110_20 (T : OrientedTriangle E o) :
    (m1P T * m1Q T * m1R T) ^ 9 * star (m1mNB T 1 1 0 2 0) = m1mNBc_110_20 T := by
  have hP := m3c_P_ne T
  have hQ := m3c_Q_ne T
  have hR := m3c_R_ne T
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((1 : TrisectorLabel) + 1) = m1P T * m1Q T * m1R T := by
    rw [show ((1 : TrisectorLabel) + 1) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s2 : m1sigma ((1 : TrisectorLabel) + 0) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((1 : TrisectorLabel) + 0) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s3 : m1sigma ((2 : TrisectorLabel) + 0) = m1P T * m1Q T * m1R T := by
    rw [show ((2 : TrisectorLabel) + 0) = 2 from by decide]
    exact m1m_sigma_two T
  unfold m1mNB m1mDrho m1mDgam m1mLamNum m1mNBc_110_20
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  simp only [
    star_add, star_mul', star_sub, star_neg, star_pow, star_one, star_zero, star_natCast,
    star_ofNat, star_intCast, star_inv, m3c_star_P, m3c_star_Q, m3c_star_R]
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem m1m_cert_110_20 (T : OrientedTriangle E o) :
    m1mNAc_110_20 T * m1mNB T 1 1 0 2 0 = m1mNA T 1 1 0 2 0 * m1mNBc_110_20 T := by
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((1 : TrisectorLabel) + 1) = m1P T * m1Q T * m1R T := by
    rw [show ((1 : TrisectorLabel) + 1) = 2 from by decide]
    exact m1m_sigma_two T
  have h_s2 : m1sigma ((1 : TrisectorLabel) + 0) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((1 : TrisectorLabel) + 0) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s3 : m1sigma ((2 : TrisectorLabel) + 0) = m1P T * m1Q T * m1R T := by
    rw [show ((2 : TrisectorLabel) + 0) = 2 from by decide]
    exact m1m_sigma_two T
  unfold m1mNAc_110_20 m1mNBc_110_20 m1mNA m1mNAb m1mNB m1mDrho m1mDgam m1mLamNum m1mLamDen
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  linear_combination ((-m1P T ^ 13 * m1Q T ^ 13 * m1R T ^ 15) + (2 : ℂ) * m1P T ^ 13 * m1Q T ^ 13 * m1R T ^ 12 + (-m1P T ^ 13 * m1Q T ^ 13 * m1R T ^ 9) + m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 13 + (-m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 12) + (-m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 10) + m1P T ^ 13 * m1Q T ^ 12 * m1R T ^ 9 + m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 14 + (-(2 : ℂ) * m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 11) + m1P T ^ 12 * m1Q T ^ 12 * m1R T ^ 8 + (-m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 12) + m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 11 + m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 9 + (-m1P T ^ 12 * m1Q T ^ 11 * m1R T ^ 8) + m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 14 + (-(2 : ℂ) * m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 11) + m1P T ^ 11 * m1Q T ^ 12 * m1R T ^ 8 + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 14 + (-(4 : ℂ) * m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 11) + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 8 + (-m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 12) + (3 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 11 + (-m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 10) + (-(3 : ℂ) * m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 8) + m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 7 + m1P T ^ 11 * m1Q T ^ 10 * m1R T ^ 6 + (-m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 10) + m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 9 + m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 7 + (-m1P T ^ 11 * m1Q T ^ 9 * m1R T ^ 6) + (-m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 13) + m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 12 + m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 10 + (-m1P T ^ 10 * m1Q T ^ 12 * m1R T ^ 9) + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 13) + (-m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 12) + (4 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 9 + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 7) + (-m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 6) + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 11 + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 10) + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 7 + (-m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 5) + m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 9 + (-m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 8) + (-m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 6) + m1P T ^ 10 * m1Q T ^ 8 * m1R T ^ 5 + m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 12 + (-m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 11) + (-m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 9) + m1P T ^ 9 * m1Q T ^ 11 * m1R T ^ 8 + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 13) + (-m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 12) + (4 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 9 + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 7) + (-m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 6) + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 13) + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 11) + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 8 + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 7) + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 5) + (-m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 11) + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 10) + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 9 + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 8 + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 7 + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 6) + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 5) + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 9 + (-(3 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 8) + m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 7 + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 6) + (3 : ℂ) * m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 5 + (-m1P T ^ 9 * m1Q T ^ 7 * m1R T ^ 4) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 12 + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 11) + m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 10 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 9) + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 8 + (-m1P T ^ 8 * m1Q T ^ 10 * m1R T ^ 7) + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 11 + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 10 + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 9) + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 8) + (-m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 7) + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 6 + m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 5 + m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 12 + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 11 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 9) + (-(4 : ℂ) * m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 8) + m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 6 + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 5 + m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 9 + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 7) + (-(3 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 6) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 4 + m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 3 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 8) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 7 + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 5 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 4) + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 11) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 8 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 7) + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 12 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 11 + (-(3 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 9) + (-(3 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 8) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 6 + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 5 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 10 + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 9 + (-(4 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 7) + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 6) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 4 + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 3 + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 10 + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 9 + (-m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 8) + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 7) + (-m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 6) + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 5 + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 4 + (-m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 8) + (3 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 7 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 6) + m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 5 + (-(3 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 4) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 3 + (-m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 11) + (3 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 10 + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 9) + m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 8 + (-(3 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 7) + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 6 + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 10) + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 9) + (3 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 8 + (3 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 7 + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 6 + (-(3 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 5) + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 4) + (-m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 10) + (-m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 8) + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 7 + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 5 + (-m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 4) + (-m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 2) + (-m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 9) + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 8) + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 6 + (4 : ℂ) * m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 5 + (-m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 3) + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 2) + m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 7 + (-m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 6) + (-m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 4) + m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 3 + m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 10 + (-m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 9) + (-m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 7) + m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 6 + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 10) + (2 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 8 + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 5) + m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 4 + (-m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 9) + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 8) + (2 : ℂ) * m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 6 + (4 : ℂ) * m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 5 + (-m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 3) + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 2) + (-m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 6) + m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 5 + m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 3 + (-m1P T ^ 5 * m1Q T ^ 3 * m1R T ^ 2) + (-m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 9) + m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 8 + m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 6 + (-m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 5) + m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 9 + m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 8 + (-(3 : ℂ) * m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 7) + (-m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 5) + (3 : ℂ) * m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 4 + (-m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 3) + (2 : ℂ) * m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 7 + (-(4 : ℂ) * m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 4) + (2 : ℂ) * m1P T ^ 4 * m1Q T ^ 4 * m1R T + m1P T ^ 4 * m1Q T ^ 3 * m1R T ^ 7 + (-(2 : ℂ) * m1P T ^ 4 * m1Q T ^ 3 * m1R T ^ 4) + m1P T ^ 4 * m1Q T ^ 3 * m1R T + (-m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 7) + m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 6 + m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 4 + (-m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 3) + m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 7 + (-(2 : ℂ) * m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 4) + m1P T ^ 3 * m1Q T ^ 3 * m1R T + m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 6 + (-m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 5) + (-m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 3) + m1P T ^ 2 * m1Q T ^ 3 * m1R T ^ 2 + (-m1P T ^ 2 * m1Q T ^ 2 * m1R T ^ 6) + (2 : ℂ) * m1P T ^ 2 * m1Q T ^ 2 * m1R T ^ 3 + (-m1P T ^ 2 * m1Q T ^ 2)) * (m1m_three T)

set_option maxRecDepth 100000 in
theorem m1m_poly_110_20 (T : OrientedTriangle E o) :
    star (m1mNA T 1 1 0 2 0) * m1mNB T 1 1 0 2 0 = m1mNA T 1 1 0 2 0 * star (m1mNB T 1 1 0 2 0) := by
  have hK : (m1P T * m1Q T * m1R T) ^ 9 ≠ 0 :=
    pow_ne_zero 9 (mul_ne_zero (mul_ne_zero (m3c_P_ne T) (m3c_Q_ne T)) (m3c_R_ne T))
  refine mul_left_cancel₀ hK ?_
  calc (m1P T * m1Q T * m1R T) ^ 9 * (star (m1mNA T 1 1 0 2 0) * m1mNB T 1 1 0 2 0)
      = ((m1P T * m1Q T * m1R T) ^ 9 * star (m1mNA T 1 1 0 2 0)) * m1mNB T 1 1 0 2 0 := by ring
    _ = m1mNAc_110_20 T * m1mNB T 1 1 0 2 0 := by rw [m1m_hNAc_110_20 T]
    _ = m1mNA T 1 1 0 2 0 * m1mNBc_110_20 T := m1m_cert_110_20 T
    _ = m1mNA T 1 1 0 2 0 * ((m1P T * m1Q T * m1R T) ^ 9 * star (m1mNB T 1 1 0 2 0)) := by rw [m1m_hNBc_110_20 T]
    _ = (m1P T * m1Q T * m1R T) ^ 9 * (m1mNA T 1 1 0 2 0 * star (m1mNB T 1 1 0 2 0)) := by ring

theorem m1m_real_110_20 (T : OrientedTriangle E o) :
    star (m3cA T 1 1 0) * m3cB T 1 1 2 0
      = m3cA T 1 1 0 * star (m3cB T 1 1 2 0) :=
  m1m_real_key T (m1m_A_frac T 1 1 0 2 0) (m1m_B_frac T 1 1 0 2 0) (m1m_poly_110_20 T)

/-! ### Representative `⟨1,2,2⟩`, red join pair `⟨2,1⟩` -/

set_option maxRecDepth 100000 in
noncomputable def m1mNAc_122_21 (T : OrientedTriangle E o) : ℂ :=
  (-m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 8) + m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 5 + m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 8 + (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 5) + (-m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 4) + m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 5 + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 4 + m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 6 + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 3) + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 5) + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 4) + (-m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 2) + m1P T ^ 4 * m1Q T ^ 6 * m1R T ^ 4 + (-m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 6) + m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 3 + m1P T ^ 4 * m1Q T ^ 3 * m1R T ^ 2 + (-(2 : ℂ) * m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 4) + (-m1P T ^ 3 * m1Q T ^ 5 * m1R T ^ 2) + (-m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 3) + m1P T ^ 3 * m1Q T ^ 3 + m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 4 + (2 : ℂ) * m1P T ^ 2 * m1Q T ^ 4 * m1R T ^ 2 + m1P T ^ 2 * m1Q T ^ 2 * m1R T ^ 3 + (-m1P T ^ 2 * m1Q T ^ 2) + (-m1P T * m1Q T ^ 3 * m1R T ^ 2)

set_option maxRecDepth 100000 in
noncomputable def m1mNBc_122_21 (T : OrientedTriangle E o) : ℂ :=
  m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 7 + (-m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 4) + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 7) + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 6) + m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 4 + m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 3 + m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 6 + (-m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 3) + (-m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 4) + m1P T ^ 4 * m1Q T ^ 4 * m1R T + m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 4 + m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 3 + (-m1P T ^ 3 * m1Q T ^ 3 * m1R T) + (-m1P T ^ 3 * m1Q T ^ 3) + (-m1P T ^ 2 * m1Q T ^ 2 * m1R T ^ 3) + m1P T ^ 2 * m1Q T ^ 2

set_option maxRecDepth 100000 in
theorem m1m_hNAc_122_21 (T : OrientedTriangle E o) :
    (m1P T * m1Q T * m1R T) ^ 8 * star (m1mNA T 1 2 2 2 1) = m1mNAc_122_21 T := by
  have hP := m3c_P_ne T
  have hQ := m3c_Q_ne T
  have hR := m3c_R_ne T
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((1 : TrisectorLabel) + 2) = 1 := by
    rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide]
    exact m1m_sigma_zero T
  have h_s2 : m1sigma ((2 : TrisectorLabel) + 2) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s3 : m1sigma ((2 : TrisectorLabel) + 1) = 1 := by
    rw [show ((2 : TrisectorLabel) + 1) = 0 from by decide]
    exact m1m_sigma_zero T
  unfold m1mNA m1mNAb m1mDrho m1mDgam m1mLamNum m1mLamDen m1mNAc_122_21
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  simp only [
    star_add, star_mul', star_sub, star_neg, star_pow, star_one, star_zero, star_natCast,
    star_ofNat, star_intCast, star_inv, m3c_star_P, m3c_star_Q, m3c_star_R]
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem m1m_hNBc_122_21 (T : OrientedTriangle E o) :
    (m1P T * m1Q T * m1R T) ^ 8 * star (m1mNB T 1 2 2 2 1) = m1mNBc_122_21 T := by
  have hP := m3c_P_ne T
  have hQ := m3c_Q_ne T
  have hR := m3c_R_ne T
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((1 : TrisectorLabel) + 2) = 1 := by
    rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide]
    exact m1m_sigma_zero T
  have h_s2 : m1sigma ((2 : TrisectorLabel) + 2) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s3 : m1sigma ((2 : TrisectorLabel) + 1) = 1 := by
    rw [show ((2 : TrisectorLabel) + 1) = 0 from by decide]
    exact m1m_sigma_zero T
  unfold m1mNB m1mDrho m1mDgam m1mLamNum m1mNBc_122_21
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  simp only [
    star_add, star_mul', star_sub, star_neg, star_pow, star_one, star_zero, star_natCast,
    star_ofNat, star_intCast, star_inv, m3c_star_P, m3c_star_Q, m3c_star_R]
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem m1m_cert_122_21 (T : OrientedTriangle E o) :
    m1mNAc_122_21 T * m1mNB T 1 2 2 2 1 = m1mNA T 1 2 2 2 1 * m1mNBc_122_21 T := by
  have h_0 : m1sigma (0 : TrisectorLabel) = 1 := m1m_sigma_zero T
  have h_1 : m1sigma (1 : TrisectorLabel) = (m1P T * m1Q T * m1R T) ^ 2 := m1m_sigma_one T
  have h_2 : m1sigma (2 : TrisectorLabel) = m1P T * m1Q T * m1R T := m1m_sigma_two T
  have h_s1 : m1sigma ((1 : TrisectorLabel) + 2) = 1 := by
    rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide]
    exact m1m_sigma_zero T
  have h_s2 : m1sigma ((2 : TrisectorLabel) + 2) = (m1P T * m1Q T * m1R T) ^ 2 := by
    rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide]
    exact m1m_sigma_one T
  have h_s3 : m1sigma ((2 : TrisectorLabel) + 1) = 1 := by
    rw [show ((2 : TrisectorLabel) + 1) = 0 from by decide]
    exact m1m_sigma_zero T
  unfold m1mNAc_122_21 m1mNBc_122_21 m1mNA m1mNAb m1mNB m1mDrho m1mDgam m1mLamNum m1mLamDen
  simp only [h_0, h_1, h_2, h_s1, h_s2, h_s3]
  linear_combination ((-m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 13) + (2 : ℂ) * m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 10 + (-m1P T ^ 11 * m1Q T ^ 11 * m1R T ^ 7) + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 13 + m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 12 + (-(4 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 10) + (-(2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 9) + (2 : ℂ) * m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 7 + m1P T ^ 10 * m1Q T ^ 10 * m1R T ^ 6 + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 10 + (-m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 9) + (-m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 7) + m1P T ^ 10 * m1Q T ^ 9 * m1R T ^ 6 + m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 12 + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 9) + m1P T ^ 9 * m1Q T ^ 10 * m1R T ^ 6 + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 13) + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 12) + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 10 + (4 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 9 + (-m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 7) + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 9 * m1R T ^ 6) + (-m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 10) + (2 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 9 + (-(2 : ℂ) * m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 6) + m1P T ^ 9 * m1Q T ^ 8 * m1R T ^ 4 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 12) + (4 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 9 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 9 * m1R T ^ 6) + m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 12 + (-m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 10) + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 9) + (2 : ℂ) * m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 7 + m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 6 + (-m1P T ^ 8 * m1Q T ^ 8 * m1R T ^ 4) + (-m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 10) + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 9) + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 7 + (3 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 6 + (-(2 : ℂ) * m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 4) + (-m1P T ^ 8 * m1Q T ^ 7 * m1R T ^ 3) + (-m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 7) + m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 6 + m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 4 + (-m1P T ^ 8 * m1Q T ^ 6 * m1R T ^ 3) + (-m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 10) + m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 9 + m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 7 + (-m1P T ^ 7 * m1Q T ^ 9 * m1R T ^ 6) + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 12 + (-m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 10) + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 9) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 7 + m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 6 + (-m1P T ^ 7 * m1Q T ^ 8 * m1R T ^ 4) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 10 + (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 9) + (-(4 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 7) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 6 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 4 + (-m1P T ^ 7 * m1Q T ^ 7 * m1R T ^ 3) + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 10 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 9 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 7) + (-(4 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 6) + m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 4 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 6 * m1R T ^ 3 + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 7 + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 6) + (-(2 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 4) + (2 : ℂ) * m1P T ^ 7 * m1Q T ^ 5 * m1R T ^ 3 + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 10 + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 9) + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 7) + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 8 * m1R T ^ 6 + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 10 + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 9 + (-(4 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 7) + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 6) + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 4 + m1P T ^ 6 * m1Q T ^ 7 * m1R T ^ 3 + (-m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 10) + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 9 + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 7 + (-(4 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 6) + (-m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 4) + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 6 * m1R T ^ 3 + (-m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 9) + m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 7 + (2 : ℂ) * m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 6 + (-(2 : ℂ) * m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 4) + (-m1P T ^ 6 * m1Q T ^ 5 * m1R T ^ 3) + m1P T ^ 6 * m1Q T ^ 5 * m1R T + (-m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 7) + m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 6 + m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 4 + (-m1P T ^ 6 * m1Q T ^ 4 * m1R T ^ 3) + (-m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 10) + m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 9 + m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 7 + (-m1P T ^ 5 * m1Q T ^ 7 * m1R T ^ 6) + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 10) + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 9) + (3 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 7 + (3 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 6 + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 4) + (-m1P T ^ 5 * m1Q T ^ 6 * m1R T ^ 3) + (-m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 9) + m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 7 + (2 : ℂ) * m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 6 + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 4) + (-m1P T ^ 5 * m1Q T ^ 5 * m1R T ^ 3) + m1P T ^ 5 * m1Q T ^ 5 * m1R T + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 7) + (4 : ℂ) * m1P T ^ 5 * m1Q T ^ 4 * m1R T ^ 4 + (-(2 : ℂ) * m1P T ^ 5 * m1Q T ^ 4 * m1R T) + m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 9 + (-(2 : ℂ) * m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 7) + (2 : ℂ) * m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 4 + (-m1P T ^ 4 * m1Q T ^ 5 * m1R T ^ 3) + (-(2 : ℂ) * m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 7) + (-m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 6) + (4 : ℂ) * m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 4 + (2 : ℂ) * m1P T ^ 4 * m1Q T ^ 4 * m1R T ^ 3 + (-(2 : ℂ) * m1P T ^ 4 * m1Q T ^ 4 * m1R T) + (-m1P T ^ 4 * m1Q T ^ 4) + m1P T ^ 4 * m1Q T ^ 3 * m1R T ^ 7 + (-(2 : ℂ) * m1P T ^ 4 * m1Q T ^ 3 * m1R T ^ 4) + m1P T ^ 4 * m1Q T ^ 3 * m1R T + m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 7 + (-m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 6) + (-m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 4) + m1P T ^ 3 * m1Q T ^ 4 * m1R T ^ 3 + m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 7 + (2 : ℂ) * m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 6 + (-(2 : ℂ) * m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 4) + (-(4 : ℂ) * m1P T ^ 3 * m1Q T ^ 3 * m1R T ^ 3) + m1P T ^ 3 * m1Q T ^ 3 * m1R T + (2 : ℂ) * m1P T ^ 3 * m1Q T ^ 3 + (-m1P T ^ 2 * m1Q T ^ 2 * m1R T ^ 6) + (2 : ℂ) * m1P T ^ 2 * m1Q T ^ 2 * m1R T ^ 3 + (-m1P T ^ 2 * m1Q T ^ 2)) * (m1m_three T)

set_option maxRecDepth 100000 in
theorem m1m_poly_122_21 (T : OrientedTriangle E o) :
    star (m1mNA T 1 2 2 2 1) * m1mNB T 1 2 2 2 1 = m1mNA T 1 2 2 2 1 * star (m1mNB T 1 2 2 2 1) := by
  have hK : (m1P T * m1Q T * m1R T) ^ 8 ≠ 0 :=
    pow_ne_zero 8 (mul_ne_zero (mul_ne_zero (m3c_P_ne T) (m3c_Q_ne T)) (m3c_R_ne T))
  refine mul_left_cancel₀ hK ?_
  calc (m1P T * m1Q T * m1R T) ^ 8 * (star (m1mNA T 1 2 2 2 1) * m1mNB T 1 2 2 2 1)
      = ((m1P T * m1Q T * m1R T) ^ 8 * star (m1mNA T 1 2 2 2 1)) * m1mNB T 1 2 2 2 1 := by ring
    _ = m1mNAc_122_21 T * m1mNB T 1 2 2 2 1 := by rw [m1m_hNAc_122_21 T]
    _ = m1mNA T 1 2 2 2 1 * m1mNBc_122_21 T := m1m_cert_122_21 T
    _ = m1mNA T 1 2 2 2 1 * ((m1P T * m1Q T * m1R T) ^ 8 * star (m1mNB T 1 2 2 2 1)) := by rw [m1m_hNBc_122_21 T]
    _ = (m1P T * m1Q T * m1R T) ^ 8 * (m1mNA T 1 2 2 2 1 * star (m1mNB T 1 2 2 2 1)) := by ring

theorem m1m_real_122_21 (T : OrientedTriangle E o) :
    star (m3cA T 1 2 2) * m3cB T 1 2 2 1
      = m3cA T 1 2 2 * star (m3cB T 1 2 2 1) :=
  m1m_real_key T (m1m_A_frac T 1 2 2 2 1) (m1m_B_frac T 1 2 2 2 1) (m1m_poly_122_21 T)





noncomputable section
open scoped Real RealInnerProductSpace ComplexConjugate Matrix
open Function Set


variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable {o : Orientation ℝ E (Fin 2)}


set_option maxHeartbeats 2000000

/-! ### Distinctness of the three labels as complex numbers -/

theorem m1m_one_ne_omega : (1 : ℂ) ≠ (omega : ℂ) :=
  fun hc => w9_omega_ne_one hc.symm

theorem m1m_one_ne_omega_sq : (1 : ℂ) ≠ (omega : ℂ) ^ 2 := by
  intro hc
  have h := congrArg Complex.im hc
  simp only [Complex.one_im, m4d_im_omega_sq] at h
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  linarith

theorem m1m_omega_ne_two : (omega : ℂ) ^ 2 ≠ (omega : ℂ) := by
  intro hc
  have h := congrArg Complex.im hc
  simp only [m4d_im_omega_sq, m4d_im_omega] at h
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- `m1sigma` is injective on the three labels. -/
theorem m1m_sigma_ne {i i' : TrisectorLabel} (h : i ≠ i') : m1sigma i ≠ m1sigma i' := by
  rcases zmod3_cases i with rfl | rfl | rfl <;> rcases zmod3_cases i' with rfl | rfl | rfl <;>
    simp only [m1sigma_zero, m1sigma_one, m1sigma_two]
  · exact absurd rfl h
  · exact m1m_one_ne_omega_sq
  · exact m1m_one_ne_omega
  · exact fun hh => m1m_one_ne_omega_sq hh.symm
  · exact absurd rfl h
  · exact m1m_omega_ne_two
  · exact fun hh => m1m_one_ne_omega hh.symm
  · exact fun hh => m1m_omega_ne_two hh.symm
  · exact absurd rfl h

theorem m1m_sigma_ne' {i i' : TrisectorLabel} (h : m1sigma i = m1sigma i') : i = i' := by
  by_contra hc
  exact m1m_sigma_ne hc h

/-- The join coefficient of an equal-sum red pair is nonzero. -/
theorem m1m_NB_ne (T : OrientedTriangle E o) {i j k i' j' : TrisectorLabel}
    (hii : i ≠ i') (hs : i + j = i' + j') : m1mNB T i j k i' j' ≠ 0 := by
  have hDr : m1mDrho T i' j' = m1mDrho T i j := by
    unfold m1mDrho
    rw [hs]
  have hkey : (1 - m1P T * m1sigma i') * m1mDrho T i j - (1 - m1P T * m1sigma i) *
      m1mDrho T i' j' = m1mDrho T i j * (m1P T * (m1sigma i - m1sigma i')) := by
    rw [hDr]
    ring
  have hsig : m1sigma i - m1sigma i' ≠ 0 := sub_ne_zero.mpr (m1m_sigma_ne hii)
  unfold m1mNB
  rw [hkey]
  refine mul_ne_zero (mul_ne_zero ?hLam (mul_ne_zero (m1m_Drho_ne T i j)
    (mul_ne_zero (m3c_P_ne T) hsig))) (m1m_Dgam_ne T j k)
  unfold m1mLamNum
  exact m3c_R_cube_sub_one_ne T

theorem m1m_B_ne (T : OrientedTriangle E o) {i j k i' j' : TrisectorLabel}
    (hii : i ≠ i') (hs : i + j = i' + j') : m3cB T i j i' j' ≠ 0 := by
  rw [m1m_B_frac]
  exact div_ne_zero (m1m_NB_ne T hii hs) (m1m_D_ne T i j k i' j')

/-! ### Closed forms of the first tricolour side and of a red equal-sum join -/

/-- Abstract key for the first tricolour side. -/
theorem m1m_side_key (u v ng dg ln ld nr dr : ℂ) (hdg : dg ≠ 0) (hld : ld ≠ 0) (hdr : dr ≠ 0) :
    (u + (v - u) * (ng / dg)) - (v + (ln / ld) * (v - u) * (nr / dr))
      = -(1 - (ng / dg) + (ln / ld) * (nr / dr)) * (v - u) := by
  field_simp
  ring

/-- Abstract key for a red equal-sum join. -/
theorem m1m_join_key (u v ln ld nr nr' dr dr' : ℂ) (hld : ld ≠ 0) (hdr : dr ≠ 0)
    (hdr' : dr' ≠ 0) :
    (v + (ln / ld) * (v - u) * (nr' / dr')) - (v + (ln / ld) * (v - u) * (nr / dr))
      = (ln / ld) * (nr' / dr' - nr / dr) * (v - u) := by
  field_simp
  ring

/-- `green(j,k) - red(i,j) = -A·(C-A)` in complex coordinates. -/
theorem m1m_side_form (T : OrientedTriangle E o) (i j k : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.green, j, k⟩ - T.constellationPoint ⟨.red, i, j⟩)
      = -(m3cA T i j k) * toComplex o (T.C - T.A) := by
  have hdg : 1 - m1Q T * m1R T * m1sigma (j + k) ≠ 0 := m1_green_den_ne T (j + k)
  have hdr : 1 - m1P T * m1Q T * m1sigma (i + j) ≠ 0 := m1_red_den_ne T (i + j)
  have hdl : (m1R T) ^ 3 * ((m1P T) ^ 3 - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 (m3c_R_ne T)) (m3c_P_cube_sub_one_ne T)
  rw [toComplex_sub]
  rw [m1_green_nf, m1_red_nf, m3c_U_eq]
  simp only [toComplex_sub]
  unfold m3cA m3cRho m3cGam m3cLam
  exact m1m_side_key (toComplex o T.A) (toComplex o T.C) (1 - m1Q T * m1sigma j)
    (1 - m1Q T * m1R T * m1sigma (j + k)) ((m1R T) ^ 3 - 1)
    ((m1R T) ^ 3 * ((m1P T) ^ 3 - 1)) (1 - m1P T * m1sigma i)
    (1 - m1P T * m1Q T * m1sigma (i + j)) hdg hdl hdr

/-- `red(i',j') - red(i,j) = B·(C-A)` in complex coordinates. -/
theorem m1m_join_form (T : OrientedTriangle E o) (i j i' j' : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.red, i', j'⟩ - T.constellationPoint ⟨.red, i, j⟩)
      = m3cB T i j i' j' * toComplex o (T.C - T.A) := by
  have hdr : 1 - m1P T * m1Q T * m1sigma (i + j) ≠ 0 := m1_red_den_ne T (i + j)
  have hdr2 : 1 - m1P T * m1Q T * m1sigma (i' + j') ≠ 0 := m1_red_den_ne T (i' + j')
  have hdl : (m1R T) ^ 3 * ((m1P T) ^ 3 - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 (m3c_R_ne T)) (m3c_P_cube_sub_one_ne T)
  rw [toComplex_sub]
  rw [m1_red_nf, m1_red_nf, m3c_U_eq]
  simp only [toComplex_sub]
  unfold m3cB m3cRho m3cLam
  exact m1m_join_key (toComplex o T.A) (toComplex o T.C) ((m1R T) ^ 3 - 1)
    ((m1R T) ^ 3 * ((m1P T) ^ 3 - 1)) (1 - m1P T * m1sigma i)
    (1 - m1P T * m1sigma i') (1 - m1P T * m1Q T * m1sigma (i + j))
    (1 - m1P T * m1Q T * m1sigma (i' + j')) hdl hdr hdr2

/-! ### From the realness identity to the first conjunct -/

/-- **The first conjunct of `tricolor_sides_parallel` from the realness identity.** -/
theorem m1m_first_of_real (T : OrientedTriangle E o) {i j k i' j' : TrisectorLabel}
    (hii : i ≠ i') (hs : i + j = i' + j')
    (hreal : star (m3cA T i j k) * m3cB T i j i' j'
      = m3cA T i j k * star (m3cB T i j i' j'))
    (hdir : T.parallelToMorleySide
      (T.constellationPoint ⟨.red, i', j'⟩ - T.constellationPoint ⟨.red, i, j⟩)) :
    T.parallelToMorleySide
      (T.constellationPoint ⟨.green, j, k⟩ - T.constellationPoint ⟨.red, i, j⟩) := by
  obtain ⟨r, hr⟩ := m3c_real_div (m1m_B_ne (k := k) T hii hs) hreal
  have hpar : Parallel (T.constellationPoint ⟨.red, i', j'⟩ - T.constellationPoint ⟨.red, i, j⟩)
      (T.constellationPoint ⟨.green, j, k⟩ - T.constellationPoint ⟨.red, i, j⟩) := by
    refine m8_parallel_of_real_ratio (o := o) (r := -r) ?_
    rw [m1m_side_form, m1m_join_form, hr]
    push_cast
    ring
  exact m3c_pMS_of_parallel_trans T hdir hpar

/-! ### Direction data for the Morley sides -/

/-- The Morley side vector of index `d` (`0 = Y-X`, `1 = Z-Y`, `2 = X-Z`) is parallel to
a Morley side. -/
theorem m1m_pMS_m3pSide (T : OrientedTriangle E o) (d : TrisectorLabel) :
    T.parallelToMorleySide (XamboMorley.OrientedTriangle.OrientedTriangle.m3pSide T d) := by
  rcases zmod3_cases d with rfl | rfl | rfl
  · rw [XamboMorley.OrientedTriangle.OrientedTriangle.m3p_side_zero]
    exact Or.inl ⟨1, by simp⟩
  · rw [XamboMorley.OrientedTriangle.OrientedTriangle.m3p_side_one]
    exact Or.inr (Or.inl ⟨1, by simp⟩)
  · rw [XamboMorley.OrientedTriangle.OrientedTriangle.m3p_side_two]
    exact Or.inr (Or.inr ⟨1, by simp⟩)

theorem m1m_par_neg_right {u v : E} (h : Parallel u v) : Parallel u (-v) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨-r, by rw [hr, neg_smul]⟩

/-- Reversing both endpoints of a joining vector preserves parallelism. -/
theorem m1m_par_neg_sub {u v w : E} (h : Parallel u (v - w)) : Parallel u (w - v) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨-r, by rw [show w - v = -(v - w) from by abel, hr, neg_smul]⟩

/-! ### Cyclic transport, backwards direction -/

/-- The third-minus-second side of a tricolour triangle forces its first side. -/
theorem m1m_pMS_of_side2 (T : OrientedTriangle E o) (i j k : TrisectorLabel)
    (hq : i + j + k ≠ 1) :
    T.parallelToMorleySide
        ((T.tricolorTriangle ⟨i, j, k⟩).third - (T.tricolorTriangle ⟨i, j, k⟩).second) →
      T.parallelToMorleySide
        ((T.tricolorTriangle ⟨i, j, k⟩).second - (T.tricolorTriangle ⟨i, j, k⟩).first) := by
  intro h
  have heq := m3c7_tricolor_equilateral_of_ne_one T ⟨i, j, k⟩ hq
  obtain ⟨-, h21⟩ := m3c_pMS_of_equilateral_of_pMS (T := T) (m1_equilateral_cycle heq) h
  exact h21

/-- **Backwards cyclic transport.**  The first conjunct for the label `⟨a,b,c⟩` at
`m7_cyclic T` yields the first conjunct for `⟨c,a,b⟩` at `T`. -/
theorem m1m_hfirst_back (T : OrientedTriangle E o) (a b c : TrisectorLabel)
    (hq : a + b + c ≠ 1)
    (h : (m7_cyclic T).parallelToMorleySide
      (((m7_cyclic T).tricolorTriangle ⟨a, b, c⟩).second -
        ((m7_cyclic T).tricolorTriangle ⟨a, b, c⟩).first)) :
    T.parallelToMorleySide
      ((T.tricolorTriangle ⟨c, a, b⟩).second - (T.tricolorTriangle ⟨c, a, b⟩).first) := by
  have hq' : c + a + b ≠ 1 := by
    intro hc
    exact hq (by rw [← hc]; abel)
  have e1 : ((m7_cyclic T).tricolorTriangle ⟨a, b, c⟩).second
      = T.constellationPoint ⟨.blue, b, c⟩ := by
    show (m7_cyclic T).constellationPoint ⟨.green, b, c⟩ = _
    rw [m3_cp_cyclic_green]
  have e2 : ((m7_cyclic T).tricolorTriangle ⟨a, b, c⟩).first
      = T.constellationPoint ⟨.green, a, b⟩ := by
    show (m7_cyclic T).constellationPoint ⟨.red, a, b⟩ = _
    rw [m3_cp_cyclic_red]
  rw [e1, e2] at h
  have h' : T.parallelToMorleySide
      (T.constellationPoint ⟨.blue, b, c⟩ - T.constellationPoint ⟨.green, a, b⟩) :=
    (m3_parallelToMorleySide_cyclic T _).mp h
  have hside : T.constellationPoint ⟨.blue, b, c⟩ - T.constellationPoint ⟨.green, a, b⟩
      = (T.tricolorTriangle ⟨c, a, b⟩).third - (T.tricolorTriangle ⟨c, a, b⟩).second := rfl
  rw [hside] at h'
  exact m1m_pMS_of_side2 T c a b hq' h'





noncomputable section
open scoped Real RealInnerProductSpace ComplexConjugate Matrix
open Function Set


variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable {o : Orientation ℝ E (Fin 2)}


set_option maxHeartbeats 4000000

/-! ### The first conjunct at the orbit representatives -/

theorem m1m_first_000 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨0, 0, 0⟩).second - (T.tricolorTriangle ⟨0, 0, 0⟩).first) := by
  have e1 : T.constellationPoint ⟨.red, 0, 0⟩ = T.X := by
    show T.constellationPoint ⟨.red, 0, 0⟩ = _
    simp only [OrientedTriangle.constellationPoint, labelAngle_zero, sub_zero]
    rfl
  have e2 : T.constellationPoint ⟨.green, 0, 0⟩ = T.Y := by
    show T.constellationPoint ⟨.green, 0, 0⟩ = _
    simp only [OrientedTriangle.constellationPoint, labelAngle_zero, sub_zero]
    rfl
  show T.parallelToMorleySide
    (T.constellationPoint ⟨.green, 0, 0⟩ - T.constellationPoint ⟨.red, 0, 0⟩)
  rw [e1, e2]
  exact Or.inl ⟨1, by simp⟩

theorem m1m_first_111 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨1, 1, 1⟩).second - (T.tricolorTriangle ⟨1, 1, 1⟩).first) := by
  show T.parallelToMorleySide
    (T.constellationPoint ⟨.green, 1, 1⟩ - T.constellationPoint ⟨.red, 1, 1⟩)
  refine m1m_first_of_real (k := 1) T (i' := 0) (j' := 2) (by decide) (by decide)
    (m1m_real_111_02 T) ?_
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par23 T 2
  rw [show ((2 : TrisectorLabel) + 1) = 0 from by decide, show ((2 : TrisectorLabel) + 2) = 1 from by decide] at hp
  refine m3c_pMS_of_parallel_trans T (m1m_pMS_m3pSide T (0)) ?_
  exact m1m_par_neg_sub hp

theorem m1m_first_222 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨2, 2, 2⟩).second - (T.tricolorTriangle ⟨2, 2, 2⟩).first) := by
  show T.parallelToMorleySide
    (T.constellationPoint ⟨.green, 2, 2⟩ - T.constellationPoint ⟨.red, 2, 2⟩)
  refine m1m_first_of_real (k := 2) T (i' := 1) (j' := 0) (by decide) (by decide)
    (m1m_real_222_10 T) ?_
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par12 T 1
  rw [show ((1 : TrisectorLabel) + 1) = 2 from by decide, show ((1 : TrisectorLabel) + 2) = 0 from by decide] at hp
  refine m3c_pMS_of_parallel_trans T (m1m_pMS_m3pSide T (0)) ?_
  exact m1m_par_neg_sub hp

theorem m1m_first_012 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨0, 1, 2⟩).second - (T.tricolorTriangle ⟨0, 1, 2⟩).first) := by
  show T.parallelToMorleySide
    (T.constellationPoint ⟨.green, 1, 2⟩ - T.constellationPoint ⟨.red, 0, 1⟩)
  refine m1m_first_of_real (k := 2) T (i' := 2) (j' := 2) (by decide) (by decide)
    (m1m_real_012_22 T) ?_
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par23 T 1
  rw [show ((1 : TrisectorLabel) + 1) = 2 from by decide, show ((1 : TrisectorLabel) + 2) = 0 from by decide] at hp
  refine m3c_pMS_of_parallel_trans T (m1m_pMS_m3pSide T (2)) ?_
  exact m1m_par_neg_sub hp

theorem m1m_first_021 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨0, 2, 1⟩).second - (T.tricolorTriangle ⟨0, 2, 1⟩).first) := by
  show T.parallelToMorleySide
    (T.constellationPoint ⟨.green, 2, 1⟩ - T.constellationPoint ⟨.red, 0, 2⟩)
  refine m1m_first_of_real (k := 1) T (i' := 2) (j' := 0) (by decide) (by decide)
    (m1m_real_021_20 T) ?_
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par12 T 2
  rw [show ((2 : TrisectorLabel) + 1) = 0 from by decide, show ((2 : TrisectorLabel) + 2) = 1 from by decide] at hp
  refine m3c_pMS_of_parallel_trans T (m1m_pMS_m3pSide T (1)) ?_
  exact m1m_par_neg_sub hp

theorem m1m_first_002 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨0, 0, 2⟩).second - (T.tricolorTriangle ⟨0, 0, 2⟩).first) := by
  show T.parallelToMorleySide
    (T.constellationPoint ⟨.green, 0, 2⟩ - T.constellationPoint ⟨.red, 0, 0⟩)
  refine m1m_first_of_real (k := 2) T (i' := 1) (j' := 2) (by decide) (by decide)
    (m1m_real_002_12 T) ?_
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par12 T 0
  rw [show ((0 : TrisectorLabel) + 1) = 1 from by decide, show ((0 : TrisectorLabel) + 2) = 2 from by decide] at hp
  refine m3c_pMS_of_parallel_trans T (m1m_pMS_m3pSide T (2)) ?_
  exact hp

theorem m1m_first_110 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨1, 1, 0⟩).second - (T.tricolorTriangle ⟨1, 1, 0⟩).first) := by
  show T.parallelToMorleySide
    (T.constellationPoint ⟨.green, 1, 0⟩ - T.constellationPoint ⟨.red, 1, 1⟩)
  refine m1m_first_of_real (k := 0) T (i' := 2) (j' := 0) (by decide) (by decide)
    (m1m_real_110_20 T) ?_
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par31 T 2
  rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide] at hp
  refine m3c_pMS_of_parallel_trans T (m1m_pMS_m3pSide T (2)) ?_
  exact hp

theorem m1m_first_122 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨1, 2, 2⟩).second - (T.tricolorTriangle ⟨1, 2, 2⟩).first) := by
  show T.parallelToMorleySide
    (T.constellationPoint ⟨.green, 2, 2⟩ - T.constellationPoint ⟨.red, 1, 2⟩)
  refine m1m_first_of_real (k := 2) T (i' := 2) (j' := 1) (by decide) (by decide)
    (m1m_real_122_21 T) ?_
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par23 T 0
  rw [show ((0 : TrisectorLabel) + 1) = 1 from by decide, show ((0 : TrisectorLabel) + 2) = 2 from by decide] at hp
  refine m3c_pMS_of_parallel_trans T (m1m_pMS_m3pSide T (1)) ?_
  exact hp

/-! ### All eighteen labels, by backwards cyclic transport -/

theorem m1m_firstall_000 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨0, 0, 0⟩).second - (T.tricolorTriangle ⟨0, 0, 0⟩).first) := by
  exact m1m_first_000 T

theorem m1m_firstall_111 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨1, 1, 1⟩).second - (T.tricolorTriangle ⟨1, 1, 1⟩).first) := by
  exact m1m_first_111 T

theorem m1m_firstall_222 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨2, 2, 2⟩).second - (T.tricolorTriangle ⟨2, 2, 2⟩).first) := by
  exact m1m_first_222 T

theorem m1m_firstall_012 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨0, 1, 2⟩).second - (T.tricolorTriangle ⟨0, 1, 2⟩).first) := by
  exact m1m_first_012 T

theorem m1m_firstall_201 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨2, 0, 1⟩).second - (T.tricolorTriangle ⟨2, 0, 1⟩).first) := by
  exact m1m_hfirst_back T 0 1 2 (by decide : ((2 : TrisectorLabel) + 0) + 1 ≠ 1) (m1m_first_012 (m7_cyclic T))

theorem m1m_firstall_120 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨1, 2, 0⟩).second - (T.tricolorTriangle ⟨1, 2, 0⟩).first) := by
  refine m1m_hfirst_back T 2 0 1 (by decide : ((1 : TrisectorLabel) + 2) + 0 ≠ 1) ?_
  exact m1m_hfirst_back (m7_cyclic T) 0 1 2 (by decide : ((1 : TrisectorLabel) + 2) + 0 ≠ 1) (m1m_first_012 (m7_cyclic (m7_cyclic T)))

theorem m1m_firstall_021 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨0, 2, 1⟩).second - (T.tricolorTriangle ⟨0, 2, 1⟩).first) := by
  exact m1m_first_021 T

theorem m1m_firstall_102 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨1, 0, 2⟩).second - (T.tricolorTriangle ⟨1, 0, 2⟩).first) := by
  exact m1m_hfirst_back T 0 2 1 (by decide : ((1 : TrisectorLabel) + 0) + 2 ≠ 1) (m1m_first_021 (m7_cyclic T))

theorem m1m_firstall_210 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨2, 1, 0⟩).second - (T.tricolorTriangle ⟨2, 1, 0⟩).first) := by
  refine m1m_hfirst_back T 1 0 2 (by decide : ((2 : TrisectorLabel) + 1) + 0 ≠ 1) ?_
  exact m1m_hfirst_back (m7_cyclic T) 0 2 1 (by decide : ((2 : TrisectorLabel) + 1) + 0 ≠ 1) (m1m_first_021 (m7_cyclic (m7_cyclic T)))

theorem m1m_firstall_002 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨0, 0, 2⟩).second - (T.tricolorTriangle ⟨0, 0, 2⟩).first) := by
  exact m1m_first_002 T

theorem m1m_firstall_200 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨2, 0, 0⟩).second - (T.tricolorTriangle ⟨2, 0, 0⟩).first) := by
  exact m1m_hfirst_back T 0 0 2 (by decide : ((2 : TrisectorLabel) + 0) + 0 ≠ 1) (m1m_first_002 (m7_cyclic T))

theorem m1m_firstall_020 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨0, 2, 0⟩).second - (T.tricolorTriangle ⟨0, 2, 0⟩).first) := by
  refine m1m_hfirst_back T 2 0 0 (by decide : ((0 : TrisectorLabel) + 2) + 0 ≠ 1) ?_
  exact m1m_hfirst_back (m7_cyclic T) 0 0 2 (by decide : ((0 : TrisectorLabel) + 2) + 0 ≠ 1) (m1m_first_002 (m7_cyclic (m7_cyclic T)))

theorem m1m_firstall_110 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨1, 1, 0⟩).second - (T.tricolorTriangle ⟨1, 1, 0⟩).first) := by
  exact m1m_first_110 T

theorem m1m_firstall_011 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨0, 1, 1⟩).second - (T.tricolorTriangle ⟨0, 1, 1⟩).first) := by
  exact m1m_hfirst_back T 1 1 0 (by decide : ((0 : TrisectorLabel) + 1) + 1 ≠ 1) (m1m_first_110 (m7_cyclic T))

theorem m1m_firstall_101 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨1, 0, 1⟩).second - (T.tricolorTriangle ⟨1, 0, 1⟩).first) := by
  refine m1m_hfirst_back T 0 1 1 (by decide : ((1 : TrisectorLabel) + 0) + 1 ≠ 1) ?_
  exact m1m_hfirst_back (m7_cyclic T) 1 1 0 (by decide : ((1 : TrisectorLabel) + 0) + 1 ≠ 1) (m1m_first_110 (m7_cyclic (m7_cyclic T)))

theorem m1m_firstall_122 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨1, 2, 2⟩).second - (T.tricolorTriangle ⟨1, 2, 2⟩).first) := by
  exact m1m_first_122 T

theorem m1m_firstall_212 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨2, 1, 2⟩).second - (T.tricolorTriangle ⟨2, 1, 2⟩).first) := by
  exact m1m_hfirst_back T 1 2 2 (by decide : ((2 : TrisectorLabel) + 1) + 2 ≠ 1) (m1m_first_122 (m7_cyclic T))

theorem m1m_firstall_221 (T : OrientedTriangle E o) :
    T.parallelToMorleySide ((T.tricolorTriangle ⟨2, 2, 1⟩).second - (T.tricolorTriangle ⟨2, 2, 1⟩).first) := by
  refine m1m_hfirst_back T 2 1 2 (by decide : ((2 : TrisectorLabel) + 2) + 1 ≠ 1) ?_
  exact m1m_hfirst_back (m7_cyclic T) 1 2 2 (by decide : ((2 : TrisectorLabel) + 2) + 1 ≠ 1) (m1m_first_122 (m7_cyclic (m7_cyclic T)))

/-! ### The root's `tricolor_sides_parallel` -/

theorem m1m_tricolor_sides_parallel (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (q : TricolorIndex)
    (hq : q.i + q.j + q.k ≠ 1) :
    let t := T.tricolorTriangle q
    T.parallelToMorleySide (t.second - t.first) ∧
      T.parallelToMorleySide (t.third - t.second) ∧
        T.parallelToMorleySide (t.first - t.third) := by
  have key : ∀ q : TricolorIndex, q.i + q.j + q.k ≠ 1 →
      (let t := T.tricolorTriangle q
       T.parallelToMorleySide (t.second - t.first)) := by
    intro q hq
    rcases q with ⟨i, j, k⟩
    rcases zmod3_cases i with rfl | rfl | rfl <;>
      rcases zmod3_cases j with rfl | rfl | rfl <;>
      rcases zmod3_cases k with rfl | rfl | rfl
    · exact m1m_firstall_000 T
    · exact absurd (by decide : ((0 : TrisectorLabel) + 0) + 1 = 1) hq
    · exact m1m_firstall_002 T
    · exact absurd (by decide : ((0 : TrisectorLabel) + 1) + 0 = 1) hq
    · exact m1m_firstall_011 T
    · exact m1m_firstall_012 T
    · exact m1m_firstall_020 T
    · exact m1m_firstall_021 T
    · exact absurd (by decide : ((0 : TrisectorLabel) + 2) + 2 = 1) hq
    · exact absurd (by decide : ((1 : TrisectorLabel) + 0) + 0 = 1) hq
    · exact m1m_firstall_101 T
    · exact m1m_firstall_102 T
    · exact m1m_firstall_110 T
    · exact m1m_firstall_111 T
    · exact absurd (by decide : ((1 : TrisectorLabel) + 1) + 2 = 1) hq
    · exact m1m_firstall_120 T
    · exact absurd (by decide : ((1 : TrisectorLabel) + 2) + 1 = 1) hq
    · exact m1m_firstall_122 T
    · exact m1m_firstall_200 T
    · exact m1m_firstall_201 T
    · exact absurd (by decide : ((2 : TrisectorLabel) + 0) + 2 = 1) hq
    · exact m1m_firstall_210 T
    · exact absurd (by decide : ((2 : TrisectorLabel) + 1) + 1 = 1) hq
    · exact m1m_firstall_212 T
    · exact absurd (by decide : ((2 : TrisectorLabel) + 2) + 0 = 1) hq
    · exact m1m_firstall_221 T
    · exact m1m_firstall_222 T
  exact m3c_tricolor_sides_parallel_of_first T h key q hq




/-- All 18 tricolor equilateral triangles have sides parallel to `XYZ`. -/
theorem _root_.XamboMorley.OrientedTriangle.tricolor_sides_parallel (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (q : TricolorIndex)
    (hq : q.i + q.j + q.k ≠ 1) :
    let t := T.tricolorTriangle q
    T.parallelToMorleySide (t.second - t.first) ∧
      T.parallelToMorleySide (t.third - t.second) ∧
      T.parallelToMorleySide (t.first - t.third) := by
  exact m1m_tricolor_sides_parallel T h q hq
