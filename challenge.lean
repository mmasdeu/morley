import Mathlib

noncomputable section

open Function Set

namespace XamboMorley

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]

/-- A positively oriented orthonormal basis of the two-dimensional plane. -/
def positiveBasis (o : Orientation ℝ E (Fin 2)) : OrthonormalBasis (Fin 2) ℝ E :=
  o.finOrthonormalBasis (by norm_num) Fact.out

/-- Oriented area in the Euclidean plane. -/
def orientedArea (o : Orientation ℝ E (Fin 2)) (v w : E) : ℝ := o.areaForm v w

/-- The positively oriented complex coordinate model of the plane. -/
def complexIsometryEquiv (o : Orientation ℝ E (Fin 2)) : E ≃ₗᵢ[ℝ] ℂ :=
  (positiveBasis o).equiv Complex.orthonormalBasisOneI (Equiv.refl (Fin 2))

def toComplex (o : Orientation ℝ E (Fin 2)) (v : E) : ℂ := complexIsometryEquiv o v

/-- Reconstruct a point of the plane from its complex coordinate. -/
def ofComplex (o : Orientation ℝ E (Fin 2)) (z : ℂ) : E :=
  (complexIsometryEquiv o).symm z

/-- The fixed point, in the paper's nondegenerate regime, of
`rotation Q ψ ∘ rotation P φ`. -/
def rotationFixedPoint (o : Orientation ℝ E (Fin 2)) (P Q : E) (φ ψ : ℝ) : E :=
  P + ofComplex o (toComplex o (Q - P) *
    ((1 - Circle.exp ψ : ℂ) / (1 - (Circle.exp φ : ℂ) * Circle.exp ψ)))

/-- A nondegenerate, positively oriented Euclidean triangle. -/
structure OrientedTriangle (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2)) where
  A : E
  B : E
  C : E
  noncollinear : ¬Collinear ℝ ({A, B, C} : Set E)
  positive : 0 < orientedArea o (B - A) (C - A)

namespace OrientedTriangle

variable {o : Orientation ℝ E (Fin 2)}

/-- The three trisected interior angles of the triangle. -/
def alpha (T : OrientedTriangle E o) : ℝ := EuclideanGeometry.angle T.B T.A T.C / 3
def beta (T : OrientedTriangle E o) : ℝ := EuclideanGeometry.angle T.C T.B T.A / 3
def gamma (T : OrientedTriangle E o) : ℝ := EuclideanGeometry.angle T.A T.C T.B / 3

/-- The first intersection point obtained from the two adjacent red trisectors. -/
def X (T : OrientedTriangle E o) : E :=
  rotationFixedPoint o T.C T.B (2 * T.gamma) (2 * T.beta)

/-- The intersection point obtained cyclically at the second vertex. -/
def Y (T : OrientedTriangle E o) : E :=
  rotationFixedPoint o T.A T.C (2 * T.alpha) (2 * T.gamma)

/-- The intersection point obtained cyclically at the third vertex. -/
def Z (T : OrientedTriangle E o) : E :=
  rotationFixedPoint o T.B T.A (2 * T.beta) (2 * T.alpha)

/-- Having all three pairwise distances equal. -/
def Equilateral (P Q R : E) : Prop := dist P Q = dist Q R ∧ dist Q R = dist R P

/-- **Frank Morley's theorem.** The interior Morley triangle of every positively
oriented nondegenerate triangle is equilateral. -/
theorem _root_.XamboMorley.OrientedTriangle.main_result (T : OrientedTriangle E o) :
    Equilateral T.X T.Y T.Z := by
  sorry

end OrientedTriangle
