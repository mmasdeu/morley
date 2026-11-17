import XamboMorleyBase
import Proofs.Guides.M6CLOSE_V
import Proofs.Orientation.M5Final

open Function Set
open XamboMorley.OrientedTriangle

namespace XamboMorley.OrientedTriangle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-- Exactly nine guide lines. -/
theorem guideLines_card (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.guideLines.ncard = 9 :=
  m6_guideLines_card T h

/-- Every constellation point is incident with exactly two guide lines. -/
theorem point_on_two_guideLines (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (q : ConstellationIndex) :
    {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard = 2 :=
  m6_point_on_two_guideLines T h q

/-- For each direction there are three parallel guide lines. -/
theorem guideLines_direction_card (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (v : E)
    (hv : v = T.Y - T.X ∨ v = T.Z - T.Y ∨ v = T.X - T.Z) :
    {ℓ ∈ T.guideLines | Parallel v ℓ.direction}.ncard = 3 :=
  m6_guideLines_direction_card T h v hv

/-- Orientation of the tricolor labels. -/
theorem tricolor_orientation (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (q : TricolorIndex) :
    (q.i + q.j + q.k = 0 → PositivelyOriented (o := o) (T.tricolorTriangle q)) ∧
    (q.i + q.j + q.k = 2 → NegativelyOriented (o := o) (T.tricolorTriangle q)) ∧
    (q.i + q.j + q.k = 1 →
      (q.i * q.j * q.k ≠ 0 ∧ PositivelyOriented (o := o) (T.tricolorTriangle q)) ∨
      (q.i * q.j * q.k = 0 ∧ NegativelyOriented (o := o) (T.tricolorTriangle q))) :=
  M5.tricolor_orientation_full T h q

end XamboMorley.OrientedTriangle
