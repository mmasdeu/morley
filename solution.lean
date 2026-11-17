import XamboMorleyBase

namespace XamboMorley.OrientedTriangle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable {o : Orientation ℝ E (Fin 2)}

/-- A proof of the proposition stated in `challenge.lean`: for every positively
oriented nondegenerate triangle, its interior Morley triangle is equilateral. -/
def _root_.XamboMorley.OrientedTriangle.main_result
    (T : _root_.XamboMorley.OrientedTriangle E o) :
  _root_.XamboMorley.OrientedTriangle.Equilateral T.X T.Y T.Z :=
  T.morley

#print axioms main_result

end XamboMorley.OrientedTriangle
