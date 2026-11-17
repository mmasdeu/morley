# What `XamboMorley.lean` formalizes

> **Completed.** All eight formerly sorried targets are now proved. The active development is modular: `XamboMorleyBase.lean` contains the main development, `Proofs/Guides/` contains the guide proofs, and `Proofs/Orientation/` contains the final orientation proof. See [the completed proof-status report](results/proof-status.md). The earlier statements-only analysis below is retained as historical context, not as the current proof status.

This document describes the declarations in [`XamboMorley.lean`](XamboMorley.lean), using that file as its only mathematical source. It describes the Lean encoding itself; it does not independently assess faithfulness to any external text.

## 1. Scope and proof status

The file imports all of Mathlib and works inside the namespace `XamboMorley`. Almost all declarations are in a section `Plane` where `E` is equipped with:

- a normed additive commutative group structure;
- a real inner-product space structure;
- a `Fact` that its real dimension is two.

Most constructions also take an orientation `o : Orientation ℝ E (Fin 2)`. Thus, the geometric setting is not just `ℝ × ℝ`: it is a generic oriented, two-dimensional real inner-product space. The file is noncomputable, as expected from its use of choice, Clifford algebras, real exponentials, and circumcenters.

This is a **statements-only development, not a completed formal proof**. Theorems are generally declared with `:= by sorry`. Proof holes also occur in data-carrying definitions, including:

- nonzero-direction fields of the line constructors;
- the group laws for `ProperMotion`;
- affine independence in `OrientedTriangle.toSimplex`;
- completeness of the manually supplied `Fintype TrisectorColor` instance.

A small number of declarations are complete by `rfl`, and `isometry_injective` directly uses Mathlib's `Isometry.injective`. These exceptions do not change the overall status: the mathematical content is mostly specified rather than proved.

It is useful to distinguish two kinds of content below:

1. **Defined objects**, such as the Clifford algebra, rotations, trisectors, and constellation points.
2. **Asserted properties of those objects**, such as isometry claims, fixed-point formulas, Morley's theorem, and cardinality results. These properties currently depend on `sorry`.

## 2. The Wessel algebra and its coordinate model

### 2.1 The Clifford-algebra implementation

`planeQuadraticForm` turns the real inner product into a quadratic form. `WesselAlgebra E` is then literally

```lean
CliffordAlgebra (planeQuadraticForm (E := E))
```

with the local notation `G[E]`. The maps

- `scalar : ℝ → G[E]`, and
- `vec : E → G[E]`

are the canonical scalar and vector embeddings. The geometric product is therefore the multiplication already present in Mathlib's Clifford algebra; the file does not define a new multiplication operation on quadruples of real numbers.

A chosen positive orthonormal basis is obtained from `o`, and its two vectors are called `e₁ o` and `e₂ o`. The pseudoscalar is

```lean
pseudoscalar o = vec (e₁ o) * vec (e₂ o).
```

The file also defines exterior products `exteriorWedge`, their re-embedding `wedge` into the Clifford algebra, and oriented area via `o.areaForm`.

The three grades are represented by submodules:

- `gradeZero`: the range of the scalar map;
- `gradeOne`: the range of the vector embedding;
- `gradeTwo`: the real span of the pseudoscalar.

The even subalgebra `evenWessel` is `CliffordAlgebra.even`.

### 2.2 Geometric complex coordinates

The functions `toComplex` and `ofComplex` convert between vectors in `E` and complex coordinates relative to the chosen positive basis. They support several definitions:

- `geometricComplex` embeds a complex number as a scalar plus a pseudoscalar part;
- `unit o φ` represents the exponential of `φ` times the pseudoscalar;
- `complexMulVector` implements right multiplication of a vector by a complex coordinate;
- `rotateVector o v φ` multiplies the complex coordinate of `v` by `Circle.exp φ` and converts back;
- `perp` is rotation by `π/2`.

`vectorInverse` is the totalized formula `(‖v‖ ^ 2)⁻¹ • vec v`. Its defining expression is zero when `v = 0`; the inverse identities are asserted only for `v ≠ 0`.

### 2.3 Algebraic statements

The file states that:

- wedge is alternating and antisymmetric, and is computed by oriented area;
- the pseudoscalar is independent of the choice of positive orthonormal basis;
- every multivector has a unique scalar–vector–pseudoscalar representation;
- `1, e₁, e₂, pseudoscalar` form a four-element basis;
- vector multiplication decomposes into an inner-product scalar and a wedge bivector;
- nonzero vectors have two-sided inverses;
- the Clifford algebra has the expected universal existence-and-uniqueness property;
- the basis multiplication table has the expected signs, including `i² = -1`;
- the even subalgebra has the scalar-plus-pseudoscalar representation and admits a real-algebra equivalence with `ℂ`.

The bit presentation is also encoded. `Bits` consists of two Boolean coordinates, `bitAdd` is bitwise XOR, and `transpositionCounter` detects the relevant reversed pair. `bitBasis_mul` states the signed multiplication formula, while `transpositionCounter_associativity_parity` states the parity identity used for associativity.

For rotations, the asserted formulas include the cosine/sine decomposition, the right- and left-Clifford-product forms, and the half-angle conjugation formula. Although these connect the coordinate definition to the Clifford product, the connections themselves remain proof holes.

## 3. Euclidean primitives

### 3.1 Translations, rotations, and decompositions

A translation is `X ↦ X + v`. A point rotation about `P` is defined by

```lean
X ↦ P + rotateVector o (X - P) φ.
```

`Parallel v w` means that there is a real scalar `r` with `w = r • v`; `Orthogonal` is vanishing real inner product. The functions `parallelComponent` and `perpComponent` give the usual orthogonal decomposition relative to a direction vector. Their formulas contain division by the inner square of that direction, so their intended use is with nonzero directions.

The file asserts that translations and rotations are isometries, that rotations fix their centers, that angle zero gives the identity, and that a nontrivial rotation has no fixed point other than its center.

### 3.2 Lines, reflections, and intersections

A `Line E` is a record containing a base point, a direction, and a proof that the direction is nonzero. The interface includes:

- membership by an existential real parameter;
- conversion to an `AffineSubspace`;
- translation of a line by a vector;
- reflection of a vector as parallel component minus perpendicular component;
- reflection in a line;
- glided reflection followed by translation;
- parallelism through vanishing oriented area of directions.

The line angle uses Mathlib's oriented angle and converts it to a real representative in `(0,π]`. `Line.intersection` is an explicit oriented-area formula with division by the oriented area of the two directions. Theorems state that, in the nonparallel case, this point lies on both lines and is the unique common point.

Reflection is also related to the Clifford expression

```lean
vec u * vec (X - P) * vectorInverse u.
```

Other assertions characterize fixed points as points of the line, prove independence of the chosen base point and parallel direction, and identify nonzero glides parallel to the line as fixed-point-free.

### 3.3 A totalized fixed-point formula

`rotationFixedPoint o P Q φ ψ` supplies a point for every choice of inputs, using complex division:

$$
P+(Q-P)\frac{1-e^{i\psi}}{1-e^{i\phi}e^{i\psi}}.
$$

The later theorems add the denominator conditions needed to interpret it as the unique fixed point of the corresponding composition. Like the totalized vector inverse and line intersection, the definition itself does not enforce these conditions.

## 4. Oriented triangles and the main Morley statement

An `OrientedTriangle E o` consists of points `A`, `B`, and `C`, a proof that they are noncollinear, and positivity of the oriented area of `(B-A, C-A)`.

The real numbers `alpha`, `beta`, and `gamma` are defined as one third of the interior Euclidean angles at `A`, `B`, and `C`. Six interior trisector lines are then defined by rotating side directions:

| Line | Base | Direction obtained by rotating |
|---|---|---|
| `AZ` | `A` | `B-A` by `α` |
| `AY` | `A` | `B-A` by `2α` |
| `BX` | `B` | `C-B` by `β` |
| `BZ` | `B` | `C-B` by `2β` |
| `CY` | `C` | `A-C` by `γ` |
| `CX` | `C` | `A-C` by `2γ` |

The points `X`, `Y`, and `Z` are not initially defined as line intersections. They are defined by three cyclic instances of `rotationFixedPoint`, using angles `2α`, `2β`, and `2γ`. Separate theorem statements identify them with the intersections `BX ∩ CX`, `CY ∩ AY`, and `AZ ∩ BZ`.

`Equilateral P Q R` is the conjunction

```lean
dist P Q = dist Q R ∧ dist Q R = dist R P.
```

The central declaration `OrientedTriangle.morley` asserts this predicate for `X`, `Y`, and `Z`. Its proof is `sorry`.

The file also defines `alphaBar`, `betaBar`, and `gammaBar` as `2π/3` plus the corresponding angle, and states both the angle sum `3α+3β+3γ=π` and the complementary-angle relations.

## 5. Composition and classification of plane isometries

### 5.1 Translation, rotation, and reflection compositions

The composition section gives formulas for:

- translation after rotation, and rotation after translation, as rotations about newly defined centers;
- unique fixed points of those compositions under nonzero denominator hypotheses;
- two rotations as either a translation or a rotation, according as the product of their unit turns is or is not one;
- translation followed by reflection, and reflection followed by translation, as gliding symmetries;
- the criterion for those glides to be pure reflections, namely perpendicularity of the translation and line direction;
- rotation followed by reflection, and reflection followed by rotation, as gliding symmetries with explicitly constructed directions and base points;
- two reflections as a rotation for nonparallel lines, or a translation for parallel lines.

The two-reflection rotation uses the computed line intersection and twice the line angle. The parallel case uses twice the perpendicular component of the displacement between the base points. Reflection is also asserted to be involutive.

Several complex trigonometric formulas rewrite `1 - Circle.exp φ`, its inverse, and its product with `Circle.exp φ` using half-angles and sine terms.

### 5.2 `ProperMotion` and its matrix model

`ProperMotion E o` is a pair of a displacement in `E` and a turn in `Circle`. Its group operations implement the semidirect-product rule

$$
(v,u)(v',u')=(v+v'u,uu').
$$

The group axioms are currently sorried fields of the instance. Relative to a chosen origin `O`, `ProperMotion.action` applies the affine rule

$$
X\longmapsto v+(X-O)u.
$$

There are special constructors for translations and rotations about the origin. The file states compatibility of the action with multiplication, identity, inverses, injectivity, and isometry.

A proper motion is converted to a `2 × 2` complex matrix of the form

$$
\begin{pmatrix}1&0\\v&u\end{pmatrix}.
$$

`matrixMul` implements the file's modified product, and `pointVector` represents a point by `(1, X-O)`. Assertions cover product, identity, inverse, determinant, and the action on points. The angular map `delta` returns the turn, with statements identifying its unit-turn kernel with translations and asserting normality of translations.

`IsProperIsometry` means representability by such a proper motion. `IsImproperIsometry` means representability by a glided line reflection. Further statements give closure properties, disjointness, closure of their union, and classification of every isometry as one of these two types.

## 6. Symmetry expressions for the Morley construction

The rotations `RA`, `RB`, and `RC` are defined as rotations through `2α`, `2β`, and `2γ` about the corresponding vertices. Side-line constructors are added for `AB`, `BC`, `CA`, and the reversed lines `BA` and `CB`.

The declared symmetry results include:

- two reflection-factorizations for each of `RA`, `RB`, and `RC`;
- `RB ∘ RC`, `RC ∘ RA`, and `RA ∘ RB` as rotations about `X`, `Y`, and `Z`, respectively;
- reflection formulas for the third powers of `RA`, `RB`, and `RC`;
- the identity obtained by composing those third powers.

Unit turns `uA`, `uB`, and `uC` are defined from angles `2α`, `2β`, and `2γ`. For each of `X`, `Y`, and `Z`, the file states three expressions: a complex fixed-point quotient and two sine-scaled rotated-vector forms. It also states their trisector-intersection descriptions.

A separate general fixed-point theorem says that, away from unit product of turns, the composition of two rotations has exactly one fixed point and is a rotation about the computed fixed point through the sum of the angles. In the unit-product case it is a translation.

## 7. The equilateral criterion and side-length formulas

### 7.1 Complex weights and the cube root of unity

`weightedTriangleExpression` applies three complex weights to the displacements of `A`, `B`, and `C` from an origin `O`. The file asserts that this expression is independent of the origin exactly when the weights sum to zero.

The barycenter is `(A+B+C)/3`, and `omega` is `Circle.exp (2π/3)`. Its cubic identity and the relation `1+ω+ω²=0` are stated. Positive-oriented triangles are then characterized as equilateral by:

- vanishing of the weighted expression with weights `1, ω, ω²`;
- its specialization to origin `A`;
- the vector relation `B-A = ω(A-C)` expressed using `complexMulVector`.

### 7.2 Side directions and the strengthened length statement

The oriented side vectors are

```text
a = C-B,  b = A-C,  c = B-A.
```

Their lengths and normalized vectors are `aLength`, `bLength`, `cLength` and `aStar`, `bStar`, `cStar`. Rotational relations between the normalized vectors are asserted, as are decompositions of each side into length times unit direction.

Four angle transforms are defined by adding or subtracting `π/3` and `2π/3`: `thetaPrime`, `thetaSecond`, `thetaStar`, and `thetaStarStar`. Accompanying statements describe their sine and cosine relations.

The scalar `delta` is defined as `aLength / sin(3α)`. The final Morley formulas assert

$$
Z-Y=4\delta\sin\alpha\sin\beta\sin\gamma\,b_*e^{i(\beta+2\gamma)},
$$

together with cyclic formulas for `X-Z` and `Y-X`. `morley_side_lengths` consequently states that all three distances are

$$
4\delta\sin\alpha\sin\beta\sin\gamma.
$$

Preliminary and intermediate versions of the `Z-Y` computation are retained as separate statements, rather than collapsed into only the final equality.

## 8. Additional Euclidean and trigonometric statements

The file next provides four groups of declarations.

1. **General inner-product geometry.** Vector length is the norm and is identified with the square root of the inner square. Two-sided Cauchy–Schwarz bounds and existence-and-uniqueness of an unoriented angle in `[0,π]` are stated.
2. **Complex coordinates.** `complexLength`, `complexDot`, and `complexArea` are defined. Statements express them in coordinates and polar form, describe an oriented angle up to sign for nonzero complex numbers, and rewrite `conj z * w` in exponential form.
3. **The sine law and circumcircle.** A triangle is converted to a Mathlib affine simplex. Its oriented area and circumdiameter are defined. Theorems relate side products and sines to twice the area, state the sine law, identify `delta` with the side-product-over-area expression and with the circumdiameter, and express side lengths using `delta`.
4. **A triple-angle identity.** The file states a cosine form of `sin(3θ)`, a divided form under `sin θ ≠ 0`, and the undivided product identity using `thetaStar` and `thetaStarStar` for every real `θ`.

## 9. Trisectors, constellation points, and guide lines

### 9.1 Exterior trisectors

`TrisectorColor` has three constructors: `red`, `green`, and `blue`. `TrisectorLabel` is `ZMod 3`, and `labelAngle` converts its canonical value to a real multiple of `2π/3`.

Six families of generalized trisectors are defined by signed rotations of the six interior lines:

- red at `B`, positive from `BX`; red at `C`, negative from `CY`;
- green at `C`, positive from `CX`; green at `A`, negative from `AY`;
- blue at `A`, positive from `AZ`; blue at `B`, negative from `BZ`.

The zero-label simplification statements recover the original interior lines.

### 9.2 The 27 indexed points

A `ConstellationIndex` contains a color and two labels. `constellationPoint` assigns a fixed-point formula using the two angles associated with that color, with cycles `(B,C)`, `(C,A)`, and `(A,B)`. `trisectorPair` assigns the corresponding pair of generalized lines. A theorem identifies each constellation point with their computed intersection, and three fixed-point theorems give the rotated-composition characterization under non-unit-product hypotheses.

The three zero-label points are asserted to be `X`, `Y`, and `Z`.

`constellation` is the range of `constellationPoint`. Its cardinality is asserted to be 27 **under the additional assumption `Injective T.constellationPoint`**. Similar injectivity hypotheses support statements that each red trisector carries three indexed constellation points.

### 9.3 The nine guide lines

`IsGuideLine` is a defined predicate requiring:

- direction parallel to one of the three sides of `XYZ`;
- incidence with six constellation indices;
- exactly two incident indices of each color.

`guideLines` is the set satisfying this predicate. Assuming injectivity of the constellation-point map, the file asserts that there are nine such lines, that every constellation point lies on exactly two, and that there are three in each of the three Morley-side directions.

A separate `circumference` definition and theorem state that rotation about the center preserves distance from that center.

## 10. The 36-triangle gallery

`TriangleVertices` stores an ordered triple, retaining enough information to discuss orientation. A `TricolorIndex` consists of labels `i`, `j`, and `k` in `ZMod 3`. Its ordered vertices are

```text
red(i,j), green(j,k), blue(k,i).
```

There are therefore 27 tricolor labels.

A monochrome triangle is indexed by a color and one further label `s`. Its three indices are `(s,0)`, `(s+1,2)`, and `(s+2,1)` in that color, with arithmetic modulo three. Three colors and three values of `s` give nine monochrome labels. `GalleryIndex` is the sum of the tricolor and monochrome label types, and `galleryTriangle` maps either kind of label to its ordered vertices.

The main gallery assertions are:

- a tricolor triangle is equilateral iff `i+j+k ≠ 1` in `ZMod 3`;
- consequently, the non-equilateral tricolor case is `i+j+k = 1`;
- every monochrome triangle is equilateral;
- the sides of every equilateral tricolor triangle, and of every monochrome triangle, are parallel to sides of `XYZ`;
- the label-level counts are 18 equilateral and 9 non-equilateral tricolor triangles;
- with `Injective T.galleryTriangle`, the gallery has 36 elements;
- with both gallery and constellation injectivity hypotheses, 27 gallery elements are equilateral.

Positive and negative orientation are defined by the sign of oriented area. For tricolor labels, the file states:

- sum zero gives positive orientation;
- sum two gives negative orientation;
- in the non-equilateral sum-one case, nonzero product `i*j*k` gives positive orientation, while zero product gives negative orientation.

The diagonal labels `(i,i,i)` are separately asserted to be positively oriented. `redMonochromeTriangles` lists the three red monochrome examples; changing the color argument supplies the other colors.

## 11. Logical reading of the file

The file provides a broad, explicit **specification** of a geometric development. Its strongest concrete contributions are the choices of representations: Clifford algebras for Wessel algebra, oriented inner-product spaces for geometry, semidirect products for proper motions, fixed-point formulas for Morley points, and finite label types for the constellation and gallery.

It does **not** yet establish the main mathematical results without proof holes. In particular, `morley`, the strengthened side-length statement, the isometry classification, and the constellation/gallery classifications are all sorried declarations. Moreover, several formulas are totalized using inverse or division operations, while their intended interpretations are supplied only by later nonzero or nonparallel hypotheses. Those hypotheses are essential when using the definitions in future proofs.

Finally, the large-count results are not asserted wholly unconditionally: the constellation and gallery cardinality statements explicitly require injectivity of their indexing maps. Any later proof effort must therefore either prove those injectivity properties for the intended configurations or retain them as assumptions.
