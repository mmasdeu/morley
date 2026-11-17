# Xambó–Morley formalization: statement and proof-status audit

> **Final update:** All eight formerly open targets have since been proved and integrated with preserved statements. The active environment has **zero `sorryAx` dependencies** across 3,523 declarations. See [the completed proof-status report](proof-status.md) for the current module layout, successful builds, and axiom checks. The audit below records the earlier statements-only baseline.

Audited source: `attachments/please-formalize-in-lean-mwvr/2026-Xambo--Morley.pdf`, 29 pages.

Audited implementation: `XamboMorley.lean`, Lean 4.33.1 with the installed Mathlib.

## Conclusion

The development covers the paper's mathematical definitions and results in source order, apart from supporting declarations inserted where Lean requires them. It is not a completed proof of the paper: eight principal declarations remain `sorry`. No new mathematical proof was added during this audit. The malformed trailing wrapper left by the preceding integration was removed, and `monochrome_sides_parallel` was restored at its original position with its original statement and proof hole.

The statement-level coverage should not be confused with a proof of every result, nor with literal source-line identity. The latter is impossible for the current file: central theorems have moved after their supporting lemmas and many proof helpers have been inserted.

## Validation performed

- `lean .scratch/m7merged.lean`: exit 0; eight principal sorries.
- After repairing the declaration placement, `lean XamboMorley.lean`: exit 0; exactly eight `declaration uses sorry` warnings.
- There are no `admit`, explicit `axiom`, or explicit `sorryAx` declarations in the source. Occurrences of `sorry` at 12, 4930, 7282, 8137, and 8138 are comments, not proof holes.
- The exported declarations were inspected with `#print axioms`. The following use only `propext`, `Classical.choice`, and `Quot.sound`, not `sorryAx`:
  - `OrientedTriangle.morley`;
  - `OrientedTriangle.morley_trisector`;
  - `OrientedTriangle.morley_side_lengths`;
  - `OrientedTriangle.constellationPoint_eq_intersection`;
  - `OrientedTriangle.monochrome_equilateral`;
  - `evenWessel_equiv_complex`.
- Each of the eight principal open results below directly or transitively depends on `sorryAx`.
- `gallery_equilateral_card` also inherits the hole in `tricolor_equilateral_iff`; it cannot be described as an unconditionally established theorem merely because its own body contains no literal `sorry`.
- Finite-count proofs using `native_decide` additionally report the generated native-decision axiom (for example, `OrientedTriangle.gallery_equilateral_card`). This is separate from the explicit geometric sorries.

Exact validation output is retained in `.scratch/root-final-compile.log`, `.scratch/root-olean-compile.log`, and `.scratch/audit-axioms.log`; these are caches, not deliverables.

## The eight open principal declarations

| Declaration | Lean location | Paper content | Formal status |
|---|---:|---|---|
| `guideLines_card` | 9241–9242 | Figure A3: nine guide lines | `sorry` |
| `point_on_two_guideLines` | 9245–9247 | Figure A3: each constellation point belongs to exactly two guide lines | `sorry` |
| `guideLines_direction_card` | 9250–9253 | Figure A3: three guide lines in each direction | `sorry` |
| `tricolor_equilateral_iff` | 9309–9312 | Appendix B/C: equilateral iff the label sum is not 1 | `sorry` |
| `tricolor_sides_parallel` | 9576–9582 | Appendix B/C: equilateral tricolor sides parallel to the original Morley triangle | `sorry` |
| `monochrome_sides_parallel` | 9585–9590 | Appendix B/C: monochrome sides parallel to the original Morley triangle | `sorry` |
| `tricolor_orientation` | 9780–9786 | Signs displayed in Figures A4–A14 | `sorry` |
| `tricolor_diagonal_positive` | 9789–9791 | Positive orientation in Figures A4–A6 | `sorry` |

The forward implication for `tricolor_equilateral_iff` on labels whose sum is not 1 has a proved helper, `m7b_tricolor_equilateral_of_ne_one`. It is only a partial helper and does not eliminate the open equivalence. The complete proof under a later nested namespace named `m3p_monochrome_sides_parallel` likewise does not discharge the original open declaration.

## Passage-by-passage source coverage

The row ranges identify the main implementation regions, not a token-for-token translation of prose or a certification of every proof. Bibliographical notes, portraits, and figures are represented by their mathematical content rather than formalized as documents or graphics.

| Paper passage | Corresponding Lean development | Assessment |
|---|---|---|
| §1, Theorem 1 and Figure 1 (pp. 1–2) | `OrientedTriangle`, interior trisectors, `X`, `Y`, `Z` at 460–562; `morley` at 10220 | Same positive-oriented nondegenerate triangle and same equilateral conclusion. The theorem was moved after its supporting results for Lean dependency order. |
| §2, ⋄1: algebra and pseudoscalar (p. 3) | 566–1164 | Mathlib's `CliffordAlgebra` of the inner-product quadratic form; scalar/vector embeddings, basis, grades, oriented area, pseudoscalar and multivector representation are present. |
| §2, ⋄2: geometric product and Table 1 (pp. 3–4) | 1166–1358 | Geometric-product formula, inversion, universal property, basis products, Boolean index arithmetic and associativity parity are declared. The Clifford construction supplies existence/associativity rather than duplicating the paper's table proof. |
| §2, ⋄3: even subalgebra (pp. 4–5) | 1360–1809 | `CliffordAlgebra.even`, its scalar/pseudoscalar representation, and the algebra equivalence with complex numbers are present. |
| §2, ⋄4–⋄5 and Equations (3)–(6) (pp. 5–6) | 1811–2121 | Points/translations, rotations, lines, reflection, glides, fixed points and isometry statements are covered. |
| §3, ⋄6–⋄7 and Equations (7)–(8) (pp. 6–8) | 2123–2333 | Translation/rotation centers and the two-rotation alternative are formalized with explicit nonzero-denominator hypotheses. |
| §3, ⋄8–⋄10 and Equations (9)–(11) (pp. 8–10) | 2335–3184 | Translation/reflection and rotation/reflection glides; two reflections as a rotation or a translation, plus reflection involutivity. |
| §3, ⋄11 and Equation (12) (pp. 10–12) | 3186–3476 | Semidirect-product `ProperMotion`, its action, matrix representation, determinant/angular character and translation kernel. |
| §3, Remark 3 (p. 12) | 3478–4046 | Proper/improper isometry predicates, closure and classification of every isometry. |
| §4, Equation (13) and Theorem 2 (p. 12) | 4048 onward, before the coordinate/fixed-point targets | Rotation definitions, reflection factorizations, compositions about `X,Y,Z`, cube formulas and the identity product. Helpers are interleaved through this region. |
| §4, Theorem 3 and Equation (14) (pp. 12–13) | 5626–5643 | Unique fixed point or translation, with the same composition order `rotation Q ψ ∘ rotation P φ`. |
| §4, Corollary 1 and Remark 4 (p. 13) | Corollary coordinate support around 4929–5624; triangle construction at 460–562 | All three forms for each of `X,Y,Z`, their intersections with the trisectors, and the sine-law coordinate expressions. |
| §4, ⋄12 and Equations (15)–(16) (p. 14) | 5645–5953 | Origin independence iff weights sum to zero, cube-root-of-unity algebra, weighted equilateral criterion and its origin-at-a-vertex specialization. The general orientation case uses a two-alternative Napoleon criterion; the positively oriented source case has the single-equation criterion. |
| §5, ⋄13–⋄14 and Equations (17), (18), (18a), (18b) (pp. 14–15) | 5955–6050 for definitions/support; final formulas at 10196–10220 | Side vectors, unit star vectors, angle transforms and all three Morley-side formulas are included. `morley_side_lengths` has the common value `4δ sin α sin β sin γ`. |
| Appendix A, ⋄17 (pp. 16–17) | 6052 onward | Norm/inner product, Cauchy–Schwarz bounds and angle existence/uniqueness. |
| Appendix A, ⋄18 (p. 17) | 6076–6205 | Complex length, inner product, oriented area, polar formulas and oriented-angle description. |
| Appendix A, ⋄19, (A1)–(A2) (pp. 17–18) | 6207–7036 | Oriented area, sine law, side-length formulas and identification of `δ` with the circumdiameter. |
| Appendix A, ⋄20, (A3)–(A4) (p. 18) | 7038–7078 | The divided identity uses the explicit hypothesis `sin θ ≠ 0`; (A4) is valid for all real `θ`. |
| Appendix B, Figure A2: colored exterior trisectors (p. 19) | 7080–7175 | Three labels in `ZMod 3`, six line families, `redC_zero = CX`, `greenC_zero = CY`, and the remaining zero-label reductions. |
| Appendix B, 27-point constellation (pp. 18–20) | `ConstellationIndex`, `constellationPoint`, `trisectorPair`; exact intersection proof at 8068; incidence and coordinate formulas thereafter | The cyclic center and sign conventions match the generalized fixed-point formulas. Indexed intersection and trisector incidences are covered. The set-count theorem additionally assumes injectivity of the indexing map. |
| Appendix B, Figure A3: guide lines (p. 20) | 8986–9253; counting/count helpers later | The six-point/two-per-color and direction conditions are present. Canonical line representatives avoid counting infinitely many rescalings of the same geometric line. Three main theorems remain sorried. |
| Appendix B, final rotation-on-circumference remark (p. 20) | 9256–9265 | Rotation about its center preserves distance from that center. |
| Appendix B/C, 27 tricolor triangles (pp. 20–26) | 9270–9305, 9307–9330, 9576–9582, 9693–9786 | Parametric labels generate all ordered triples, the equilateral criterion/count and orientation classes are declared; equilateral, parallelism and orientation geometry remains open as listed above. |
| Appendix C, nine monochrome triangles (pp. 21, 27–28) | 9290–9297, 9322–9573, 9584–9590, `redMonochromeTriangles` at 9795 | The same `monochromeTriangle` family with each color covers Figures A15–A17. Equilateralism has a checked proof; parallel-side geometry remains sorried. |
| Appendix C, 36-gallery totals (p. 21) | 9701–9767 | The label-level counts are 36, 18, 9, and 27. Image cardinality results assume injectivity; the 27-equilateral result inherits the open tricolor criterion. |

## Meaning-carrying definitions checked

These are definition choices that materially affect whether the statements say what the paper says:

1. **Wessel algebra:** `WesselAlgebra E` is Mathlib's Clifford algebra of `planeQuadraticForm`. This matches the geometric-product relation and avoids importing a commutative multiplication on ordinary vectors.
2. **Rotation and fixed-point order:** `rotationFixedPoint o P Q φ ψ` represents the fixed point of `rotation Q ψ ∘ rotation P φ`, consistent with Equation (14).
3. **Interior Morley centers:** `X` uses centers `(C,B)` with angles `(2γ,2β)`, `Y` uses `(A,C)` with `(2α,2γ)`, and `Z` uses `(B,A)` with `(2β,2α)`. Corollary 1's formulas follow this convention.
4. **Generalized labels:** the fixed-point angles subtract `labelAngle`, and the generalized trisectors use corresponding positive/negative rotations. Their zero-label reductions match the interior trisectors.
5. **Intersections:** the line-intersection formula has a positive sign on the scaled direction. The proved membership statements, rather than the comment alone, are what make this convention usable.
6. **Equilateral:** exactly the equalities `dist P Q = dist Q R` and `dist Q R = dist R P`. Degenerate equal-point configurations are not excluded by this predicate, as in the paper's distance-only criterion; the ambient source triangle remains nondegenerate.
7. **Guide-line representatives:** `Line.isCanonical` requires a unit direction, perpendicular-foot base, and an angular-sector restriction. `guideLines` counts these representatives rather than arbitrary records of a geometric line. Uniqueness of the representative is formalized; the actual geometric classification remains among the sorries.
8. **Angles and totalized formulas:** division in complex fixed-point formulas and line intersections is totalized by Lean. The meaningful uniqueness/membership conclusions carry nonzero or nonparallel hypotheses instead of assuming every denominator is nonzero.

These checks establish correspondence of the inspected definitions; they do not substitute for checking the eight missing proofs.

## Remaining statement-level limitations

- The paper asserts its geometric conclusions for an arbitrary triangle as defined there. Several corresponding constellation/gallery declarations have an additional hypothesis `Injective T.constellationPoint` or `Injective T.galleryTriangle`. They are conditional formal statements, not yet the unconditional paper claim, even where such injectivity is expected to follow in generic configurations.
- The source has separate displayed figures; the Lean file uses parametric definitions and orientation predicates instead of one declaration per drawing. This is appropriate for the mathematical content, but not a pixel-level formal representation of Appendix C.
- Later helper blocks include nested `OrientedTriangle.OrientedTriangle` names and extensive integration comments. They compile, but the source is no longer a minimal literal line-by-line transcription.
- The existing top-level `XamboMorley.md` predates much of the integrated proof work and describes an older all-sorried version. This audit reflects the current Lean file and compiler output instead.

## Scope note

The retained task is a formal specification with the remaining proofs intentionally sorried. The prior proof-completion swarm was stopped and its files preserved. No claim is made that any of the eight open results became proved during this audit. No Git commit was created; all project files remain untracked, as they were at the start of this continuation.
