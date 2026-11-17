# Completed Lean formalization status

## Result

The entire `XamboMorley` environment now has **zero `sorryAx` dependencies**. An environment-wide check covered **3,523 declarations**.

All eight formerly open targets are proved:

- `OrientedTriangle.guideLines_card`
- `OrientedTriangle.point_on_two_guideLines`
- `OrientedTriangle.guideLines_direction_card`
- `OrientedTriangle.tricolor_equilateral_iff`
- `OrientedTriangle.tricolor_sides_parallel`
- `OrientedTriangle.monochrome_sides_parallel`
- `OrientedTriangle.tricolor_diagonal_positive`
- `OrientedTriangle.tricolor_orientation`

Their original statements and injectivity premises are preserved. Individual axiom checks for these eight, `OrientedTriangle.morley`, and `evenWessel_equiv_complex` are exactly `[propext, Classical.choice, Quot.sound]`. No additional trust assumptions are asserted here for other declarations carrying pre-existing `native_decide` computations.

## Module layout

- `XamboMorleyBase.lean` contains the main Wessel/Morley development and proved supporting results.
- `XamboMorley.lean` is a compatibility wrapper exporting the three guide-line theorems and the final orientation theorem.
- `Proofs/Guides/` contains the line constructions, incidence certificates, counting arguments, and canonicalization needed for the guide results.
- `Proofs/Orientation/` contains the algebraic key, trigonometric parameterizations, exact oriented-area formula, nine sum-one signs, and final orientation assembly.

The modular arrangement preserves the original namespaces used by the independently verified proof components. It avoids the namespace mirroring and duplicate declaration issues caused by flattening them into one source file.

## Proof methods

- The guide-line upper bound follows from finite incidence counting: each of the nine six-index sets has six incidences, every index belongs to exactly two of those sets, and any guide line outside the known nine would force a contradiction between six disjoint two-element index sets and the nine indices. The three direction classes are pairwise disjoint and have at most three members each.
- The lower bound and exact point incidence are obtained by double counting guide-line incidences.
- Tricolor equilaterality is established by exact algebraic side identities and geometric rotated-line uniqueness arguments.
- Parallel side directions follow from exact phase/realness certificates and cyclic transport.
- For sum-one tricolor triangles, the final orientation proof uses exact vertex normal forms and the algebraic key connecting the oriented area to the tangent-variable `Lamab` expression. Its sign is evaluated using the two possible angle-sum identities. Combined with the previously proved sum-zero and sum-two clauses, this proves all nine sum-one signs and hence `tricolor_orientation`.

## Validation performed

With the repository root on `LEAN_PATH` together with `Proofs/Guides` and `Proofs/Orientation`:

```bash
lean -o XamboMorleyBase.olean XamboMorleyBase.lean
lean -o XamboMorley.olean XamboMorley.lean
```

Both completed successfully with **no `declaration uses sorry` warning and no compilation errors**.

The complete orientation dependency chain was also rebuilt independently:

```bash
cd Proofs/Orientation
for f in M8KLocal M5Tan M5Trig M5Pre M5Area M5Final; do
  lean -o "$f.olean" "$f.lean"
done
```

Every guide source module was compiled with its native namespace rather than flattened into the root.

An explicit `#print axioms` check over all eight original principals produced no `sorryAx`. The environment audit additionally produced:

```text
total 3523, sorry-dependent 0: []
```

Source scanning finds no executable `:= by sorry`, `admit`, explicit new `axiom`, or use of `sorryAx`. The only textual `sorry` occurrences left are stale explanatory comments, not proof holes.

No Git commit was created.
