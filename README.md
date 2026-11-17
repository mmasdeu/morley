# Wessel's Algebra and Morley's Theorem in Lean

Complete Lean formalization of Sebastian Xambó-Descamps, *Wessel's Algebra and Morley's Theorem* (Geometry 2026, 3, 9).

## Main results

- Frank Morley's theorem: the interior Morley triangle is equilateral.
- The generalized constellation, tricolor equilaterality and side directions.
- Nine guide lines, three per Morley direction, with each constellation point on exactly two.
- Monochrome side directions, diagonal positivity, and all tricolor orientation classes.

The environment-wide audit found **3523 declarations with zero `sorryAx` dependencies**. The original principal results use only `propext`, `Classical.choice`, and `Quot.sound`.

## Files

- `XamboMorley.lean`: the compatibility wrapper for the completed development.
- `XamboMorleyBase.lean`: Wessel's algebra, trisectors, constellations, Morley's theorem, and supporting results.
- `Proofs/Guides/`: guide-line incidence, canonicalization, and counting proofs.
- `Proofs/Orientation/`: trigonometric and algebraic orientation proofs.
- `challenge.lean`: a 76-line, Mathlib-only statement of `main_result`, with the intentional `sorry` for the comparator.
- `solution.lean`: the corresponding application of the completed `T.morley` proof.

## Build and validation

```sh
lake build challenge solution
```

The completed development was compiled with Lean 4.33.1. The comparator configuration is `comparator.json`; Lean 4.35.0 or later provides `lake comparator` and `lake check`. Those newer commands have not been run in the current older environment, so no claim of acceptance by the latest built-in comparator is made.
