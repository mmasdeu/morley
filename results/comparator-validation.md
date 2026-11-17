# Comparator challenge and solution

## Files

- `challenge.lean`: **76 lines** importing only Mathlib. It contains only the geometry essential to the theorem statement: an oriented orthonormal basis, oriented area, complex coordinates, the fixed-point rotation formula, a nondegenerate positively oriented triangle and its trisected interior angles, the three interior Morley vertices, and `Equilateral`. `main_result` is stated with `sorry`. It does **not** import `XamboMorleyBase`.
- `solution.lean`: **18 lines** proving that proposition by `T.morley`. Both files import `XamboMorleyBase`, rather than duplicating its definitions.
- `lakefile.lean`: a self-contained `challenge` and the `solution` target using the original base proof library, with local prebuilt `mathlib` and `cslib` dependencies. `solution` is the default target used by `lake check`.
- `comparator.json`: selects only `XamboMorley.OrientedTriangle.main_result` and the three standard axioms.
- `lean-toolchain`: `leanprover/lean4:v4.33.1`, the version actually compiled here.

The main definition proves `Equilateral T.X T.Y T.Z` for each positively oriented nondegenerate triangle. Only the definitions required to understand Morley's statement are in `challenge.lean`; its `sorry` refers to exactly the equilaterality of the interior Morley triangle, not a generic placeholder. `solution.lean` remains an application of the completed `T.morley`.

## Verified here

```sh
lake build solution
# Build completed successfully (8707 jobs).

lake build challenge solution
# Build completed successfully (8710 jobs), with the intended `declaration uses sorry` warning in `challenge.lean` only.
```

The latter succeeded on November 17, 2026. The individual axiom output was:

```text
'XamboMorley.OrientedTriangle.main_result' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

`lake-manifest.json` was produced by the successful local build.

## Comparator and Lake check status

The [official validation guide](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) uses `lake comparator` with the challenge/solution configuration. On Lean 4.35.0 or later, the corresponding invocation for this project is:

```sh
lake comparator comparator.json
```

`lake check` runs the standard-axiom check on a project's default targets, not on an identifier `def main_result`.

The currently installed compiler is Lean 4.33.1. It reports `unknown command 'check'` and `unknown command 'comparator'`. The built-in commands were introduced in 4.35.0, so those two commands were **not executed successfully here**. No claim is made that the latest Lake comparator has already accepted the artifacts in this VM. No newer shared toolchain was installed or selected.

The legacy standalone comparator's configuration schema and local target-name details were checked against [its official README](https://github.com/leanprover/comparator). The sources compile independently with matching exact declaration names and proof result types; comparator acceptance remains a separate validation step on a supported toolchain.
