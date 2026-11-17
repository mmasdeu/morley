import Lake
open Lake DSL

/-- The Wessel/Morley comparator challenge and proof. -/
package xambo_morley where
  packagesDir := ".lake/packages"
  buildDir := ".lake/build"

require mathlib from "/opt/mathlib"
require cslib from "/opt/cslib"

/-- Shared geometric definitions, imported by both independent challenge and proof. -/
lean_lib XamboMorleyBase where
  globs := #[Glob.one `XamboMorleyBase]

/-- The trusted theorem statement. -/
lean_lib challenge where
  globs := #[Glob.one `challenge]

/-- The independently compiled proof of the same statement, and the default target
for `lake check`. -/
@[default_target]
lean_lib solution where
  globs := #[Glob.one `solution]
