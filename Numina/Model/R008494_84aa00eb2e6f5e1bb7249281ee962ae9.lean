import Mathlib
open Mathlib
lemma algebra_1194 (bricks brenda_alone brandon_alone : ℚ) (h1 : bricks = 9 * brenda_alone) (h2 : bricks = 10 * brandon_alone) (h3 : bricks = 5 * (brenda_alone + brandon_alone - 10)) : bricks = 900 := by
  have eq1 : brenda_alone = bricks / 9 := by
    linarith
  have eq2 : brandon_alone = bricks / 10 := by
    linarith
  rw [eq1, eq2] at h3
  linarith