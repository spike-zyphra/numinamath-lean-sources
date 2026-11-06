import Mathlib

/-Let k be a non-negative integer. Show that there exist non-negative integers x,y,z,w,v such that
16x+17y+23z+39w+40v=100k-/

theorem number_theory_640273 (k: ℕ): ∃ x y z w v : ℕ, 16 * x + 17 * y + 23 * z + 39 * w + 40 * v = 100 * k := by

  use (2 * k)
  use (4 * k)
  use 0
  use 0
  use 0
  ring