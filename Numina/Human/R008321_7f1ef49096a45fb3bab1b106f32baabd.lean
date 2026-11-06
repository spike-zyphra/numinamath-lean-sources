import Mathlib

/- Show that if \( a \) and \( b \) are real numbers, then \( [a+b] \geq [a] + [b] \), where \( [x] \) denotes the greatest integer less than or equal to \( x \).-/
theorem number_theory_4824 (a b : ℝ) : ⌊a + b⌋ ≥ ⌊a⌋ + ⌊b⌋ := by
  -- exact `Int.le_floor_add` in Mathlib
  apply Int.le_floor_add
