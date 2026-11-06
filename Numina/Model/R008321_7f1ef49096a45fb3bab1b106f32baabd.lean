import Mathlib

theorem number_theory_4824 (a b : ℝ) : ⌊a + b⌋ ≥ ⌊a⌋ + ⌊b⌋ := by
  exact Int.le_floor_add a b