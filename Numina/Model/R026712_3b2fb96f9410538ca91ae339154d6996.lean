import Mathlib

theorem algebra_156169 (x y : ℕ) (h : x + y = 100) :
    x * y ≤ 2500 ∧ ∃ x y, x + y = 100 ∧ x * y = 2500 := by
  have h1 : y = 100 - x := by
    omega
  have h2 : x ≤ 100 := by
    omega
  have h3 : x * y ≤ 2500 := by
    rw [show y = 100 - x by linarith [h1]]
    by_cases h4 : x ≤ 50
    · -- x ≤ 50
      interval_cases x <;> omega
    · -- x > 50
      have h5 : x ≤ 100 := by
        omega
      interval_cases x <;> omega
  constructor
  · -- Show that x * y ≤ 2500
    exact h3
  · -- Show existence
    use 50, 50
    all_goals norm_num