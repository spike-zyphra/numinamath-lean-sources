import Mathlib

theorem inequalities_2426 {a b : ℝ} (hab : a > b ∧ b > 0) : a / b > 1 := by
  have h1 : a > b := hab.1
  have h2 : b > 0 := hab.2
  have h3 : a - b > 0 := by linarith
  have h4 : a / b - 1 > 0 := by
    have h5 : a / b - 1 = (a - b) / b := by
      field_simp
      <;> ring
    rw [h5]
    apply div_pos
    exact h3
    all_goals linarith
  linarith
  all_goals linarith