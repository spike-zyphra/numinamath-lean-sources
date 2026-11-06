import Mathlib

theorem algebra_417 {a : ℝ} : (1 ^ 4 + a ^ 4 + (a + 1) ^ 4) / (1 ^ 2 + a ^ 2 + (a + 1) ^ 2) = a ^ 2 + a + 1 := by
  have h1 : (1 ^ 4 + a ^ 4 + (a + 1) ^ 4 : ℝ) = (a ^ 2 + a + 1) * (1 ^ 2 + a ^ 2 + (a + 1) ^ 2) := by
    ring
  have h2 : (1 ^ 2 + a ^ 2 + (a + 1) ^ 2 : ℝ) ≠ 0 := by
    have hne : (1 ^ 2 + a ^ 2 + (a + 1) ^ 2 : ℝ) > (0 : ℝ) := by
      nlinarith [sq_nonneg a]
    linarith

  field_simp [h2]
  <;> nlinarith [h1]
  all_goals tauto
  <;> nlinarith
  all_goals tauto