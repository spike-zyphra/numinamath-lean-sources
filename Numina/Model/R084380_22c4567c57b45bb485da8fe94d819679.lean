import Mathlib

theorem algebra_4628 {x : ℝ} (hx : x > 0) (h : x - 1 / x = Real.sqrt 77) : x + 1 / x = 9 := by
  have h1 : x ≠ 0 := by linarith
  have h2 : (x - 1 / x) ^ 2 = 77 := by
    rw [h]
    rw [Real.sq_sqrt]
    all_goals norm_num
  have h3 : (x - 1 / x) ^ 2 = x^2 + (1 / x)^2 - 2 := by
    field_simp [h1]
    <;> ring
  have h4 : x^2 + (1 / x)^2 = 79 := by
    linarith [h2, h3]
  have h5 : (x + 1 / x) ^ 2 = 81 := by
    have h6 : (x + 1 / x) ^ 2 = x^2 + (1 / x)^2 + 2 := by
      field_simp [h1]
      <;> ring
    rw [h6]
    nlinarith [h4]
  have h7 : x + 1 / x > 0 := by
    positivity
  have h8 : x + 1 / x = 9 := by
    nlinarith [h5, h7]
  exact h8