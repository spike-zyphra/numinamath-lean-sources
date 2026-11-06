import Mathlib

theorem algebra_13279 {x : ℝ} (hx : x > 0) (h : x + 1/x = 3) : x^4 + 1/x^4 = 47 := by
  have h1 : x ≠ 0 := by linarith
  have h2 : x^2 + 1 / x^2 = 7 := by
    have h2 : x + 1 / x = 3 := h
    calc
      x ^ 2 + 1 / x ^ 2 = (x + 1 / x) ^ 2 - 2 := by
        field_simp [h1]
        <;> ring
      _ = 3 ^ 2 - 2 := by rw [h2]
      _ = (9 : ℝ) - 2 := by norm_num
      _ = (7 : ℝ) := by norm_num
  calc
    x ^ 4 + 1 / x ^ 4 = (x^2 + 1 / x^2) ^ 2 - 2 := by
      field_simp [h1]
      <;> ring
    _ = 7 ^ 2 - 2 := by rw [h2]
    _ = (49 : ℝ) - 2 := by norm_num
    _ = (47 : ℝ) := by norm_num