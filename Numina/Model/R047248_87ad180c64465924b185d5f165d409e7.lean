import Mathlib



theorem algebra_187766 {a b : ℝ} (h : a * b * (a + b) = 1) :
    a / (a ^ 3 + a + 1) = b / (b ^ 3 + b + 1) := by
  have h1 : a ^ 3 + a + 1 ≠ 0 := by 
    by_contra h3
    have h4 : a = 0 := by
      nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a + b), sq_nonneg (a - b),
        sq_nonneg (a * b - 1), sq_nonneg (a + 1), sq_nonneg (b + 1),
        sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2)]
    have h5 : a * b * (a + b) = 0 := by
      rw [h4]
      ring
    linarith
  have h2 : b ^ 3 + b + 1 ≠ 0 := by 
    by_contra h3
    have h4 : b = 0 := by 
      nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a + b), sq_nonneg (a - b),
        sq_nonneg (a * b - 1), sq_nonneg (a + 1), sq_nonneg (b + 1),
        sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2)]
    have h5 : a * b * (a + b) = 0 := by 
      rw [h4]
      ring
    linarith
  have h3 : a * (b ^ 3 + b + 1) = b * (a ^ 3 + a + 1) := by
    nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2 - 1), sq_nonneg (a * b - 1),
      sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2)]
  have h4 : a / (a ^ 3 + a + 1) - b / (b ^ 3 + b + 1) = 0 := by
    have h5 : a / (a ^ 3 + a + 1) - b / (b ^ 3 + b + 1) = (a * (b ^ 3 + b + 1) - b * (a ^ 3 + a + 1)) / ((a ^ 3 + a + 1) * (b ^ 3 + b + 1)) := by
      field_simp [h1, h2]
      ring
    rw [h5]
    have h6 : a * (b ^ 3 + b + 1) - b * (a ^ 3 + a + 1) = 0 := by linarith [h3]
    rw [h6]
    norm_num
  linarith