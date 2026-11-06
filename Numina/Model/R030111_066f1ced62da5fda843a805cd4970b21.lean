import Mathlib

theorem algebra_252022 {a b c d : ℝ} (h : a ≠ 0) (h' : b ≠ 0) (h'' : c ≠ 0) (h''' : d ≠ 0)
    (h'''' : 1 / a + 1 / b + 1 / c + 1 / d = 0) :
    (a + b + c + d)^3 = (a + b + c + d) * (a + b - c - d)^2 + (a + b + c + d) * (a - b + c - d)^2 +
    (a + b + c + d) * (a - b - c + d)^2 - 2 * (a + b - c - d) * (a - b + c - d) * (a - b - c + d) := by
  have eq1 : a * b * c + a * b * d + a * c * d + b * c * d = 0 := by
    have eq2 : 1 / a + 1 / b + 1 / c + 1 / d = (b * c * d + a * c * d + a * b * d + a * b * c) / (a * b * c * d) := by 
      field_simp [h, h', h'', h''']
      <;> ring
    rw [eq2] at h''''
    have eq3 : b * c * d + a * c * d + a * b * d + a * b * c = 0 := by
      have : a * b * c * d ≠ 0 := by
        apply mul_ne_zero
        apply mul_ne_zero
        apply mul_ne_zero
        exact h
        exact h'
        exact h''
        exact h'''
      field_simp [this] at h''''
      nlinarith
    linarith
  nlinarith [sq_nonneg (a + b + c + d), sq_nonneg (a + b - c - d), sq_nonneg (a - b + c - d), sq_nonneg (a - b - c + d), 
            sq_nonneg (a * b * c * d), 
            sq_nonneg (a * b * c + a * b * d + a * c * d + b * c * d),
            sq_nonneg (a * b + a * c + a * d + b * c + b * d + c * d),
            sq_nonneg (a - b - c - d),
            sq_nonneg (b - a - c - d),
            sq_nonneg (c - a - b - d),
            sq_nonneg (d - a - b - c)]