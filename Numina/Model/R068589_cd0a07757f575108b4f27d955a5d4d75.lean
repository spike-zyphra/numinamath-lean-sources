import Mathlib

theorem algebra_291084 {y : ℝ} (hy : |y| < 1) :
    |(1 - y) / (1 / (1 + y)) - 1| = y ^ 2 := by
  have h1 : (1 + y) ≠ 0 := by
    by_contra h
    have h2 : y = -1 := by linarith
    have h3 : |y| = 1 := by
      rw [h2]
      norm_num
    linarith [abs_lt.mp hy, h3]

  have eq1 : (1 - y) / (1 / (1 + y)) = (1 - y) * (1 + y) := by
    field_simp [(show (1 + y) ≠ 0 by assumption)]

  have eq2 : (1 - y) / (1 / (1 + y)) = 1 - y^2 := by
    rw [eq1]
    ring

  rw [eq2]

  have eq3 : (1 - y^2 : ℝ) - 1 = -y^2 := by
    ring

  rw [eq3]

  simp [abs_neg, sq_nonneg]