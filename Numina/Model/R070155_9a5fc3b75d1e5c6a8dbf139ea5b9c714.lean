import Mathlib

theorem algebra_3935
    {x y : ℝ}
    (h₀ : x ≠ 0)
    (h₁ : y ≠ 0)
    (h₂ : 6 / x + 2 / y = 15)
    (h₃ : 7 / x + 4 / y = 20) :
    x - y = -1 / 6 := by
  have eq1 : 6 * y + 2 * x = 15 * x * y := by
    field_simp [h₀, h₁] at h₂
    nlinarith
  have eq2 : 7 * y + 4 * x = 20 * x * y := by
    field_simp [h₀, h₁] at h₃
    nlinarith
  have eq4 : x = 1 / 2 := by
    nlinarith [sq_pos_of_ne_zero h₀, sq_pos_of_ne_zero h₁, sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x - 1 / 2), sq_nonneg (y - 2 / 3), h₀, h₁]
  have eq5 : y = 2 / 3 := by
    rw [eq4] at eq1
    nlinarith [sq_pos_of_ne_zero h₀, sq_pos_of_ne_zero h₁, sq_nonneg (x * y), sq_nonneg (y), sq_nonneg (y - 2 / 3), sq_nonneg (x - 1 / 2)]
  rw [eq4, eq5]
  norm_num