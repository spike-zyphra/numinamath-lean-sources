import Mathlib

theorem algebra_112730 : {(x, y) : ℝ × ℝ | x + y = 1 ∧ x^3 + y^3 = 19} = {(3, -2), (-2, 3)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume h : (x, y) satisfies both equations
    rintro ⟨h₁, h₂⟩
    have h3 : y = 1 - x := by linarith
    rw [h3] at h₂
    have h4 : x^2 - x - 6 = 0 := by
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x + 2), sq_nonneg (x - (1 - x))]
    -- Now solve the quadratic equation
    have h5 : (x - 3) * (x + 2) = 0 := by
      nlinarith [h4]
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- Case where x = 3
      have hx : x = 3 := by linarith
      have hy : y = -2 := by linarith [hx, h3]
      left
      simp [hx, hy]
    · -- Case where x = -2
      have hx : x = -2 := by linarith
      have hy : y = 3 := by linarith [hx, h3]
      right
      simp [hx, hy]
  · -- Show that (3, -2) and (-2, 3) satisfy both equations
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (3, -2)
      constructor
      · norm_num
      · norm_num
    · -- Check (-2, 3)
      constructor
      · norm_num
      · norm_num