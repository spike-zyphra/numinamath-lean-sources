import Mathlib

theorem algebra_253605 : {(x, y, z) : ℝ × ℝ × ℝ | x^2 + 1 = 2 * y ∧ y^2 + 1 = 2 * z ∧ z^2 + 1 = 2 * x} = {(1, 1, 1)} := by
  ext ⟨x, y, z⟩
  simp [-one_div]
  constructor
  · -- Assume (x, y, z) satisfy the system
    rintro ⟨h₁, h₂, h₃⟩
    have h4 : (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 = 0 := by
      nlinarith
    have hx1 : x - 1 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
    have hy1 : y - 1 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
    have hz1 : z - 1 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
    have hx2 : x = 1 := by linarith
    have hy2 : y = 1 := by linarith
    have hz2 : z = 1 := by linarith
    simp [hx2, hy2, hz2]
  · -- Show that (1, 1, 1) satisfies the system
    rintro (⟨rfl, rfl, rfl⟩)
    constructor
    · -- Check the first equation
      norm_num
    constructor
    · -- Check the second equation
      norm_num
    · -- Check the third equation
      norm_num