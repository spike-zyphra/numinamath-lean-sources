import Mathlib

theorem algebra_155857 :
    {(x, y, z) : ℝ × ℝ × ℝ | x ^ 3 - y = 6 ∧ y ^ 3 - z = 6 ∧ z ^ 3 - x = 6} = {(2, 2, 2)} := by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Assume (x, y, z) is a solution.
    rintro ⟨h1, h2, h3⟩
    have h4 : (x - 2) ^ 2 + (y - 2) ^ 2 + (z - 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2),
          sq_nonneg (x^2 - 4), sq_nonneg (y^2 - 4), sq_nonneg (z^2 - 4),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    have hx1 : x - 2 = 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2)]
    have hy1 : y - 2 = 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2)]
    have hz1 : z - 2 = 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2)]
    have hx2 : x = 2 := by linarith
    have hy2 : y = 2 := by linarith
    have hz2 : z = 2 := by linarith
    simp [hx2, hy2, hz2]
  · -- Show (2, 2, 2) is a solution
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · -- Check first equation
      norm_num
    constructor
    · -- Check second equation
      norm_num
    · -- Check third equation
      norm_num