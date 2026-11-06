import Mathlib

theorem algebra_213356 :
  {(x, y, z) : ℝ × ℝ × ℝ | x^2 - 22*y - 69*z + 703 = 0 ∧ y^2 + 23*x + 23*z - 1473 = 0 ∧ z^2 - 63*x + 66*y + 2183 = 0} =
  {(20, -22, 23)} := by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Forward direction: if (x, y, z) satisfies the system, then (x, y, z) = (20, -22, 23)
    rintro ⟨h₁, h₂, h₃⟩
    have h4 : (x - 20)^2 + (y + 22)^2 + (z - 23)^2 = 0 := by
      nlinarith
    have hx : x = 20 := by
      nlinarith [sq_nonneg (x - 20), sq_nonneg (y + 22), sq_nonneg (z - 23)]
    have hy : y = -22 := by
      nlinarith [sq_nonneg (x - 20), sq_nonneg (y + 22), sq_nonneg (z - 23)]
    have hz : z = 23 := by
      nlinarith [sq_nonneg (x - 20), sq_nonneg (y + 22), sq_nonneg (z - 23)]
    simp [hx, hy, hz]
  · -- Backward direction: (20, -22, 23) satisfies the system
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num