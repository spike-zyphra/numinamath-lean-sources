import Mathlib

theorem algebra_231609 :
    {(x, y, z) : ℝ × ℝ × ℝ | x ^ 2 + y ^ 2 + z ^ 2 = 2 ∧ x - z = 2} = {(1, 0, -1)} := by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Assume (x, y, z) is in the set; prove it's (1, 0, -1)
    rintro ⟨h₁, h₂⟩
    have h3 : x = z + 2 := by
      linarith
    rw [h3] at h₁
    have h4 : y ^ 2 + 2 * (z + 1) ^ 2 = 0 := by
      nlinarith
    have h5 : y ^ 2 = 0 := by
      nlinarith [sq_nonneg (y), sq_nonneg (z + 1)]
    have h6 : y = 0 := by
      nlinarith
    have h7 : (z + 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (y), sq_nonneg (z + 1)]
    have h8 : z + 1 = 0 := by
      nlinarith [sq_nonneg (z + 1)]
    have h9 : z = -1 := by
      linarith
    have h10 : x = 1 := by
      linarith [h3, h9]
    simp [h10, h6, h9]
  · -- Show (1, 0, -1) is in the set
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · norm_num
    · norm_num