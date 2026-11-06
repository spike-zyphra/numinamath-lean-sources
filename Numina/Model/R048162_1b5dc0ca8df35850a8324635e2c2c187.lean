import Mathlib

theorem algebra_251189 :
    {(x, y, z) : ℝ × ℝ × ℝ | x^2 + x - 1 = y ∧ y^2 + y - 1 = z ∧ z^2 + z - 1 = x} = {(-1, -1, -1), (1, 1, 1)} := by 
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- First, show that if (x,y,z) satisfy the system, then they must be one of the two solutions
    rintro ⟨h₁, h₂, h₃⟩
    have h4 : x^2 + y^2 + z^2 = 3 := by 
      nlinarith 
    have h5 : (x - 1) * (x + 1) = 0 := by 
      nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (z + 1), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), mul_self_nonneg (x + 1), mul_self_nonneg (y + 1), mul_self_nonneg (z + 1)]
    cases' (mul_eq_zero.mp h5) with h6 h7 
    · -- Case where x - 1 = 0, so x = 1
      have hx : x = 1 := by linarith
      have hy : y = 1 := by
        rw [hx] at h₁ 
        nlinarith 
      have hz : z = 1 := by 
        rw [hy] at h₂ 
        nlinarith 
      right
      simp [hx, hy, hz]
    · -- Case where x + 1 = 0, so x = -1
      have hx : x = -1 := by linarith 
      have hy : y = -1 := by 
        rw [hx] at h₁ 
        nlinarith 
      have hz : z = -1 := by 
        rw [hy] at h₂ 
        nlinarith 
      left
      simp [hx, hy, hz]
  · -- Show that the given solutions satisfy the system.
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · -- Check (-1, -1, -1)
      constructor
      · -- Check first equation
        norm_num 
      constructor 
      · -- Check second equation 
        norm_num 
      · -- Check third equation 
        norm_num 
    · -- Check (1, 1, 1)
      constructor 
      · -- Check first equation 
        norm_num 
      constructor 
      · -- Check second equation 
        norm_num 
      · -- Check third equation 
        norm_num