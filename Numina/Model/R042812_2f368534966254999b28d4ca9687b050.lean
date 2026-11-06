import Mathlib

theorem algebra_129782 :
    {(x, y, z) : ℝ × ℝ × ℝ | x + y = 2 ∧ x * y - z ^ 2 = 1}.ncard = 1 := by
  have h1 : {(x, y, z) : ℝ × ℝ × ℝ | x + y = 2 ∧ x * y - z ^ 2 = 1} = {(1, 1, 0)} := by
    ext ⟨x, y, z⟩
    simp [-mul_add, -add_mul]
    constructor
    · -- Assume ⟨x, y, z⟩ satisfies the system
      rintro ⟨h₁, h₂⟩
      have h3 : y = 2 - x := by linarith
      rw [h3] at h₂
      have h4 : (x - 1) ^ 2 + z ^ 2 = 0 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg z]
      have hx1 : (x - 1) ^ 2 = 0 := by
        linarith [sq_nonneg (x - 1), sq_nonneg z]
      have hx2 : x - 1 = 0 := by
        rw [sq_eq_zero_iff] at hx1
        linarith
      have hz1 : z ^ 2 = 0 := by
        linarith [sq_nonneg (x - 1), sq_nonneg z]
      have hz2 : z = 0 := by
        rw [sq_eq_zero_iff] at hz1
        linarith
      have hx3 : x = 1 := by linarith
      have hy1 : y = 1 := by 
        rw [show x = 1 by linarith [hx3]] at h3
        linarith
      simp [hx3, hy1, hz2]
    · -- Show that (1, 1, 0) satisfies the system
      rintro ⟨rfl, rfl, rfl⟩
      constructor <;> norm_num
  rw [h1]
  simp [Set.ncard_singleton]