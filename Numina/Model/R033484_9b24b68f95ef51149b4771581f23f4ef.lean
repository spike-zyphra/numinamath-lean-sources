import Mathlib

theorem algebra_15698 : IsGreatest {z : ℝ | ∃ x y, z = (x + 2*y + 3) / √(x^2 + y^2 + 1)} √14 := by
  constructor
  · -- Show that √14 is achieved, using x = 1/3, y = 2/3
    use 1 / 3, 2 / 3
    have h1 : (1 / 3 : ℝ) + 2 * (2 / 3) + 3 = 14 / 3 := by norm_num
    have h2 : (1 / 3 : ℝ) ^ 2 + (2 / 3 : ℝ) ^ 2 + 1 = 14 / 9 := by norm_num
    have h3 : Real.sqrt ((1 / 3 : ℝ) ^ 2 + (2 / 3 : ℝ) ^ 2 + 1) = Real.sqrt (14 / 9) := by
      rw [h2]
    have h4 : Real.sqrt (14 / 9 : ℝ) = Real.sqrt 14 / 3 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h4] at h3
    rw [h1, h3]
    field_simp
  · -- Show that √14 is the greatest such value
    rintro z ⟨x, y, rfl⟩
    suffices h : ((x + 2 * y + 3) / √(x ^ 2 + y ^ 2 + 1))^2 ≤ 14 by
      rw [show 14 = √14^2 by simp] at h
      exact (abs_le_of_sq_le_sq' h (by simp)).2
    have h1 : 0 < Real.sqrt (x^2 + y^2 + 1) := by
      apply Real.sqrt_pos.2
      nlinarith [sq_nonneg x, sq_nonneg y]
    have h2 : ((x + 2 * y + 3) / Real.sqrt (x ^ 2 + y ^ 2 + 1))^2 = (x + 2 * y + 3) ^ 2 / (x ^ 2 + y ^ 2 + 1) := by
      field_simp
    rw [h2]
    have h3 : (x + 2 * y + 3) ^ 2 ≤ 14 * (x ^ 2 + y ^ 2 + 1) := by
      nlinarith [sq_nonneg (x * 2 - y * 1), sq_nonneg (y * 3 - x * 2), sq_nonneg (x - 1 / 3), sq_nonneg (y - 2 / 3), Real.sqrt_nonneg (x^2 + y^2 + 1), sq_nonneg (3 * x - 2 * y), sq_nonneg (y + 1), sq_nonneg (x + 1)]
    have h4 : (x + 2 * y + 3) ^ 2 / (x ^ 2 + y ^ 2 + 1) ≤ 14 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    exact h4