import Mathlib

theorem algebra_306340 {x y z : ℝ} (h₀ : x * y / (x + y) = 1 / 9) (h₁ : y * z / (y + z) = 1 / 11) (h₂ : x * z / (x + z) = 1 / 12) :
    x = 1 / 5 ∧ y = 1 / 4 ∧ z = 1 / 7 := by
  have hxy : x + y ≠ 0 := by
    by_contra h
    have : x * y / (x + y) = 0 := by
      rw [h]
      norm_num
    linarith

  have hyz : y + z ≠ 0 := by
    by_contra h
    have : y * z / (y + z) = 0 := by
      rw [h]
      norm_num
    linarith
  
  have hzx : x + z ≠ 0 := by
    by_contra h
    have : x * z / (x + z) = 0 := by
      rw [h]
      norm_num
    linarith

  have eq1 : 9 * x * y - x - y = 0 := by
    have h3 : x + y ≠ 0 := hxy
    field_simp [h3] at h₀
    linarith
  have eq2 : 11 * y * z - y - z = 0 := by
    have h4 : y + z ≠ 0 := hyz
    field_simp [h4] at h₁
    linarith
  
  have eq3 : 12 * x * z - x - z = 0 := by
    have h5 : x + z ≠ 0 := hzx
    field_simp [h5] at h₂
    linarith
  
  have h3 : x ≠ 0 := by
    by_contra hx
    have hx0 : x = 0 := by linarith
    rw [hx0] at eq1
    have : - y = 0 := by
      nlinarith
    have hy0 : y = 0 := by
      linarith
    rw [hy0] at eq2
    have : - z = 0 := by
      nlinarith
    have hz0 : z = 0 := by
      nlinarith
    have h4 : x + z = 0 := by
      nlinarith
    exfalso
    apply hzx
    linarith

  have h4 : y ≠ 0 := by
    by_contra hy0
    have hy00 : y = 0 := by linarith
    rw [hy00] at eq1
    have hx0 : x = 0 := by
      nlinarith
    exfalso
    apply h3
    linarith
  
  have h5 : z ≠ 0 := by
    by_contra hz0
    have hz00 : z = 0 := by linarith
    rw [hz00] at eq2
    have hy0 : y = 0 := by
      nlinarith
    exfalso
    apply h4
    linarith
  
  -- y = 1/4
  have hy2 : y = 1/4 := by
    apply (mul_left_inj' (show (y : ℝ) ≠ 0 by exact h4)).mp
    -- manipulate from h₀ and h₁
    nlinarith [sq_pos_of_ne_zero h4, sq_nonneg (x - 1/5), sq_nonneg (z - 1/7), 
      sq_pos_of_ne_zero (show (x : ℝ) ≠ 0 by exact h3), sq_pos_of_ne_zero (show (z : ℝ) ≠ 0 by exact h5),
      mul_ne_zero (show x ≠ 0 by exact h3) (show z ≠ 0 by exact h5)]
  
  have hx2 : x = 1/5 := by
    rw [show y = 1/4 by linarith [hy2]] at eq1
    apply (mul_left_inj' (show (x : ℝ) ≠ 0 by exact h3)).mp
    nlinarith [sq_pos_of_ne_zero (show (x : ℝ) ≠ 0 by exact h3), sq_pos_of_ne_zero (show (z : ℝ) ≠ 0 by exact h5), sq_nonneg (z - 1/7)]

  have hz2 : z = 1/7 := by
    rw [show y = 1/4 by linarith [hy2]] at eq2
    apply (mul_left_inj' (show (z : ℝ) ≠ 0 by exact h5)).mp
    nlinarith [sq_pos_of_ne_zero (show (z : ℝ) ≠ 0 by exact h5), sq_pos_of_ne_zero (show (x : ℝ) ≠ 0 by exact h3), sq_nonneg (x - 1/5)]
  
  constructor
  · exact hx2
  constructor
  · exact hy2
  · exact hz2