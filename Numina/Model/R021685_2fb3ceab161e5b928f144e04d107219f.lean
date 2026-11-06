import Mathlib

theorem algebra_207573 {x1 x2 : ℝ} (hx : x1^2 + 5 * x1 + 1 = 0 ∧ x2^2 + 5 * x2 + 1 = 0)
    (hx12 : x1 ≠ x2) :
    ((x1 * Real.sqrt 6) / (1 + x2))^2 + ((x2 * Real.sqrt 6) / (1 + x1))^2 = 220 := by
  rcases hx with ⟨h1, h2⟩
  have h3 : x1 + x2 = -5 := by
    have h4 : x1^2 + 5 * x1 + 1 - (x2^2 + 5 * x2 + 1) = 0 := by linarith
    have h5 : (x1 - x2) * (x1 + x2 + 5) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- x1 - x2 = 0
      exfalso
      apply hx12
      linarith
    · -- x1 + x2 + 5 = 0
      linarith
  have h4 : x1 * x2 = 1 := by
    nlinarith [sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by
      intro h
      apply hx12
      linarith
    ), sq_nonneg (x1 + x2), sq_nonneg (x1 * x2)]
  
  have hx12ne : 1 + x2 ≠ 0 := by
    by_contra h
    have h22 : x2 = -1 := by linarith
    rw [h22] at h2
    nlinarith
  
  have hx12ne' : 1 + x1 ≠ 0 := by
    by_contra h
    have h11 : x1 = -1 := by linarith
    rw [h11] at h1
    nlinarith
  
  have h10 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h8 : ((x1 * Real.sqrt 6) / (1 + x2)) ^ 2 = (6 * x1^2) / (1 + x2)^2 := by
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num), Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num), h10]
  
  have h9 : ((x2 * Real.sqrt 6) / (1 + x1)) ^ 2 = (6 * x2^2) / (1 + x1)^2 := by
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num), Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num), h10]
  
  rw [h8, h9]
  field_simp [hx12ne, hx12ne', pow_two, h10]
  <;> nlinarith [h1, h2, h3, h4, Real.sqrt_nonneg 6, Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num)]