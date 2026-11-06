import Mathlib

theorem algebra_46 {a b : ℝ} (h₀ : a^2 * (b^2 + 1) + b * (b + 2 * a) = 40) (h₁ : a * (b + 1) + b = 8) :
    1 / a^2 + 1 / b^2 = 8 := by
  have h2 : a * b + a + b = 8 := by
    linarith 
  have h3 : (a * b) ^ 2 + (a + b) ^ 2 = 40 := by
    nlinarith [h₀, h2]
  have h4 : (a + b) ^ 2 - 8 * (a + b) + 12 = 0 := by 
    nlinarith [h3, h2]
  have h5 : (a + b - 6) * (a + b - 2) = 0 := by
    nlinarith 
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- Let's proceed with case $a + b = 6$
    have h8 : a + b = 6 := by linarith
    have h9 : a * b = 2 := by
      nlinarith [h2, h8]
    have ha1 : a ≠ 0 := by
      by_contra h00
      have h01 : a = 0 := by linarith 
      rw [h01] at h9 
      nlinarith 
    have hb1 : b ≠ 0 := by
      by_contra h00
      have h01 : b = 0 := by linarith 
      rw [h01] at h9 
      nlinarith 
    have h10 : a ^ 2 + b ^ 2 = 32 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 6)]
    have h11 : 1 / a^2 + 1 / b^2 = (a ^ 2 + b ^ 2) / (a * b) ^ 2 := by 
      field_simp [ha1, hb1]
      <;> nlinarith 
    rw [h11]
    rw [show (a ^ 2 + b ^ 2) = (32 : ℝ) by nlinarith, show (a * b) ^ 2 = (4 : ℝ) by nlinarith]
    all_goals 
      norm_num 
  · -- Let's proceed with case $a + b = 2$
    have h10 : a + b = 2 := by linarith
    have h11 : a * b = 6 := by
      nlinarith [h2, h10]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2)]