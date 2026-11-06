import Mathlib

theorem algebra_233171 {a b : ℝ} (ha : a^3 - 3 * a * b^2 = 44) (hb : b^3 - 3 * a^2 * b = 8) :
    a^2 + b^2 = 10 * 2 ^ ((1 : ℝ) / 3) := by 
  have h1 : (a^2 + b^2)^3 = (2000 : ℝ) := by
    nlinarith [sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a + b),
      sq_nonneg (a^2 - b^2), sq_nonneg (a^3 - 3 * a * b^2), sq_nonneg (b^3 - 3 * a^2 * b)]
  have h2 : a^2 + b^2 = 10 * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
    have eq1 : (a^2 + b^2)^3 = (2000 : ℝ) := h1
    have eq3 : (10 * (2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2000 : ℝ) := by
      have h3 : (10 * (2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (10 : ℝ) ^ 3 * ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
        ring
      rw [h3]
      have h4 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith
      rw [h4]
      all_goals norm_num
    have eq4 : (a^2 + b^2)^3 = (10 * (2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
      linarith [eq1, eq3]
    have h5 : 0 ≤ a^2 + b^2 := by 
      nlinarith [sq_nonneg a, sq_nonneg b]
    have h6 : 0 ≤ (10 * (2 : ℝ) ^ ((1 : ℝ) / 3)) := by
      positivity
    have h7 : a^2 + b^2 = (10 * (2 : ℝ) ^ ((1 : ℝ) / 3)) := by
      have h8 : (a^2 + b^2)^3 = (10 * (2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
        linarith
      have h9 : (a^2 + b^2) = (10 * (2 : ℝ) ^ ((1 : ℝ) / 3)) := by
        have h10 : (a^2 + b^2)^3 = (10 * (2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := h8
        have h11 : ((a^2 + b^2)^2 + (a^2 + b^2) * (10 * (2 : ℝ) ^ ((1 : ℝ) / 3)) + (10 * (2 : ℝ) ^ ((1 : ℝ) / 3))^2) ≠ 0 := by
          nlinarith [Real.rpow_nonneg (show (2 : ℝ) ≥ 0 by norm_num), sq_nonneg (a^2 + b^2), sq_nonneg (10 * (2 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg (a^2 + b^2 - (10 * (2 : ℝ) ^ ((1 : ℝ) / 3)))]
        have h12 : (a^2 + b^2)^3 = (10 * (2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := h8
        have h13 : (a^2 + b^2 - (10 * (2 : ℝ) ^ ((1 : ℝ) / 3))) * (((a^2 + b^2)^2 + (a^2 + b^2) * (10 * (2 : ℝ) ^ ((1 : ℝ) / 3)) + (10 * (2 : ℝ) ^ ((1 : ℝ) / 3))^2)) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.mp h13) with h14 h15
        · linarith
        · exfalso
          have h16 : ((a^2 + b^2)^2 + (a^2 + b^2) * (10 * (2 : ℝ) ^ ((1 : ℝ) / 3)) + (10 * (2 : ℝ) ^ ((1 : ℝ) / 3))^2) ≠ 0 := h11
          contradiction
      linarith
    linarith
  linarith