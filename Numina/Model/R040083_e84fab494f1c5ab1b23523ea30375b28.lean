import Mathlib

open Real

theorem inequalities_602400 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    sqrt 5 ≤ sqrt (1 + a^2) + sqrt (1 + b^2) ∧
    sqrt (1 + a^2) + sqrt (1 + b^2) < 1 + sqrt 2 := by

  have h1 : sqrt 5 ≤ sqrt (1 + a^2) + sqrt (1 + b^2) := by
    have h2 : a + b = 1 := h
    have h3 : b = 1 - a := by linarith
    have h6 : (sqrt (1 + a^2) + sqrt (1 + b^2)) ^ 2 ≥ 5 := by
      rw [h3]
      have h7 : sqrt (1 + a ^ 2) ≥ 0 := Real.sqrt_nonneg (1 + a ^ 2)
      have h8 : sqrt (1 + (1 - a) ^ 2) ≥ 0 := Real.sqrt_nonneg (1 + (1 - a) ^ 2)
      have h9 : (sqrt (1 + a ^ 2)) ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (show 0 ≤ (1 + a ^ 2 : ℝ) by positivity)
      have h10 : (sqrt (1 + (1 - a) ^ 2)) ^ 2 = 1 + (1 - a) ^ 2 := Real.sq_sqrt (show 0 ≤ (1 + (1 - a) ^ 2 : ℝ) by positivity)
      have h7' : (sqrt (1 + a ^ 2) + sqrt (1 + (1 - a) ^ 2)) ^ 2 = (sqrt (1 + a ^ 2)) ^ 2 + (sqrt (1 + (1 - a) ^ 2)) ^ 2 + 2 * (sqrt (1 + a ^ 2) * sqrt (1 + (1 - a) ^ 2)) := by ring
      rw [h7'] at *
      nlinarith [sq_nonneg (sqrt (1 + a ^ 2) - sqrt (1 + (1 - a) ^ 2)), sq_nonneg (a - (1 - a)), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + a ^ 2 : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + (1 - a) ^ 2 : ℝ) by positivity), Real.sqrt_nonneg (1 + a ^ 2), Real.sqrt_nonneg (1 + (1 - a) ^ 2), mul_nonneg (Real.sqrt_nonneg (1 + a ^ 2)) (Real.sqrt_nonneg (1 + (1 - a) ^ 2)), sq_nonneg (sqrt (1 + a ^ 2) + sqrt (1 + (1 - a) ^ 2) - Real.sqrt 5), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (1 + a ^ 2 : ℝ) by positivity), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (1 + (1 - a) ^ 2 : ℝ) by positivity), sq_nonneg (sqrt (1 + a ^ 2) ^ 2 - sqrt (1 + (1 - a) ^ 2) ^ 2), h, mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ (1 - a : ℝ) by nlinarith)]
    have h8 : (sqrt 5 : ℝ) ^ 2 ≤ (sqrt (1 + a^2) + sqrt (1 + b^2)) ^ 2 := by
      have h6' : (sqrt (1 + a^2) + sqrt (1 + b^2)) ^ 2 ≥ 5 := h6
      have h8' : (sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      nlinarith [h6', h8', Real.sqrt_nonneg (1 + a^2), Real.sqrt_nonneg (1 + b^2)]
    have h2' : (sqrt 5 : ℝ) ≤ sqrt (1 + a^2) + sqrt (1 + b^2) := by
      nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (1 + a^2), Real.sqrt_nonneg (1 + b^2), h8]
    linarith

  have h4 : sqrt (1 + a^2) + sqrt (1 + b^2) < 1 + sqrt 2 := by
    have h3 : b = 1 - a := by linarith
    rw [h3] at *
    have h5 : sqrt (1 + a^2) + sqrt (1 + (1 - a)^2) < 1 + sqrt 2 := by
      have h5_pos : sqrt (1 + a^2) + sqrt (1 + (1 - a)^2) ≥ 0 := by positivity
      have h6_pos : (1 + sqrt 2) ≥ 0 := by positivity
      have h7 : (sqrt (1 + a^2) + sqrt (1 + (1 - a)^2))^2 < (1 + sqrt 2) ^ 2 := by
        have h8 : (sqrt (1 + a^2) + sqrt (1 + (1 - a)^2))^2 =
            (sqrt (1 + a^2))^2 + (sqrt (1 + (1 - a)^2))^2 + 2 * (sqrt (1 + a^2) * sqrt (1 + (1 - a)^2)) := by ring
        have h9 : (sqrt (1 + a^2))^2 = 1 + a^2 := Real.sq_sqrt (show 0 ≤ (1 + a^2 : ℝ) by positivity)
        have h10 : (sqrt (1 + (1 - a)^2))^2 = 1 + (1 - a)^2 := Real.sq_sqrt (show 0 ≤ (1 + (1 - a)^2 : ℝ) by positivity)
        have h7' : (sqrt (1 + a^2) * sqrt (1 + (1 - a)^2)) ^ 2 = (1 + a^2) * (1 + (1 - a) ^ 2) := by
          calc
            (sqrt (1 + a^2) * sqrt (1 + (1 - a)^2)) ^ 2
              = (sqrt (1 + a^2)) ^ 2 * (sqrt (1 + (1 - a)^2)) ^ 2 := by ring
            _ = (1 + a^2) * (1 + (1 - a) ^ 2) := by rw [h9, h10]
        have h7_pos : sqrt (1 + a^2) * sqrt (1 + (1 - a)^2) ≥ 0 := by positivity
        rw [h8, h9, h10]
        have h15 : (1 + a ^ 2) + (1 + (1 - a) ^ 2) + 2 * (sqrt (1 + a^2) * sqrt (1 + (1 - a)^2)) < (1 + sqrt 2) ^ 2 := by
          nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (sqrt (1 + a ^ 2) - sqrt (1 + (1 - a) ^ 2)), 
          sq_nonneg (sqrt (1 + a^2) * sqrt (1 + (1 - a)^2) - Real.sqrt ((1 + a^2) * (1 + (1 - a)^2))), Real.sq_sqrt (show 0 ≤ (1 + a^2) * (1 + (1 - a)^2) by positivity), 
          Real.sqrt_nonneg (1 + a^2), Real.sqrt_nonneg (1 + (1 - a) ^ 2), 
          Real.sq_sqrt (show 0 ≤ (1 + a^2 : ℝ) by positivity), 
          Real.sq_sqrt (show 0 ≤ (1 + (1 - a) ^ 2 : ℝ) by positivity), 
          mul_nonneg (Real.sqrt_nonneg (1 + a^2)) (Real.sqrt_nonneg (1 + (1 - a) ^ 2)), 
          sq_nonneg (a * (a - 1)), 
          Real.sqrt_nonneg (2 : ℝ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          mul_pos ha (show (0 : ℝ) < (1 - a) by nlinarith [show 0 < (1 - a : ℝ) by linarith]), 
          sq_nonneg (Real.sqrt 5 - 1 - Real.sqrt 2), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        linarith
      nlinarith [Real.sqrt_nonneg (1 + a^2), Real.sqrt_nonneg (1 + (1 - a)^2), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show 0 ≤ (1 + a^2 : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (1 + (1 - a) ^ 2 : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    linarith
  exact ⟨h1, h4⟩