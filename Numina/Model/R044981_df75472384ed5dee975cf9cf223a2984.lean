import Mathlib

theorem algebra_128850 (a b c d : ℝ) (ha : (5 : ℝ)^a = 4) (hb : (4 : ℝ)^b = 3)
    (hc : (3 : ℝ)^c = 2) (hd : (2 : ℝ)^d = 5) :
    (a * b * c * d)^2018 = 1 := by
  have ha2 : a * Real.log 5 = Real.log 4 := by
    have h1 : Real.log ((5 : ℝ) ^ a) = Real.log (4 : ℝ) := by
      rw [ha]
    have h2 : Real.log ((5 : ℝ) ^ a) = a * Real.log 5 := by 
      rw [Real.log_rpow]
      all_goals linarith
    linarith [h1, h2]
  have hb2 : b * Real.log 4 = Real.log 3 := by
    have h1 : Real.log ((4 : ℝ) ^ b) = Real.log (3 : ℝ) := by 
      rw [hb]
    have h2 : Real.log ((4 : ℝ) ^ b) = b * Real.log 4 := by 
      rw [Real.log_rpow]
      all_goals linarith
    linarith [h1, h2]
  have hc2 : c * Real.log 3 = Real.log 2 := by
    have h1 : Real.log ((3 : ℝ) ^ c) = Real.log (2 : ℝ) := by
      rw [hc]
    have h2 : Real.log ((3 : ℝ) ^ c) = c * Real.log 3 := by
      rw [Real.log_rpow]
      all_goals linarith
    linarith [h1, h2]
  have hd2 : d * Real.log 2 = Real.log 5 := by
    have h1 : Real.log ((2 : ℝ) ^ d) = Real.log (5 : ℝ) := by
      rw [hd]
    have h2 : Real.log ((2 : ℝ) ^ d) = d * Real.log 2 := by
      rw [Real.log_rpow]
      all_goals linarith
    linarith [h1, h2]
  have h1 : a * b * c * d = 1 := by
    have h2 : (a * b * c * d) * (Real.log 5 * Real.log 4 * Real.log 3 * Real.log 2) = 
          (Real.log 4 * Real.log 3 * Real.log 2 * Real.log 5) := by
      calc
        (a * b * c * d) * (Real.log 5 * Real.log 4 * Real.log 3 * Real.log 2)
          = (a * Real.log 5) * (b * Real.log 4) * (c * Real.log 3) * (d * Real.log 2) := by
            ring
        _ = (Real.log 4) * (Real.log 3) * (Real.log 2) * (Real.log 5) := by
          rw [ha2, hb2, hc2, hd2]
        _ = (Real.log 4 * Real.log 3 * Real.log 2 * Real.log 5) := by
          ring
    have h3 : Real.log 5 ≠ 0 := by
      have h4 : Real.log 5 > 0 := by
        apply Real.log_pos
        all_goals norm_num
      linarith
    have h4 : Real.log 4 ≠ 0 := by
      have h4 : Real.log 4 > 0 := by
        apply Real.log_pos
        all_goals norm_num
      linarith
    have h5 : Real.log 3 ≠ 0 := by
      have h6 : Real.log 3 > 0 := by
        apply Real.log_pos
        all_goals norm_num
      linarith
    have h6 : Real.log 2 ≠ 0 := by
      have h7 : Real.log 2 > 0 := by
        apply Real.log_pos
        all_goals norm_num
      linarith
    have h7 : Real.log 5 * Real.log 4 * Real.log 3 * Real.log 2 ≠ 0 := by
      simp [h3, h4, h5, h6]
    apply (mul_left_inj' h7).mp
    linarith
  rw [h1]
  norm_num