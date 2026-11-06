import Mathlib

theorem algebra_224155 {a b : ℝ} (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1)
    (h1 : Real.logb a 125 = Real.logb 5 3) (h2 : Real.logb b 16 = Real.logb 4 7) :
    a ^ ((Real.logb 5 3) ^ 2) - b ^ ((Real.logb 4 7) ^ 2) = -22 := by
  have ha1 : 0 < a := ha.1
  have ha2 : a ≠ 1 := ha.2
  have hb1 : 0 < b := hb.1
  have hb2 : b ≠ 1 := hb.2
  have h3 : a ^ ((Real.logb 5 3) ^ 2) = 27 := by
    have h4 : Real.logb a 125 = Real.logb 5 3 := h1
    have h5 : a ^ (Real.logb 5 3) = 125 := by
      rw [← h4]
      field_simp [Real.rpow_logb, ha1, ha2, show (125 : ℝ) > 0 by norm_num]
    have h6 : a ^ ((Real.logb 5 3) ^ 2) = (a ^ (Real.logb 5 3)) ^ (Real.logb 5 3 : ℝ) := by
      rw [← Real.rpow_mul]
      ring
      all_goals
        positivity
    rw [h6, h5]
    have h7 : (125 : ℝ) ^ (Real.logb 5 3 : ℝ) = 27 := by
      have h8 : (125 : ℝ) ^ (Real.logb 5 3 : ℝ) = (5 ^ (3 : ℝ)) ^ (Real.logb 5 3 : ℝ) := by
        norm_num
      rw [h8]
      have h9 : (5 ^ (3 : ℝ)) ^ (Real.logb 5 3 : ℝ) = (5 : ℝ) ^ (3 * Real.logb 5 3 : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      rw [h9]
      have h10 : (5 : ℝ) ^ (3 * Real.logb 5 3 : ℝ) = ((5 : ℝ) ^ (Real.logb 5 3 : ℝ)) ^ (3 : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      rw [h10]
      have h11 : (5 : ℝ) ^ (Real.logb 5 3 : ℝ) = (3 : ℝ) := by
        rw [Real.rpow_logb]
        all_goals norm_num
      rw [h11]
      all_goals norm_num
    linarith
  have h8 : b ^ ((Real.logb 4 7) ^ 2) = 49 := by
    have h9 : Real.logb b 16 = Real.logb 4 7 := h2
    have h10 : b ^ (Real.logb 4 7 : ℝ) = 16 := by
      rw [← h9]
      field_simp [Real.rpow_logb, hb1, hb2, show (16 : ℝ) > 0 by norm_num]
    have h11 : b ^ ((Real.logb 4 7) ^ 2) = (b ^ (Real.logb 4 7 : ℝ)) ^ (Real.logb 4 7 : ℝ) := by
      rw [← Real.rpow_mul]
      ring
      all_goals
        positivity
    rw [h11, h10]
    have h12 : (16 : ℝ) ^ (Real.logb 4 7 : ℝ) = 49 := by
      have h13 : (16 : ℝ) ^ (Real.logb 4 7 : ℝ) = (4 ^ (2 : ℝ)) ^ (Real.logb 4 7 : ℝ) := by
        norm_num
      rw [h13]
      have h14 : (4 ^ (2 : ℝ)) ^ (Real.logb 4 7 : ℝ) = (4 : ℝ) ^ (2 * Real.logb 4 7 : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      rw [h14]
      have h15 : (4 : ℝ) ^ (2 * Real.logb 4 7 : ℝ) = ((4 : ℝ) ^ (Real.logb 4 7 : ℝ)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      rw [h15]
      have h16 : (4 : ℝ) ^ (Real.logb 4 7 : ℝ) = (7 : ℝ) := by
        rw [Real.rpow_logb]
        all_goals norm_num
      rw [h16]
      all_goals norm_num
    linarith
  linarith [h3, h8]