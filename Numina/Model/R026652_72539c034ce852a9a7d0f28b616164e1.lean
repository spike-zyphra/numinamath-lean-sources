import Mathlib

theorem algebra_12718 {a b : ℝ} (ha : a > 0) (hb : b > 0)
    (h1 : 4^a - 3 * a^b = 16) (h2 : Real.logb 2 a = (a + 1) / b) :
    a^b = 16 := by
  have h3 : a ^ b = 2 ^ (a + 1) := by
    have eq2 : Real.logb 2 (a ^ b) = a + 1 := by
      have h6 : Real.logb 2 (a ^ b) = b * Real.logb 2 a := by
        rw [Real.logb_rpow_eq_mul_logb_of_pos]
        all_goals linarith
      rw [h6, h2]
      field_simp [hb]
      <;> nlinarith
    have eq3 : a ^ b = (2 : ℝ) ^ (a + 1) := by
      have h9 : (a ^ b : ℝ) = (2 : ℝ) ^ (a + 1) := by
        have h8 : Real.logb 2 (a ^ b) = a + 1 := eq2
        have h9 : (a ^ b : ℝ) = (2 : ℝ) ^ (a + 1) := by
          rw [←h8]
          field_simp [Real.rpow_logb, show (2: ℝ) > 1 by norm_num, show (2: ℝ) ≠ 1 by norm_num, show (0: ℝ) < 2 by norm_num, ha]
        linarith
      linarith
    linarith
  have h4 : (4 : ℝ) ^ a = 2 ^ (2 * a : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring
    all_goals norm_num
  have h5 : (4 : ℝ) ^ a - 3 * (a ^ b : ℝ) = 16 := h1
  rw [h3] at h5
  rw [h4] at h5
  have h8 : (2 : ℝ) ^ (2 * a : ℝ) - 3 * (2 ^ (a + 1 : ℝ)) = 16 := by
    linarith [h5]
  have h9 : (2 : ℝ) ^ (2 * a : ℝ) = ((2 : ℝ) ^ (a : ℝ)) ^ 2 := by
    calc
      (2 : ℝ) ^ (2 * a : ℝ) = (2 : ℝ) ^ (2 * (a : ℝ)) := by ring_nf
      _ = ((2 : ℝ) ^ (a : ℝ)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring
        all_goals norm_num
  have h10 : (2 ^ (a + 1 : ℝ) : ℝ) = 2 * (2 ^ (a : ℝ) : ℝ) := by
    rw [show a + 1 = a + (1 : ℝ) by ring]
    rw [Real.rpow_add]
    rw [Real.rpow_one]
    norm_num
    all_goals linarith
  rw [h9, h10] at h8
  have h11 : ((2 : ℝ) ^ (a : ℝ)) ^ 2 - 6 * ( (2 : ℝ) ^ (a : ℝ) ) - 16 = 0 := by
    nlinarith [h8]
  have h12 : ((2 : ℝ) ^ (a : ℝ) - 8) * ((2 : ℝ) ^ (a : ℝ) + 2) = 0 := by
    nlinarith [h11]
  cases' (mul_eq_zero.mp h12) with h13 h14
  · -- Case where (2^a) = 8
    have h15 : (2 : ℝ) ^ (a : ℝ) = (8 : ℝ) := by linarith [h13]
    have h16 : a = (3 : ℝ) := by
      have h17 : (2 : ℝ) ^ (a : ℝ) = (8 : ℝ) := h15
      have h18 : a = Real.logb (2 : ℝ) (8 : ℝ) := by
        rw [←h17]
        field_simp [Real.logb_rpow]
      have h19 : Real.logb (2 : ℝ) (8 : ℝ) = 3 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h19] at h18
      linarith
    rw [h16] at h3
    norm_num at h3 ⊢
    linarith
  · -- Case where (2^a) + 2 = 0
    have h15 : (2 : ℝ) ^ (a : ℝ) = -2 := by linarith [h14]
    have h16 : (2 : ℝ) ^ (a : ℝ) > 0 := by positivity
    nlinarith