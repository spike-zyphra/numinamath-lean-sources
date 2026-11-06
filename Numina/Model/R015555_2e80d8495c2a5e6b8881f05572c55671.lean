import Mathlib

theorem algebra_210724 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h1 : 4^a - 3 * a^b = 16)
    (h2 : Real.logb 2 a = (a + 1) / b) : a^b = 16 := by

  have h3 : 0 < a := by linarith
  have h4 : 0 < b := by linarith

  have h5 : Real.logb 2 a = (a + 1) / b := h2
  have h6 : a = (2 : ℝ) ^ ((a + 1) / b) := by
    have h8 : a > 0 := by linarith
    have h9 : (2 : ℝ) > 1 := by norm_num
    have h10 : (2 : ℝ) ^ ((a + 1) / b) = a := by
      rw [←h5]
      field_simp [Real.rpow_logb, ha, show (2 : ℝ) > 1 by norm_num, show (2 : ℝ) ≠ 1 by norm_num, show (a : ℝ) > 0 by linarith]
      all_goals linarith
    linarith [h10]

  have h7 : a ^ b = (2 : ℝ) ^ (a + 1 : ℝ) := by
    have h7a : a ^ b = ((2 : ℝ) ^ ((a + 1) / b)) ^ b := by
      have h7a_sub : ((2 : ℝ) ^ ((a + 1) / b)) ^ b = a ^ b := by
        calc
          ((2 : ℝ) ^ ((a + 1) / b)) ^ b = (a) ^ b := by 
            have h7a_1 : (2 : ℝ) ^ ((a + 1) / b) = a := by linarith [h6] 
            rw [h7a_1]
          _ = a ^ b := by ring 
      linarith [h7a_sub]
    have h8b : ((2 : ℝ) ^ ((a + 1) / b)) ^ b = (2 : ℝ) ^ (( (a + 1 : ℝ) / b ) * b) := by
      rw [← Real.rpow_mul]
      ring_nf
      all_goals positivity 
    have h8c : (2 : ℝ) ^ (( (a + 1 : ℝ) / b ) * b) = (2 : ℝ) ^ (a + 1 : ℝ) := by
      have h7b : (( (a + 1 : ℝ) / b ) * b ) = (a + 1 : ℝ) := by
        field_simp [show b ≠ 0 by linarith] 
        <;> nlinarith 
      rw [h7b]
    rw [h7a, h8b, h8c]

  have h1' : (4 : ℝ) ^ a = (2 : ℝ) ^ (2 * a) := by
    calc
      (4 : ℝ) ^ a = ((2 : ℝ) ^ (2 : ℝ)) ^ a := by norm_num
      _ = (2 : ℝ) ^ (2 * a) := by
        rw [← Real.rpow_mul]
        ring
        all_goals linarith

  have h8 : (4 : ℝ) ^ a - 3 * a^b = 16 := h1
  rw [h1'] at h8
  rw [h7] at h8

  have h9 : ((2 : ℝ) : ℝ) ^ (2 * a) = ((2 : ℝ) ^ (a)) ^ 2 := by
    calc
      (2 : ℝ) ^ (2 * a) = (2 : ℝ) ^ (2 * a) := by rfl
      _ = ((2 : ℝ) ^ a) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring
        all_goals linarith

  have h10 : (2 : ℝ) ^ (a + 1) = 2 * ((2 : ℝ) ^ a) := by
    calc
      (2 : ℝ) ^ (a + 1) = (2 : ℝ) ^ (a + 1) := by rfl
      _ = (2 : ℝ) ^ a * (2 : ℝ) ^ (1 : ℝ) := by
        rw [← Real.rpow_add]
        ring
        all_goals linarith
      _ = 2 * ((2 : ℝ) ^ a) := by
        simp
        <;> ring

  rw [h9, h10] at h8

  have h11 : ((2 : ℝ) ^ a) ^ 2 - 6 * ((2 : ℝ) ^ a) - 16 = 0 := by
    nlinarith

  have h13 : ((2 : ℝ) ^ a) = 8 := by
    have h10 : ((2 : ℝ) ^ a) > 0 := by positivity
    nlinarith [sq_nonneg (((2 : ℝ) ^ a) - 8)]

  have h14 : (2 : ℝ) ^ (a + 1) = 16 := by
    calc
      (2 : ℝ) ^ (a + 1) = 2 * ((2 : ℝ) ^ a) := by
        calc
          (2 : ℝ) ^ (a + 1) = (2 : ℝ) ^ a * (2 : ℝ) ^ (1 : ℝ) := by
            rw [← Real.rpow_add]
            ring
            all_goals linarith
          _ = 2 * ((2 : ℝ) ^ a) := by
            simp
            <;> ring
      _ = 2 * (8 : ℝ) := by
        rw [h13]
      _ = (16 : ℝ) := by
        norm_num

  rw [h7]
  rw [h14]