import Mathlib

theorem algebra_10560 : round (Real.logb 7 2400 : ℝ) = 4 := by

  have h1 : 3.5 < Real.logb 7 2400 := by
    have h2400 : Real.logb 7 2400 = Real.log 2400 / Real.log 7 := by
      field_simp [Real.logb]
    rw [h2400]
    have h3 : Real.log 2400 > 3.5 * Real.log 7 := by
      have h4 : Real.log 343 = 3 * Real.log 7 := by
        have h5 : (343 : ℝ) = (7: ℝ) ^ 3 := by norm_num
        rw [h5]
        have h6 : Real.log ((7 : ℝ) ^ 3) = (3 : ℝ) * Real.log 7 := by
          simp [Real.log_pow]
        linarith
      have h5 : Real.log (343 : ℝ) = 3 * Real.log 7 := h4
      have h6 : Real.log (343 * Real.sqrt 7) = Real.log 343 + Real.log (Real.sqrt 7) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      have h7 : Real.log (Real.sqrt 7) = (1 / 2 : ℝ) * Real.log 7 := by
        have h8 : Real.log (Real.sqrt 7) = (1 / 2 : ℝ) * Real.log 7 := by
          have h9 : Real.log (Real.sqrt 7) = Real.log ((7 : ℝ) ^ (1 / 2 : ℝ)) := by
            rw [show Real.sqrt 7 = (7 : ℝ) ^ (1 / 2 : ℝ) by
              rw [Real.sqrt_eq_rpow]]
          rw [h9]
          rw [Real.log_rpow]
          all_goals norm_num
          all_goals norm_num
          all_goals norm_num
        linarith
      have h8 : Real.log (343 * Real.sqrt 7) = 3.5 * Real.log 7 := by
        rw [h6]
        rw [h5, h7]
        all_goals ring_nf
      have h5_pos : 0 < Real.sqrt 7 := by positivity
      have h6_pos : 0 < (343 : ℝ) * Real.sqrt 7 := by positivity
      have h7_pos : (343 : ℝ) * Real.sqrt 7 < (2400 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg 7]
      have h9 : Real.log 2400 > Real.log (343 * Real.sqrt 7) := by
        apply Real.log_lt_log
        all_goals nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg 7]
      linarith [h8, h9]
    have h3_pos : 0 < Real.log 7 := by
      apply Real.log_pos
      all_goals norm_num
    have h4 : Real.log 2400 / Real.log 7 > 3.5 := by
      apply (lt_div_iff' (by positivity)).mpr
      linarith
    linarith

  have h2 : Real.logb 7 2400 < (4.5 : ℝ) := by
    have h2400 : Real.logb 7 2400 = Real.log 2400 / Real.log 7 := by
      field_simp [Real.logb]
    rw [h2400]
    have h3 : Real.log 2400 < 4.5 * Real.log 7 := by
      have h4 : Real.log (2401 : ℝ) = 4 * Real.log 7 := by
        have h5 : (2401 : ℝ) = (7 : ℝ) ^ 4 := by norm_num
        rw [h5]
        have h6 : Real.log ((7 : ℝ) ^ 4) = (4 : ℝ) * Real.log 7 := by
          simp [Real.log_pow]
        linarith
      have h5 : 0 < Real.sqrt 7 := by positivity
      have h6_pos : 0 < (2401 : ℝ) * Real.sqrt 7 := by positivity
      have h7_pos : (2400 : ℝ) < (2401 : ℝ) * Real.sqrt 7 := by
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
      have h8 : Real.log (2401 * Real.sqrt 7) = 4.5 * Real.log 7 := by
        have h9 : Real.log (2401 * Real.sqrt 7) = Real.log 2401 + Real.log (Real.sqrt 7) := by
          rw [Real.log_mul (by positivity) (by positivity)]
        have h10 : Real.log (2401 : ℝ) = 4 * Real.log 7 := h4
        have h11 : Real.log (Real.sqrt 7) = (1 / 2 : ℝ) * Real.log 7 := by
          have h12 : Real.log (Real.sqrt 7) = (1 / 2 : ℝ) * Real.log 7 := by
            have h13 : Real.log (Real.sqrt 7) = Real.log ((7 : ℝ) ^ (1 / 2 : ℝ)) := by
              rw [show Real.sqrt 7 = (7 : ℝ) ^ (1 / 2 : ℝ) by
                rw [Real.sqrt_eq_rpow]]
            rw [h13]
            rw [Real.log_rpow]
            all_goals norm_num
            all_goals norm_num
          linarith
        rw [h9, h10, h11]
        all_goals ring_nf
      have h9 : Real.log 2400 < Real.log (2401 * Real.sqrt 7) := by
        apply Real.log_lt_log
        all_goals nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg 7]
      linarith [h8, h9]
    have h4_pos : 0 < Real.log 7 := by
      apply Real.log_pos
      all_goals norm_num
    have h4 : Real.log 2400 / Real.log 7 < 4.5 := by
      apply (div_lt_iff' (by positivity)).mpr
      linarith
    linarith

  rw [round_eq]
  simp only [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> linarith [h1, h2]
  all_goals norm_num