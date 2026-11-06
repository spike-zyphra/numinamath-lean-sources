import Mathlib

open Real

theorem algebra_177159 : 2 < 1 / logb (1 / 2) (1 / 3) + 1 / logb (1 / 5) (1 / 3) ∧
    1 / logb (1 / 2) (1 / 3) + 1 / logb (1 / 5) (1 / 3) < 3 := by

  have h1 : 1 / logb (1 / 2) (1 / 3) = Real.logb 3 2 := by
    have h2 : logb (1 / 2) (1 / 3) = (Real.log (1 / 3)) / (Real.log (1 / 2)) := by
      field_simp [Real.logb]
    rw [h2]
    have h3 : Real.log (1 / 3) = - Real.log 3 := by
      simp [Real.log_div, show (1 : ℝ) = 1 by rfl]
    have h4 : Real.log (1 / 2) = - Real.log 2 := by
      simp [Real.log_div, show (1 : ℝ) = 1 by rfl]
    rw [h3, h4]
    have h5 : Real.log 3 ≠ 0 := by
      positivity
    field_simp [Real.logb]
    <;> ring_nf 
  have h6 : 1 / logb (1 / 5) (1 / 3) = Real.logb 3 5 := by
    have h7 : logb (1 / 5) (1 / 3) = (Real.log (1 / 3)) / (Real.log (1 / 5)) := by
      field_simp [Real.logb]
    rw [h7]
    have h8 : Real.log (1 / 3) = - Real.log 3 := by
      simp [Real.log_div, show (1 : ℝ) = 1 by rfl]
    have h9 : Real.log (1 / 5) = - Real.log 5 := by
      simp [Real.log_div, show (1 : ℝ) = 1 by rfl]
    rw [h8, h9]
    have h10 : Real.log 3 ≠ 0 := by
      positivity
    field_simp [Real.logb]
    <;> ring_nf 
  rw [h1, h6]
  constructor
  · -- Prove that 2 < log_3 2 + log_3 5
    have h10 : 2 < Real.logb 3 2 + Real.logb 3 5 := by
      have h11 : Real.logb 3 2 + Real.logb 3 5 = Real.logb 3 10 := by
        have h12 : Real.logb 3 2 + Real.logb 3 5 = Real.logb 3 (2 * 5) := by
          rw [Real.logb_mul (by norm_num) (by norm_num)]
        rw [h12]
        all_goals norm_num
      rw [h11]
      have h13 : Real.logb 3 10 > 2 := by
        have h14 : Real.logb 3 10 > Real.logb 3 (9 : ℝ) := by
          apply Real.logb_lt_logb
          all_goals norm_num
        have h15 : Real.logb 3 (9 : ℝ) = 2 := by
          have h16 : Real.logb 3 (9 : ℝ) = Real.logb 3 ((3 : ℝ) ^ (2 : ℝ)) := by
            norm_num
          rw [h16]
          rw [Real.logb_rpow_eq_mul_logb_of_pos]
          all_goals norm_num
        linarith
      linarith
    linarith
  · -- Prove that Real.logb 3 2 + Real.logb 3 5 < 3
    have h20 : Real.logb 3 2 + Real.logb 3 5 < 3 := by
      have h11 : Real.logb 3 2 + Real.logb 3 5 = Real.logb 3 10 := by
        have h12 : Real.logb 3 2 + Real.logb 3 5 = Real.logb 3 (2 * 5) := by
          rw [Real.logb_mul (by norm_num) (by norm_num)]
        rw [h12]
        all_goals norm_num
      rw [h11]
      have h21 : Real.logb 3 10 < 3 := by
        have h22 : Real.logb 3 10 < Real.logb 3 (27 : ℝ) := by
          apply Real.logb_lt_logb
          all_goals norm_num
        have h23 : Real.logb 3 (27 : ℝ) = 3 := by
          have h24 : Real.logb 3 (27 : ℝ) = Real.logb 3 ((3 : ℝ) ^ (3 : ℝ)) := by
            norm_num
          rw [h24]
          rw [Real.logb_rpow_eq_mul_logb_of_pos]
          all_goals norm_num
        linarith
      linarith
    linarith