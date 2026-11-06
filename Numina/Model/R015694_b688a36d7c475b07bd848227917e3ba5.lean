import Mathlib

theorem number_theory_128780 : (11 : ℝ) ^ ((1 : ℝ) / 3) < Real.sqrt 5 ∧ Real.sqrt 5 < 2 * (2 ^ ((1 : ℝ) / 6)) := by
  have h1 : (11 : ℝ) ^ ((1 : ℝ) / 3) < Real.sqrt 5 := by
    have h2 : (11 : ℝ) ^ ((1 : ℝ) / 3) = ((11 : ℝ) ^ (2 / 6 : ℝ)) := by
      norm_num
    have h3 : Real.sqrt 5 = ((5 : ℝ) ^ (3 / 6 : ℝ)) := by
      have h4 : (5 : ℝ) ^ (3 / 6 : ℝ) = (5 : ℝ) ^ (1 / 2 : ℝ) := by
        norm_num
      rw [h4]
      have h5 : (5 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 5 := by
        rw [← Real.sqrt_eq_rpow]
      rw [h5]
    have h6 : (11 : ℝ) ^ ((1 : ℝ) / 3) = (121 : ℝ) ^ ((1 : ℝ) / 6) := by
      rw [show (11 : ℝ) ^ ((1 : ℝ) / 3) = ((11 : ℝ) ^ (2 / 6 : ℝ)) by norm_num]
      have h7 : (11 : ℝ) ^ (2 / 6 : ℝ) = ((11 : ℝ) ^ (2 : ℝ)) ^ (1 / 6 : ℝ) := by
        rw [← Real.rpow_mul]
        ring
        all_goals linarith
      rw [h7]
      have h8 : (11 : ℝ) ^ (2 : ℝ) = (121 : ℝ) := by
        norm_num
      rw [h8]
    have h7 : Real.sqrt 5 = (125 : ℝ) ^ ((1 : ℝ) / 6) := by
      rw [h3]
      have h5_pow : (5 : ℝ) ^ (3 / 6 : ℝ) = (5 ^ 3 : ℝ) ^ (1 / 6 : ℝ) := by
        have h8 : (5 : ℝ) ^ (3 / 6 : ℝ) = ((5 : ℝ) ^ (3 : ℝ)) ^ (1 / 6 : ℝ) := by
          rw [← Real.rpow_mul]
          ring
          all_goals norm_num
        rw [h8]
        all_goals
          norm_num
      rw [h5_pow]
      all_goals
        norm_num
    rw [h6, h7]
    have h8 : (121 : ℝ) < (125 : ℝ) := by norm_num
    have h9 : (121 : ℝ) ^ ((1 : ℝ) / 6) < (125 : ℝ) ^ ((1 : ℝ) / 6) := by
      apply Real.rpow_lt_rpow
      all_goals
        linarith
    linarith
  have h3 : Real.sqrt 5 < 2 * (2 ^ ((1 : ℝ) / 6)) := by
    have h4 : Real.sqrt 5 = (125 : ℝ) ^ ((1 : ℝ) / 6) := by
      have h5 : Real.sqrt 5 = ((5 : ℝ) ^ (3 / 6 : ℝ)) := by
        have h4 : (5 : ℝ) ^ (3 / 6 : ℝ) = (5 : ℝ) ^ (1 / 2 : ℝ) := by
          norm_num
        rw [h4]
        have h6 : (5 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 5 := by
          rw [← Real.sqrt_eq_rpow]
        rw [h6]
      rw [h5]
      have h5_pow : (5 : ℝ) ^ (3 / 6 : ℝ) = (5 ^ 3 : ℝ) ^ (1 / 6 : ℝ) := by
        have h8 : (5 : ℝ) ^ (3 / 6 : ℝ) = ((5 : ℝ) ^ (3 : ℝ)) ^ (1 / 6 : ℝ) := by
          rw [← Real.rpow_mul]
          ring
          all_goals norm_num
        rw [h8]
        all_goals
          norm_num
      rw [h5_pow]
      all_goals
        norm_num
    have h6 : (2 * (2 : ℝ) ^ ((1 : ℝ) / 6)) = (128 : ℝ) ^ ((1 : ℝ) / 6) := by
      have h7 : (2 * (2 : ℝ) ^ ((1 : ℝ) / 6)) = (2 : ℝ) ^ (1 + (1 / 6 : ℝ)) := by
        have h8 : (2 : ℝ) ^ (1 + (1 / 6 : ℝ)) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (1 / 6 : ℝ) := by
          rw [← Real.rpow_add]
          ring
          all_goals norm_num
        have h9 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by
          simp
        rw [h8, h9]
        all_goals
          ring
      have h12 : (2 : ℝ) ^ (1 + (1 / 6 : ℝ)) = ((2 ^ 7 : ℝ) ) ^ (1 / 6 : ℝ) := by
        have h13 : (2 ^ 7 : ℝ) = (2 : ℝ) ^ (7 : ℝ) := by norm_num
        rw [h13]
        have h11 : ((2 : ℝ) ^ (7 : ℝ)) ^ (1 / 6 : ℝ) = (2 : ℝ) ^ (7 * (1 / 6 : ℝ) ) := by
          rw [← Real.rpow_mul]
          ring
          all_goals norm_num
        have h12 : 7 * (1 / 6 : ℝ) = (1 + (1 / 6 : ℝ) ) := by
          norm_num
        rw [h11, h12]
      have h14 : (2 ^ 7 : ℝ) = (128 : ℝ) := by norm_num
      rw [h7, h12, h14]
    rw [h4, h6]
    have h8 : (125 : ℝ) < (128 : ℝ) := by norm_num
    have h9 : (125 : ℝ) ^ ((1 : ℝ) / 6) < (128 : ℝ) ^ ((1 : ℝ) / 6) := by
      apply Real.rpow_lt_rpow
      all_goals
        linarith
    linarith
  constructor <;> linarith [h1, h3]