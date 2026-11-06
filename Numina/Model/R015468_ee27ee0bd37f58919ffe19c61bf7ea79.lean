import Mathlib

theorem number_theory_3257 : (5 : ℝ) ^ ((1 : ℝ) / 5) < √2 ∧ √2 < 3 ^ ((1 : ℝ) / 3) := by
  have h1 : (5 : ℝ) ^ ((1 : ℝ) / 5) < Real.sqrt 2 := by
    have h2 : (5 : ℝ) ^ ((1 : ℝ) / 5) < (2 : ℝ) ^ ((1 : ℝ) / 2) := by
      have h4 : ((5 : ℝ) ^ ((1 : ℝ) / 5)) ^ (10 : ℝ) < ((2 : ℝ) ^ ((1 : ℝ) / 2)) ^ (10 : ℝ) := by
        have h5 : ((5 : ℝ) ^ ((1 : ℝ) / 5)) ^ (10 : ℝ) = (5 : ℝ) ^ (2 : ℝ) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals linarith
        have h6 : ((2 : ℝ) ^ ((1 : ℝ) / 2)) ^ (10 : ℝ) = (2 : ℝ) ^ (5 : ℝ) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals linarith
        rw [h5, h6]
        norm_num
      have h7 : (5 : ℝ) ^ ((1 : ℝ) / 5) < (2 : ℝ) ^ ((1 : ℝ) / 2) := by
        by_contra h
        push_neg at h
        have h8 : ( (5 : ℝ) ^ ((1 : ℝ) / 5) ) ≥ ( (2 : ℝ) ^ ((1 : ℝ) / 2) ) := by linarith
        have h9 : ( (5 : ℝ) ^ ((1 : ℝ) / 5) ) ^ (10 : ℝ) ≥ ( (2 : ℝ) ^ ((1 : ℝ) / 2) ) ^ (10 : ℝ) := by
          apply Real.rpow_le_rpow
          all_goals linarith [h8, show (0 : ℝ) ≤ (5 : ℝ) ^ ((1 : ℝ) / 5) by positivity, show (0 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) by positivity
          ]
        linarith [h4, h9]
      linarith
    have h1' : Real.sqrt 2 = (2 : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      all_goals linarith
    rw [h1'] at *
    linarith [h2]
  have h2 : Real.sqrt 2 < (3 : ℝ) ^ ((1 : ℝ) / 3) := by
    have h5 : (2 : ℝ) ^ ((1 : ℝ) / 2) < (3 : ℝ) ^ ((1 : ℝ) / 3) := by
      have h7 : ( (2 : ℝ) ^ ((1 : ℝ) / 2) ) ^ (6 : ℝ) < ( (3 : ℝ) ^ ((1 : ℝ) / 3) ) ^ (6 : ℝ) := by
        have h8 : ( (2 : ℝ) ^ ((1 : ℝ) / 2) ) ^ (6 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals linarith
        have h9 : ( (3 : ℝ) ^ ((1 : ℝ) / 3) ) ^ (6 : ℝ) = (3 : ℝ) ^ (2 : ℝ) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals linarith
        rw [h8, h9]
        norm_num
      have h7' : (2 : ℝ) ^ ((1 : ℝ) / 2) < (3 : ℝ) ^ ((1 : ℝ) / 3) := by
        by_contra h
        push_neg at h
        have h10 : ( (2 : ℝ) ^ ((1 : ℝ) / 2) ) ≥ ( (3 : ℝ) ^ ((1 : ℝ) / 3) ) := by linarith
        have h11 : ( (2 : ℝ) ^ ((1 : ℝ) / 2) ) ^ (6 : ℝ) ≥ ( (3 : ℝ) ^ ((1 : ℝ) / 3) ) ^ (6 : ℝ) := by
          apply Real.rpow_le_rpow
          all_goals nlinarith [h10, show (0 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) by positivity, show (0 : ℝ) ≤ (3 : ℝ) ^ ((1 : ℝ) / 3) by positivity
          ]
        linarith [h7, h11]
      linarith
    have h1' : Real.sqrt 2 = (2 : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
    linarith [h1', h5]
  constructor
  · exact h1
  · exact h2