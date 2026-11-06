import Mathlib

theorem algebra_2530 (x : ℝ) :
    (2 : ℝ) ^ x - (3 / 5) ^ x - 7 / 5 = 0 ↔ x = 1 := by
  constructor
  · -- Assume (2 : ℝ) ^ x - (3 / 5) ^ x - 7 / 5 = 0 imply x = 1
    intro h
    have h1 : (2 : ℝ) ^ x - (3 / 5 : ℝ) ^ x = 7 / 5 := by linarith
    have h2 : x = 1 := by
      by_cases h3 : x > (1 : ℝ)
      · -- Assume x > 1
        have h4 : (2 : ℝ) ^ x > (2 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt (by linarith)
          linarith
        have h5 : (3 / 5 : ℝ) ^ x < (3 / 5 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_gt
          all_goals linarith
        have h6 : (3 / 5 : ℝ) ^ (1 : ℝ) = (3 / 5 : ℝ) := by norm_num
        have h2 : (3 / 5 : ℝ) ^ x < (3 / 5 : ℝ) := by linarith [h5, h6]
        have h8 : (2 : ℝ) ^ x > (2 : ℝ) := by linarith [h4, show (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) by norm_num]
        nlinarith [h1, h4, h5, h6, show (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) by norm_num]
      by_cases h4 : x < (1 : ℝ)
      · -- Assume x < 1
        have h4 : x < (1 : ℝ) := h4
        have h5 : (2 : ℝ) ^ x < (2 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt (by linarith)
          linarith
        have h6 : (3 / 5 : ℝ) ^ x > (3 / 5 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_gt
          all_goals linarith
        have h7 : (3 / 5 : ℝ) ^ (1 : ℝ) = (3 / 5 : ℝ) := by norm_num
        have h8 : (3 / 5 : ℝ) ^ x > (3 / 5 : ℝ) := by linarith [h6, h7]
        have h9 : (2 : ℝ) ^ x < (2 : ℝ) := by linarith [h5, show (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) by norm_num]
        nlinarith [h1, h5, h6, h7, show (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) by norm_num]
      -- x = 1
      linarith
    linarith [h2]
  · -- Assume x = 1 imply (2 : ℝ) ^ x - (3 / 5) ^ x - 7 / 5 = 0
    intro h
    rw [h]
    norm_num
    all_goals linarith