import Mathlib

theorem algebra_181128 (x : ℝ) :
    x = 71 ↔
    ∀ x' : ℝ, |13 - x'| + |58 - x'| + |71 - x'| + |75 - x'| + |79 - x'| ≥
      |13 - x| + |58 - x| + |71 - x| + |75 - x| + |79 - x| := by
  constructor
  · -- Assume x = 71, prove that the sum is minimized
    intro hx
    rw [hx]
    intro x'
    have h1 : |13 - x'| + |58 - x'| + |71 - x'| + |75 - x'| + |79 - x'| ≥ |13 - (71 : ℝ)| + |58 - (71 : ℝ)| + |71 - (71 : ℝ)| + |75 - (71 : ℝ)| + |79 - (71 : ℝ)| := by
      by_cases h1 : x' ≥ 79
      · -- x' >= 79
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        norm_num
        all_goals linarith
      by_cases h2 : x' ≥ 75
      · -- 75 <= x' < 79
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_pos (by linarith)]
        norm_num
        all_goals linarith
      by_cases h3 : x' ≥ 71
      · -- 71 <= x' < 75
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)]
        norm_num
        all_goals linarith
      by_cases h4 : x' ≥ 58
      · -- 58 <= x' < 71
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)]
        norm_num
        all_goals linarith
      by_cases h5 : x' ≥ 13
      · -- 13 <= x' < 58
        rw [abs_of_nonpos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)]
        norm_num
        all_goals linarith
      · -- x' < 13
        rw [abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)]
        norm_num
        all_goals linarith
    linarith
  · -- Assume that x is a minimizer, prove x = 71
    intro h
    have h1 := h 71
    have h2 : |13 - (71 : ℝ)| + |58 - (71 : ℝ)| + |71 - (71 : ℝ)| + |75 - (71 : ℝ)| + |79 - (71 : ℝ)| = (83 : ℝ) := by
      norm_num [abs]
    have h3 : |13 - x| + |58 - x| + |71 - x| + |75 - x| + |79 - x| ≤ (83 : ℝ) := by
      linarith [h1, h2]
    by_cases h4 : x ≥ 79
    · -- x' >= 79
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h3
      norm_num at h3
      all_goals linarith
    by_cases h5 : x ≥ 75
    · -- 75 <= x' < 79
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_pos (by linarith)] at h3
      norm_num at h3
      all_goals linarith
    by_cases h6 : x ≥ 71
    · -- 71 <= x' < 75
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)] at h3
      norm_num at h3
      all_goals linarith
    by_cases h7 : x ≥ 58
    · -- 58 <= x' < 71
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)] at h3
      norm_num at h3
      all_goals linarith
    by_cases h8 : x ≥ 13
    · -- 13 <= x' < 58
      rw [abs_of_nonpos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)] at h3
      norm_num at h3
      all_goals linarith
    · -- x' < 13
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)] at h3
      norm_num at h3
      all_goals linarith