import Mathlib

theorem inequalities_289689 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x > 0.7 ∨ y > 0.7 ∨ (1 / (x + y)) > 0.7 := by

  by_cases h1 : x > 0.7 
  · -- Assume x > 0.7
    left 
    exact h1 
  · -- Assume x ≤ 0.7
    by_cases h2 : y > 0.7 
    · -- Assume y > 0.7 
      right 
      left 
      exact h2 
    · -- Assume y ≤ 0.7 
      have h3 : x ≤ 0.7 := by linarith 
      have h4 : y ≤ 0.7 := by linarith 
      have h5 : x + y ≤ (0.7 : ℝ) + (0.7 : ℝ) := by linarith 
      have h6 : x + y > 0 := by linarith 
      by_cases h7 : x + y = 1.4 
      · -- When x + y = 1.4 
        have h8 : 1 / (x + y) = 5 / 7 := by 
          rw [h7]
          norm_num 
        right 
        right 
        rw [h8]
        norm_num 
      · -- When x + y ≠ 1.4 
        have h8 : x + y < (1.4 : ℝ) := by 
          by_contra h 
          push_neg at h 
          have h9 : x + y = (1.4 : ℝ) := by 
            linarith 
          trivial 
        have h9 : 1 / (x + y) > 1 / (1.4 : ℝ) := by 
          apply one_div_lt_one_div_of_lt 
          all_goals 
            nlinarith 
        have h10 : (1 / (1.4 : ℝ) : ℝ) > 0.7 := by norm_num 
        right 
        right 
        linarith