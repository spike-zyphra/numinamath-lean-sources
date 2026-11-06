import Mathlib

open Real Set

theorem algebra_11370 :
    IsLeast {x | ∃ a b : ℝ, x = max (max (|a + b|) (|a - b|)) (|1 - b|)} (1 / 2) := by 
  constructor
  · -- Show 1/2 is achievable, using a = 0, b = 1/2
    use 0, 1 / 2
    have h1 : |(0 + (1 / 2) : ℝ)| = 1 / 2 := by
      norm_num [abs]
    have h2 : |(0 - (1 / 2) : ℝ)| = 1 / 2 := by
      norm_num [abs]
    have h3 : |(1 - (1 / 2) : ℝ)| = 1 / 2 := by
      norm_num [abs]
    rw [h1, h2, h3]
    norm_num [max_eq_left, max_eq_right]
    all_goals norm_num
  · -- Now we need to show there is no smaller value
    intro x hx
    rcases hx with ⟨a, b, h_eq⟩
    by_contra h
    push_neg at h
    have h1 : max (max (|a + b|) (|a - b|)) (|1 - b|) < (1 / 2 : ℝ) := by
      linarith [h_eq, h]
    have h2 : |a + b| < (1 / 2 : ℝ) := by
      have h21 : max (max (|a + b|) (|a - b|)) (|1 - b|) ≥ |a + b| := by
        simp [max_le_iff]
      linarith [h1, h21]
    have h3 : |a - b| < (1 / 2 : ℝ) := by
      have h31 : max (max (|a + b|) (|a - b|)) (|1 - b|) ≥ |a - b| := by
        simp [max_le_iff]
      linarith [h1, h31]
    have h4 : |1 - b| < (1 / 2 : ℝ) := by
      have h41 : max (max (|a + b|) (|a - b|)) (|1 - b|) ≥ |1 - b| := by
        simp [max_le_iff]
      linarith [h1, h41]
    have h5 : (1 / 2 : ℝ) < b := by
      linarith [abs_lt.mp h4]
    have h6 : b < (3 / 2 : ℝ) := by
      linarith [abs_lt.mp h4]
    have h7 : - (1 / 2 : ℝ) < a + b := by
      linarith [abs_lt.mp h2]
    have h8 : a + b < (1 / 2 : ℝ) := by
      linarith [abs_lt.mp h2]
    have h9 : - (1 / 2 : ℝ) < a - b := by
      linarith [abs_lt.mp h3]
    have h10 : a - b < (1 / 2 : ℝ) := by
      linarith [abs_lt.mp h3]
    linarith