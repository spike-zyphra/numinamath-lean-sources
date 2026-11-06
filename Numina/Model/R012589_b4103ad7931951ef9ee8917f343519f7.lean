import Mathlib

theorem algebra_12331 (x : ℝ) (hx : x = abs (x - abs (x - 6))) :
    x = 2 ∨ x = 6 := by 
  have h1 : x - abs (x - 6) ≥ 0 ∨ x - abs (x - 6) < 0 := by 
    by_cases h : x - abs (x - 6) ≥ 0 
    · left 
      linarith 
    · right 
      linarith 
  cases h1 with 
  | inl h =>
    have h2 : abs (x - abs (x - 6)) = x - abs (x - 6) := by 
      rw [abs_of_nonneg] 
      linarith 
    rw [h2] at hx 
    have h3 : abs (x - 6) = 0 := by 
      linarith 
    have h4 : x - 6 = 0 := by 
      rw [abs_eq_zero] at h3 
      linarith 
    right 
    linarith 
  | inr h =>
    have h2 : abs (x - abs (x - 6)) = abs (x - 6) - x := by 
      rw [abs_of_neg] 
      linarith 
      all_goals linarith 
    rw [h2] at hx 
    have h3 : 2 * x = abs (x - 6) := by 
      linarith 
    by_cases h4 : x - 6 ≥ 0 
    · -- x - 6 ≥ 0
      have h5 : abs (x - 6) = x - 6 := by 
        rw [abs_of_nonneg] 
        linarith 
      rw [h5] at h3 
      have h6 : x ≤ (0 : ℝ) := by 
        linarith 
      linarith 
    · -- x - 6 < 0 
      have h5 : abs (x - 6) = 6 - x := by 
        rw [abs_of_neg] 
        linarith 
        all_goals linarith 
      rw [h5] at h3 
      have h6 : x = 2 := by 
        linarith 
      left 
      exact h6