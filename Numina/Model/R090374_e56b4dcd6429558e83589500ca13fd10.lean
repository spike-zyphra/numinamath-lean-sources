import Mathlib

theorem algebra_3940 {x y : ℤ} (h : 0 < x ∧ 0 < y) (h' : (2 * x + y) * (2 * y - x) = 13) :
    x = 5 ∧ y = 3 := by
  have h1 : (2 * x + y) = 1 ∨ (2 * x + y) = 13 := by 
    have h2 : (2 * x + y) * (2 * y - x) = 13 := h'
    have h3 : (2 * x + y) ∣ 13 := by 
      use (2 * y - x)
      all_goals linarith
    have h4 : (2 * x + y) > 0 := by 
      nlinarith [h.1, h.2]
    have h5 : (2 * y - x) > 0 := by 
      nlinarith [h.1, h.2]
    have h6 : (2 * x + y) ∣ 13 := h3
    have h6_1 : (2 * x + y) ≤ 13 := by 
      exact Int.le_of_dvd (by nlinarith) h6
    interval_cases k : (2 * x + y) <;> omega 
  cases h1 with
  | inl h2_1 =>
    have h3_1 : (2 * y - x) = 13 := by
      rw [h2_1] at h'
      have : (1) * (2 * y - x) = 13 := by linarith
      have : (2 * y - x) = 13 := by linarith 
      exact this 
    have h3_2 : y < 1 := by 
      nlinarith 
    linarith [h3_2, h.2] 
  | inr h2_13 => 
    have h3_1 : (2 * y - x) = 1 := by 
      rw [h2_13] at h'
      have : (13) * (2 * y - x) = 13 := by linarith 
      have : (2 * y - x) = 1 := by linarith
      exact this 
    have h4 : y = 3 := by 
      omega 
    have h5 : x = 5 := by 
      omega 
    exact ⟨h5, h4⟩