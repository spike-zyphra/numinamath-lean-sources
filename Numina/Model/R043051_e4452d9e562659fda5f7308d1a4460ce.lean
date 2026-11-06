import Mathlib

open Real

theorem inequalities_186202 (a b : ℝ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : a ≠ 1) (h₂ : b ≠ 1) :
    abs (logb a b) + abs (logb b a) ≥ 2 := by 
  have h3 : logb a b = (log b) / (log a) := by 
    field_simp [logb]
  have h4 : logb b a = (log a) / (log b) := by 
    field_simp [logb]

  have h5 : log b ≠ 0 := by
    by_contra h
    have : b = 1 := by 
      rw [log_eq_zero] at h 
      rcases h with (r | r | r)
      · linarith
      · linarith
      · linarith 
    contradiction

  have h6 : log a ≠ 0 := by
    by_contra h
    have : a = 1 := by 
      rw [log_eq_zero] at h 
      rcases h with (r | r | r)
      · linarith 
      · linarith 
      · linarith 
    contradiction

  have h9 : logb a b * logb b a = 1 := by 
    rw [show logb a b = (log b) / (log a) by field_simp [logb], 
        show logb b a = (log a) / (log b) by field_simp [logb]]
    field_simp [h5, h6]

  by_cases h : logb a b > 0

  · -- Assume logb a b > 0
    have h10 : logb b a > 0 := by 
      nlinarith [h9, h]

    rw [abs_of_pos h, abs_of_pos h10]

    have h11 : logb a b + logb b a ≥ 2 := by 
      nlinarith [sq_nonneg (logb a b - 1), h9]
    
    linarith

  · -- Assume logb a b ≤ 0
    have h12 : logb a b < 0 := by 
      by_contra h'
      push_neg at h'
      have h13 : logb a b = 0 := by 
        nlinarith 
      rw [h13] at h9 
      nlinarith 
    have h13 : logb b a < 0 := by 
      nlinarith [h9, h12]

    rw [abs_of_neg h12, abs_of_neg h13]

    have h14 : logb a b * logb b a = 1 := h9
    nlinarith [sq_nonneg (logb a b + 1), sq_nonneg (logb b a + 1), h14, sq_pos_of_neg h12, sq_pos_of_neg h13]