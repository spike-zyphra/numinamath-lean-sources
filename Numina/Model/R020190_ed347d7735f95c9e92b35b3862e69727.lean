import Mathlib

theorem inequalities_190215 (x : ℝ) :
    (x ^ 4 - 2 * x ^ 2 - 8) / (x ^ 2 + 2 * x + 1) < 0 ↔
    x ∈ Set.Ioo (-2) (-1) ∪ Set.Ioo (-1) 2 := by

  have h1 : x^4 - 2*x^2 - 8 = (x^2 - 4)*(x^2 + 2) := by
    ring
  have h2 : x^2 - 4 = (x - 2) * (x + 2) := by
    ring
  have h3 : x^2 + 2 * x + 1 = (x + 1) ^ 2 := by
    ring
  rw [h1] at *
  rw [h2] at *
  rw [h3] at *
  simp only [Set.mem_union, Set.mem_Ioo]
  constructor
  · -- (→) Assume the fraction is negative, prove x in the set
    intro h
    have h4 : ((x - 2) * (x + 2) * (x ^ 2 + 2)) / ((x + 1) ^ 2) < 0 := by
      simpa using h
    have h5 : (x - 2) * (x + 2) * (x ^ 2 + 2) < 0 := by
      have h8 : (x + 1) ^ 2 ≥ 0 := by positivity
      by_contra h6
      push_neg at h6
      have h7 : ((x - 2) * (x + 2) * (x ^ 2 + 2)) / ((x + 1) ^ 2) ≥ 0 := by
        apply div_nonneg
        linarith
        all_goals nlinarith
      linarith
    have h6 : (x - 2) * (x + 2) < 0 := by 
      nlinarith [show x ^ 2 + 2 > 0 by nlinarith]
    
    have h7 : -2 < x := by
      nlinarith
    have h8 : x < 2 := by
      nlinarith
    have h9 : x ≠ -1 := by
      by_contra h10
      rw [h10] at h4
      norm_num at h4
    by_cases h11 : x < -1
    · -- Case where x ∈ (-2, -1)
      left
      exact ⟨h7, h11⟩
    · -- Case where x ∈ (-1, 2)
      have h13 : x > -1 := by 
        by_contra h14
        push_neg at h14
        have h15 : x ≤ -1 := by nlinarith
        have h16 : x = -1 := by nlinarith
        contradiction 
      right 
      exact ⟨h13, h8⟩
  
  · -- (←) Assume x in the set, prove the fraction is negative 
    intro h
    rcases h with (h | h)
    · -- Case x ∈ (-2, -1)
      rcases h with ⟨h11, h12⟩
      have h5 : (x - 2) * (x + 2) * (x ^ 2 + 2) < 0 := by
        have h6 : x - 2 < 0 := by linarith
        have h7 : x + 2 > 0 := by linarith
        have h8 : x ^ 2 + 2 > 0 := by nlinarith
        have h9 : (x - 2) * (x + 2) < 0 := by nlinarith
        nlinarith
      have h6 : (x + 1) ^ 2 > 0 := by 
        nlinarith
      apply div_neg_of_neg_of_pos 
      linarith 
      nlinarith 
    · -- Case x ∈ (-1, 2)
      rcases h with ⟨h11, h12⟩
      have h5 : (x - 2) * (x + 2) * (x ^ 2 + 2) < 0 := by 
        have h6 : x - 2 < 0 := by linarith 
        have h7 : x + 2 > 0 := by linarith 
        have h8 : x ^ 2 + 2 > 0 := by nlinarith 
        have h9 : (x - 2) * (x + 2) < 0 := by nlinarith 
        nlinarith 
      have h6 : (x + 1) ^ 2 > 0 := by 
        nlinarith 
      apply div_neg_of_neg_of_pos 
      linarith 
      nlinarith