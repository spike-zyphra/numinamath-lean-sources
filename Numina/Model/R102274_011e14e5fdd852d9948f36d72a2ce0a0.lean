import Mathlib

theorem inequalities_189902 (x : ℝ) :
    abs (x^2 - 5 * x) < 6 ↔ x ∈ Set.Ioo (-1) 2 ∪ Set.Ioo 3 6 := by
  constructor
  · -- Forward implication: abs (x^2 - 5 * x) < 6 → x ∈ (-1, 2) ∪ (3, 6)
    intro h
    have h1 : -6 < x^2 - 5 * x := by linarith [abs_lt.mp h]
    have h2 : x^2 - 5 * x < 6 := by linarith [abs_lt.mp h]
    
    have h3 : -1 < x := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]
    
    have h4 : x < 6 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]
    
    have h7 : x < 2 ∨ x > 3 := by
      by_contra h
      push_neg at h
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]
    
    cases h7 with
    | inl h8 =>
      have h9 : x ∈ Set.Ioo (-1) 2 := ⟨by linarith, by linarith⟩
      left
      exact h9
    | inr h10 =>
      have h11 : x ∈ Set.Ioo 3 6 := ⟨by linarith, by linarith⟩
      right
      exact h11
  
  · -- Backward implication: x ∈ (-1, 2) ∪ (3, 6) → abs (x^2 - 5 * x) < 6
    rintro (h | h)
    · -- Case where x ∈ (-1, 2)
      have h1 : -1 < x := h.1
      have h2 : x < 2 := h.2
      have h3 : -6 < x^2 - 5 * x := by 
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]
      have h4 : x^2 - 5 * x < 6 := by 
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]
      apply abs_lt.mpr
      constructor <;> nlinarith
  
    · -- Case where x ∈ (3, 6)
      have h1 : 3 < x := h.1
      have h2 : x < 6 := h.2
      have h3 : -6 < x^2 - 5 * x := by 
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]
      have h4 : x^2 - 5 * x < 6 := by 
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]
      apply abs_lt.mpr
      constructor <;> nlinarith