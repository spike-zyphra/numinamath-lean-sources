import Mathlib

theorem inequalities_251208 (a b c : ℝ) (h : abs ((a + b) / 2) + abs ((a - b) / 2) < c) :
    abs a < c ∧ abs b < c := by 
  have h1 : abs a < c := by
    have h2 : abs a ≤ abs ((a + b) / 2) + abs ((a - b) / 2) := by 
      have h3 : abs a = abs ( ((a + b) / 2 ) + ((a - b) / 2 ) ) := by
        have h4 : ((a + b) / 2 ) + ((a - b) / 2 ) = a := by 
          ring
        rw [h4]
      rw [h3]
      have h4 : abs ( ((a + b) / 2 ) + ((a - b) / 2 ) ) ≤ abs ((a + b) / 2) + abs ((a - b) / 2) := by 
        apply abs_add
      linarith
    have h3 : abs ((a + b) / 2) + abs ((a - b) / 2) < c := h
    linarith
  -- Prove that $|b| < c$ by a similar method
  have h2 : abs b < c := by 
    have h4 : abs b ≤ abs ((a + b) / 2) + abs ((a - b) / 2) := by 
      have h3 : abs b = abs ( ((a + b) / 2 ) - ((a - b) / 2 ) ) := by 
        have h4 : ((a + b) / 2 ) - ((a - b) / 2 ) = b := by 
          ring
        rw [h4]
      rw [h3]
      have h5 : abs ( ((a + b) / 2 ) - ((a - b) / 2 ) ) ≤ abs ((a + b) / 2) + abs ((a - b) / 2 ) := by 
        cases' abs_cases ((a + b) / 2 ) with h1 h1 <;> 
        cases' abs_cases ((a - b) / 2 ) with h2 h2 <;> 
        cases' abs_cases (( (a + b) / 2 ) - ((a - b) / 2 ) ) with h3 h3 <;> 
        all_goals 
          linarith
      linarith
    have h3 : abs ((a + b) / 2) + abs ((a - b) / 2) < c := h
    linarith 
  constructor 
  · exact h1
  · exact h2