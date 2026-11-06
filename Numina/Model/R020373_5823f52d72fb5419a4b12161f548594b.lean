import Mathlib

theorem algebra_274919 (a b : ℕ) (h₀ : a - b = 4) (h₁ : a^3 - b^3 = 988) :
    a = 11 ∧ b = 7 := by 
  have h2 : a = b + 4 := by 
    omega 
  have eq1 : a^3 = b^3 + 988 := by 
    omega 
  rw [show a = b + 4 by omega] at eq1 
  have h5 : b ≤ 22 := by 
    by_contra h 
    push_neg at h 
    have h6 : b ≥ 23 := by omega 
    have h7 : (b + 4) ^ 3 > b ^ 3 + 988 := by 
      have h8 : b ≥ 23 := h6 
      have h9 : (b + 4) ^ 3 = b^3 + 12 * b^2 + 48 * b + 64 := by 
        ring 
      nlinarith [sq_nonneg (b + 2), sq_nonneg (b - 7 : ℤ), sq_nonneg (b - 4 : ℤ), sq_nonneg (b : ℤ)]
    nlinarith 
  interval_cases b <;> try { 
    omega 
  } 
  <;> try { 
    tauto 
  }