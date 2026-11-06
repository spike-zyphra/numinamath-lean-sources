import Mathlib

theorem algebra_287621 (r p : ℤ) :
    r^2 - r * (p + 6) + p^2 + 5 * p + 6 = 0 ↔
    (r = 3 ∧ p = 1) ∨ (r = 4 ∧ p = 1) ∨ (r = 0 ∧ p = -2) ∨
    (r = 4 ∧ p = -2) ∨ (r = 0 ∧ p = -3) ∨ (r = 3 ∧ p = -3) := by
  constructor
  · -- Forward direction: Equation implies the pairs
    intro h
    have h1 : r^2 - r * (p + 6) + p^2 + 5 * p + 6 = 0 := h
    have h5 : p ≤ 5 := by
      nlinarith [sq_nonneg (r - 2), sq_nonneg (p - 1), sq_nonneg (r - p - 2), sq_nonneg (r + 1), sq_nonneg (p - r)]
    have h6 : p ≥ -5 := by
      nlinarith [sq_nonneg (r - 2), sq_nonneg (p - 1), sq_nonneg (r - p - 2), sq_nonneg (r + 1), sq_nonneg (p - r)]
    interval_cases p <;> try { 
      omega 
    } <;> try { 
      have h11 : r ≤ 10 := by 
        nlinarith 
      have h12 : r ≥ -10 := by 
        nlinarith 
      interval_cases r <;> omega 
    } 
  · -- Backward direction: Pairs satisfy the equation
    rintro (⟨hr, hp⟩ | ⟨hr, hp⟩ | ⟨hr, hp⟩ | ⟨hr, hp⟩ | ⟨hr, hp⟩ | ⟨hr, hp⟩)
    · -- (r = 3 ∧ p = 1) ∨  
      rw [hr, hp]
      norm_num
    · -- (r = 4 ∧ p = 1) ∨  
      rw [hr, hp]
      norm_num
    · -- (r = 0 ∧ p = -2) ∨ 
      rw [hr, hp]
      norm_num
    · -- (r = 4 ∧ p = -2) ∨ 
      rw [hr, hp]
      norm_num
    · -- (r = 0 ∧ p = -3) ∨ 
      rw [hr, hp]
      norm_num
    · -- (r = 3 ∧ p = -3) := by 
      rw [hr, hp]
      norm_num