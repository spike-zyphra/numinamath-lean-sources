import Mathlib

theorem algebra_212835 (x y : ℤ) : x^2 - x * y + y^2 = 2 * x - y ↔
    (x = 0 ∧ y = -1) ∨ (x = 1 ∧ y = -1) ∨ (x = 0 ∧ y = 0) ∨ (x = 2 ∧ y = 0) ∨
    (x = 1 ∧ y = 1) ∨ (x = 2 ∧ y = 1) := by 
  constructor
  · -- Forward direction: If (x,y) satisfies the equation, it is a listed solution
    intro h
    have h1 : x^2 - x * y + y^2 - 2 * x + y = 0 := by linarith
    have h2 : y ≥ -1 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - 1), sq_nonneg (x - 1)]
    have h3 : y ≤ 1 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - 1), sq_nonneg (x - 1)]
    interval_cases y <;> 
      try { 
        ring_nf at h1 
        have h4 : x ≤ 3 := by nlinarith
        have h5 : x ≥ -1 := by nlinarith
        interval_cases x <;> 
          omega
      }
  · -- Backward direction: Each listed pair (x,y) satisfies the equation
    rintro (h | h | h | h | h | h)
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num