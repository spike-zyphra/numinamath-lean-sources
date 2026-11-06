import Mathlib

theorem number_theory_318525 (x y : ℤ) : x^2 + x * y + 2 * y^2 = 29 ↔
    (x = 1 ∧ y = -4) ∨ (x = 3 ∧ y = -4) ∨ (x = -1 ∧ y = 4) ∨ (x = -3 ∧ y = 4) := by
  constructor
  · -- Assume x^2 + x*y + 2*y^2 = 29, prove (x = 1 ∧ y = -4) ∨ (x = 3 ∧ y = -4) ∨ (x = -1 ∧ y = 4) ∨ (x = -3 ∧ y = 4)
    intro eq
    have h1 : y ≥ -4 := by
      nlinarith [sq_nonneg (2 * x + y), sq_nonneg (y : ℤ)]
    have h2 : y ≤ 4 := by
      nlinarith [sq_nonneg (2 * x + y), sq_nonneg (y : ℤ)]
    interval_cases y <;> try { 
      have : x ≤ 11 := by nlinarith
      have : x ≥ -11 := by nlinarith
      interval_cases x <;> omega
    }
  · -- Assume (x = 1 ∧ y = -4) ∨ (x = 3 ∧ y = -4) ∨ (x = -1 ∧ y = 4) ∨ (x = -3 ∧ y = 4), prove x^2 + x*y + 2*y^2 = 29
    rintro (h | h | h | h)
    · -- Case (x = 1 ∧ y = -4)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (x = 3 ∧ y = -4)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (x = -1 ∧ y = 4)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (x = -3 ∧ y = 4)
      rcases h with ⟨rfl, rfl⟩
      norm_num