import Mathlib

theorem algebra_103770 (x y : ℤ) :
    x + y = x ^ 2 - x * y + y ^ 2 ↔
    (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨
    (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 2) := by
  constructor
  · -- Assume equation, prove solutions
    rintro H
    have h1 : (x + y - 2) ^ 2 + 3 * (x - y) ^ 2 = 4 := by
      nlinarith [sq_nonneg (x + y - 2), sq_nonneg (x - y)]
    have h2 : (x + y - 2) ^ 2 ≤ 4 := by nlinarith
    have h3 : (x + y - 2) ^ 2 ≥ 0 := by nlinarith
    have h4 : (x - y) ^ 2 ≥ 0 := by nlinarith
    have h5 : x + y - 2 ≥ -2 := by nlinarith
    have h6 : x + y - 2 ≤ 2 := by nlinarith
    have h7 : (x - y) ^ 2 ≤ 1 := by nlinarith
    have h8 : x - y ≥ -1 := by nlinarith
    have h9 : x - y ≤ 1 := by nlinarith
    interval_cases h : x + y - 2 <;> interval_cases k : x - y <;> omega
  · -- Assume solutions, prove equation
    rintro (h | h | h | h | h | h)
    · -- (0, 0)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (1, 0)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (0, 1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (2, 1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (1, 2)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (2, 2)
      rcases h with ⟨rfl, rfl⟩
      norm_num