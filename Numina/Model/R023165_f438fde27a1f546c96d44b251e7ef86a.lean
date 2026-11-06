import Mathlib

theorem algebra_210773 (x : ℤ) :
    x^4 - 101 * x^2 + 100 < 0 ↔
    x = -9 ∨ x = -8 ∨ x = -7 ∨ x = -6 ∨ x = -5 ∨ x = -4 ∨
      x = -3 ∨ x = -2 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨
      x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 := by
  constructor
  · -- Assume x^4 - 101 * x^2 + 100 < 0, prove the disjunction
    intro h
    have h1 : x^4 - 101 * x^2 + 100 < 0 := h
    have h2 : x ^ 4 - 101 * x ^ 2 + 100 = (x ^ 2 - 1) * (x ^ 2 - 100) := by
      ring
    rw [h2] at h1
    have h3 : (x ^ 2 - 1 : ℤ) * (x ^ 2 - 100 : ℤ) < 0 := by linarith
    have h4 : (x ^ 2 - 1 : ℤ) > 0 ∧ (x ^ 2 - 100 : ℤ) < 0 ∨ (x ^ 2 - 1 : ℤ) < 0 ∧ (x ^ 2 - 100 : ℤ) > 0 := by 
      apply mul_neg_iff.mp at h3
      tauto
    rcases h4 with (h4 | h4)
    · -- Case 1: (x^2 - 1) > 0 and (x^2 - 100) < 0
      have h5 : x^2 > 1 := by linarith
      have h6 : x^2 < 100 := by linarith
      have h7 : x > -10 := by 
        nlinarith
      have h8 : x < 10 := by 
        nlinarith
      have h9 : x < -1 ∨ x > 1 := by 
        by_contra h
        push_neg at h
        nlinarith
      rcases h9 with (h10 | h11)
      · -- x < -1
        have h12 : x ≥ -9 := by 
          nlinarith
        have : x = -9 ∨ x = -8 ∨ x = -7 ∨ x = -6 ∨ x = -5 ∨ x = -4 ∨ x = -3 ∨ x = -2 := by 
          omega
        tauto
      · -- x > 1
        have h13 : x ≤ 9 := by 
          nlinarith
        have : x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 := by 
          omega
        tauto
    · -- Case 2: (x^2 - 1) < 0 and (x^2 - 100) > 0
      have h7 : x^2 < 1 := by linarith
      have h8 : x^2 > 100 := by linarith
      nlinarith
  · -- Assume the disjunction, prove x^4 - 101 * x^2 + 100 < 0
    intro h
    rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | 
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      norm_num