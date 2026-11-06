import Mathlib

theorem algebra_20349 (x : ℚ) :
    2 * x ^ 4 - x ^ 3 - 18 * x ^ 2 + 14 * x + 15 = 0 ↔ x = 5 / 2 ∨ x = -3 := by 
  constructor 
  · -- Forward implication: if the equation holds, then x is either 5/2 or -3
    intro h 
    have eq : 2 * x ^ 4 - x ^ 3 - 18 * x ^ 2 + 14 * x + 15 = 0 := h
    have eq2 : (2 * x - 5) * (x + 3) * (x ^ 2 - x - 1) = 0 := by 
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 3 / 2), sq_nonneg (x - 5 / 2), sq_nonneg (x ^ 2 -x - 1), sq_nonneg (x ^ 2 - 1)]
    cases' (mul_eq_zero.mp eq2) with h1 h1
    · cases' (mul_eq_zero.mp h1) with h2 h3
      · -- Case (2 * x - 5) = 0
        left
        linarith 
      · -- Case (x + 3) = 0 
        right 
        linarith 
    · -- Case (x ^ 2 - x - 1) = 0
      have eq3 : x ^ 2 - x - 1 = 0 := h1 
      exfalso 
      have eq4 : x ^ 2 - x - 1 = 0 := eq3 
      have h4 : x ^ 2 - x - 1 = 0 := eq3 
      have h5 : (2 * x - 1) ^ 2 = 5 := by 
        nlinarith 
      have h6 : (2 * x - 1) ^ 2 = 5 := h5 
      have h7 : ¬ IsSquare (5 : ℚ) := by 
        native_decide 
      have h8 : IsSquare (5 : ℚ) := by 
        use (2 * x - 1)
        linarith 
      contradiction 
  · -- Backward implication: if x is either 5/2 or -3, then the equation holds
    rintro (h | h) 
    · -- h : x = 5/2 
      rw [h]
      norm_num 
    · -- h : x = -3 
      rw [h]
      norm_num