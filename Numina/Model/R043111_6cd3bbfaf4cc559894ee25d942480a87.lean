import Mathlib

theorem algebra_262352 (x : ℝ) :
    (x^3 + x^2 + x + 1) * ∑ i ∈ Finset.range 12, x^i =
    (∑ i ∈ Finset.range 8, x^i)^2 ↔ x = -1 ∨ x = 0 := by
  constructor
  · -- Forward implication: if the equation holds, then x is either -1 or 0
    intro h
    simp [Finset.sum_range_succ, pow_succ, pow_zero, add_assoc] at h
    -- Thus equation to powers of x 
    have h2 : x ^ 4 * (x ^ 4 - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x ^ 4 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 6 - 1), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (x ^ 4 - x ^ 2), sq_nonneg (x ^ 3 - 1), sq_nonneg (x ^ 3 + 1), sq_nonneg (x ^ 4 - x ^ 2 - 1), sq_nonneg (x ^ 4 - 1)]
    cases' (mul_eq_zero.mp h2) with h8 h11
    · -- First case :x ^4 = 0 
      right
      have h3 : x ^ 4 = 0 := by nlinarith
      have h4 : x = 0 := by
        have h5 : x ^ 4 = 0 := h3
        simp at h5 
        all_goals nlinarith 
      exact h4
    · -- Second case : (x^4 - 1)^2 =0 
      have h5 : (x ^ 4 - 1) ^ 2 = 0 := by
        nlinarith 
      have h7 : x ^ 4 - 1 = 0 := by
        nlinarith [sq_nonneg (x ^ 4 - 1)]
      have h8 : x ^ 4 = 1 := by linarith 
      have h13 : x = 1 ∨ x = -1 := by 
        have h14 : x ^ 4 = 1 := h8 
        have h15 : x ^ 2 = 1 := by 
          nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x)] 
        have h17 : x ^ 2 = 1 := h15 
        have h18 : x = 1 ∨ x = -1 := by 
          rw [sq_eq_one_iff] at h17 
          tauto 
        tauto 
      cases' h13 with h14 h15
      · -- x =1 contradicts the equation 
        exfalso 
        rw [h14] at h 
        norm_num at h 
      · 
        left 
        exact h15 
  · -- Backward implication: if x is either -1 or 0, then it satisfies the equation
    rintro (h | h)
    · -- x = -1 
      rw [h] 
      norm_num [Finset.sum_range_succ]
    · -- x = 0 
      rw [h] 
      norm_num [Finset.sum_range_succ]