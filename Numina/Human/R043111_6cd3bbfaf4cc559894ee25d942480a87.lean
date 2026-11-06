import Mathlib

/-Solve the equation
(x^3 + x^2 + x + 1) * ∑ i ∈ Finset.range 12, x^i = (∑ i ∈ Finset.range 8, x^i)^2 -/
theorem algebra_262352 (x : ℝ) :
    (x^3 + x^2 + x + 1) * ∑ i ∈ Finset.range 12, x^i =
    (∑ i ∈ Finset.range 8, x^i)^2 ↔ x = -1 ∨ x = 0 := by

  constructor
  · -- Assume the equation holds, we need to prove x = -1 or x = 0
    intro h
    simp [Finset.sum_range_succ, pow_succ, pow_zero, add_assoc] at h -- expand the sum 

-- use completing the square to derive the equation
    have h2 : x^4 * (x^4 - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x^11 + x^10 + x^9 + x^8 + x^7 + x^6 + x^5 + x^4 + x^3 + x^2 + x + 1),
        sq_nonneg (x^7 + x^6 + x^5 + x^4 + x^3 + x^2 + x + 1),
        sq_nonneg (x^3 + x^2 + x + 1),
        sq_nonneg (x^4 - 1),
        sq_nonneg (x^4),
        sq_nonneg (x^2 + 1),
        sq_nonneg (x + 1)]

    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case x^4 = 0
      right
      have : x = 0 := by
        have h4' : x^4 = 0 := by linarith
        simp at h4'
        linarith
      exact this

    · -- Case (x^4 - 1) ^ 2 = 0 
      left
      have h5 : x^4 - 1 = 0 := by
        rw [sq_eq_zero_iff] at h4
        linarith

      have h7 : x^2 = 1 := by 
        have h8 : x^4 - 1 = 0 := h5
        have h9 : x^2 = 1 := by
          have h10 : x^4 - 1 = (x^2 - 1) * (x^2 + 1) := by ring
          rw [h10] at h8
          cases' (mul_eq_zero.mp h8) with h11 h12
          · -- x^2 - 1 = 0
            have h13 : x^2 - 1 = 0 := h11
            linarith
          · -- x^2 + 1 = 0, but x is real, so no solution
            have h14 : x^2 + 1 = 0 := h12
            nlinarith [sq_nonneg (x)]
        exact h9

      have h8 : x = 1 ∨ x = -1 := by
        have h9 : x^2 = 1 := h7
        have h10 : x = 1 ∨ x = -1 := by
          rw [sq_eq_one_iff] at h9
          exact h9
        exact h10

      cases' h8 with h9 h10
      · -- x = 1, but 1 is not a solution
        exfalso
        rw [h9] at h
        norm_num at h
      · -- x = -1, valid solution
        exact h10
  · -- Verify the solutions satisfy the equation
    rintro (h | h)
    · -- Verify x = -1 is a solution
      rw [h]
      norm_num [Finset.sum_range_succ]
    · -- Verify x = 0 is a solution
      rw [h]
      norm_num [Finset.sum_range_succ]

    