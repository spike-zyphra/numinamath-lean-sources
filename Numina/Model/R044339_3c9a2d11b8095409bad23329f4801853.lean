import Mathlib

theorem algebra_200800 (x : ℝ) (hx : x ≠ 0) (h : x + 1/x ≤ 4) :
    x^3 + 1/x^3 ∈ Set.Iic (-2) ∪ Set.Icc 2 52 := by

  have h2 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
    field_simp [hx]
    ring

  have h3 : (x + 1 / x ≤ -2) ∨ (2 ≤ x + 1 / x ∧ x + 1 / x ≤ 4) := by
    by_cases h4 : x > 0
    · -- If x > 0, then x + 1/x ≥ 2 by AM-GM.
      have h5 : x + 1 / x ≥ 2 := by
        have h6 : x + 1 / x - 2 ≥ 0 := by
          have h7 : x + 1 / x - 2 = (x - 1) ^ 2 / x := by
            field_simp [hx]
            ring
          rw [h7]
          apply div_nonneg
          · -- (x - 1) ^ 2 ≥ 0
            nlinarith
          · -- x > 0
            linarith
        linarith
      have h8 : 2 ≤ x + 1 / x := by linarith
      right
      constructor <;> linarith
    · -- If x ≤ 0, and x ≠ 0, then x < 0.
      have h5 : x < 0 := by
        by_contra h6
        push_neg at h6
        have h7 : x = 0 := by linarith
        contradiction
      -- For x < 0, x + 1/x ≤ -2.
      have h8 : x + 1 / x ≤ -2 := by
        have h9 : x + 1 / x + 2 ≤ 0 := by
          have h10 : x + 1 / x + 2 = (x + 1) ^ 2 / x := by
            field_simp [hx]
            ring
          rw [h10]
          apply div_nonpos_of_nonneg_of_nonpos
          · -- (x + 1) ^ 2 ≥ 0
            nlinarith
          · -- x < 0
            linarith
        linarith
      left
      linarith
  rcases h3 with (hx1 | h3)
  · -- Case 1: x + 1/x ≤ -2.
    have h4 : (x + 1 / x) ^ 3 - 3 * (x + 1 / x) ≤ -2 := by
      nlinarith [sq_nonneg ((x + 1 / x) + 2), sq_nonneg (x^2 + 1), sq_nonneg ((x + 1 / x)^2 -4), sq_nonneg (x - (-1/x)), sq_nonneg (x * (x + 1/x) +1), sq_nonneg ((x + 1/x +2)), sq_nonneg ((x - (-1)) ^ 2)]
    have h5 : x^3 + 1/x^3 ≤ -2 := by
      linarith [h2, h4]
    left
    simp only [Set.mem_Iic] at *
    all_goals 
      try linarith [h5]
  · -- Case 2: 2 ≤ x + 1/x ≤ 4.
    have h4 : 2 ≤ (x + 1 / x) := by linarith [h3.1]
    have h5 : (x + 1 / x) ≤ 4 := by linarith [h3.2]
    have h6 : 2 ≤ (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
      nlinarith [sq_nonneg ((x + 1 / x) - 2), sq_nonneg ((x + 1 / x) - 4), sq_nonneg ((x + 1 / x) ^ 2 - 4), sq_nonneg (x^2 +1), sq_nonneg ((x +1/x) *x -1*x), sq_nonneg ((x +1/x) * x^2 -1 *x^2), sq_nonneg ((x +1/x -3) *x^2), sq_nonneg (x -2), sq_nonneg (x +2)]
    have h7 : (x + 1 / x) ^ 3 - 3 * (x + 1 / x) ≤ 52 := by
      nlinarith [sq_nonneg ((x + 1 / x) - 4), sq_nonneg ((x + 1 / x) - 2), sq_nonneg ((x + 1 / x) ^ 2 -16), sq_nonneg (x^2 +1), sq_nonneg ((x +1/x) *x -1*x), sq_nonneg ((x +1/x) * x^2 -1 *x^2), sq_nonneg ((x +1/x -3) *x^2), sq_nonneg (x -2), sq_nonneg (x +2)]
    have h11 : x^3 + 1 / x^3 ≥ 2 := by
      nlinarith [h2, h6]
    have h12 : x^3 + 1 / x^3 ≤ 52 := by
      nlinarith [h2, h7]
    right
    simp only [Set.mem_Icc] at *
    all_goals
      try tauto
      <;> try nlinarith [h11, h12]