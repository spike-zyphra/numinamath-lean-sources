import Mathlib

theorem algebra_2032 (x : ℝ) :
    (x^2 + 5 * x + 1) * (x^2 + 4 * x) = 20 * (x + 1)^2 ↔
    x = 2 ∨ x = -2 ∨ x = (-9 + Real.sqrt 61) / 2 ∨ x = (-9 - Real.sqrt 61) / 2 := by
  constructor
  · -- Proof of the forward direction: if the equation holds, x is one of the four roots
    intro h
    have h1 : (x^2 + 5 * x + 1) * (x^2 + 4 * x) - 20 * (x + 1)^2 = 0 := by linarith
    have h2 : x^4 + 9 * x^3 + x^2 - 36 * x - 20 = 0 := by
      nlinarith [sq_nonneg (x^2), sq_nonneg (x + 1), sq_nonneg (x - 2), sq_nonneg (x + 2),
        sq_nonneg (x^2 + 9 * x + 5), sq_nonneg (x^2 - 4), h1]
    have h3 : (x^2 - 4) * (x^2 + 9 * x + 5) = 0 := by
      nlinarith [sq_nonneg (x), sq_nonneg (x + 2), sq_nonneg (x - 2), sq_nonneg (x^2 + 9 * x + 5),
        sq_nonneg (x^2 - 4), h2]
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case where $x^2 - 4 = 0$ so $x = \pm 2$
      have h42 : x^2 = 4 := by
        linarith
      have h43 : x = 2 ∨ x = -2 := by
        have h7 : x^2 = 4 := h42
        have h8 : x = 2 ∨ x = -2 := by
          have h81 : x^2 - 4 = 0 := by linarith
          have h82 : (x - 2) * (x + 2) = 0 := by
            nlinarith
          cases' (mul_eq_zero.mp h82) with h83 h84
          · -- Case where $x - 2 = 0$ so $x = 2$
            left
            linarith
          · -- Case where $x + 2 = 0$ so $x = -2$
            right
            linarith
        tauto
      tauto
    · -- Case where the quartic factors are roots of x^2 + 9 x + 5 = 0
      -- Solving the quadratic using formula
      have h51 : x^2 + 9 * x + 5 = 0 := by
        nlinarith
      have h52 : (x - (-9 + Real.sqrt 61) / 2) * (x - (-9 - Real.sqrt 61) / 2) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (61 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (61 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h52) with h53 h54
      · -- Case where $x - (-9 + Real.sqrt 61)/2 = 0$ so $x = (-9 + Real.sqrt 61)/2$
        right
        right
        left
        linarith
      · -- Case where $x - (-9 - Real.sqrt 61)/2 = 0$ so $x = (-9 - Real.sqrt 61)/2$
        right
        right
        right
        linarith
  · -- Proof of the reverse direction: if x is one of the four roots, it satisfies the equation
    rintro (h | h | h | h)
    · -- Case where x = 2
      rw [h]
      norm_num
    · -- Case where x = -2
      rw [h]
      norm_num
    · -- Case where x = (-9 + Real.sqrt 61)/2
      rw [h]
      nlinarith [sq_nonneg (Real.sqrt 61), Real.sqrt_pos.mpr (by norm_num : (61 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (61 : ℝ) by norm_num)]
    · -- Case where x = (-9 - Real.sqrt 61)/2
      rw [h]
      nlinarith [sq_nonneg (Real.sqrt 61), Real.sqrt_pos.mpr (by norm_num : (61 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (61 : ℝ) by norm_num)]