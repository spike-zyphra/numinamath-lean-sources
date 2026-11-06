import Mathlib

/- Three. (Full marks 12 points) Solve the equation:
$$
\frac{13 x-x^{2}}{x+1}\left(x+\frac{13-x}{x+1}\right)=42 \text {. }
$$ -/
theorem algebra_328299 (x : ℝ) (hx : x ≠ -1) :
    (13 * x - x ^ 2) / (x + 1) * (x + (13 - x) / (x + 1)) = 42 ↔
    x = 1 ∨ x = 6 ∨ x = 3 + Real.sqrt 2 ∨ x = 3 - Real.sqrt 2 := by

  constructor
  · -- Assume left side, prove right side (solve the equation)
    intro h

    -- Establish that x+1 ≠ 0 from our hypothesis
    have h1 : x + 1 ≠ 0 := by
      intro h2
      apply hx
      linarith

    -- Name the original equation for reference
    have eq1 : (13 * x - x^2) / (x + 1) * (x + (13 - x) / (x + 1)) = 42 := h

    -- Simplify the left side of the equation using algebraic manipulation
    have eq2 : (13 * x - x^2) / (x + 1) * (x + (13 - x) / (x + 1)) = (13 * x - x^2) * (x^2 + 13) / (x + 1) ^ 2 := by
      have denom_ne_zero : x + 1 ≠ 0 := h1
      field_simp [denom_ne_zero]
      ring

    rw [eq2] at eq1

    -- Multiply both sides by (x+1)^2 to eliminate the denominator
    have eq3 : (13 * x - x^2) * (x^2 + 13) = 42 * (x + 1) ^ 2 := by
      have denom_ne_zero : x + 1 ≠ 0 := h1
      field_simp [denom_ne_zero] at eq1
      nlinarith

    -- Factor the resulting polynomial equation to (x-1)(x-6)(x²-6x+7) = 0
    have poly_eq : (x - 1) * (x - 6) * (x^2 - 6 * x + 7) = 0 := by
      ring_nf at eq3 ⊢
      nlinarith [sq_nonneg (x^2), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x - 6), sq_nonneg (x^2 - 6 * x + 7)]

    -- Apply the zero product property to find all solutions
    cases' (mul_eq_zero.mp poly_eq) with h4 h5

    · cases' (mul_eq_zero.mp h4) with h6 h7
      · -- First solution: x = 1
        left
        linarith
      · -- Second solution: x = 6
        right
        left
        linarith
    · -- Handle the quadratic factor x² - 6x + 7 = 0
      have h8 : x^2 - 6 * x + 7 = 0 := h5
      -- Factor the quadratic as (x-(3+√2))(x-(3-√2)) = 0
      have h9 : (x - (3 + Real.sqrt 2)) * (x - (3 - Real.sqrt 2)) = 0 := by
        ring_nf
        have h10 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
        nlinarith [h8, h10]
      cases' (mul_eq_zero.mp h9) with h11 h12
      · -- Third solution: x = 3 + √2
        right
        right
        left
        linarith
      · -- Fourth solution: x = 3 - √2
        right
        right
        right
        linarith

  · -- Assume right side, prove left side (verify solutions)
    rintro (h | h | h | h)
    · -- Verify that x = 1 satisfies the original equation
      rw [h]
      norm_num
    · -- Verify that x = 6 satisfies the original equation
      rw [h]
      norm_num
    · -- Verify that x = 3 + √2 satisfies the original equation
      rw [h]
      -- Prove that the denominator is not zero
      have h1 : (3 + Real.sqrt 2) + 1 ≠ 0 := by
        have h1 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
        linarith [h1]
      field_simp [h1]
      ring_nf
      -- Use the fact that (√2)² = 2 to simplify the expression
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
      nlinarith [h2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ))]
    · -- Verify that x = 3 - √2 satisfies the original equation
      rw [h]
      -- Prove that the denominator is not zero
      have h1 : (3 - Real.sqrt 2) + 1 ≠ 0 := by
        have h1 : Real.sqrt 2 < 4 := by
          rw [Real.sqrt_lt] <;> norm_num
        nlinarith [h1, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ))]
      field_simp [h1]
      ring_nf
      -- Use the fact that (√2)² = 2 to simplify the expression
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
      nlinarith [h2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ))]
