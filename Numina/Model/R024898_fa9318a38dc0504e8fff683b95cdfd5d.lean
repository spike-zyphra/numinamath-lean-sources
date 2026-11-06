import Mathlib

theorem inequalities_200478 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ Real.sqrt ((x^2 + y^2) / 2) - (x + y) / 2 ∧
    Real.sqrt ((x^2 + y^2) / 2) - (x + y) / 2 ≤ |x - y| / 2 := by

  have h1 : 0 ≤ Real.sqrt ((x^2 + y^2) / 2) - (x + y) / 2 := by
    have h4 : Real.sqrt ((x ^ 2 + y ^ 2) / 2) ≥ (x + y) / 2 := by
      have h2 : (Real.sqrt ((x ^ 2 + y ^ 2) / 2)) ^ 2 ≥ ((x + y) / 2) ^ 2 := by
        have h3 : (Real.sqrt ((x ^ 2 + y ^ 2) / 2)) ^ 2 = (x ^ 2 + y ^ 2) / 2 := by
          rw [Real.sq_sqrt]
          nlinarith [sq_nonneg (x - y)]
        nlinarith [sq_nonneg (x - y), h3]
      have h3 : Real.sqrt ((x ^ 2 + y ^ 2) / 2) ≥ 0 := by positivity
      have h4 : (x + y) / 2 ≥ 0 := by nlinarith
      nlinarith [Real.sqrt_nonneg ((x ^ 2 + y ^ 2) / 2)]
    linarith [show 0 ≤ Real.sqrt ((x^2 + y^2) / 2) by positivity]

  have h2 : Real.sqrt ((x^2 + y^2) / 2) - (x + y) / 2 ≤ |x - y| / 2 := by
    by_cases h : x ≥ y
    · -- x ≥ y, so |x - y| = x - y
      have h5 : |x - y| = x - y := by
        rw [abs_of_nonneg]
        nlinarith
      have h3 : Real.sqrt ((x ^ 2 + y ^ 2) / 2) ≤ x := by
        have h4 : (Real.sqrt ((x ^ 2 + y ^ 2) / 2)) ^ 2 ≤ x ^ 2 := by
          have h31 : (Real.sqrt ((x^2 + y^2) / 2)) ^ 2 = (x ^ 2 + y ^ 2) / 2 := by
            rw [Real.sq_sqrt]
            nlinarith [sq_nonneg (x - y)]
          nlinarith [sq_nonneg (x - y)]
        have h5 : Real.sqrt ((x ^ 2 + y ^ 2) / 2) ≤ x := by
          nlinarith [Real.sqrt_nonneg ((x ^ 2 + y ^ 2) / 2), sq_nonneg (Real.sqrt ((x ^ 2 + y ^ 2) / 2) - x)]
        linarith
      linarith [h5, h3]

    · -- y > x, so |x - y| = y - x
      have h6 : |x - y| = y - x := by
        rw [abs_of_neg]
        nlinarith
        all_goals nlinarith
      have h3 : Real.sqrt ((x ^ 2 + y ^ 2) / 2) ≤ y := by
        have h4 : (Real.sqrt ((x ^ 2 + y ^ 2) / 2)) ^ 2 ≤ y ^ 2 := by
          have h31 : (Real.sqrt ((x^2 + y^2) / 2)) ^ 2 = (x ^ 2 + y ^ 2) / 2 := by
            rw [Real.sq_sqrt]
            nlinarith [sq_nonneg (x - y)]
          nlinarith [sq_nonneg (y - x)]
        have h5 : Real.sqrt ((x ^ 2 + y ^ 2) / 2) ≤ y := by
          nlinarith [Real.sqrt_nonneg ((x ^ 2 + y ^ 2) / 2), sq_nonneg (Real.sqrt ((x ^ 2 + y ^ 2) / 2) - y)]
        linarith
      linarith [h6, h3]

  constructor
  · exact h1
  · exact h2