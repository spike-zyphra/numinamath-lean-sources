import Mathlib

theorem algebra_129089 (a b : ℝ) (ha : a ≠ b) :
    ∃ x1 x2, x1 ≠ x2 ∧ (x1 + a) * (x1 + b) = 2 * x1 + a + b ∧
    (x2 + a) * (x2 + b) = 2 * x2 + a + b := by

  use (- (a + b - 2 ) + Real.sqrt ((a - b) ^ 2 + 4 )) / 2,
    (- (a + b - 2 ) - Real.sqrt ((a - b) ^ 2 + 4 )) / 2
  constructor
  · -- Show x1 ≠ x2.
    by_contra h
    have h1 : (- (a + b - 2 ) + Real.sqrt ((a - b) ^ 2 + 4 )) / 2 =
      (- (a + b - 2 ) - Real.sqrt ((a - b) ^ 2 + 4 )) / 2 := by
      linarith [h]
    have h2 : Real.sqrt ((a - b) ^ 2 + 4 ) = 0 := by
      linarith [h1]
    have h3 : Real.sqrt ((a - b) ^ 2 + 4 ) > 0 := by
      have h4 : (a - b) ^ 2 + 4 > 0 := by
        have h5 : (a - b) ^ 2 > 0 := by
          apply pow_two_pos_of_ne_zero
          intro h6
          apply ha
          linarith
        nlinarith
      positivity
    linarith [h2, h3]
  constructor
  · -- Show that the first root is a solution
    nlinarith [ Real.sqrt_nonneg ((a - b) ^ 2 + 4 ) , Real.sq_sqrt (show 0 ≤ (a - b ) ^ 2 + 4 by positivity) ]
  · -- Show that the second root is a solution
    nlinarith [ Real.sqrt_nonneg ((a - b) ^ 2 + 4 ) , Real.sq_sqrt (show 0 ≤ (a - b ) ^ 2 + 4 by positivity) ]