import Mathlib

theorem algebra_317413 (a b c : ℝ) :
    ∃ x : ℝ, x^2 + (a - b)*x + (b - c) = 0 ∨
          x^2 + (b - c)*x + (c - a) = 0 ∨
          x^2 + (c - a)*x + (a - b) = 0 := by
  by_cases h1 : (a - b) ^ 2 - 4 * (b - c) ≥ 0
  · -- First equation has a solution, construct it using quadratic formula
    use (b - a + Real.sqrt ((a - b) ^ 2 - 4 * (b - c))) / 2
    left
    ring_nf
    rw [Real.sq_sqrt (by nlinarith)]
    nlinarith
  · -- First discriminant is negative. Now check the second equation.
    by_cases h2 : (b - c) ^ 2 - 4 * (c - a) ≥ 0
    · -- Second equation has a solution. Construct it.
      use (c - b + Real.sqrt ((b - c) ^ 2 - 4 * (c - a))) / 2
      right
      left
      ring_nf
      rw [Real.sq_sqrt (by nlinarith)]
      nlinarith
    · -- Second discriminant is also negative
      have h3 : (c - a) ^ 2 - 4 * (a - b) ≥ 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      use (a - c + Real.sqrt ((c - a) ^ 2 - 4 * (a - b))) / 2
      right
      right
      ring_nf
      rw [Real.sq_sqrt (by nlinarith)]
      nlinarith