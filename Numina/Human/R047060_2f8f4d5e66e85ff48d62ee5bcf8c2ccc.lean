import Mathlib

open Real Set
open scoped BigOperators

/- 6. A. The minimum value of the algebraic expression $\sqrt{x^{2}+4}+\sqrt{(12-x)^{2}+9}$ is $\qquad$ . -/
theorem algebra_157199 :
  IsLeast {y : ℝ | ∃ x, y = sqrt (x^2 + 4) + sqrt ((12 - x)^2 + 9)} 13 := by
  constructor
  · -- First, show that 13 belongs to the set
    -- We use x = 24/5 as the value that gives us the minimum
    use 24 / 5
    -- Prove that sqrt((24/5)^2 + 4) = 26/5
    have h1 : sqrt ((24 / 5:ℝ) ^ 2 + 4) = 26 / 5 := by
      rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
    -- Prove that sqrt((12 - 24/5)^2 + 9) = 39/5
    have h2 : sqrt ((12 - (24 / 5:ℝ)) ^ 2 + 9) = 39 / 5 := by
      rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
    -- Show that 26/5 + 39/5 = 13
    linarith [h1, h2]
  · -- Now, show that 13 is a lower bound of the set
    intro y hy
    -- Extract the x value from the hypothesis
    rcases hy with ⟨x, hx⟩
    -- Prove that for any x, the expression is at least 13
    have h1 : sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9) ≥ 13 := by
      -- Both square roots are non-negative
      have h2 : sqrt (x ^ 2 + 4) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 4)
      have h3 : sqrt ((12 - x) ^ 2 + 9) ≥ 0 := Real.sqrt_nonneg ((12 - x) ^ 2 + 9)
      -- Proof by contradiction
      by_contra h
      push_neg at h
      -- If the sum is less than 13
      have h4 : sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9) < 13 := by linarith
      -- Then the square of the sum is less than 13^2
      have h5 : (sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9)) ^ 2 < (13 : ℝ) ^ 2 := by nlinarith [h4, h2, h3]
      -- Expand the square of the sum using (a+b)^2 = a^2 + b^2 + 2ab
      have h6 : (sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9)) ^ 2 = (sqrt (x ^ 2 + 4)) ^ 2 + (sqrt ((12 - x) ^ 2 + 9)) ^ 2 + 2 * (sqrt (x ^ 2 + 4)) * (sqrt ((12 - x) ^ 2 + 9)) := by ring
      -- Simplify the squares of square roots
      have h7 : (sqrt (x ^ 2 + 4)) ^ 2 = x^2 + 4 := by rw [Real.sq_sqrt]; nlinarith
      have h8 : (sqrt ((12 - x) ^ 2 + 9)) ^ 2 = (12 - x) ^ 2 + 9 := by rw [Real.sq_sqrt]; nlinarith
      rw [h7, h8] at h6
      rw [h6] at h5
      -- Derive a contradiction using the fact that (x - 24/5)^2 ≥ 0
      nlinarith [sq_nonneg (x - 24 / 5), Real.sq_sqrt (show 0 ≤ (x ^ 2 + 4) by nlinarith), Real.sq_sqrt (show 0 ≤ ((12 - x) ^ 2 + 9) by nlinarith), mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 4)) (Real.sqrt_nonneg ((12 - x) ^ 2 + 9))]
    -- Conclude that y ≥ 13
    linarith [h1, hx]
