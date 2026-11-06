import Mathlib

open Real Set
open scoped BigOperators

/- Given $ y = \frac { 2 0 2 1 } { x ^ { 2 } - 8 x + 6 0 } $ and $y$ is a positive integer, $x$ is a real number, find the maximum value of $y$.

Given $ y = \frac { 2 0 2 1 } { x ^ { 2 } - 8 x + 6 0 } $ and $y$ is a positive integer, $x$ is a real number, find the maximum value of $y$. -/
theorem algebra_629486 {y : ℕ} (hy : ∃ x : ℝ, y = 2021 / (x^2 - 8 * x + 60)) :
    y ≤ 45 := by
  rcases hy with ⟨x, hx⟩
  -- Prove that the denominator x^2 - 8x + 60 cannot be zero
  have h1 : (x^2 - 8 * x + 60) ≠ 0 := by
    by_contra h
    -- Use the fact that (x-4)^2 is always non-negative
    have : (x - 4) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith
  -- Restate the equation for y from the hypothesis
  have h2 : y = 2021 / (x^2 - 8 * x + 60) := by
    exact hx
  -- Prove that the denominator is strictly positive
  have h3 : (x ^ 2 - 8 * x + 60) > 0 := by nlinarith
  -- Prove that y ≤ 45 by contradiction
  have h4 : y ≤ 45 := by
    by_contra h
    push_neg at h
    -- If y > 45, then y ≥ 46 (since y is a natural number)
    have h5 : y ≥ 46 := by linarith
    -- Convert y ≥ 46 to use real numbers instead of natural numbers
    have h7 : (y : ℝ) ≥ (46 : ℝ) := by
      exact_mod_cast h5
    -- Prove that the denominator must be at most 2021/46
    have h8 : (x ^ 2 - 8 * x + 60) ≤ (2021 : ℝ) / 46 := by
      -- Use the fact that y = 2021 / (x^2 - 8x + 60) as a real number
      have h9 : (y : ℝ) = 2021 / (x^2 - 8 * x + 60) := by
        exact_mod_cast h2
      -- Restate that the denominator is positive
      have h10 : (x^2 - 8 * x + 60) > 0 := h3
      -- Rearrange the equation to get 2021 = y * (x^2 - 8x + 60)
      have h11 : (2021 : ℝ) = (y : ℝ) * (x^2 - 8 * x + 60) := by
        have h12 : (x^2 - 8 * x + 60) ≠ 0 := h1
        field_simp [h12] at h9
        linarith
      -- Use nonlinear arithmetic to derive the upper bound
      nlinarith [h7, h11, h10]
    -- Prove that the denominator is at least 44 using the fact that (x-4)^2 ≥ 0
    have h12 : (x ^ 2 - 8 * x + 60) ≥ 44 := by
      nlinarith [sq_nonneg (x - 4)]
    -- Restate the upper bound on the denominator
    have h13 : (x ^ 2 - 8 * x + 60) ≤ (2021 : ℝ) / 46 := by linarith
    -- Prove that 2021/46 < 44 by numerical computation
    have h14 : (2021 : ℝ) / 46 < 44 := by norm_num
    -- Derive a contradiction: the denominator is ≥ 44 but also ≤ 2021/46 < 44
    linarith [h12, h13, h14]
  -- Return the result that y ≤ 45
  exact h4
