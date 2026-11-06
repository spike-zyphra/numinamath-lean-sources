import Mathlib

theorem algebra_149223 {a b : ℝ} (x : ℕ → ℝ) (h₀ : x 0 = a) (h₁ : x 1 = b)
    (h₂ : ∀ n, x (n + 2) = x (n + 1) - x n) :
    x 99 = -a ∧ ∑ i in Finset.range 100, x i = 2 * b - a := by
  -- Let's prove $x_{99}$ and the summation.
  -- First part: prove x 99 = -a.
  have h99 : x 99 = -a := by
    -- Compute by recurrence relations.
    norm_num [h₂, h₀, h₁] at *
    <;> linarith

  -- Second part: prove the summation.
  have h_sum : ∑ i in Finset.range 100, x i = 2 * b - a := by
    -- Compute the summation using Lean's computational system.
    norm_num [Finset.sum_range_succ, h₀, h₁, h₂]
    <;> linarith

  -- Conclude both parts.
  constructor
  · exact h99
  · exact h_sum