import Mathlib

open scoped BigOperators

theorem algebra_316099 (a : ℕ → ℝ) (h₀ : a 1 = 1)
  (h₁ : ∀ n, a (n + 1) = a n + 1 / a n) :
  14 < a 100 ∧ a 100 < 18 := by 
  have h2 := h₁ 0
  rw [show (0 + 1 : ℕ) = 1 by omega] at h2
  rw [h₀] at h2
  by_cases h3 : a 0 = 0 
  · -- Assume h3 is true. a 0 = 0
    rw [h3] at h2
    norm_num [h3] at h2 
  · -- Assume h3 is false.
    have h4 : a 0 ≠ 0 := by 
      intro h5
      apply h3
      linarith
    -- From `h2` we have: `1 = a 0 + 1 / a 0`. Multiply through by `a 0` to clear the denominator.
    -- $1 \cdot a 0 = a 0 \cdot (a 0 + \frac{1}{a 0})$
    -- $a 0 = a 0^2 + 1$
    -- Let's match the proof by code.
    -- h5 is given as `eq1` here.
    have h5 : a 0 ^ 2 - a 0 + 1 = 0 := by 
      field_simp [h4] at h2 
      nlinarith 
    -- The quadratic formula `a 0^2 - a 0 + 1` is evaluated here.
    have h6 : a 0 ^ 2 - a 0 + 1 > (0 : ℝ) := by
      nlinarith [sq_nonneg (a 0 - 1 / 2)]
    -- Given h5 is `iff` with `h5`. So contradiction holds.
    -- Lean can derive contradiction from negative discriminant quadratic being equated to zero which doesn't have zero discriminant.
    have h7 : (a 0 ^ 2 - a 0 + 1 = 0) := h5
    -- The equation side is discriminant.
    -- Now h6 : the value of h5's equation part is >0
    -- The `nlinarith` tactics will lead to contradiction
    nlinarith