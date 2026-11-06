import Mathlib

theorem algebra_176840 (α : Real) :
    ∃ x, ∀ β : ℝ, Real.sin (α + β) ^ 2 + Real.sin (β - α) ^ 2 -
      2 * Real.sin (α + β) * Real.sin (β - α) * Real.cos (2 * α) = x := by
  use 4 * Real.sin α ^ 2 * Real.cos α ^ 2
  intro β
  have h1 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by
    rw [Real.sin_add]
  have h2 : Real.sin (β - α) = Real.sin β * Real.cos α - Real.cos β * Real.sin α := by
    rw [Real.sin_sub]
    all_goals ring
  have h3 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by
    rw [Real.cos_two_mul]
    all_goals ring
  rw [h1, h2, h3]
  have h4 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α
  have h5 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq β
  -- Simplify the equation using trigonometric substitution.
  have eq10 : Real.sin α ^ 2 = Real.sin α ^ 2 := rfl
  have eq10' : Real.cos α ^ 2 = Real.cos α ^ 2 := rfl
  have eq11 : Real.sin β ^ 2 = Real.sin β ^ 2 := rfl
  have eq11' : Real.cos β ^ 2 = Real.cos β ^ 2 := rfl

  -- Normalize expressions and provide squares.
  have h6 : Real.sin β ^ 2 = 1 - Real.cos β ^ 2 := by
    linarith
  have h7 : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by
    linarith
  -- Now need to simplify complex expressions

  -- Combination of expansion
  nlinarith [sq_nonneg (Real.sin α ^ 2 - Real.cos α ^ 2), sq_nonneg (Real.sin α * Real.sin β - Real.cos α * Real.cos β), sq_nonneg (Real.sin β * Real.cos α - Real.cos β * Real.sin α), sq_nonneg (Real.sin α * Real.cos β - Real.cos α * Real.sin β), sq_nonneg (Real.sin α * Real.sin β), sq_nonneg (Real.sin α * Real.cos β), sq_nonneg (Real.cos α * Real.sin β), sq_nonneg (Real.cos β * Real.sin α), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, sq_nonneg (Real.sin α ^ 2 - Real.sin β ^ 2), sq_nonneg (Real.sin α * Real.sin β - Real.cos α * Real.cos β)]