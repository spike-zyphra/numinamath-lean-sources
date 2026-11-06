import Mathlib

/- Let $(x,y)$ be an ordered pair of real numbers that satisfies the equation $x^2+y^2=14x+48y$. What is the maximum value of $y$? -/
theorem algebra_18861 :
    IsGreatest {y | ∃ x : ℝ, x ^ 2 + y ^ 2 = 14 * x + 48 * y} 49 := by
  -- Simplify the goal into two parts.
  simp [IsGreatest, upperBounds]
  refine ⟨?_, ?_⟩
  . -- Show that the maximum could be attained.
    use 7
    norm_num
  . -- Show that 49 is indeed an upper bound.
    intro y x h₀
    replace h₀ : (x - 7) ^ 2 + (y - 24) ^ 2 = 625 := by linarith only [h₀]
    have h₁ : (y - 24) ^ 2 ≤ 25 ^ 2 := by linarith only [h₀, show (x - 7) ^ 2 ≥ 0 by positivity]
    rw [sq_le_sq] at h₁
    simp [abs] at h₁
    linarith only [h₁]

