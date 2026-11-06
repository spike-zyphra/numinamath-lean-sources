import Mathlib

/- Let $x$ and $y$ be real numbers. Find the minimum value of the algebraic expression $5x^2 + 4y^2 - 8xy + 2x + 4$. -/
theorem algebra_9065 :
  IsLeast {z : ℝ | ∃ x y, z = 5 * x ^ 2 + 4 * y ^ 2 - 8 * x * y + 2 * x + 4} 3 := by

  -- The minimum value of the expression 5x^2 + 4y^2 - 8xy + 2x + 4 is 3.
  -- Prove that 3 is a lower bound:
  constructor
  -- Simplify the expression:
  . dsimp
    -- Show that 3 can be achieved by setting x = -1 and y = -1:
    have h₀ : (3 : ℝ) = 5 * (-1) ^ 2 + 4 * (-1) ^ 2 - 8 * (-1) * (-1) + 2 * (-1) + 4 := by norm_num
    exact ⟨-1, -1, h₀⟩
  -- Prove that 3 is the greatest lower bound:
  . rintro z hxy
    -- Simplify the expression in the hypothesis:
    dsimp at hxy
    -- Extract x, y, and the equality from the hypothesis:
    obtain ⟨x, y, hz⟩ := hxy
    -- Rewrite the expression using algebraic manipulation:
    have h₁ : 5 * x ^ 2 + 4 * y ^ 2 - 8 * x * y + 2 * x + 4 = 4 * (x - y) ^ 2 + (x + 1) ^ 2 + 3 := by ring
    -- Substitute and use the non-negativity of squares:
    rw [hz, h₁]
    linarith [sq_nonneg (x - y), sq_nonneg (x + 1)]
