import Mathlib

theorem algebra_20180 {a b : ℤ} (ha : a ≠ b) (h : ∀ x, (a * x + b) * (2 * x + 3) = 20 * x ^ 2 + 44 * x + 21) :
    a + b = 17 := by
  have eq1 := h 0
  have eq2 := h 1
  -- From `eq1`: $(a * 0 + b) * (2 * 0 + 3) = 20 * 0 ^ 2 + 44 * 0 + 21$ simplifies to $3b = 21$ so $b = 7$.
  -- From `eq2`: $(a * 1 + b) * (2 * 1 + 3) = 20 * 1 ^ 2 + 44 * 1 + 21$ simplifies to $5(a + b) = 85$ so $a + b = 17$.
  
  linarith