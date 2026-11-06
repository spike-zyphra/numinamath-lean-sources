import Mathlib

/- If $4$ wands are equivalent to $6$ rands and $24$ rands are equivalent to $8$ fands, how many wands are equivalent to $5$ fands? -/
theorem algebra_20491 (a b c : ℝ) (h₀ : 4 * a = 6 * b) (h₁ : 24 * b = 8 * c) :
    5 * c = 10 * a := by linarith