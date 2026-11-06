import Mathlib

/- $5$ green balls and $2$ red balls together weigh $10$ pounds, and $1$ green ball and $4$ red balls together weigh $7$ pounds. If all red balls weigh the same amount and all green balls weigh the same, then what is the weight of $8$ red and $8$ green balls together? -/
theorem algebra_19638 {x y : ℝ} (h₀ : 5 * x + 2 * y = 10) (h₁ : x + 4 * y = 7) :
    8 * x + 8 * y = 68 / 3 := by 
  linarith