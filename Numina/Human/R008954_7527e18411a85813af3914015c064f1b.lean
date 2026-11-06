import Mathlib

/- When Marika bought her house she paid $80\%$ of the purchase price of the house with a loan. She paid the remaining $\$49,400$ of the purchase price with her savings. What was the purchase price of her house? -/
theorem algebra_21286 {x : ℝ} (hx : x ≠ 0) (h : 80 / 100 * x + 49400 = x) :
    x = 247000 := by
    -- trivial calculation
    linarith
