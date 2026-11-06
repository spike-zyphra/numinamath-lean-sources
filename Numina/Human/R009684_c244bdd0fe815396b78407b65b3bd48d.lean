import Mathlib

/- Darren has borrowed $100$ clams from Ethan at a $10\%$ simple daily interest. Meanwhile, Fergie has borrowed $150$ clams from Gertie at a $5\%$ simple daily interest. In how many days will Darren and Fergie owe the same amounts, assuming that they will not make any repayments in that time period? -/
theorem algebra_13106 (d f t : ℝ) (h₀ : d = 100 * (1 + 10 / 100 * t)) (h₁ : f = 150 * (1 + 5 / 100 * t)) :
    d = f → t = 20 := by
  intro eq
  linarith