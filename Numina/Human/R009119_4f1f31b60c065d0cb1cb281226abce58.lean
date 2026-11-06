import Mathlib

/- Trey receives a $5\%$ commission on every sale he makes. On the sale of a $\$60$ coat (before any discounts), how many more cents will he receive if his commission is based on the original price of the coat rather than the price of the coat after a $20\%$ discount? -/
theorem algebra_19821 {x : ℝ} (hx : x = 60) :
    (x * 0.05 - (x * 0.8) * 0.05) * 100 = 60 := by 
  rw [hx]; ring