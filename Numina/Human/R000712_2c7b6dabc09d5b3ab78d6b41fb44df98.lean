import Mathlib

/- If Alex gives Bob a penny, Bob will have three times as many pennies as Alex has. If Bob gives Alex a penny, Bob will have twice as many pennies as Alex has. How many pennies does Bob currently have? -/
theorem algebra_14224 {x y : ℤ} (hx : x ≥ 1) (hy : y ≥ 1) (h1 : y + 1 = 3 * (x - 1)) (h2 : y - 1 = 2 * (x + 1)) :
    y = 17 := by linarith
