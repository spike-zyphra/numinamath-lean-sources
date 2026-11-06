import Mathlib

/- If $5^x=100$, what is the value of $5^{x+2}$? -/
theorem algebra_10670 {x : ℝ} (hx : (5 : ℝ) ^ x = 100) : (5 : ℝ) ^ (x + 2) = 2500 := by
  calc
    -- we get $5^{x+2}$ by multiply $5^2$
    (5 : ℝ) ^ (x + 2) = 5 ^ x * (5^(2 : ℝ)) := by rw [Real.rpow_add]; linarith
    -- subsititude $5^x = 100$, we get $2500$
    _ = 2500 := by rw [hx]; linarith