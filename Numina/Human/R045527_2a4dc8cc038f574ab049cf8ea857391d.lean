import Mathlib

/- The proper divisors of 12 are 1, 2, 3, 4 and 6. A proper divisor of an integer $N$ is a positive divisor of $N$ that is less than $N$. What is the sum of the proper divisors of the sum of the proper divisors of 284? -/
theorem algebra_18688 {a b c d : ℤ} (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
    (hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (h1 : a + b = 10) (h2 : a + c = 18)
    (h3 : a + d = 19) (h4 : b + c = 20) (h5 : b + d = 21) (h6 : c + d = 29) :
    a = 4 ∧ b = 6 ∧ c = 14 ∧ d = 15 := by
    -- Adding Equations (1) and (6) and subtracting (2)
  have hb_val : b = 6 := by
    linarith [h1, h2, h4]
  
  -- Plugging b = 6 into Equation (1) to find a
  have ha_val : a = 4 := by
    linarith [h1, hb_val]
  
  -- Plugging a = 4 into Equation (2) to find c
  have hc_val : c = 14 := by
    linarith [h2, ha_val]
  
  -- Plugging c = 14 into Equation (6) to find d
  have hd_val : d = 15 := by
    linarith [h6, hc_val]
  
  -- Asserting the final values of a, b, c, and d
  exact ⟨ha_val, hb_val, hc_val, hd_val⟩