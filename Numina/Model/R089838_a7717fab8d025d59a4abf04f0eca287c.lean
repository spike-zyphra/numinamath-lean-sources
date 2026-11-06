import Mathlib

theorem algebra_306501 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h1 : a + Real.sqrt a = 2008) (h2 : b^2 + b = 2008) : a + b = 2008 := by
  have h3 : Real.sqrt a > 0 := by 
    apply Real.sqrt_pos.2 
    linarith
  have h4 : Real.sqrt a ^ 2 = a := by
    rw [Real.sq_sqrt]
    linarith
  nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ a by linarith), 
          h2, 
          mul_pos ha hb
        ]