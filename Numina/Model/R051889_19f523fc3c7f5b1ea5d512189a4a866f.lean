import Mathlib

theorem algebra_12572 {a b : ℝ} (ha : a ≠ b) (h : a ^ 2 + a * a + b = b ^ 2 + b * a + b) :
    (2 ^ 2 + 2 * a + b) = 4 := by
  -- Let's then compute f(2) where f(x) = x² + a*x + b.
  have h1 : 2 * a ^ 2 - a * b - b ^ 2 = 0 := by
    nlinarith
  
  have h2 : (a - b) * (2 * a + b) = 0 := by
    nlinarith [h1]

  cases' (mul_eq_zero.mp h2) with h3 h4
  
  · 
    -- Case where a - b = 0 (contradicts a ≠ b)
    exfalso 
    exact ha (by linarith)
  
  · 
    -- Case where 2a + b = 0 (which gives b = -2a)
    have hb : b = -2 * a := by 
      linarith

    rw [hb]
    -- Now f(2) = 4 + 2a + (-2a). Let's compute this value.
    
    ring