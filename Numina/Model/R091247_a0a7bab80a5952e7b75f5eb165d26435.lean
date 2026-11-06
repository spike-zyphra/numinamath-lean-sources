import Mathlib

theorem algebra_320437 {x : ℝ} (hx : x^3 + x^2 + x + 1 = 0) :
    x^97 + x^98 + x^99 + x^100 + x^101 + x^102 + x^103 = -1 := by
  have h2 : x^2 + 1 ≠ 0 := by 
    nlinarith [sq_nonneg x]
  have h3 : (x^2 + 1) * (x + 1) = 0 := by
    ring_nf
    linarith [hx]
  cases' (mul_eq_zero.1 h3) with h4 h5 
  · 
    exfalso 
    exact h2 (by linarith)
  · 
    have hx_val : x = -1 := by
      linarith
    rw [hx_val]
    norm_num