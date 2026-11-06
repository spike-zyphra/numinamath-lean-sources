import Mathlib

theorem algebra_1568
    (x : ℝ)
    (hx : x^3 + 2 * x^2 + 2 * x + 1 = 0) :
    x^1994 + x^1997 + x^2000 = 1 := by

  have h1 : (x + 1) * (x^2 + x + 1) = 0 := by 
    ring_nf at hx ⊢
    linarith
  
  cases' (mul_eq_zero.mp h1) with h2 h3
  
  · -- Case where $x + 1 = 0$, so $x = -1$
    have hx_eq : x = -1 := by linarith
    rw [hx_eq]
    norm_num
  
  · -- Case where $x^2 + x + 1 = 0$, but this has no real roots
    have h4 : x^2 + x + 1 > 0 := by
      nlinarith [sq_nonneg (x + 1/2)]
    nlinarith [h3, h4]