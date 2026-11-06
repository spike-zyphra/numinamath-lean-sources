import Mathlib

theorem algebra_202277 (x y z : ℝ) (h : x + y + z - 2*(x*y + y*z + x*z) + 4*x*y*z = 1/2) :
    x = 1/2 ∨ y = 1/2 ∨ z = 1/2 := by
  have h4 : (x - 1/2) * (y - 1/2) * (z - 1/2) = 0 := by 
    have h0 : 8 * ((x - 1/2) * (y - 1/2) * (z - 1/2)) = 0 := by
      ring_nf
      linarith
    have h5 : (x - 1/2) * (y - 1/2) * (z - 1/2) = 0 := by
      linarith
    exact h5
  cases' (mul_eq_zero.mp h4) with h2 h2
  cases' (mul_eq_zero.mp h2) with h1 h1
  · -- Case where $(x - 1/2) = 0$, so $x = 1/2$
    left
    linarith
  · -- Case where $(y - 1/2) = 0$, so $y = 1/2$
    right
    left
    linarith
  · -- Case where $z - 1/2 = 0$, so $z = 1/2$
    right
    right
    nlinarith