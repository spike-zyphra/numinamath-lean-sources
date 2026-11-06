import Mathlib

theorem algebra_149952 (x : ℝ) (hx : 24*x^3-10*x^2-101*x-60=0) :
    (x=-3/4 ∨ x=-4/3 ∨ x=5/2) := by
  have h1 : (x + 3/4) * (x + 4/3) * (x - 5/2) = 0 := by
    ring_nf at hx ⊢
    nlinarith [sq_nonneg (x + 3/4), sq_nonneg (x + 4/3), sq_nonneg (x - 5/2)]
  cases' (mul_eq_zero.mp h1) with h2 h3
  · cases' (mul_eq_zero.mp h2) with h4 h5
    · -- case where $x + 3/4 = 0$ so $x = -3/4$
      left
      linarith
    · -- case where $x + 4/3 = 0$ so $x = -4/3$
      right
      left
      linarith
  · -- case where $x - 5/2 = 0$ so $x = 5/2$
    right
    right
    linarith