import Mathlib

theorem algebra_7266 (x : ℝ) (hx : x^3-2*x^2-x+2=0) :
    x=2 ∨ x=-1 ∨ x=1 := by 
  have h : (x - 1) * (x + 1) * (x - 2) = 0 := by 
    ring_nf at hx ⊢
    linarith 
  cases' (mul_eq_zero.mp h) with h1 h2 
  cases' (mul_eq_zero.mp h1) with h3 h4 
  · -- Case: (x - 1) * (x + 1) = 0, so x - 1 = 0. Thus x = 1.
    right
    right 
    linarith 
  · -- Case: (x - 1) * (x + 1) = 0, so x + 1 = 0. Thus x = -1.
    right 
    left 
    linarith 
  · -- Case: (x - 2) = 0. Thus x = 2.
    left 
    linarith