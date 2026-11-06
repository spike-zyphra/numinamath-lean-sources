import Mathlib

theorem algebra_119443 (a b : ℝ) (h : 3*a^2+3*b^2-2*a-14*b+46/3=0) :
    4/3 ≤ a+b ∧ a+b ≤ 4 := by 
  have h1: 3*(a-1/3)^2+3*(b-7/3)^2 = 4/3 := by
    ring_nf at h ⊢
    linarith
  have h2: (a+b-4/3)*(a+b-4) ≤ 0 := by
    nlinarith [sq_nonneg (a - b + 2), sq_nonneg (a - 1 / 3), sq_nonneg (b - 7 / 3)]
  constructor
  · nlinarith
  · nlinarith