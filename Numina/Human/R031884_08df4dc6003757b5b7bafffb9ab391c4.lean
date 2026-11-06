import Mathlib

/- At the theater children get in for half price.
The price for 5 adult tickets and 4 child tickets is 24.50 $. 
How much would 8 adult tickets and 6 child tickets cost? 
(A) $35
(B) $38.50
(C) $40
(D) $42
(E) $42.50 -/ 
theorem algebra_96124 (a c x: ℝ) (h : a = 2 * c) (h₀ : 5 * a + 4 * c = 24.50) (h₁ : 8 * a + 6 * c = x) : x = 38.50 := by
  --substitute the condition that children enter at half the price
  rw[h] at h₀ h₁
  ring_nf at h₀ h₁
  --find the price of a ticket for children
  have hk := congrFun (congrArg HMul.hMul h₀) (1/14)
  simp at hk
  --find the required price
  rw[hk] at h₁
  rw[← h₁]
  ring_nf