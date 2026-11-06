import Mathlib

theorem algebra_298497 {a : ℝ} (ha : a ≠ 0) (h : ∃ x, x > 1 ∧ 2*a*x^2-2*x-3*a-2=0 ∧ ∃ x, x < 1 ∧ 2*a*x^2-2*x-3*a-2=0) :
    a > 0 ∨ a < 0 := by 
  by_contra h'
  push_neg at h'
  have h1 : a = 0 := by
    linarith
  contradiction