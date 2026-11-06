import Mathlib

theorem algebra_2684 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a / b + b / c = 3.5) (h' : a / b = b / c + 0.5) :
    a / b = 2 := by 
  have eq5 : b / c = a / b - 0.5 := by linarith
  rw [eq5] at h
  ring_nf at h ⊢
  <;> nlinarith