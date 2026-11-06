import Mathlib

theorem algebra_21518 (a : ℕ → ℝ) (ha : a 0 = 32) (ha1 : a 1 = 8)
    (h : ∀ n, a (n + 2) = (a n + a (n + 1)) / 2) :
    a 4 = 17 := by
  have ha2 : a 2 = (a 0 + a 1) / 2 := h 0
  rw [ha, ha1] at ha2
  norm_num at ha2

  have ha3 : a 3 = (a 1 + a 2) / 2 := h 1
  rw [ha1, ha2] at ha3
  norm_num at ha3

  have ha4 : a 4 = (a 2 + a 3) / 2 := h 2
  rw [ha2, ha3] at ha4
  norm_num at ha4
  linarith