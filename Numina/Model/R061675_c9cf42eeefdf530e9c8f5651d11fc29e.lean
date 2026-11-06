import Mathlib

theorem algebra_173781 (m l : ℝ) (hl : l = 20 * m) (h : m > 0) (h' : l > 0)
    (h'' : m * (3 / 4) = 2 * m) :
    (l - 3 * m) / (m / 2) = 15 := by 
  have h1 : m ≠ 0 := by linarith
  have h2 : (3 / 4 : ℝ) = 2 := by 
    apply (mul_left_inj' h1).mp
    linarith
  linarith