import Mathlib

theorem algebra_102625 {a b : ℝ} (ha : a ≠ 0) (h : a * (-5) + b = 0) (h' : a * 5 + b = 0)
    (h'' : ∃ x, x ∈ Set.Icc 0 5 ∧ a * x ^ 2 + a * x + b = 0) :
    -a / 2 = 20 := by
  have eq1 : b = 5 * a := by 
    linarith 
  have eq2 : 10 * a = 0 := by
    rw [eq1] at h'
    linarith 
  have ha_zero : a = 0 := by 
    linarith 
  contradiction