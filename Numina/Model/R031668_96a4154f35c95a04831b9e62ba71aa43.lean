import Mathlib

theorem algebra_174965 {a b : ℝ} (ha : a ≠ 0) (h : 1/5 * (-5)^2 + a * (-5) + b = 0)
    (h' : 1/5 * 5^2 + a * 5 + b = 0) (h'' : ∃ x, 1/5 * x^2 + a * x + b = 0 ∧ x ∈ Set.Icc (-5) 5) :
    -a = 20 := by
  have eq1 : -5 * a + b = -5 := by 
    linarith
  have eq2 : 5 * a + b = -5 := by 
    linarith
  have h1 : a = 0 := by 
    linarith [eq1, eq2]
  contradiction