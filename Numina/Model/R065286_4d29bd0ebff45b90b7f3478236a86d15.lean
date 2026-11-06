import Mathlib

theorem algebra_308640 {k a b m n : ℝ} (ha : a ≠ 0) (h : k / (-2) = m ∧ k / 5 = n)
    (h1 : m = a * (-2) + b) (h2 : n = a * 5 + b) : 3 * a + b = 0 := by
  have eq1 : k / (-2) = a * (-2) + b := by 
    linarith [h.1, h1]
  have eq2 : k / 5 = a * 5 + b := by 
    linarith [h.2, h2]

  have eq3 : k = 4 * a - 2 * b := by
    linarith [eq1]

  have eq4 : k = 25 * a + 5 * b := by 
    linarith [eq2]

  have eq5 : 4 * a - 2 * b = 25 * a + 5 * b := by 
    linarith [eq3, eq4]

  have eq6 : b = -3 * a := by 
    linarith

  linarith [eq6]