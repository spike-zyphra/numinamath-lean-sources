import Mathlib

theorem inequalities_129464 (x y : ℝ) (h1 : 3 ≤ x + y ∧ x + y ≤ 5) (h2 : -1 ≤ x - y ∧ x - y ≤ 1) :
    3 * x + y ≤ 11 := by 
  have h3 : 3 ≤ x + y := h1.1
  have h4 : x + y ≤ 5 := h1.2
  have h5 : -1 ≤ x - y := h2.1
  have h6 : x - y ≤ 1 := h2.2
  linarith