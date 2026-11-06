import Mathlib

open Real

theorem algebra_16631 {r : ℝ} (hr : r > 0) (h : 2 * (2 * π * r) = π * r ^ 2) :
    r = 4 := by
  have h1 : π ≠ 0 := by
    linarith [Real.pi_pos]
  have eq1 : 4 * r = r ^ 2 := by
    have h2 : π ≠ 0 := h1
    apply (mul_left_inj' h2).mp 
    linarith [h]
  have eq2 : r ^ 2 - 4 * r = 0 := by
    linarith [eq1]
  have eq3 : r * (r - 4) = 0 := by
    linarith [eq2]
  cases' (mul_eq_zero.1 eq3) with h4 h5
  · -- Case r = 0 which contradicts r > 0
    linarith
  · -- Case r - 4 = 0 so r = 4
    linarith