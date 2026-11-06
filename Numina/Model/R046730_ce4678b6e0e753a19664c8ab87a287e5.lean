import Mathlib

theorem algebra_145836 {x y : ℝ} (h1 : x^2 * y - x * y^2 - 5 * x + 5 * y + 3 = 0)
    (h2 : x^3 * y - x * y^3 - 5 * x^2 + 5 * y^2 + 15 = 0) :
    (x, y) = (4, 1) := by
  have eq1 : (x - y) * (x * y - 5) = -3 := by
    nlinarith
  have eq2 : x + y = 5 := by
    have eq5 : x ^ 3 * y - x * y ^ 3 = x * y * (x ^ 2 - y ^ 2) := by 
      ring
    have eq6 : -5 * x ^ 2 + 5 * y ^ 2 = -5 * (x ^ 2 - y ^ 2) := by 
      ring
    have eq3 : x ^ 3 * y - x * y ^ 3 - 5 * x ^ 2 + 5 * y ^ 2 + 15 = 0 := h2
    have eq7 : x ^ 3 * y - x * y ^ 3 - 5 * x ^ 2 + 5 * y ^ 2 + 15 = 
      (x * y * (x ^ 2 - y ^ 2) ) + (-5 * (x ^ 2 - y ^ 2)) + 15 := by
      nlinarith [eq5, eq6]
    rw [eq7] at eq3
    have eq8 : (x ^ 2 - y ^ 2) * (x * y - 5) = (x - y) * (x + y) * (x * y - 5) := by
      ring
    have eq9 : (x * y * (x ^ 2 - y ^ 2) ) + (-5 * (x ^ 2 - y ^ 2)) + 15 = (x ^ 2 - y ^ 2) * (x * y - 5) + 15 := by
      nlinarith
    rw [eq9] at eq3 
    rw [eq8] at eq3 
    have eq10 : (x - y) * (x * y - 5) = -3 := eq1
    have eq12 : (x - y) * (x + y) * (x * y - 5) = -3 * (x + y) := by
      calc
        (x - y) * (x + y) * (x * y - 5) = (x + y) * ((x - y) * (x * y - 5) ) := by ring
        _ = (x + y) * (-3) := by rw [eq1]
        _ = -3 * (x + y) := by ring
    rw [eq12] at eq3
    nlinarith
  have eq3 : y = 5 - x := by linarith
  rw [eq3] at eq1
  have eq4 : x = 4 := by
    have h3 : (x - 4) * (2 * x ^ 2 - 7 * x + 7) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- When x-4 =0, then x=4
      linarith
    · -- When 2x^2 -7x + 7 =0
      have h6 : (2 * x ^ 2 - 7 * x + 7) = 0 := by linarith
      nlinarith [sq_nonneg (x - 7 / 4), sq_nonneg (x - 4)]
  have eq5 : y = 1 := by
    rw [eq4] at eq3
    linarith
  simp [eq4, eq5]