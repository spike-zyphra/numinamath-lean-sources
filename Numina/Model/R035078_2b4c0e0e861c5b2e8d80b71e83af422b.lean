import Mathlib

theorem algebra_263898 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : 1 / x + 1 / y = 1) (h2 : 2 / x + 3 / y = 4) :
    x = -1 ∧ y = 1 / 2 := by
  have eq1 : x + y = x * y := by
    field_simp [hx, hy] at h1
    linarith
  have eq2 : 2 * y + 3 * x = 4 * (x * y) := by
    field_simp [hx, hy] at h2
    linarith
  have eq3 : x = -2 * y := by 
    nlinarith
  have eq4 : 2 * y ^ 2 - y = 0 := by 
    rw [eq3] at eq1
    linarith
  have eq5 : y * (2 * y - 1) = 0 := by 
    linarith
  cases' (mul_eq_zero.1 eq5) with hy1 hy2
  · -- case y = 0 
    exfalso
    apply hy
    linarith
  · -- case 2 * y -1 =0 
    have y_val : y = 1 / 2 := by linarith
    have x_val : x = -1 := by
      rw [y_val] at eq3
      linarith
    constructor
    · -- x = -1 
      exact x_val
    · -- y = 1 / 2 
      exact y_val