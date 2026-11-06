import Mathlib

theorem algebra_94010 {x y z : ℝ} (hz : z ≠ 0) (h1 : 2*x-3*y-z=0) (h2 : x+3*y-14*z=0) :
    (x^2+3*x*y)/(y^2+z^2) = 7 := by
  have eq3 : y = 3 * z := by
    have h3 : 9 * y = 27 * z := by
      nlinarith
    linarith
  have eq1 : x = 5 * z := by
    rw [eq3] at h1
    nlinarith
  have num_eq : x^2 + 3 * x * y = 70 * z^2 := by
    rw [eq1, eq3]
    nlinarith
  have den_eq : y^2 + z^2 = 10 * z^2 := by
    rw [eq3]
    nlinarith
  have h4 : z^2 ≠ 0 := by
    exact pow_ne_zero 2 hz
  rw [num_eq, den_eq]
  field_simp [h4]
  <;> nlinarith