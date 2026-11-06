import Mathlib

theorem algebra_228285 {x1 x2 m : ℝ} (h : x1^2 + x2^2 = (x1 + x2)^2 - 2 * x1 * x2)
    (h1 : x1 + x2 = -(m + 1)) (h2 : x1 * x2 = 2 * m - 2) (h3 : (m + 3)^2 ≥ 0) :
    x1^2 + x2^2 = (m - 1)^2 + 4 := by
  have eq3 : x1^2 + x2^2 = m^2 - 2*m + 5 := by
    have h4 : x1^2 + x2^2 = (x1 + x2) ^ 2 - 2 * (x1 * x2) := by
      linarith
    rw [h4]
    rw [h1, h2]
    nlinarith

  have eq4 : m ^ 2 - 2 * m + 5 = (m - 1) ^ 2 + 4 := by
    ring

  rw [eq3]
  exact eq4