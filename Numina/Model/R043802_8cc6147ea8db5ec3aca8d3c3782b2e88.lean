import Mathlib

open Real

theorem algebra_236107 {x : ℝ} (hx : x = sqrt (86 + 41 * x)) : x = 43 := by
  have h1 : x ≥ 0 := by
    have h2 : x = sqrt (86 + 41 * x) := hx
    have h4 : sqrt (86 + 41 * x) ≥ 0 := Real.sqrt_nonneg (86 + 41 * x)
    linarith [h2, h4]

  have h_eq : x ^ 2 = 86 + 41 * x := by
    have h2 : x = sqrt (86 + 41 * x) := hx
    have h5 : x ^ 2 = (sqrt (86 + 41 * x)) ^ 2 := by
      rw [show sqrt (86 + 41 * x) = x by linarith [h2]]
    have h6 : (sqrt (86 + 41 * x)) ^ 2 = 86 + 41 * x := by
      apply Real.sq_sqrt 
      nlinarith [show 0 ≤ x by linarith, hx]
    linarith [h5, h6]

  have h_eq2 : x ^ 2 - 41 * x - 86 = 0 := by
    nlinarith [h_eq]

  have h_eq3 : (x - 43) * (x + 2) = 0 := by
    nlinarith [h_eq2]

  cases' (mul_eq_zero.mp h_eq3) with h_eq4 h_eq5
  · -- Case x - 43 = 0, so x = 43
    linarith
  · -- Case x + 2 = 0, so x = -2
    nlinarith [h1, sq_nonneg (x + 2)]