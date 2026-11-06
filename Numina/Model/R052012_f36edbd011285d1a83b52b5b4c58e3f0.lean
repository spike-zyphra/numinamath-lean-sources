import Mathlib

theorem algebra_5868 {x y : ℝ} (hx : 0 ≤ x) (h1 : Real.sqrt x + 2 * y ^ 2 = 15) (h2 : 2 * Real.sqrt x - 4 * y ^ 2 = 6) :
    x = 81 := by
  have eq1 : 2 * y ^ 2 = 15 - Real.sqrt x := by 
    linarith
  have eq2 : y ^ 2 = (15 - Real.sqrt x) / 2 := by
    linarith [eq1]
  have eq3 : 2 * Real.sqrt x - 4 * ( (15 - Real.sqrt x) / 2 ) = 6 := by 
    rw [eq2] at h2
    linarith
  have eq4 : 4 * Real.sqrt x = 36 := by
    nlinarith
  have eq5 : Real.sqrt x = 9 := by
    nlinarith
  have hx_eq : x = 81 := by
    have h3 : Real.sqrt x = 9 := eq5
    have h4 : x = (Real.sqrt x) ^ 2 := by
      rw [Real.sq_sqrt]
      linarith [show 0 ≤ x by linarith]
    rw [h3] at h4
    nlinarith
  exact hx_eq