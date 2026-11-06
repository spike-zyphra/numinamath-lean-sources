import Mathlib

theorem algebra_185077 {z : ℝ} (hz : z = (Real.sqrt 3 - 1)/2) :
    ((z - 1)*(z + 2)*(z - 3)*(z + 4))/23 = 3/4 := by
  rw [hz]
  have eq1 : ((Real.sqrt 3 - 1)/2 - 1) * ((Real.sqrt 3 - 1)/2 + 2) = ((Real.sqrt 3 - 1)/2)^2 + (Real.sqrt 3 - 1)/2 - 2 := by ring
  have eq2 : ((Real.sqrt 3 - 1)/2 - 3) * ((Real.sqrt 3 - 1)/2 + 4) = ((Real.sqrt 3 - 1)/2)^2 + (Real.sqrt 3 - 1)/2 - 12 := by ring
  have h_eq3 : (((Real.sqrt 3 - 1)/2 - 1) * ((Real.sqrt 3 - 1)/2 + 2)) * (((Real.sqrt 3 - 1)/2 - 3) * ((Real.sqrt 3 - 1)/2 + 4)) =
      (((Real.sqrt 3 - 1)/2)^2 + (Real.sqrt 3 - 1)/2 - 2) * (((Real.sqrt 3 - 1)/2)^2 + (Real.sqrt 3 - 1)/2 - 12) := by
    rw [eq1, eq2]
  have eq3 : ((Real.sqrt 3 - 1)/2 - 1) * ((Real.sqrt 3 - 1)/2 + 2) * ((Real.sqrt 3 - 1)/2 - 3) * ((Real.sqrt 3 - 1)/2 + 4) =
      (((Real.sqrt 3 - 1)/2)^2 + (Real.sqrt 3 - 1)/2 - 2) * (((Real.sqrt 3 - 1)/2)^2 + (Real.sqrt 3 - 1)/2 - 12) := by
    calc ((Real.sqrt 3 - 1)/2 - 1) * ((Real.sqrt 3 - 1)/2 + 2) * ((Real.sqrt 3 - 1)/2 - 3) * ((Real.sqrt 3 - 1)/2 + 4)
        = (((Real.sqrt 3 - 1)/2 - 1) * ((Real.sqrt 3 - 1)/2 + 2)) * (((Real.sqrt 3 - 1)/2 - 3) * ((Real.sqrt 3 - 1)/2 + 4)) := by ring
    _ = (((Real.sqrt 3 - 1)/2)^2 + (Real.sqrt 3 - 1)/2 - 2) * (((Real.sqrt 3 - 1)/2)^2 + (Real.sqrt 3 - 1)/2 - 12) := by rw [h_eq3]
  have eq4 : ((Real.sqrt 3 - 1)/2)^2 + (Real.sqrt 3 - 1)/2 = 1/2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have eq5 : ((Real.sqrt 3 - 1)/2)^2 + (Real.sqrt 3 - 1)/2 - 2 = -3/2 := by
    nlinarith [eq4]
  have eq6 : ((Real.sqrt 3 - 1)/2)^2 + (Real.sqrt 3 - 1)/2 - 12 = -23/2 := by
    nlinarith [eq4]
  have eq7 : (((Real.sqrt 3 - 1)/2)^2 + (Real.sqrt 3 - 1)/2 - 2) * (((Real.sqrt 3 - 1)/2)^2 + (Real.sqrt 3 - 1)/2 - 12) = 69/4 := by
    rw [eq5, eq6]
    norm_num
  rw [eq3]
  rw [eq7]
  norm_num