import Mathlib

theorem algebra_97733 {R : ℝ} (hR : R > 0) (h : R = (1 - R) / R) :
    R ^ (R ^ (R ^ 2 + 1 / R) + 1 / R) + 1 / R = 2 := by
  have h1 : R ≠ 0 := by nlinarith 
  have eq1 : R * R = 1 - R := by
    field_simp [h1] at h
    nlinarith
  have eq2 : R ^ 2 = 1 - R := by
    nlinarith
  have eq3 : 1 / R = 1 + R := by 
    field_simp [h1]
    nlinarith [eq2]
  have eq4 : R ^ 2 + 1 / R = 2 := by
    rw [eq3]
    nlinarith [eq2]
  -- Show that R^(R^2 + 1/R) = R^2
  have eq5 : R ^ (R ^ 2 + 1 / R) = R ^ 2 := by 
    rw [eq4]
    all_goals norm_num
    all_goals nlinarith
  -- Show that R^(R^(R^2 + 1/R) + 1/R) = R^2
  have eq6 : R ^ (R ^ (R ^ 2 + 1 / R) + 1 / R) = R ^ 2 := by 
    have h_eq1 : R ^ (R ^ 2 + 1 / R) = R ^ 2 := eq5
    have h_eq2 : R ^ (R ^ 2 + 1 / R) + 1 / R = 2 := by
      rw [h_eq1]
      rw [eq3]
      nlinarith [eq2]
    rw [h_eq2]
    all_goals norm_num
    all_goals nlinarith
  -- Compute the final result
  calc
    R ^ (R ^ (R ^ 2 + 1 / R) + 1 / R) + 1 / R = R ^ 2 + 1 / R := by rw [eq6]
    _ = 2 := eq4