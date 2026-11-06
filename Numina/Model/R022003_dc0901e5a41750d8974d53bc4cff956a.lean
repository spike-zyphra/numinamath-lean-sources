import Mathlib

theorem algebra_11458 (x : ℝ) (hx : x ≠ 0) : (1/5 + 5/x) = (12/x + 1/12) ↔ x = 60 := by
  constructor
  · -- Assume (1/5 + 5/x) = (12/x + 1/12), prove x = 60
    intro h
    have eq1 : 1/5 + 5/x = 12/x + 1/12 := by
      simpa using h
    have eq2 : (1 / 5 + 5 / x) - (12 / x + 1 / 12) = 0 := by linarith
    have eq3 : (1 / 5 - 1 / 12 : ℝ) - (7 / x) = 0 := by
      have eq4 : (1 / 5 + 5 / x) - (12 / x + 1 / 12 : ℝ) = (1 / 5 - 1 / 12 : ℝ) - 7 / x := by
        field_simp [hx]
        ring
      linarith [eq4, eq2]
    have eq4 : (1 / 5 - 1 / 12 : ℝ) = 7 / 60 := by norm_num
    rw [eq4] at eq3
    have eq5 : x ≠ 0 := hx
    have eq6 : 7 * x = 420 := by 
      field_simp [eq5] at eq3 
      linarith
    linarith 
  · -- Assume x = 60, prove (1/5 + 5/x) = (12/x + 1/12)
    intro h_eq 
    rw [h_eq] 
    norm_num