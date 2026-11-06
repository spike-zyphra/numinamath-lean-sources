import Mathlib

theorem algebra_2391 {m n t s : ℝ} (hm : 0 < m) (hn : 0 < n) (hmn : m / n = t) (hsum : m + n = s) (ht : 1 < t) : min m n = s / (1 + t) := by
  have h5 : m = n * t := by 
    have h6 : n ≠ 0 := by linarith 
    field_simp [h6] at hmn 
    linarith 
  have h7 : n = s / (1 + t) := by
    have eq1 : n * (t + 1) = s := by 
      have hsub : m + n = s := hsum 
      rw [h5] at hsub 
      linarith 
    have eq2 : n = s / (t + 1) := by 
      have h8 : t + 1 ≠ 0 := by linarith 
      field_simp [h8] at eq1 ⊢ 
      linarith 
    have eq3 : t + 1 = 1 + t := by ring 
    rw [eq3] at eq2 
    exact eq2 
  have h8 : n < m := by 
    rw [h5] 
    have h10 : 1 < t := ht 
    nlinarith 
  have h9 : min m n = n := by 
    apply min_eq_right 
    linarith 
  rw [h9] 
  rw [h7] 
  all_goals linarith