import Mathlib

open Real

theorem algebra_222376 {x : ℝ} (hx : 0 < x ∧ x ≠ 1) :
    1 / logb 3 x + 1 / logb 4 x + 1 / logb 5 x = 1 / logb 60 x := by
  have h1 : 0 < x := hx.1
  have h2 : x ≠ 1 := hx.2
  have eq1 : 1 / logb 3 x = (log 3) / log x := by
    have h3 : logb 3 x = log x / log 3 := by
      field_simp [logb]
    rw [h3]
    field_simp
    all_goals linarith
  have eq2 : 1 / logb 4 x = (log 4) / log x := by
    have h4 : logb 4 x = log x / log 4 := by
      field_simp [logb]
    rw [h4]
    field_simp
    all_goals linarith
  have eq3 : 1 / logb 5 x = (log 5) / log x := by
    have h5 : logb 5 x = log x / log 5 := by
      field_simp [logb]
    rw [h5]
    field_simp
    all_goals linarith
  have eq4 : 1 / logb 60 x = log 60 / log x := by
    have h6 : logb 60 x = log x / log 60 := by
      field_simp [logb]
    rw [h6]
    field_simp
    all_goals linarith
  have h7 : log 60 = log 3 + log 4 + log 5 := by
    rw [show (60 : ℝ) = 3 * 4 * 5 by norm_num]
    simp [log_mul, mul_pos, mul_pos]
    all_goals linarith
  rw [eq1, eq2, eq3, eq4]
  have h8 : log 3 + log 4 + log 5 = log 60 := by
    linarith [h7]
  field_simp [(show log x ≠ 0 from by
    by_contra h
    have : x = 1 := by
      have h' : log x = 0 := by linarith
      rw [log_eq_zero] at h'
      rcases h' with (r | r | r)
      · linarith
      · linarith
      · linarith
    contradiction)]
  <;> nlinarith [h8]