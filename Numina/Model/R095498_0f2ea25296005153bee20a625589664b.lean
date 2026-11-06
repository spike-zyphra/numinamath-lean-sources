import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_230034 {a b c : ℝ} (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
  (h1 : logb 10 a + logb b c = 3) (h2 : logb 10 b + logb a c = 4) :
  logb 10 a * logb 10 c ≤ 16 / 3 := by
  have h1' : logb 10 a + logb b c = 3 := h1
  have h2' : logb 10 b + logb a c = 4 := h2
  have h3 : logb b c = logb 10 c / logb 10 b := by 
    field_simp [logb]
    all_goals linarith
  have h4 : logb a c = logb 10 c / logb 10 a := by 
    field_simp [logb]
    all_goals linarith
  rw [h3] at h1'
  rw [h4] at h2'
  have eq3 : logb 10 a * logb 10 b + logb 10 c = 3 * logb 10 b := by
    have h5 : logb 10 b ≠ 0 := by 
      apply ne_of_gt
      apply logb_pos 
      all_goals linarith
    field_simp [h5] at h1' ⊢
    linarith
  have eq4 : logb 10 b * logb 10 a + logb 10 c = 4 * logb 10 a := by
    have h6 : logb 10 a ≠ 0 := by 
      apply ne_of_gt
      apply logb_pos 
      all_goals linarith
    field_simp [h6] at h2' ⊢
    linarith
  have eq6 : 3 * logb 10 b = 4 * logb 10 a := by
    nlinarith 
  have eq7 : logb 10 b = 4 / 3 * logb 10 a := by 
    nlinarith 
  have eq8 : logb 10 c = 4 * logb 10 a - 4 / 3 * (logb 10 a)^2 := by
    have h6 : logb 10 c = 3 * logb 10 b - logb 10 a * logb 10 b := by 
      nlinarith 
    rw [eq7] at h6 
    nlinarith 
  have eq9 : logb 10 a * logb 10 c = logb 10 a * (4 * logb 10 a - 4 / 3 * (logb 10 a)^2) := by
    rw [eq8]
  have h12 : logb 10 a > 0 := by
    apply logb_pos 
    all_goals linarith
  nlinarith [sq_nonneg (logb 10 a - 2)]