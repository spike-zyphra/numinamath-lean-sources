import Mathlib

theorem algebra_14147 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h1 : a^2 / b = 1) (h2 : b^2 / c = 2) (h3 : c^2 / a = 3) :
  a = 12 ^ ((1 : ℝ) / 7) := by
  have eq1 : a^2 = b := by 
    have pos1 : 0 < b := hb
    field_simp at h1
    nlinarith
  have eq2 : b^2 = 2 * c := by
    have pos1 : 0 < c := hc
    field_simp at h2
    nlinarith
  have eq3 : c^2 = 3 * a := by
    have pos1 : 0 < a := ha
    field_simp at h3
    nlinarith
  have eq4 : c = a^4 / 2 := by 
    -- substitute b = a^2 from eq1 into eq2
    have h5 : b = a^2 := by linarith [eq1]
    rw [h5] at eq2
    nlinarith
  -- substitute c = a^4 / 2 into eq3
  have eq5 : (a^4 / 2) ^ 2 = 3 * a := by 
    rw [eq4] at eq3
    nlinarith
  have eq6 : a ^ 7 = 12 := by
    nlinarith [sq_nonneg (a ^ 4 - 2 * a ^ 0), sq_nonneg (a ^ 3 - 6), sq_nonneg (a ^ 2 - 2 ^ 2), sq_nonneg (a - (a ^ 3 / a ^ 0)), sq_nonneg (a ^ 2 - (a ^ 4 / a ^ 2)), sq_nonneg (a ^ 2 - 2 ^ 2), sq_nonneg (a ^ 3 - (a ^ 4 / a ^ 0)), sq_pos_of_pos ha]
  -- convert a^7 = 12 to a = 12^(1/7)
  have eq7 : a = (12 : ℝ) ^ ((1 : ℝ) / 7) := by 
    have h8 : a ^ (7 : ℝ) = (12 : ℝ) := by 
      exact_mod_cast eq6
    have h9 : a = (a ^ (7 : ℝ)) ^ ((1 : ℝ) / 7) := by 
      rw [← Real.rpow_mul]
      field_simp
      all_goals linarith
    rw [h8] at h9
    all_goals try linarith [h9]
  exact_mod_cast eq7