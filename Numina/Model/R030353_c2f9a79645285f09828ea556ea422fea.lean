import Mathlib

theorem algebra_228810 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : 1 / a + 2 / b + 3 / c = 1) (h2 : a / 1 + b / 2 + c / 3 = 0) :
    1 / a^2 + 4 / b^2 + 9 / c^2 = 1 := by 
  have eq2 : 6 * a + 3 * b + 2 * c = 0 := by
    have eq3 : a + b / 2 + c / 3 = 0 := by 
      simpa using h2
    linarith [eq3]

  have eq4 : 1 / a^2 + 4 / b^2 + 9 / c^2 = (1 / a + 2 / b + 3 / c) ^ 2 - 2 * (2 / (a * b) + 3 / (a * c) + 6 / (b * c)) := by 
    field_simp
    ring

  have eq5 : 2 / (a * b) + 3 / (a * c) + 6 / (b * c) = 0 := by
    have eq5 : 2 * c + 3 * b + 6 * a = 0 := by 
      linarith [eq2]
    have eq6 : 2 / (a * b) + 3 / (a * c) + 6 / (b * c) = (2 * c + 3 * b + 6 * a) / (a * b * c) := by
      field_simp
      ring
    rw [eq6, eq5]
    norm_num
  rw [eq4]
  rw [h1, eq5]
  all_goals norm_num