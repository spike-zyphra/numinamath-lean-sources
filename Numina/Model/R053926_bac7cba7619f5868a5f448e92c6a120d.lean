import Mathlib

theorem algebra_897 {x : ℝ} (hx : x ≠ 0) (h : x + 1/x = 3) :
    (x^3 + 1/x^3 + 7)/(x^4 + 1/x^4 + 3) = 1/2 := by
  have h1 : x^2 + 1/x^2 = 7 := by
    have h2 : x^2 + 1/x^2 = (x + 1/x)^2 - 2 := by
      field_simp
      ring
    rw [h2, h]
    all_goals norm_num
  have h2 : x^3 + 1/x^3 = 18 := by
    have h3 : x^3 + 1/x^3 = (x + 1/x)^3 - 3 * (x + 1/x) := by
      field_simp
      ring
    rw [h3, h]
    all_goals norm_num
  have h3 : x^4 + 1/x^4 = 47 := by
    have h4 : x^4 + 1/x^4 = (x^2 + 1/x^2)^2 - 2 := by
      field_simp
      ring
    rw [h4, h1]
    all_goals norm_num
  have hn : x^3 + 1/x^3 + 7 = 25 := by
    linarith [h2]
  have hd : x^4 + 1/x^4 + 3 = 50 := by
    linarith [h3]
  rw [hn, hd]
  all_goals norm_num