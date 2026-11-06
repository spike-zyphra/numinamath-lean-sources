import Mathlib

theorem algebra_199579 {x : ℝ} (hx : x ≠ 0) (h : x - 1/x = Real.sqrt 2007) :
    x^4 + 1/x^4 = 4036079 := by
  have h1 : x ^ 2 + 1 / x ^ 2 = 2009 := by
    have eq1 : x ^ 2 + 1 / x ^ 2 = (x - 1 / x) ^ 2 + 2 := by
      field_simp
      <;> ring
    rw [eq1, h]
    have h2 : (Real.sqrt 2007 : ℝ) ^ 2 = 2007 := Real.sq_sqrt (by norm_num)
    rw [h2]
    all_goals norm_num
  have h3 : x ^ 4 + 1 / x ^ 4 = (x ^ 2 + 1 / x ^ 2) ^ 2 - 2 := by
    field_simp
    <;> ring
  rw [h3, h1]
  all_goals norm_num