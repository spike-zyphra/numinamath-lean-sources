import Mathlib

theorem algebra_157336 {r : ℚ} (hr : r ≠ 0) (h : (r + 1 / r) ^ 2 = 3) :
    r ^ 3 + 1 / r ^ 3 = 0 := by
  have h1 : r ^ 2 + 1 / r ^ 2 = 1 := by
    have eq1 : (r + 1 / r) ^ 2 = r ^ 2 + 2 + 1 / r ^ 2 := by
      field_simp
      <;> ring
    rw [eq1] at h
    linarith
  have h2 : r ^ 3 + 1 / r ^ 3 = (r + 1 / r) * (r ^ 2 + 1 / r ^ 2 - 1) := by
    field_simp
    <;> ring
  rw [h2, h1]
  <;> norm_num
  all_goals
    linarith