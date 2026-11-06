import Mathlib

theorem algebra_205408 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h : x * 24 = y * 27) :
    (x - y) / y * 100 = 12.5 := by
  have h1 : x = 27 / 24 * y := by
    linarith
  have h2 : x = 9 / 8 * y := by
    rw [h1]
    norm_num
    <;> linarith
  have h3 : x - y = 1 / 8 * y := by
    rw [h2]
    linarith
  calc
    (x - y) / y * 100 = (1 / 8 * y) / y * 100 := by rw [h3]
    _ = (1 / 8) * 100 := by
      field_simp [hy]
      <;> linarith
    _ = 12.5 := by norm_num