import Mathlib

theorem algebra_169122 {x y : ℝ} (hx : x = 2 * y) (hy : 0 < y) (hxy : x > 0) :
    (x * 0.9 + y * 0.81) / (x + y) = 0.87 := by

  have h1 : x + y = 3 * y := by
    rw [hx]
    linarith

  have h2 : x * 0.9 + y * 0.81 = 2.61 * y := by
    rw [hx]
    ring

  have h3 : y ≠ 0 := by linarith

  have h4 : (x * 0.9 + y * 0.81) / (x + y) = (2.61 * y) / (3 * y) := by
    rw [h2, h1]

  have h5 : (2.61 * y) / (3 * y) = (2.61 / (3 : ℝ)) := by
    have h6 : y ≠ 0 := by linarith
    field_simp
    <;> ring

  have h6 : (2.61 / (3 : ℝ)) = (0.87 : ℝ) := by norm_num

  rw [h4, h5, h6]
  all_goals norm_num