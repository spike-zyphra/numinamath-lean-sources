import Mathlib

theorem algebra_128337 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (hxy : x / y = 21 / 16) (hxy' : (x - 18) / (y - 18) = 15 / 11) :
    x - 18 = 150 := by
  have h3 : y ≠ 0 := by
    by_contra h
    rw [h] at hxy
    norm_num at hxy
    all_goals linarith
  have h4 : y - 18 ≠ 0 := by
    by_contra h
    have h5 : y = 18 := by linarith
    rw [h5] at hxy'
    norm_num at hxy'
    all_goals linarith
  have eq1 : 16 * x = 21 * y := by
    have h6 : y ≠ 0 := h3
    field_simp [h6] at hxy ⊢
    linarith
  have eq2 : 11 * (x - 18) = 15 * (y - 18) := by
    have h7 : y - 18 ≠ 0 := h4
    field_simp [h7] at hxy' ⊢
    linarith
  linarith [eq1, eq2]