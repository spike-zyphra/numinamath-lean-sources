import Mathlib

theorem algebra_200679 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : (x + z) / (2 * z - x) = (z + 2 * y) / (2 * x - z)) (h' : (z + 2 * y) / (2 * x - z) = x / y) :
    x / y = 2 := by

  have h2 : 2 * z - x ≠ 0 := by
    by_contra h2
    have : x = 2 * z := by linarith
    rw [this] at h
    field_simp [(show 2 * z - (2 * z) = (0 : ℝ) by linarith), (show 2 * (2 * z) - z = (3 * z : ℝ) by linarith)] at h
    <;> nlinarith

  have h3 : 2 * x - z ≠ 0 := by
    by_contra h3
    have : z = 2 * x := by linarith
    rw [this] at h
    field_simp [(show 2 * (2 * x) - x = (3 * x : ℝ) by linarith), (show 2 * x - x = (x : ℝ) by linarith)] at h
    <;> nlinarith

  have h4 : y ≠ 0 := by linarith

  have eq1 : (x + z) * (2 * x - z) = (z + 2 * y) * (2 * z - x) := by
    have h2' : 2 * z - x ≠ 0 := h2
    have h3' : 2 * x - z ≠ 0 := h3
    field_simp [h2', h3'] at h ⊢
    linarith

  have eq2 : y * (z + 2 * y) = x * (2 * x - z) := by 
    have h3' : 2 * x - z ≠ 0 := h3
    have h4' : y ≠ 0 := h4
    field_simp [h3', h4'] at h' ⊢
    linarith

  have eq3 : x = 2 * y := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, sq_nonneg (x - 2 * y), sq_nonneg (z - 2 * y), sq_nonneg (x - z)]

  have h5 : x / y = 2 := by
    have h6 : y ≠ 0 := h4
    field_simp [h6]
    linarith

  exact h5