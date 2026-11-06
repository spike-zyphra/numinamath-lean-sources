import Mathlib

theorem algebra_261949 {x y : ℝ} (h : x + y = x * y) (hx : x = 987654321) :
    y = 1 + 1 / 987654320 := by
  rw [hx] at h
  have h1 : (987654321 : ℝ) + y = (987654321 : ℝ) * y := by
    linarith
  have h2 : y = (987654321 : ℝ) / (987654320 : ℝ) := by
    have h3 : (987654321 : ℝ) + y = (987654321 : ℝ) * y := h1
    have h4 : (987654321 - (1 : ℝ)) * y = 987654321 := by
      linarith
    have hx1 : (987654321 - (1 : ℝ)) ≠ 0 := by
      norm_num
    have h5 : y = (987654321 : ℝ) / (987654321 - (1 : ℝ)) := by
      field_simp [hx1]
      linarith
    rw [h5]
    have hx2 : (987654321 - (1 : ℝ)) = (987654320 : ℝ) := by
      norm_num
    rw [hx2]
  rw [h2]
  norm_num
  <;> field_simp <;> norm_num