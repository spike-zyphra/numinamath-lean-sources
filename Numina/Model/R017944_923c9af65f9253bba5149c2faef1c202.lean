import Mathlib

theorem algebra_166180 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : 1 / x + 1 / y + 1 / z = 3) (h2 : 1 / (x * y) + 1 / (y * z) + 1 / (z * x) = 3)
    (h3 : 1 / (x * y * z) = 1) :
    x = 1 ∧ y = 1 ∧ z = 1 := by

  have eq1 : x * y * z = 1 := by
    have h4 : x * y * z ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact hx
      exact hy
      exact hz
    field_simp at h3
    nlinarith

  have eq2 : y * z + x * z + x * y = 3 := by
    have h4 : x * y * z ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact hx
      exact hy
      exact hz
    have eq1' : x * y * z = 1 := eq1
    have h5 : (1 / x + 1 / y + 1 / z) * (x * y * z) = 3 * (x * y * z) := by
      rw [h1]
      all_goals nlinarith
    have h7 : (1 / x + 1 / y + 1 / z) * (x * y * z) = y * z + x * z + x * y := by
      field_simp [hx, hy, hz]
      <;> ring
    rw [h7] at h5
    rw [eq1'] at h5
    linarith

  have eq3 : x + y + z = 3 := by
    have h4 : x * y * z ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact hx
      exact hy
      exact hz
    have eq1' : x * y * z = 1 := eq1
    have h2' : 1 / (x * y) + 1 / (y * z) + 1 / (z * x) = 3 := h2
    have h5 : (1 / (x * y) + 1 / (y * z) + 1 / (z * x)) * (x * y * z) = 3 * (x * y * z) := by 
      rw [h2']
      all_goals nlinarith
    have h8 : (1 / (x * y) + 1 / (y * z) + 1 / (z * x)) * (x * y * z) = x + y + z := by
      field_simp [hx, hy, hz]
      <;> ring
    rw [h8] at h5
    rw [eq1'] at h5
    linarith

  have h4 : (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1)]

  have hx1 : x - 1 = 0 := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), h4]

  have hy1 : y - 1 = 0 := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), h4]

  have hz1 : z - 1 = 0 := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), h4]

  have hx2 : x = 1 := by linarith
  have hy2 : y = 1 := by linarith
  have hz2 : z = 1 := by linarith
  exact ⟨hx2, hy2, hz2⟩