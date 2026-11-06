import Mathlib

theorem algebra_93422 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a * b = a - b) :
    a / b + b / a - a * b = 2 := by 
  have h1 : a * b = a - b := h
  have h2 : a * (1 - b) = b := by 
    nlinarith
  have h3 : 1 - b ≠ 0 := by
    by_contra h4
    have h5 : b = 1 := by linarith
    rw [h5] at h
    nlinarith
  have eq1 : a / b = (1) / (1 - b) := by 
    have h4 : a = b / (1 - b) := by
      have : 1 - b ≠ 0 := h3
      field_simp at h2 ⊢
      <;> nlinarith
    rw [h4]
    field_simp [(show 1 - b ≠ 0 by exact h3), hb]
    <;> nlinarith 
  have eq2 : b / a = 1 - b := by 
    have h4 : a = b / (1 - b) := by
      have : 1 - b ≠ 0 := h3
      field_simp at h2 ⊢
      <;> nlinarith
    rw [h4]
    field_simp [(show 1 - b ≠ 0 by exact h3), hb]
    <;> nlinarith 
  have eq3 : a * b = b ^ 2 / (1 - b) := by 
    have h4 : a = b / (1 - b) := by
      have : 1 - b ≠ 0 := h3
      field_simp at h2 ⊢
      <;> nlinarith
    rw [h4]
    field_simp [(show 1 - b ≠ 0 by exact h3)]
    <;> nlinarith 
  rw [eq1, eq2, eq3]
  field_simp [(show 1 - b ≠ 0 by exact h3), hb]
  <;> nlinarith [sq_nonneg (b - 1)]