import Mathlib

theorem algebra_262700 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : b / a - a / b = 1) :
    (b ^ 2 / a ^ 2 - a ^ 2 / b ^ 2) ^ 2 = 5 := by
  have eq1 : b ^ 2 / a ^ 2 - a ^ 2 / b ^ 2 = (b / a - a / b) * (b / a + a / b) := by
    field_simp [ha, hb]
    <;> ring
  have eq2 : (b / a + a / b) ^ 2 = 5 := by
    have h1 : (b / a - a / b) ^ 2 = 1 := by
      rw [h]
      norm_num
    have h2 : (b / a + a / b) ^ 2 = (b / a - a / b) ^ 2 + 4 := by
      field_simp [ha, hb]
      <;> ring
    rw [h1] at h2
    linarith
  have eq3 : (b ^ 2 / a ^ 2 - a ^ 2 / b ^ 2) = (b / a + a / b) := by
    rw [eq1]
    rw [h]
    <;> ring
  calc
    (b ^ 2 / a ^ 2 - a ^ 2 / b ^ 2) ^ 2 = (b / a + a / b) ^ 2 := by rw [eq3]
    _ = 5 := eq2