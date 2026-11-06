import Mathlib

theorem algebra_255567 {a : ℝ} (ha : a ≠ 0) (h : a + 1 / a = 1) : a ^ 5 + 1 / a ^ 5 = 1 := by
  have h1 : a ^ 2 + 1 = a := by
    field_simp [ha] at h
    nlinarith
  have h2 : a ^ 2 + 1 / a ^ 2 = -1 := by 
    calc
      a ^ 2 + 1 / a ^ 2 = (a + 1 / a) ^ 2 - 2 := by 
        field_simp [ha]
        nlinarith
      _ = 1 ^ 2 - 2 := by rw [h]
      _ = -1 := by norm_num
  have h3 : a ^ 3 + 1 / a ^ 3 = -2 := by
    calc
      a ^ 3 + 1 / a ^ 3 = (a + 1 / a) * (a ^ 2 + 1 / a ^ 2) - (a + 1 / a) := by 
        field_simp [ha]
        nlinarith
      _ = 1 * (-1) - (1) := by rw [h, h2]
      _ = -2 := by norm_num
  have h4 : a ^ 4 + 1 / a ^ 4 = -1 := by
    calc
      a ^ 4 + 1 / a ^ 4 = (a ^ 2 + 1 / a ^ 2) ^ 2 - 2 := by
        field_simp [ha]
        nlinarith
      _ = (-1) ^ 2 - 2 := by rw [h2]
      _ = -1 := by norm_num
  calc
    a ^ 5 + 1 / a ^ 5 = (a + 1 / a) * (a ^ 4 + 1 / a ^ 4) - (a ^ 3 + 1 / a ^ 3) := by 
      field_simp [ha]
      nlinarith
    _ = 1 * (-1) - (-2) := by rw [h, h4, h3]
    _ = 1 := by norm_num