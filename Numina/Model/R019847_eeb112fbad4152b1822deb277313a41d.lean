import Mathlib

theorem algebra_4039 {x y z : ℝ} (h : ((x + y) ^ 2 + (y + z) ^ 2 + (x + z) ^ 2) / ((x + y) * (y + z) + (y + z) * (x + z) + (x + y) * (x + z)) = 38 / 31) :
    (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + x * z) = 13 / 6 := by

  have hx1 : (x + y) * (y + z) + (y + z) * (x + z) + (x + y) * (x + z) ≠ 0 := by 
    by_contra h1
    have eq1 : ((x + y) ^ 2 + (y + z) ^ 2 + (x + z) ^ 2) / ((x + y) * (y + z) + (y + z) * (x + z) + (x + y) * (x + z)) = 0 := by
      rw [h1]
      norm_num
    rw [show ((x + y) ^ 2 + (y + z) ^ 2 + (x + z) ^ 2) / ((x + y) * (y + z) + (y + z) * (x + z) + (x + y) * (x + z)) = 38 / 31 by linarith [h]] at eq1
    linarith
  have hx2 : (x * y + y * z + x * z) ≠ 0 := by 
    by_contra h2
    have hx4 : (x * y + y * z + x * z) = 0 := by 
      linarith [h2]
    have hx5 : (x + y) * (y + z) + (y + z) * (x + z) + (x + y) * (x + z) = (x^2 + y^2 + z^2) + 3 * (x * y + y * z + x * z) := by 
      ring
    have hx6 : (x + y) ^ 2 + (y + z) ^ 2 + (x + z) ^ 2 = 2 * (x^2 + y^2 + z^2) + 2 * (x * y + y * z + x * z) := by 
      ring_nf
      <;> nlinarith
      <;> ring
    have hx7 : (x + y) * (y + z) + (y + z) * (x + z) + (x + y) * (x + z) = (x^2 + y^2 + z^2) := by
      rw [hx5]
      rw [hx4]
      all_goals norm_num 
      <;> nlinarith
    have hx8 : (x + y) ^ 2 + (y + z) ^ 2 + (x + z) ^ 2 = 2 * (x^2 + y^2 + z^2) := by 
      rw [hx6]
      rw [hx4]
      all_goals norm_num 
      <;> nlinarith
    have eq1 : ((x + y) ^ 2 + (y + z) ^ 2 + (x + z) ^ 2) / ((x + y) * (y + z) + (y + z) * (x + z) + (x + y) * (x + z)) = 2 := by
      rw [hx8, hx7]
      have hx9 : x^2 + y^2 + z^2 ≠ 0 := by 
        by_contra h9
        have hx10 : (x + y) * (y + z) + (y + z) * (x + z) + (x + y) * (x + z) = 0 := by
          nlinarith [h9, hx4]
        tauto 
      field_simp [hx9]
      <;> ring_nf <;> field_simp [hx9] <;> nlinarith
      all_goals linarith [hx4]
    have eq2 : ((x + y) ^ 2 + (y + z) ^ 2 + (x + z) ^ 2) / ((x + y) * (y + z) + (y + z) * (x + z) + (x + y) * (x + z)) = 38 / 31 := h
    rw [eq1] at eq2
    nlinarith 
  have hx3 : 31 * ((x + y) ^ 2 + (y + z) ^ 2 + (x + z) ^ 2) = 38 * ((x + y) * (y + z) + (y + z) * (x + z) + (x + y) * (x + z)) := by 
    have hx1' : (x + y) * (y + z) + (y + z) * (x + z) + (x + y) * (x + z) ≠ 0 := hx1
    field_simp at h ⊢
    nlinarith 
  have hx4 : 6 * (x ^ 2 + y ^ 2 + z ^ 2) = 13 * (x * y + y * z + x * z) := by 
    have hx5 : (x + y) * (y + z) + (y + z) * (x + z) + (x + y) * (x + z) = (x^2 + y^2 + z^2) + 3 * (x * y + y * z + x * z) := by 
      ring 
    have hx6 : (x + y) ^ 2 + (y + z) ^ 2 + (x + z) ^ 2 = 2 * (x^2 + y^2 + z^2) + 2 * (x * y + y * z + x * z) := by 
      ring_nf 
      <;> nlinarith
    rw [hx5] at hx3 
    rw [hx6] at hx3 
    linarith 
    all_goals linarith [hx4] 
  have hx5 : (x * y + y * z + x * z) ≠ 0 := hx2
  field_simp at *
  <;> nlinarith [hx4]
  all_goals linarith 
  all_goals nlinarith