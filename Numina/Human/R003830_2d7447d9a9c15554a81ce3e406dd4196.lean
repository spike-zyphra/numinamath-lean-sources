import Mathlib

theorem algebra_215003 {a : ℝ} (ha : a ≠ 0) (h : a / 3 - 3 / a = 4) :
    (a^8 - 6561) / (81 * a^4) * (3 * a / (a^2 + 9)) = 72 := by
  calc 
    _ = (a ^ 4 / 81 - 81 / (a ^ 4)) * (3 * a / (a^2 + 9)) := by 
      field_simp
      ring
    _ = (a^2 / 9 + 9/ a^2) * (a^2 / 9 - 9/ a^2 ) * (3 * a / (a^2 + 9)) := by 
      field_simp
      ring
    _ = (a^2 / 9 - 2+ 9/ a^2 + 2) * (a / 3 - 3 / a) *(a / 3 + 3/ a)* (3 * a / (a^2 + 9)) := by 
      field_simp
      ring
    _ = ((a / 3 - 3 / a)^ 2 + 2) * (a / 3 - 3 / a) := by 
      field_simp
      ring
    _ = (4 ^ 2 + 2) * 4 := by rw [h]
    _ = 72 := by norm_num