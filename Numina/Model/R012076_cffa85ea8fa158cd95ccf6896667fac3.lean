import Mathlib

theorem algebra_199491 {a x y z : ℝ} (hpos : a > 0)
  -- volumes after first transfer
  (h₁ : (x - y) / a^2 = (2 * x + y - z) / (2 * a)^2)
  (h₁' : (2 * x + y - z) / (2 * a)^2 = (3 * x + z) / (3 * a)^2)
  -- volume after second transfer
  (h₂ : (x - y + 128 + 4/7) / a^2 = 2 * (2 * x + y - z) / (2 * a)^2)
  (h₃ : (x - y + 128 + 4/7) + 100 = x) : x = 500 := by
  have eq1 : 4 * (x - y) = 2 * x + y - z := by
    have h3 : a > 0 := hpos
    have h4 : a^2 > 0 := by
      nlinarith 
    field_simp at h₁ 
    <;> nlinarith [sq_pos_of_pos hpos]
  have eq3 : 9 * (2 * x + y - z) = 4 * (3 * x + z) := by
    have h3 : a > 0 := hpos
    have h4 : a^2 > 0 := by
      nlinarith 
    field_simp at h₁' 
    <;> nlinarith [sq_pos_of_pos hpos]
  have eq4 : x - y + 128 + 4/7 = 4 * (2 * x + y - z) := by
    have h4 : a > 0 := hpos
    have h4 : a^2 > 0 := by
      nlinarith 
    field_simp at h₂ 
    <;> nlinarith [sq_pos_of_pos hpos]
  linarith