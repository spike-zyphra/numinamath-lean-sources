import Mathlib

theorem algebra_96704 {a : ℝ} (ha : a ≠ 0) (h : 4 = a + 1 / a) :
a ^ 4 + 1 / a ^ 4 = 194 := by
  -- Let's derive a^2 + 1/a^2
  -- Start with 4 = a + 1/a
  have h4 : a + 1/a = 4 := by linarith
  -- We square both sides of the equation 4 = a + 1/a to get a^2 + 1/a^2
  have h3 : a^2 + 1/a^2 = 14 := by
    calc
      a^2 + 1/a^2 = (a + 1/a) ^ 2 - 2 := by
        field_simp [ha]
        <;> ring
      _ = 4 ^ 2 - 2 := by rw [h4]
      _ = 14 := by norm_num
  -- To find a^4 + 1/a^4, we square a^2 + 1/a^2 = 14
  calc
    a^4 + 1/a^4 = (a^2 + 1/a^2) ^ 2 - 2 := by
      field_simp [ha]
      <;> ring
    _ = 14 ^ 2 - 2 := by rw [h3]
    _ = 194 := by norm_num