import Mathlib

theorem algebra_63853 {a b : ℝ} (ha : a^5 * b^8 = 12) (hb : a^8 * b^13 = 18) : a * b = 128 / 3 := by
  have h1 : (a * b) = (a^5 * b^8) ^ 5 / (a^8 * b^13) ^ 3 := by
    field_simp
    <;> ring_nf
    <;> norm_num
  have h2 : (a^5 * b^8) ^ 5 = 12 ^ 5 := by
    rw [ha]
    <;> norm_num
  have h3 : (a^8 * b^13) ^ 3 = 18 ^ 3 := by
    rw [hb]
    <;> norm_num
  rw [h1, h2, h3]
  norm_num