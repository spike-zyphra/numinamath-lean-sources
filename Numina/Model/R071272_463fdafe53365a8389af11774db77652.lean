import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11581 :
  IsLeast {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 1 ∧ t = 1/x + 1/y + 1/z} 9 := by
  constructor
  · -- Show that 9 is achievable, using x = y = z = 1/3
    use 1 / 3, 1 / 3, 1 / 3
    norm_num
  · -- Show that no value less than 9 belongs to the set
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, hxyz, ht⟩
    have h1 : 1/x + 1/y + 1/z ≥ 9 := by
      have hxyz1 : x + y + z = 1 := hxyz
      have h4 : x * y * z > 0 := mul_pos (mul_pos hx hy) hz
      have h5 : x * y + y * z + z * x ≥ 9 * (x * y * z) := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          hxyz, sq_nonneg (x + y + z - 1)]
      have h6 : 1/x + 1/y + 1/z - 9 ≥ 0 := by
        have h7 : 1/x + 1/y + 1/z - 9 = (y * z + x * z + x * y - 9 * (x * y * z)) / (x * y * z) := by
          field_simp
          <;> ring
        have h8 : (y * z + x * z + x * y - 9 * (x * y * z)) / (x * y * z) ≥ 0 := by
          apply div_nonneg
          nlinarith [h5]
          positivity
        linarith [h7, h8]
      linarith [h6]
    linarith [ht, h1]