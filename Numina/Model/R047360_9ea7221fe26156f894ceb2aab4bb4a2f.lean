import Mathlib

open Real Set

theorem algebra_13753 :
    IsLeast {k : ℝ | ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = 3 ∧ 4 / x + 9 / y + 16 / z = k}  27 := by
  constructor
  · -- First part: show that 27 is in the set.
    use 2 / 3, 1, 4 / 3
    norm_num
  · -- Second part: show that 27 is the least element in the set.
    intro k hk
    rcases hk with ⟨x, y, z, hx, hy, hz, h1, h2⟩
    have h4 : 4 / x + 9 / y + 16 / z ≥ 27 := by
      have h5 : 0 < x * y * z := by
        apply mul_pos
        apply mul_pos
        exact hx
        exact hy
        exact hz
      have h6 : 4 / x + 9 / y + 16 / z - 27 ≥ 0 := by
        have h7 : 4 / x + 9 / y + 16 / z - 27 = (4 * y * z + 9 * x * z + 16 * x * y - 27 * (x * y * z)) / (x * y * z) := by
          field_simp
          ring
        rw [h7]
        have h8 : 4 * y * z + 9 * x * z + 16 * x * y ≥ 27 * (x * y * z) := by
          nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (y - 1), sq_nonneg (z - 4 / 3),
            sq_nonneg (x * y - 2 / 3 * 1), sq_nonneg (x * z - 2 / 3 * 4 / 3), sq_nonneg (y * z - 1 * 4 / 3),
            mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
            h1]
        have h9 : (4 * y * z + 9 * x * z + 16 * x * y - 27 * (x * y * z)) ≥ 0 := by linarith [h8]
        have h10 : (4 * y * z + 9 * x * z + 16 * x * y - 27 * (x * y * z)) / (x * y * z) ≥ 0 := by
          apply div_nonneg
          linarith [h9]
          positivity
        linarith
      linarith
    linarith [h2, h4]