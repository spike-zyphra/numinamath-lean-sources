import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_234034 :
  IsLeast {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 1 ∧ t = 1/x + 4/y + 9/z} 36 := by
  constructor
  · -- First, we'll show that 36 belongs to the set
    use 1 / 6, 1 / 3, 1 / 2
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    norm_num
  · -- Now we show that 36 is the least element
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, ht⟩
    have h2 : 1 / x + 4 / y + 9 / z ≥ 36 := by
      have h3 : 1 / x + 4 / y + 9 / z - 36 ≥ 0 := by
        have h4 : x + y + z = 1 := h1
        have h5 : 0 < x * y * z := by
          positivity
        have h6 : (1 / x + 4 / y + 9 / z - 36) * (x * y * z) ≥ 0 := by
          have h7 : (1 / x + 4 / y + 9 / z - 36) * (x * y * z) =
            y * z + 4 * x * z + 9 * x * y - 36 * (x * y * z) := by
            field_simp [show x ≠ 0 by linarith, show y ≠ 0 by linarith, show z ≠ 0 by linarith]
            ring
          rw [h7]
          nlinarith [sq_nonneg (x - 1 / 6), sq_nonneg (y - 1 / 3), sq_nonneg (z - 1 / 2), 
            sq_nonneg (y - 2 * x), sq_nonneg (z - 3 * x), 
            mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
            h4
          ]
        have h8 : (1 / x + 4 / y + 9 / z - 36) ≥ 0 := by
          nlinarith [show (1 / x + 4 / y + 9 / z - 36) * (x * y * z) ≥ 0 by linarith, 
            positivity, 
            mul_pos hx hy, 
            mul_pos hx hz, 
            mul_pos hy hz
          ]
        linarith
      linarith
    linarith [ht, h2]