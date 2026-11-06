import Mathlib

open Real

theorem inequalities_69664 : IsGreatest {M : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ M = x / (2 * x + y) + y / (2 * y + z) + z / (2 * z + x)} 1 := by
  constructor
  · -- Show 1 is in the set
    use 1, 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show 1 is the greatest in the set
    intro M hM
    rcases hM with ⟨x, y, z, hx, hy, hz, hM⟩
    have h1 : x / (2 * x + y) + y / (2 * y + z) + z / (2 * z + x) ≤ 1 := by
      have h2 : 0 < (2 * x + y) * (2 * y + z) * (2 * z + x) := by positivity
      have h3 : x / (2 * x + y) + y / (2 * y + z) + z / (2 * z + x) - 1 ≤ 0 := by
        have h4 : x / (2 * x + y) + y / (2 * y + z) + z / (2 * z + x) - 1 = (x * (2 * y + z) * (2 * z + x) + y * (2 * x + y) * (2 * z + x) + z * (2 * x + y) * (2 * y + z) - (2 * x + y) * (2 * y + z) * (2 * z + x)) / ((2 * x + y) * (2 * y + z) * (2 * z + x)) := by
          field_simp
          <;> ring
        rw [h4] at *
        apply div_nonpos_of_nonpos_of_nonneg
        · -- Show that numerator is non-positive
          have h5 : x * (2 * y + z) * (2 * z + x) + y * (2 * x + y) * (2 * z + x) + z * (2 * x + y) * (2 * y + z) - (2 * x + y) * (2 * y + z) * (2 * z + x) ≤ 0 := by
            nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
                      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
                      sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), 
                      sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), 
                      sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
                      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
          linarith
        · -- Show the denominator is non-negative
          positivity
      linarith
    linarith [hM, h1]