import Mathlib

open Real

theorem algebra_13829 : IsLeast {4*z/(2*x + y) + 4*x/(y + 2*z) + y/(x + z) | (x : ℝ) (y : ℝ) (z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)} 3 := by
  constructor
  · -- Show 3 is in the set
    use 1, 2, 1, by norm_num, by norm_num, by norm_num
    norm_num
  · -- Show no value less than 3 is in the set
    intro a h
    rcases h with ⟨x, y, z, hx, hy, hz, ha⟩
    have h1 : 0 < (x * y * z) := by
      apply mul_pos
      apply mul_pos
      exact hx
      exact hy
      exact hz
    have h2 : 4 * z / (2 * x + y) + 4 * x / (y + 2 * z) + y / (x + z) - 3 ≥ 0 := by
      have h4 : 0 < (2 * x + y) * (y + 2 * z) * (x + z) := by
        positivity
      have h5 : 4 * z / (2 * x + y) + 4 * x / (y + 2 * z) + y / (x + z) - 3 =
        (4 * z * (y + 2 * z) * (x + z) + 4 * x * (2 * x + y) * (x + z) + y * (2 * x + y) * (y + 2 * z) - 3 * (2 * x + y) * (y + 2 * z) * (x + z)) / ((2 * x + y) * (y + 2 * z) * (x + z)) := by
        field_simp
        ring
      rw [h5] at *
      apply div_nonneg
      nlinarith [sq_nonneg (x - z), sq_nonneg (y - 2 * x), sq_nonneg (y - 2 * z),
        sq_nonneg (x + z - y / 2), sq_nonneg (x - z), sq_nonneg (y - 2 * (x + z)),
          mul_pos hx hy, mul_pos hy hz, mul_pos hx hz
        ]
      all_goals positivity
    linarith