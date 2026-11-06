import Mathlib

theorem algebra_13645 {x y z : ℤ} (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : x + 2 * y + 4 * z = 4 * x * y * z) : x + y + z = 4 := by
  have hx1 : x ≥ 1 := by linarith
  have hy1 : y ≥ 1 := by linarith
  have hz1 : z ≥ 1 := by linarith
  have h5 : z = 1 := by
    by_cases h8 : z > 1
    · -- Assume z ≥ 2 
      have h8' : z ≥ 2 := by linarith
      have h6 : x ≤ 4 := by
        nlinarith [sq_nonneg (x - 1 : ℤ), sq_nonneg (y - 1 : ℤ), sq_nonneg (z - 1 : ℤ), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]
      have h7 : y ≤ 4 := by
        nlinarith [sq_nonneg (x - 1 : ℤ), sq_nonneg (y - 1 : ℤ), sq_nonneg (z - 1 : ℤ), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]
      interval_cases x <;> interval_cases y <;> omega 
    · -- Case that z ≤ 1. Because z is integer. z ≥ 1. So z=1
      have h9 : z = 1 := by linarith
      assumption
  rw [h5] at h -- Substitute z=1 in h
  have h2 : x = 2 := by
    have hx1 : x ≥ 1 := by linarith
    have hy1 : y ≥ 1 := by linarith
    have hx2 : x ≤ 4 := by
      nlinarith [sq_nonneg (x - 2 : ℤ), sq_nonneg (y - 1 : ℤ), 
        mul_pos hx hy
      ]
    have h8 : y ≤ 4 := by
      nlinarith [sq_nonneg (x - 2 : ℤ), sq_nonneg (y - 1 : ℤ), 
          mul_pos hx hy
      ]
    interval_cases x <;> interval_cases y <;> omega 
  have h3' : y = 1 := by 
    have hx1 : x ≥ 1 := by linarith
    have hy1 : y ≥ 1 := by linarith
    have hx2 : x ≤ 4 := by
      nlinarith [sq_nonneg (x - 2 : ℤ), sq_nonneg (y - 1 : ℤ), 
          mul_pos hx hy
      ]
    have h8 : y ≤ 4 := by 
      nlinarith [sq_nonneg (x - 2 : ℤ), sq_nonneg (y - 1 : ℤ), 
          mul_pos hx hy
      ]
    interval_cases x <;> interval_cases y <;> omega 
  linarith [h2, h3', h5]