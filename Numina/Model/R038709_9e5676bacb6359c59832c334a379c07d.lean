import Mathlib

open Real Set

theorem algebra_15369 :
  IsLeast {(x + 2 * y) * (y + 2 * z) * (x * z + 1) | (x : ℝ) (y : ℝ) (z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxyz : x * y * z = 1)} 16 := by 
  constructor
  · -- Show 16 is in the set
    use 2, 1, (1 / 2)
    norm_num 
  · -- Show 16 is the least element in the set 
    intro k hk 
    rcases hk with ⟨x, y, z, hx, hy, hz, hxyz, hk⟩
    have h4 : x + 2 * y ≥ 2 * Real.sqrt (2 * (x * y)) := by 
      nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (Real.sqrt (2 * (x * y)) - (x / 2)), 
          Real.sqrt_nonneg (2 * (x * y)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (x * y)) by nlinarith) 
        ]
    have h5 : y + 2 * z ≥ 2 * Real.sqrt (2 * (y * z)) := by
      nlinarith [sq_nonneg (y - 2 * z), sq_nonneg (Real.sqrt (2 * (y * z)) - (y / 2)), 
          Real.sqrt_nonneg (2 * (y * z)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (y * z)) by nlinarith)
        ]
    have h6 : x * z + 1 ≥ 2 * Real.sqrt (x * z) := by 
      nlinarith [sq_nonneg (x * z - 1), sq_nonneg (Real.sqrt (x * z) - 1), 
          Real.sqrt_nonneg (x * z), Real.sq_sqrt (show (0 : ℝ) ≤ x * z by nlinarith)
        ]
    have h7 : (x + 2 * y) * (y + 2 * z) * (x * z + 1) ≥ 16 := by 
      have h8 : (x + 2 * y) * (y + 2 * z) * (x * z + 1) ≥ (2 * Real.sqrt (2 * (x * y))) * (2 * Real.sqrt (2 * (y * z))) * (2 * Real.sqrt (x * z)) := by
        have h4' : x + 2 * y ≥ 2 * Real.sqrt (2 * (x * y)) := h4 
        have h5' : y + 2 * z ≥ 2 * Real.sqrt (2 * (y * z)) := h5 
        have h6' : x * z + 1 ≥ 2 * Real.sqrt (x * z) := h6 
        have h9 : 0 < (2 * Real.sqrt (2 * (x * y))) := by 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 * (x * y) by nlinarith), Real.sqrt_nonneg (2 * (x * y))]
        have h10 : 0 < (2 * Real.sqrt (2 * (y * z))) := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 * (y * z) by nlinarith), Real.sqrt_nonneg (2 * (y * z))]
        have h11 : 0 < (2 * Real.sqrt (x * z)) := by 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < x * z by nlinarith), Real.sqrt_nonneg (x * z)]
        have h12 : (x + 2 * y) * ((y + 2 * z) * (x * z + 1)) ≥ (2 * Real.sqrt (2 * (x * y))) * ((y + 2 * z) * (x * z + 1)) := by 
            apply mul_le_mul_of_nonneg_right 
            linarith 
            nlinarith 
        have h13 : (2 * Real.sqrt (2 * (x * y))) * ((y + 2 * z) * (x * z + 1)) ≥ (2 * Real.sqrt (2 * (x * y))) * ((2 * Real.sqrt (2 * (y * z))) * (x * z + 1)) := by 
            apply mul_le_mul_of_nonneg_left
            nlinarith 
            nlinarith 
        have h14 : (2 * Real.sqrt (2 * (x * y))) * ((2 * Real.sqrt (2 * (y * z))) * (x * z + 1)) ≥ (2 * Real.sqrt (2 * (x * y))) * ((2 * Real.sqrt (2 * (y * z))) * (2 * Real.sqrt (x * z))) := by 
            apply mul_le_mul_of_nonneg_left 
            nlinarith 
            nlinarith 
        linarith 
      have h9 : (2 * Real.sqrt (2 * (x * y))) * (2 * Real.sqrt (2 * (y * z))) * (2 * Real.sqrt (x * z)) = 16 := by
        have h9a : Real.sqrt (2 * (x * y)) * Real.sqrt (2 * (y * z)) * Real.sqrt (x * z) = 2 := by
          have h11a : Real.sqrt (2 * (x * y)) * Real.sqrt (2 * (y * z)) * Real.sqrt (x * z) = Real.sqrt (2 * (x * y) * (2 * (y * z)) * (x * z)) := by
            rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
          have h13a : 2 * (x * y) * (2 * (y * z)) * (x * z) = 4 := by 
            nlinarith [hxyz, mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]
          rw [h11a] 
          rw [h13a] 
          have h14a : Real.sqrt ((4 : ℝ)) = (2 : ℝ) := by 
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
          linarith [h14a] 
        calc 
          (2 * Real.sqrt (2 * (x * y))) * (2 * Real.sqrt (2 * (y * z))) * (2 * Real.sqrt (x * z)) = 8 * (Real.sqrt (2 * (x * y)) * Real.sqrt (2 * (y * z)) * Real.sqrt (x * z)) := by ring 
          _ = 8 * 2 := by rw [h9a] 
          _ = (16 : ℝ) := by norm_num 
      linarith 
    linarith [hk, h7]