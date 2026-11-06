import Mathlib

theorem algebra_274778 (w x z : ℚ) (hw : w = 4) (hx : x = 9) (hz : z = 25) :
    Real.sqrt (w / x) + Real.sqrt (x / z) = 19 / 15 := by
  have hw2 : (w : ℝ) = 4 := by exact_mod_cast hw
  have hx2 : (x : ℝ) = 9 := by exact_mod_cast hx
  have hz2 : (z : ℝ) = 25 := by exact_mod_cast hz
  have h1 : Real.sqrt (w / x) = 2 / 3 := by 
    rw [show (w / x : ℝ) = (4 / 9 : ℝ) by 
      rw [hw2, hx2]
      all_goals norm_num
    ]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : Real.sqrt (x / z) = 3 / 5 := by 
    rw [show (x / z : ℝ) = (9 / 25 : ℝ) by 
      rw [hx2, hz2]
      all_goals norm_num
    ]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h1, h2]
  norm_num