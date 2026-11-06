import Mathlib

theorem inequalities_600607 (x y : ℝ) (hx : |x| < 1) (hy : |y| < 1) :
    |(x - y) / (1 - x * y)| < 1 := by
  have h1 : -1 < x := by linarith [abs_lt.mp hx]
  have h2 : x < 1 := by linarith [abs_lt.mp hx]
  have h3 : -1 < y := by linarith [abs_lt.mp hy]
  have h4 : y < 1 := by linarith [abs_lt.mp hy]

  have h5 : 0 < 1 - x * y := by
    nlinarith [sq_nonneg (x * y - x - y + 1), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  
  have h6 : -1 < (x - y) / (1 - x * y) := by
    apply (lt_div_iff₀ h5).mpr
    nlinarith [mul_pos (sub_pos.mpr (by linarith : 1 - x > 0)) (sub_pos.mpr (by linarith : 1 - y > 0)), 
      mul_pos (sub_pos.mpr (by linarith : x + 1 > 0)) (sub_pos.mpr (by linarith : y + 1 > 0)), 
      mul_pos (sub_pos.mpr (by linarith : 1 - x > 0)) (sub_pos.mpr (by linarith : x + 1 > 0)), 
      mul_pos (sub_pos.mpr (by linarith : 1 - y > 0)) (sub_pos.mpr (by linarith : y + 1 > 0))
    ]
  
  have h7 : (x - y) / (1 - x * y) < 1 := by
    apply (div_lt_iff₀ h5).mpr
    nlinarith [mul_pos (sub_pos.mpr (by linarith : 1 - x > 0)) (sub_pos.mpr (by linarith : 1 - y > 0)), 
      mul_pos (sub_pos.mpr (by linarith : x + 1 > 0)) (sub_pos.mpr (by linarith : y + 1 > 0)), 
      mul_pos (sub_pos.mpr (by linarith : 1 - x > 0)) (sub_pos.mpr (by linarith : x + 1 > 0)), 
      mul_pos (sub_pos.mpr (by linarith : 1 - y > 0)) (sub_pos.mpr (by linarith : y + 1 > 0))
    ]

  apply abs_lt.mpr
  constructor <;> nlinarith [h6, h7]