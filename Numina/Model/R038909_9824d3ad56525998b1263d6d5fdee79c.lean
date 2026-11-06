import Mathlib

open Real

theorem algebra_215246 {a b : ℝ}
    (ha : a = (Real.sqrt 5 + Real.sqrt 3) / (Real.sqrt 5 - Real.sqrt 3))
    (hb : b = (Real.sqrt 5 - Real.sqrt 3) / (Real.sqrt 5 + Real.sqrt 3)) :
    a^4 + b^4 + (a + b)^4 = 7938 := by

  have h1 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 5 ^ 2 - Real.sqrt 3 ^ 2 = 2 := by
    linarith [h1, h2]

  -- Calculate a + b = 8
  have h4 : a + b = 8 := by
    rw [ha, hb]
    have h7 : Real.sqrt 5 - Real.sqrt 3 ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), 
            mul_pos (show (0 : ℝ) < (5 : ℝ) by norm_num) (show (0: ℝ) < (3 : ℝ) by norm_num), 
              Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)
      ]
    have h8 : Real.sqrt 5 + Real.sqrt 3 ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), 
            mul_pos (show (0 : ℝ) < (5 : ℝ) by norm_num) (show (0: ℝ) < (3 : ℝ) by norm_num), 
              Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)
      ]
    field_simp [h7, h8, Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), 
            mul_pos (show (0 : ℝ) < (5 : ℝ) by norm_num) (show (0: ℝ) < (3 : ℝ) by norm_num)]
    <;> nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), mul_pos (show (0 : ℝ) < (5 : ℝ) by norm_num) (show (0: ℝ) < (3 : ℝ) by norm_num)]

  -- Calculate a * b = 1
  have h5 : a * b = 1 := by
    rw [ha, hb]
    have h7 : Real.sqrt 5 - Real.sqrt 3 ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), 
            mul_pos (show (0 : ℝ) < (5 : ℝ) by norm_num) (show (0: ℝ) < (3 : ℝ) by norm_num), 
              Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)
      ]
    have h8 : Real.sqrt 5 + Real.sqrt 3 ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), 
            mul_pos (show (0 : ℝ) < (5 : ℝ) by norm_num) (show (0: ℝ) < (3 : ℝ) by norm_num), 
              Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)
      ]
    field_simp [h7, h8, Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), 
            mul_pos (show (0 : ℝ) < (5 : ℝ) by norm_num) (show (0: ℝ) < (3 : ℝ) by norm_num)]
    <;> nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), mul_pos (show (0 : ℝ) < (5 : ℝ) by norm_num) (show (0: ℝ) < (3 : ℝ) by norm_num)]

  -- Calculate a ^ 2 + b ^ 2 = 62
  have h7 : a ^ 2 + b ^ 2 = 62 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 1), 
      sq_nonneg (a + b - 8), 
      sq_nonneg (a * b - 1), 
      h4, 
      h5
    ]

  -- Calculate a ^ 4 + b ^ 4 = 3842
  have h8 : a ^ 4 + b ^ 4 = 3842 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), 
      sq_nonneg (a ^ 2 + b ^ 2 - 62), 
      sq_nonneg (a ^ 2 - b ^ 2), 
      sq_nonneg (a ^ 2 * b ^ 2 - 1), 
      sq_nonneg (a * b - 1), 
      h7, 
      h5
    ]

  -- Calculate (a + b) ^ 4 = 4096
  have h9 : (a + b) ^ 4 = 4096 := by 
    rw [h4]
    norm_num

  -- Calculate total sum
  nlinarith [h8, h9]