import Mathlib

theorem algebra_184973 : (4 + Real.sqrt 15) * (Real.sqrt 10 - Real.sqrt 6) * (Real.sqrt (4 - Real.sqrt 15)) = 2 := by
  have h1 : Real.sqrt 15 ^ 2 = 15 := by
    exact Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 10 ^ 2 = 10 := by
    exact Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 6 ^ 2 = 6 := by
    exact Real.sq_sqrt (by norm_num)
  have h4 : (4 + Real.sqrt 15) * (Real.sqrt 10 - Real.sqrt 6) = Real.sqrt 10 + Real.sqrt 6 := by
    nlinarith [Real.sqrt_nonneg 15, Real.sqrt_nonneg 10, Real.sqrt_nonneg 6, 
          Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), 
          mul_nonneg (Real.sqrt_nonneg 15) (Real.sqrt_nonneg 10), 
          mul_nonneg (Real.sqrt_nonneg 15) (Real.sqrt_nonneg 6), 
          sq_nonneg (Real.sqrt 10 - Real.sqrt 6), 
          sq_nonneg (Real.sqrt 15 - Real.sqrt 10), 
          sq_nonneg (Real.sqrt 15 - Real.sqrt 6)
        ]
  have h5' : 0 ≤ (4 : ℝ) - Real.sqrt 15 := by
    nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num), Real.sqrt_nonneg 15]
  have h8 : Real.sqrt (4 - Real.sqrt 15) ^ 2 = 4 - Real.sqrt 15 := by
    rw [Real.sq_sqrt]
    nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num)]
  have h9 : Real.sqrt (4 - Real.sqrt 15) ≥ 0 := by 
    apply Real.sqrt_nonneg
  -- Expanding the product using distributive property
  have eq1 : (Real.sqrt 10 + Real.sqrt 6) * Real.sqrt (4 - Real.sqrt 15) = 
    Real.sqrt (10 * (4 - Real.sqrt 15)) + Real.sqrt (6 * (4 - Real.sqrt 15)) := by 
    have h10 : Real.sqrt (10 * (4 - Real.sqrt 15)) = Real.sqrt 10 * Real.sqrt (4 - Real.sqrt 15) := by 
      rw [Real.sqrt_mul (by
        nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num)]
      )]
    have h11 : Real.sqrt (6 * (4 - Real.sqrt 15)) = Real.sqrt 6 * Real.sqrt (4 - Real.sqrt 15) := by
      rw [Real.sqrt_mul (by
        nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num)]
      )]
    nlinarith [Real.sqrt_nonneg (4 - Real.sqrt 15), h10, h11, 
      mul_nonneg (Real.sqrt_nonneg 10) (Real.sqrt_nonneg (4 - Real.sqrt 15)), 
      mul_nonneg (Real.sqrt_nonneg 6) (Real.sqrt_nonneg (4 - Real.sqrt 15)), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)
    ]
  -- Simplifying Real.sqrt (10 * (4 - Real.sqrt 15))
  have eq2 : Real.sqrt (10 * (4 - Real.sqrt 15)) = 5 - Real.sqrt 15 := by
    have h10 : Real.sqrt (10 * (4 - Real.sqrt 15)) = Real.sqrt ((5 - Real.sqrt 15) ^ 2) := by 
      have h11 : (5 - Real.sqrt 15 : ℝ) ^ 2 = 10 * (4 - Real.sqrt 15) := by
        nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num)]
      rw [h11]
    have h12 : Real.sqrt ((5 - Real.sqrt 15 : ℝ) ^ 2) = (5 - Real.sqrt 15 : ℝ) := by
      rw [Real.sqrt_sq (show 0 ≤ (5 - Real.sqrt 15 : ℝ) by
        nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num)]
      )]
    rw [h10, h12]
  -- Simplifying Real.sqrt (6 * (4 - Real.sqrt 15))
  have eq3 : Real.sqrt (6 * (4 - Real.sqrt 15)) = Real.sqrt 15 - 3 := by
    have h10 : Real.sqrt (6 * (4 - Real.sqrt 15)) = Real.sqrt ((Real.sqrt 15 - 3) ^ 2) := by 
      have h11 : (Real.sqrt 15 - 3 : ℝ) ^ 2 = 6 * (4 - Real.sqrt 15) := by 
        nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num)]
      rw [h11]
    have h12 : Real.sqrt ((Real.sqrt 15 - 3 : ℝ) ^ 2) = (Real.sqrt 15 - 3 : ℝ) := by 
      rw [Real.sqrt_sq (show 0 ≤ (Real.sqrt 15 - 3 : ℝ) by
        nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num)]
      )]
    rw [h10, h12]
  -- Using eq1, eq2, eq3 to obtain the final result
  have eq4 : (Real.sqrt 10 + Real.sqrt 6) * Real.sqrt (4 - Real.sqrt 15) = 2 := by
    rw [eq1, eq2, eq3]
    <;> nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num)]
  calc 
    (4 + Real.sqrt 15) * (Real.sqrt 10 - Real.sqrt 6) * (Real.sqrt (4 - Real.sqrt 15))
        = ((4 + Real.sqrt 15) * (Real.sqrt 10 - Real.sqrt 6)) * (Real.sqrt (4 - Real.sqrt 15)) := by ring
    _ = (Real.sqrt 10 + Real.sqrt 6) * (Real.sqrt (4 - Real.sqrt 15)) := by 
      rw [h4]
    _ = 2 := by 
      linarith [eq4]