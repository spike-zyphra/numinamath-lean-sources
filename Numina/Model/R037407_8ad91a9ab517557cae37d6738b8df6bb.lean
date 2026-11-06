import Mathlib

theorem algebra_1183 {x y : ℝ} (hx : x = Real.sqrt 2 + Real.sqrt 3) (h : x^8 + 1 = x^4 * (6 * y + 8)) : y = 15 := by
  have h1 : x^2 = 5 + 2 * Real.sqrt 6 := by
    rw [hx]
    have h2 : (Real.sqrt 2 + Real.sqrt 3) ^ 2 = 5 + 2 * Real.sqrt 6 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3,
          Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sqrt_nonneg (6 : ℝ),
          Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3),
          sq_nonneg (Real.sqrt 2 - Real.sqrt 3),
          mul_self_nonneg (Real.sqrt 2 - Real.sqrt 3),
          Real.sqrt_le_sqrt (show 2 ≤ (3 : ℝ) by norm_num)
        ]
    linarith [h2]
  have h2 : x^4 = 49 + 20 * Real.sqrt 6 := by
    calc
      x^4 = (x^2) ^ 2 := by ring_nf
      _ = (5 + 2 * Real.sqrt 6) ^ 2 := by rw [h1]
      _ = 49 + 20 * Real.sqrt 6 := by 
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  have h3 : x^8 = 4801 + 1960 * Real.sqrt 6 := by
    calc
      x^8 = (x^4) ^ 2 := by ring_nf
      _ = (49 + 20 * Real.sqrt 6) ^ 2 := by rw [h2]
      _ = 4801 + 1960 * Real.sqrt 6 := by
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  rw [h3, h2] at h
  ring_nf at h
  have h4 : Real.sqrt 6 > 0 := by
    apply Real.sqrt_pos.mpr
    all_goals norm_num
  nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, sq_nonneg (x^2 + 1), sq_nonneg (x^2 - 5), sq_nonneg (x^2 - 5), sq_nonneg (y - 15), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)
    ]