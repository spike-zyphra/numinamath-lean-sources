import Mathlib

theorem algebra_306651 {x : ℝ} (hx : x = (Real.sqrt 5 + 1) / 2) :
    (x^3 + x + 1) / x^5 = (Real.sqrt 5 - 1) / 2 := by
  have h1 : x ^ 2 = x + 1 := by 
    rw [hx]
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), 
        Real.sqrt_nonneg 5
      ]
  have h2 : x ^ 3 + x + 1 = 3 * x + 2 := by
    calc 
      x ^ 3 + x + 1 = (x * (x ^ 2)) + x + 1 := by ring_nf
      _ = x * ((x ^ 2) ) + x + 1 := by ring_nf
      _ = x * (x + 1) + x + 1 := by rw [h1]
      _ = (x ^ 2) + x * 2 + 1 := by ring_nf
      _ = (x + 1) + x * 2 + 1 := by rw [h1]
      _ = 3 * x + 2 := by ring_nf
  have h3 : x ^ 5 = 5 * x + 3 := by
    have h4 : x ^ 4 = (x + 1) ^ 2 := by
      calc
        x ^ 4 = (x ^ 2) ^ 2 := by ring_nf
        _ = (x + 1) ^ 2 := by rw [h1]
    calc
      x ^ 5 = x * (x ^ 4) := by ring_nf
      _ = x * ((x + 1) ^ 2) := by rw [h4]
      _ = 5 * x + 3 := by
        nlinarith [h1, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0) ]

  rw [h2, h3]

  have hx' : 5 * x + 3 ≠ 0 := by
    rw [hx]
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0), 
        Real.sqrt_nonneg 5, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), 
        Real.sqrt_nonneg 5
      ]
  field_simp [hx', Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), 
    Real.sqrt_nonneg 5
  ]
  <;> nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0), 
      Real.sqrt_nonneg 5, 
      Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), 
      Real.sqrt_nonneg 5
    ]