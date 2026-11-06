import Mathlib

open Real

theorem inequalities_113985 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b > 2007 * a + 2008 * b) :
    a + b > (√2007 + √2008)^2 := by
  have h1 : (√2007 + √2008) ^ 2 = (√2007) ^ 2 + (√2008) ^ 2 + 2 * (√2007 * √2008) := by 
    ring
  have h2 : (√2007) ^ 2 = 2007 := by 
    exact Real.sq_sqrt (by norm_num)
  have h3 : (√2008) ^ 2 = 2008 := by
    exact Real.sq_sqrt (by norm_num)
  have h4 : (√2007 * √2008) = √(2007 * 2008) := by
    rw [← Real.sqrt_mul (by norm_num)]
  have h5 : (√2007 + √2008) ^ 2 = 2007 + 2008 + 2 * √(2007 * 2008) := by 
    rw [h1, h2, h3, h4]
    all_goals ring_nf
  have h6 : a * b > 2007 * a + 2008 * b := h
  have h7 : (a - 2008) * (b - 2007) > 2007 * 2008 := by 
    nlinarith 
  have h8 : a > (2008 : ℝ) := by
    nlinarith [sq_nonneg (a - 2008), sq_nonneg (b - 2007), 
        mul_pos ha hb
    ]
  have h9 : b > (2007 : ℝ) := by 
    nlinarith [sq_nonneg (a - 2008), sq_nonneg (b - 2007), 
        mul_pos ha hb
    ]
  have h10 : a + b > 4015 + 2 * Real.sqrt (2007 * 2008) := by 
    have h11 : (a - 2008) * (b - 2007) > 2007 * 2008 := h7 
    have h12 : a - 2008 > 0 := by nlinarith 
    have h13 : b - 2007 > 0 := by nlinarith 
    have h15 : (a - 2008) + (b - 2007) > 2 * Real.sqrt (2007 * 2008) := by 
      nlinarith [sq_nonneg ((a - 2008) - (b - 2007)), sq_nonneg ((a - 2008) + (b - 2007) - 2 * Real.sqrt (2007 * 2008)), Real.sqrt_nonneg (2007 * 2008), 
          Real.sq_sqrt (show 0 ≤ (2007 * 2008 : ℝ) by norm_num), 
          mul_pos (show 0 < a - 2008 by linarith) (show 0 < b - 2007 by linarith), 
          sq_nonneg ( (a - 2008) * (b - 2007) - 2007 * 2008 ), 
          Real.sqrt_nonneg (2007 * 2008)
        ]
    linarith 
  nlinarith [h5, h10, Real.sqrt_nonneg 2007, Real.sqrt_nonneg 2008, 
    Real.sqrt_nonneg (2007 * 2008), 
    mul_pos ha hb
  ]