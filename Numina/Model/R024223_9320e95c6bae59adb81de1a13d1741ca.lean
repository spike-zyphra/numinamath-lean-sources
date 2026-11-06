import Mathlib

theorem inequalities_159077 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    a * b + b * c + c * a ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c ∧
    Real.sqrt a + Real.sqrt b + Real.sqrt c ≤ 3 := by

  have h1 : Real.sqrt a + Real.sqrt b + Real.sqrt c ≤ 3 := by
    nlinarith [sq_nonneg (Real.sqrt a - 1), sq_nonneg (Real.sqrt b - 1), sq_nonneg (Real.sqrt c - 1),
      Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith), Real.sq_sqrt (show 0 ≤ c by linarith), 
      h, Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c,
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
  have h2 : a * b + b * c + c * a ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by 
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      sq_nonneg (Real.sqrt a - 1), sq_nonneg (Real.sqrt b - 1), sq_nonneg (Real.sqrt c - 1),
      Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c,
      Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith), Real.sq_sqrt (show 0 ≤ c by linarith), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      h, Real.sqrt_le_sqrt (show 0 ≤ a by linarith), Real.sqrt_le_sqrt (show 0 ≤ b by linarith), Real.sqrt_le_sqrt (show 0 ≤ c by linarith)
    ]

  constructor
  · -- Show a * b + b * c + c * a ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c
    linarith
  · -- Show Real.sqrt a + Real.sqrt b + Real.sqrt c ≤ 3
    linarith