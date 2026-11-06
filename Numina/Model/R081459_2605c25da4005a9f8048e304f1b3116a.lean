import Mathlib

theorem inequalities_281760 (a b : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) :
    1 + a + b > 3 * Real.sqrt (a * b) := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  have hab1 : 0 < a * b := mul_pos ha1 hb1
  have hab2 : a * b < 1 := by nlinarith [mul_pos ha1 hb1]
  have h1 : Real.sqrt (a * b) ≥ 0 := by positivity
  have h2 : 0 < 1 + a + b := by nlinarith

  have h3 : (1 + a + b) ^ 2 > 9 * (a * b) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1),
      mul_pos ha1 hb1, ha2, hb2
    ]

  have h4 : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (by nlinarith)
  nlinarith [Real.sqrt_nonneg (a * b), h4, h3, sq_nonneg (Real.sqrt (a * b) - (1 + a + b)/3), 
      sq_nonneg (a * b - (1 + a + b)^2 / 9) 
  ]