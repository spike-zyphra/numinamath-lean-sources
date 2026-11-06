import Mathlib

theorem inequalities_75976 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c + a * b + a * c + b * c = 3) :
    2 ≤ a + b + c + a * b * c ∧ a + b + c + a * b * c ≤ 3 := by
  constructor
  · -- Lower bound: 2 ≤ a + b + c + a * b * c
    have h1 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h2 : 2 ≤ a + b + c + a * b * c := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
                sq_nonneg (a + b + c - 2), sq_nonneg (a * b + a * c + b * c - 1),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
                  mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
                  mul_pos (show 0 < a by linarith) (show 0 < c by linarith), 
                  mul_pos (show 0 < b by linarith) (show 0 < c by linarith)
                ]
    linarith
  · -- Upper bound: a + b + c + a * b * c ≤ 3
    have h1 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h2 : a + b + c + a * b * c ≤ 3 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
                sq_nonneg (a + b + c - 1), sq_nonneg (a * b + a * c + b * c - 1),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
                  mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
                  mul_pos (show 0 < a by linarith) (show 0 < c by linarith), 
                  mul_pos (show 0 < b by linarith) (show 0 < c by linarith)
                ]
    linarith