import Mathlib

open Real

theorem algebra_275569 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    1 < (a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)) ∧
    (a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)) < 2 := by
  constructor
  · -- First, prove that $S > 1$ (i.e., $1 < S$)
    have h1 : 0 < a + b + c := by linarith
    have h2 : 0 < a + b + d := by linarith
    have h3 : 0 < b + c + d := by linarith
    have h4 : 0 < a + c + d := by linarith
    have h5 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 1 > 0 := by 
      have h6 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 1 = 
          (a * (a + b + c) * (b + c + d) * (a + c + d) + 
            b * (a + b + d) * (b + c + d) * (a + c + d) + 
            c * (a + b + d) * (a + b + c) * (a + c + d) + 
            d * (a + b + d) * (a + b + c) * (b + c + d) - 
            (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)
          ) / ((a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) := by 
        field_simp
        ring
      rw [h6] at *
      apply div_pos
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
          sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
          sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), 
          sq_nonneg (a + d - b - c), 
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
          mul_pos hb hc, mul_pos hb hd, 
          mul_pos hc hd
        ]
      positivity
    linarith
  · -- Now, prove that $S < 2$ (i.e., $S < 2$)
    have h1 : 0 < a + b + c := by linarith
    have h2 : 0 < a + b + d := by linarith
    have h3 : 0 < b + c + d := by linarith
    have h4 : 0 < a + c + d := by linarith
    have h5 : 2 - (a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)) > 0 := by
      have h5 : 2 - (a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)) = 
          (2 * (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) - 
            ( a * (a + b + c) * (b + c + d) * (a + c + d) + 
              b * (a + b + d) * (b + c + d) * (a + c + d) + 
              c * (a + b + d) * (a + b + c) * (a + c + d) + 
              d * (a + b + d) * (a + b + c) * (b + c + d) ) ) / ((a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) := by 
        field_simp
        ring
      rw [h5] at *
      apply div_pos
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
          sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
          sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), 
          sq_nonneg (a + d - b - c), 
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
          mul_pos hb hc, mul_pos hb hd, 
          mul_pos hc hd
        ]
      positivity
    linarith