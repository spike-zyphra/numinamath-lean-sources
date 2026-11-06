import Mathlib

open Real

theorem inequalities_157382 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    sqrt (a + 1 / 2) + sqrt (b + 1 / 2) >
    (sqrt 6 + sqrt 2) / 2 := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : a + b = 1 := h

  have h9 : (sqrt (a + 1 / 2) + sqrt (b + 1 / 2)) ^ 2 > ((sqrt 6 + sqrt 2) / 2) ^ 2 := by
    have h10 : (sqrt (a + 1 / 2) + sqrt (b + 1 / 2)) ^ 2 =
        (sqrt (a + 1 / 2)) ^ 2 + (sqrt (b + 1 / 2)) ^ 2 + 2 * (sqrt (a + 1 / 2) * sqrt (b + 1 / 2)) := by ring

    have h11 : ((sqrt 6 + sqrt 2) / 2) ^ 2 = ((sqrt 6 + sqrt 2) ^ 2) / 4 := by ring

    rw [h10, h11]

    have h12 : (sqrt (a + 1 / 2)) ^ 2 = a + 1 / 2 := by 
      rw [Real.sq_sqrt]
      linarith

    have h13 : (sqrt (b + 1 / 2)) ^ 2 = b + 1 / 2 := by 
      rw [Real.sq_sqrt]
      nlinarith

    rw [h12, h13]

    have h14 : 0 < a * b := mul_pos h1 h2

    have h15 : (a + 1 / 2) * (b + 1 / 2) > 0 := by
      nlinarith

    have h16 : Real.sqrt ((a + 1 / 2) * (b + 1 / 2)) ≥ 0 := by positivity

    have h17 : sqrt (a + 1 / 2) * sqrt (b + 1 / 2) = Real.sqrt ((a + 1 / 2) * (b + 1 / 2)) := by
      have h44 : Real.sqrt ((a + 1 / 2) * (b + 1 / 2)) = Real.sqrt (a + 1 / 2) * Real.sqrt (b + 1 / 2) := by
        rw [← Real.sqrt_mul (by nlinarith)]
      linarith [h44]

    have h18 : Real.sqrt ((a + 1 / 2) * (b + 1 / 2)) ^ 2 = (a + 1 / 2) * (b + 1 / 2) := by
      rw [Real.sq_sqrt]
      nlinarith

    have h19 : 4 * ((a + 1 / 2) * (b + 1 / 2)) > 3 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 0), sq_pos_of_pos (show 0 < a * b by nlinarith), h3]

    nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (2 : ℝ), 
      Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num), 
      Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), 
      Real.sqrt_nonneg ((a + 1 / 2) * (b + 1 / 2)), 
      Real.sq_sqrt (show (a + 1 / 2) * (b + 1 / 2) ≥ 0 by nlinarith), 
      mul_nonneg (Real.sqrt_nonneg (6 : ℝ)) (Real.sqrt_nonneg (2 : ℝ)), 
      h17, h19
      ]
  -- Now from h9 we can prove the original inequality.
  have h10 : sqrt (a + 1 / 2) + sqrt (b + 1 / 2) ≥ 0 := by positivity
  have h11 : (sqrt 6 + sqrt 2) / 2 ≥ 0 := by positivity
  have h12 : sqrt (a + 1 / 2) + sqrt (b + 1 / 2) > (sqrt 6 + sqrt 2) / 2 := by 
    nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (2 : ℝ), 
      Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num), 
      Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), 
        Real.sqrt_nonneg (a + 1 / 2), Real.sqrt_nonneg (b + 1 / 2), 
          h9, h10, h11
        ]
  exact h12