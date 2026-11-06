import Mathlib

open Real

theorem inequalities_119981 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a ≤ 1) (h2 : a + b ≤ 5) :
    sqrt a + sqrt b ≤ 3 := by

  have h3 : sqrt a ≥ 0 := Real.sqrt_nonneg a
  have h4 : sqrt b ≥ 0 := Real.sqrt_nonneg b

  have h5 : (sqrt a + sqrt b) ^ 2 = (sqrt a) ^ 2 + (sqrt b) ^ 2 + 2 * (sqrt a * sqrt b) := by
    ring

  have h6 : (sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
  have h7 : (sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith)
  have h8 : sqrt a * sqrt b ≥ 0 := mul_nonneg (by positivity) (by positivity)

  have h9 : sqrt a * sqrt b ≤ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (1 - a) by linarith) (show 0 ≤ b by linarith), sq_nonneg (sqrt a - 1), sq_nonneg (sqrt b - 2), Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), Real.sqrt_nonneg a, Real.sqrt_nonneg b, sq_nonneg (a - 1), sq_nonneg (b - 4)
            ]
  have h13 : (sqrt a + sqrt b) ^ 2 ≤ 9 := by
    nlinarith [h5, h6, h7, h9, h2]

  have h14 : sqrt a + sqrt b ≤ 3 := by
    nlinarith [sq_nonneg (sqrt a + sqrt b), sq_nonneg (sqrt a + sqrt b - 3), h13, Real.sqrt_nonneg a, Real.sqrt_nonneg b
            ]
  exact h14