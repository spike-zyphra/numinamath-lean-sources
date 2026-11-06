import Mathlib

open Real

theorem inequalities_159825 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 1) :
    3 ≤ sqrt (a^2 + a * b + b^2) + sqrt (b^2 + b * c + c^2) +
        sqrt (c^2 + c * a + a^2) := by
  have h5 : sqrt (a^2 + a * b + b^2) >= (Real.sqrt 3 / 2) * (a + b) := by
    have h2 : (a ^ 2 + a * b + b ^ 2) >= ((Real.sqrt 3 / 2) * (a + b)) ^ 2 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), sq_nonneg (a - b)]
    have h4 : (a ^ 2 + a * b + b ^ 2 : ℝ) ≥ 0 := by positivity
    have h5' : ( (Real.sqrt 3 / 2) * (a + b) ) ≥ 0 := by positivity
    have h7 : Real.sqrt (a^2 + a * b + b^2) ≥ Real.sqrt ( ((Real.sqrt 3 / 2) * (a + b)) ^ 2 ) := Real.sqrt_le_sqrt (by linarith)
    have h9 : Real.sqrt ( ((Real.sqrt 3 / 2) * (a + b)) ^ 2 ) = (Real.sqrt 3 / 2) * (a + b) := by
      rw [Real.sqrt_sq]
      positivity
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (a ^ 2 + a * b + b ^ 2)
    ]
  have h6 : sqrt (b^2 + b * c + c^2) >= (Real.sqrt 3 / 2) * (b + c) := by
    have h2 : (b ^ 2 + b * c + c ^ 2) >= ((Real.sqrt 3 / 2) * (b + c)) ^ 2 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), sq_nonneg (b - c)]
    have h4 : (b ^ 2 + b * c + c ^ 2 : ℝ) ≥ 0 := by positivity
    have h5 : ( (Real.sqrt 3 / 2) * (b + c) ) ≥ 0 := by positivity
    have h7 : Real.sqrt (b^2 + b * c + c^2) ≥ Real.sqrt ( ((Real.sqrt 3 / 2) * (b + c)) ^ 2 ) := Real.sqrt_le_sqrt (by linarith)
    have h9 : Real.sqrt ( ((Real.sqrt 3 / 2) * (b + c)) ^ 2 ) = (Real.sqrt 3 / 2) * (b + c) := by
      rw [Real.sqrt_sq]
      positivity
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (b ^ 2 + b * c + c ^ 2)
    ]
  have h7 : sqrt (c^2 + c * a + a^2) >= (Real.sqrt 3 / 2) * (c + a) := by
    have h2 : (c ^ 2 + c * a + a ^ 2) >= ((Real.sqrt 3 / 2) * (c + a)) ^ 2 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), sq_nonneg (c - a)]
    have h4 : (c ^ 2 + c * a + a ^ 2 : ℝ) ≥ 0 := by positivity
    have h5 : ( (Real.sqrt 3 / 2) * (c + a) ) ≥ 0 := by positivity
    have h7 : Real.sqrt (c^2 + c * a + a^2) ≥ Real.sqrt ( ((Real.sqrt 3 / 2) * (c + a)) ^ 2 ) := Real.sqrt_le_sqrt (by linarith)
    have h9 : Real.sqrt ( ((Real.sqrt 3 / 2) * (c + a)) ^ 2 ) = (Real.sqrt 3 / 2) * (c + a) := by
      rw [Real.sqrt_sq]
      positivity
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (c ^ 2 + c * a + a ^ 2)
    ]
  have h3 : sqrt (a^2 + a * b + b^2) + sqrt (b^2 + b * c + c^2) + sqrt (c^2 + c * a + a^2) >= Real.sqrt 3 * (a + b + c) := by
    nlinarith [h5, h6, h7, Real.sqrt_nonneg 3, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
  have h4 : (a + b + c) ^ 2 ≥ 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h]
  have h4' : a + b + c ≥ Real.sqrt 3 := by
    have h5 : (a + b + c) ^ 2 ≥ (Real.sqrt 3) ^ 2 := by
      nlinarith [h4, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    have h6 : (0 : ℝ) ≤ a + b + c := by positivity
    have h7 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (a + b + c - Real.sqrt 3)]
  have h9 : Real.sqrt 3 * (a + b + c) ≥ 3 := by
    nlinarith [h4', Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg (3)
    ]
  linarith [h3, h9]