import Mathlib

open Real

theorem inequalities_312259 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    a^2 + b^2 + c^2 + 2 * sqrt 3 * sqrt (a * b * c) ≤ 1 := by
  have h1 : a + b + c = 1 := h
  have h2 : a^2 + b^2 + c^2 = (a + b + c) ^ 2 - 2 * (a * b + b * c + c * a) := by 
    ring
  rw [h1] at h2
  have h3 : a^2 + b^2 + c^2 = 1 - 2 * (a * b + b * c + c * a) := by
    rw [h2]
    all_goals nlinarith
  have h4 : (a * b + b * c + c * a) ^ 2 ≥ 3 * (a * b * c) * (a + b + c) := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h5 : (a * b + b * c + c * a) ^ 2 ≥ 3 * (a * b * c) := by
    rw [show (3 * (a * b * c) * (a + b + c)) = 3 * (a * b * c) by 
        rw [h1]
        all_goals norm_num
      ] at h4
    linarith
  have h6 : sqrt 3 * sqrt (a * b * c) ≤ (a * b + b * c + c * a) := by
    have h7 : (sqrt 3 * sqrt (a * b * c)) ^ 2 ≤ (a * b + b * c + c * a) ^ 2 := by
      have h8 : (sqrt 3 * sqrt (a * b * c)) ^ 2 = 3 * (a * b * c) := by
        calc
          (sqrt 3 * sqrt (a * b * c)) ^ 2
            = (sqrt 3) ^ 2 * (sqrt (a * b * c)) ^ 2 := by ring
          _ = 3 * (a * b * c) := by
            have h81 : (sqrt 3) ^ 2 = 3 := by norm_num [Real.sq_sqrt]
            have h82 : (sqrt (a * b * c)) ^ 2 = a * b * c := by
              apply Real.sq_sqrt
              positivity
            rw [h81, h82]
            <;> nlinarith
      nlinarith [h8, h5, show 0 ≤ 3 * (a * b * c) by nlinarith, 
            show 0 ≤ (a * b + b * c + c * a) ^ 2 by positivity ]
    have h8 : 0 ≤ sqrt 3 * sqrt (a * b * c) := by 
      positivity
    have h9 : 0 ≤ (a * b + b * c + c * a) := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (a * b * c)]
  nlinarith [h3, Real.sqrt_nonneg 3, Real.sqrt_nonneg (a * b * c), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (a * b * c) by positivity), 
      h6, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]