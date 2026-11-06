import Mathlib

open Real

theorem inequalities_62152 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 1) :
    sqrt 3 ≤ a * sqrt (b ^ 2 + c ^ 2 + b * c) +
    b * sqrt (c ^ 2 + a ^ 2 + c * a) +
    c * sqrt (a ^ 2 + b ^ 2 + a * b) := by

  have h1 : ∀ x y : ℝ, 0 < x → 0 < y → sqrt (x^2 + y^2 + x * y) ≥ (sqrt 3 / 2) * (x + y) := by
    intro x y hx hy
    have h2 : (sqrt 3 / 2) * (x + y) ≤ sqrt (x ^ 2 + y ^ 2 + x * y) := by
      have h3 : ((sqrt 3 / 2) * (x + y)) ^ 2 ≤ x ^ 2 + y ^ 2 + x * y := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (x - y)]
      have h4 : ((sqrt 3 / 2) * (x + y)) ≥ 0 := by positivity
      have h5 : sqrt (x ^ 2 + y ^ 2 + x * y) ≥ 0 := by positivity
      nlinarith [Real.sq_sqrt (show 0 ≤ x ^ 2 + y ^ 2 + x * y by positivity), h3, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    linarith

  have h2 := h1 b c hb hc
  have h3 := h1 c a hc ha
  have h4 := h1 a b ha hb

  have h5 : a * sqrt (b ^ 2 + c ^ 2 + b * c) +
      b * sqrt (c ^ 2 + a ^ 2 + c * a) +
      c * sqrt (a ^ 2 + b ^ 2 + a * b) ≥ sqrt 3 := by

    have h6 : a * sqrt (b ^ 2 + c ^ 2 + b * c) ≥ a * ((sqrt 3 / 2) * (b + c)) := by 
      have h7 : sqrt (b ^ 2 + c ^ 2 + b * c) ≥ (sqrt 3 / 2) * (b + c) := h2
      nlinarith

    have h7 : b * sqrt (c ^ 2 + a ^ 2 + c * a) ≥ b * ((sqrt 3 / 2) * (c + a)) := by 
      have h8 : sqrt (c ^ 2 + a ^ 2 + c * a) ≥ (sqrt 3 / 2) * (c + a) := h3
      nlinarith

    have h8 : c * sqrt (a ^ 2 + b ^ 2 + a * b) ≥ c * ((sqrt 3 / 2) * (a + b)) := by 
      have h9 : sqrt (a ^ 2 + b ^ 2 + a * b) ≥ (sqrt 3 / 2) * (a + b) := h4
      nlinarith

    have h9 : a * ((sqrt 3 / 2) * (b + c)) + b * ((sqrt 3 / 2) * (c + a)) + c * ((sqrt 3 / 2) * (a + b)) = sqrt 3 := by
      nlinarith [h, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

    linarith [h6, h7, h8, h9]

  linarith [h5]