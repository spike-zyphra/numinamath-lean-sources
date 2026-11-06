import Mathlib

open Real Set
open scoped Real

theorem inequalities_278546 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a * cos θ ^ 2 + b * sin θ ^ 2 < c) :
  sqrt a * cos θ ^ 2 + sqrt b * sin θ ^ 2 < sqrt c := by

  have h1 : cos θ ^ 2 + sin θ ^ 2 = 1 := by
    have h2 : cos θ ^ 2 + sin θ ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq θ
    linarith

  have h2 : sqrt a * cos θ ^ 2 + sqrt b * sin θ ^ 2 ≥ 0 := by
    have ha1 : sqrt a ≥ 0 := Real.sqrt_nonneg a
    have hb1 : sqrt b ≥ 0 := Real.sqrt_nonneg b
    have hc1 : cos θ ^ 2 ≥ 0 := by positivity
    have hc2 : sin θ ^ 2 ≥ 0 := by positivity
    nlinarith [mul_nonneg ha1 hc1, mul_nonneg hb1 hc2]

  have h5 : sqrt c ≥ 0 := Real.sqrt_nonneg c

  have h6_sq : (sqrt a * cos θ ^ 2 + sqrt b * sin θ ^ 2) ^ 2 ≤ a * cos θ ^ 2 + b * sin θ ^ 2 := by 
    have h7 : sqrt a ≥ 0 := Real.sqrt_nonneg a
    have h8 : sqrt b ≥ 0 := Real.sqrt_nonneg b
    have h7a : sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
    have h7b : sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
    have h10 : cos θ ^ 2 ≥ 0 := by positivity
    have h11 : sin θ ^ 2 ≥ 0 := by positivity
    have h13 : (a - b) ^ 2 ≥ 0 := by positivity
    have h50 : (sqrt a * cos θ ^ 2 + sqrt b * sin θ ^ 2) ^ 2 = 
      (sqrt a) ^ 2 * cos θ ^ 4 + (sqrt b) ^ 2 * sin θ ^ 4 + 2 * (sqrt a * sqrt b) * (cos θ ^ 2 * sin θ ^ 2) := by ring
    rw [h50]
    rw [show (sqrt a: ℝ) ^ 2 = a by linarith [Real.sq_sqrt (show 0 ≤ a by linarith)]] 
    rw [show (sqrt b: ℝ) ^ 2 = b by linarith [Real.sq_sqrt (show 0 ≤ b by linarith)]]
    nlinarith [sq_nonneg (a - b), sq_nonneg (cos θ ^ 2 - sin θ ^ 2), 
      mul_nonneg (show 0 ≤ (cos θ ^ 2 : ℝ) by positivity) (show 0 ≤ (sin θ ^ 2 : ℝ) by positivity), 
      sq_nonneg (sqrt a * cos θ ^ 2 - sqrt b * sin θ ^ 2), 
      sq_nonneg (sqrt a - sqrt b)
    ]

  have h7_sq_lt_c : (sqrt a * cos θ ^ 2 + sqrt b * sin θ ^ 2) ^ 2 < c := by 
    have h7' : (sqrt a * cos θ ^ 2 + sqrt b * sin θ ^ 2) ^ 2 ≤ a * cos θ ^ 2 + b * sin θ ^ 2 := h6_sq
    nlinarith

  have h4 : sqrt a * cos θ ^ 2 + sqrt b * sin θ ^ 2 < sqrt c := by 
    have h9 : (sqrt a * cos θ ^ 2 + sqrt b * sin θ ^ 2) ≥ 0 := h2
    have h10 : sqrt c ≥ 0 := h5
    have h11 : (sqrt c) ^ 2 = c := by 
      rw [Real.sq_sqrt]
      linarith
    have h12 : (sqrt a * cos θ ^ 2 + sqrt b * sin θ ^ 2) ^ 2 < (sqrt c) ^ 2 := by 
      linarith [h7_sq_lt_c, h11]
    have h14 : sqrt a * cos θ ^ 2 + sqrt b * sin θ ^ 2 < sqrt c := by 
      nlinarith [Real.sqrt_nonneg c, Real.sqrt_nonneg a, Real.sqrt_nonneg b, h12, h9, h10, 
        Real.sq_sqrt (show (0 : ℝ) ≤ c by linarith)]
    exact h14

  exact h4