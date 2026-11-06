import Mathlib

theorem inequalities_291650 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) :
    13 ≤ (5 + 2 * b + c ^ 2) / (1 + a) + (5 + 2 * c + a ^ 2) / (1 + b) +
        (5 + 2 * a + b ^ 2) / (1 + c) := by
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  have h3 : 0 < 1 + c := by linarith
  have h12 : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity
  have h4 : (5 + 2 * b + c ^ 2) / (1 + a) + (5 + 2 * c + a ^ 2) / (1 + b) + (5 + 2 * a + b ^ 2) / (1 + c) - 13 ≥ 0 := by
    have h5 : (5 + 2 * b + c ^ 2) / (1 + a) + (5 + 2 * c + a ^ 2) / (1 + b) + (5 + 2 * a + b ^ 2) / (1 + c) - 13 = 
        (( (5 + 2 * b + c ^ 2) * (1 + b) * (1 + c) + (5 + 2 * c + a ^ 2) * (1 + a) * (1 + c) + (5 + 2 * a + b ^ 2) * (1 + a) * (1 + b) - 13 * ((1 + a) * (1 + b) * (1 + c)) ) ) / ((1 + a) * (1 + b) * (1 + c)) := by
      field_simp
      ring
    rw [h5]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc 
    ] 
    positivity 
  linarith