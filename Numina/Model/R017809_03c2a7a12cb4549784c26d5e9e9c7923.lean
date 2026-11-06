import Mathlib
open Real

theorem inequalities_8682 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c = 1) :
    1 - (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * √(a * b * c) := by
  have h1 : a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + a * c + b * c) := by
    ring
  rw [h] at h1
  have h2 : 1 - (a ^ 2 + b ^ 2 + c ^ 2) = 2 * (a * b + a * c + b * c) := by
    rw [h1]
    linarith
  rw [h2]
  have h3 : (2 * (a * b + a * c + b * c) : ℝ) ≥ 2 * √(a * b * c) := by
    have h5 : a * b + a * c + b * c ≥ √(a * b * c) := by
      have h4 : (√(a * b * c)) ^ 2 = a * b * c := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith [sq_nonneg (√(a * b * c) - (a * b + a * c + b * c)), Real.sqrt_nonneg (a * b * c),
        sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
        Real.sq_sqrt (show 0 ≤ (a * b * c : ℝ) by positivity)
        ]
    linarith
  linarith