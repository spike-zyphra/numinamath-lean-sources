import Mathlib

open Real
open scoped BigOperators

theorem inequalities_600768 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  2 ≤ 3 * (a ^ 4 + b ^ 4 + c ^ 4) / (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 +
      (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) := by
  have h1 : 0 < a ^ 2 + b ^ 2 + c ^ 2 := by
    nlinarith
  have h2 : 0 < (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
    nlinarith
  have h3 : 3 * (a ^ 4 + b ^ 4 + c ^ 4) + (a * b + b * c + c * a) * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
      sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
      mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
      mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
      mul_pos (sub_pos.mpr h) (sub_pos.mpr h'')
      ]
  have h4 : 3 * (a ^ 4 + b ^ 4 + c ^ 4) / (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 
          (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 := by
    have h9 : 3 * (a ^ 4 + b ^ 4 + c ^ 4) / (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 
          (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) - 2 ≥ 0 := by
      have h9 : 3 * (a ^ 4 + b ^ 4 + c ^ 4) / (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 
          (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) - 2 = 
          (3 * (a ^ 4 + b ^ 4 + c ^ 4) + (a * b + b * c + c * a) * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) / ((a ^ 2 + b ^ 2 + c ^ 2) ^ 2) := by
        field_simp
        ring
      rw [h9]
      apply div_nonneg
      linarith 
      all_goals nlinarith 
    linarith 
  linarith