import Mathlib

open Real
open scoped BigOperators

theorem inequalities_305390 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) ∧
  a / (b + c) + b / (c + a) + c / (a + b) < 2 := by
  constructor
  · -- Prove 3/2 ≤ a / (b + c) + b / (c + a) + c / (a + b)
    have h1 : 0 < b + c := by linarith
    have h2 : 0 < c + a := by linarith
    have h3 : 0 < a + b := by linarith
    have h4 : a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
      have h5 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
        have h6 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
            (2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) := by 
          field_simp
          ring
        rw [h6]
        apply div_nonneg
        · -- Prove the numerator is non-negative
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                    sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                    sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
                    sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
                    sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
                    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
                    mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
                    mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
                    mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
                   ]
        · -- Prove the denominator is positive
          positivity
      linarith
    linarith
  · -- Prove a / (b + c) + b / (c + a) + c / (a + b) < 2
    have h1 : 0 < b + c := by linarith
    have h2 : 0 < c + a := by linarith
    have h3 : 0 < a + b := by linarith
    have h4 : a / (b + c) + b / (c + a) + c / (a + b) < 2 := by
      have h5 : a / (b + c) + b / (c + a) + c / (a + b) - 2 < 0 := by
        have h6 : a / (b + c) + b / (c + a) + c / (a + b) - 2 =
            (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 2 * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by 
          field_simp
          ring
        rw [h6]
        apply div_neg_of_neg_of_pos
        · -- Prove the numerator is negative
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                    sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                    sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
                    sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
                    sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
                    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
                    mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
                    mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
                    mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
                   ]
        · -- Prove the denominator is positive
          positivity
      linarith
    linarith