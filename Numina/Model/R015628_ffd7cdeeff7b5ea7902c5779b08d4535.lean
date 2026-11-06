import Mathlib

open Real
open scoped BigOperators

theorem inequalities_7076 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) (S : ℝ)
  (hS : S = (a + b - c) ^ 2 + (b + c - a) ^ 2 + (c + a - b) ^ 2) :
  (a ^ 2 + b ^ 2) / (a + b) + (b ^ 2 + c ^ 2) / (b + c) +
  (c ^ 2 + a ^ 2) / (c + a) ≤ 3 * S / (a + b + c) := by

  have h1 : 0 < a + b := by linarith
  have h2 : 0 < b + c := by linarith
  have h3 : 0 < c + a := by linarith
  have h4 : 0 < a + b + c := by linarith

  have h5 : (a + b + c) > 0 := by linarith
  have hS1 : 0 < S := by
    rw [hS]
    nlinarith [sq_pos_of_pos (show (a + b - c : ℝ) > 0 by linarith), 
      sq_pos_of_pos (show (b + c - a : ℝ) > 0 by linarith), 
      sq_pos_of_pos (show (c + a - b : ℝ) > 0 by linarith)]

  have h7 : (a ^ 2 + b ^ 2) / (a + b) + (b ^ 2 + c ^ 2) / (b + c) + (c ^ 2 + a ^ 2) / (c + a) - 3 * S / (a + b + c) ≤ 0 := by

    have h8 : 0 < (a + b) * (b + c) * (c + a) * (a + b + c) := by
      positivity

    have h9 : (a ^ 2 + b ^ 2) / (a + b) + (b ^ 2 + c ^ 2) / (b + c) + (c ^ 2 + a ^ 2) / (c + a) - 3 * S / (a + b + c) =
        ( (a ^ 2 + b ^ 2) * (b + c) * (c + a) * (a + b + c) + (b ^ 2 + c ^ 2) * (a + b) * (c + a) * (a + b + c) + (c ^ 2 + a ^ 2) * (a + b) * (b + c) * (a + b + c) - 3 * S * (a + b) * (b + c) * (c + a) ) / ((a + b) * (b + c) * (c + a) * (a + b + c)) := by
      field_simp
      ring

    rw [h9] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is nonpositive
      have h12 : (a ^ 2 + b ^ 2) * (b + c) * (c + a) * (a + b + c) + (b ^ 2 + c ^ 2) * (a + b) * (c + a) * (a + b + c) + (c ^ 2 + a ^ 2) * (a + b) * (b + c) * (a + b + c) - 3 * S * (a + b) * (b + c) * (c + a) ≤ 0 := by
        rw [hS]
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg ( (a + b - c) - (b + c - a) ), sq_nonneg ( (b + c - a) - (c + a - b) ), sq_nonneg ( (c + a - b) - (a + b - c) ), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
          mul_pos (sub_pos.mpr h'') (sub_pos.mpr h), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          mul_pos (sub_pos.mpr h) (show (a * b) > 0 by nlinarith), 
          mul_pos (sub_pos.mpr h') (show (b * c) > 0 by nlinarith), 
          mul_pos (sub_pos.mpr h'') (show (c * a) > 0 by nlinarith)
        ]
      linarith

    · -- Show that the denominator is nonnegative
      positivity

  linarith