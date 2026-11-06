import Mathlib

open Real
open scoped BigOperators

theorem inequalities_600277 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  2 < (b + c) / a + (c + a) / b + (a + b) / c - (a^3 + b^3 + c^3) / (a * b * c) ∧
  (b + c) / a + (c + a) / b + (a + b) / c - (a^3 + b^3 + c^3) / (a * b * c) ≤ 3 := by
  have h₁ : 0 < a * b * c := by positivity
  have h₂ : 0 < a * b := by positivity
  have h₃ : 0 < a * c := by positivity
  have h₄ : 0 < b * c := by positivity
  have h₅ : 0 < a * b * c := h₁
  constructor
  · -- Prove the lower bound: 2 < (b + c) / a + (c + a) / b + (a + b) / c - (a^3 + b^3 + c^3) / (a * b * c)
    have h6 : (b + c) / a + (c + a) / b + (a + b) / c - (a^3 + b^3 + c^3) / (a * b * c) > 2 := by
      have h7 : 0 < a * b * c := h₅
      have h8 : (b + c) / a + (c + a) / b + (a + b) / c - (a^3 + b^3 + c^3) / (a * b * c) - 2 > 0 := by
        have h9 : 0 < a * b * c := h₅
        have h10 : ( (b + c) / a + (c + a) / b + (a + b) / c - (a^3 + b^3 + c^3) / (a * b * c) - 2 ) =
            ( (b + c) * b * c + (c + a) * a * c + (a + b) * a * b - (a^3 + b^3 + c^3) - 2 * (a * b * c) ) / (a * b * c) := by
          field_simp
          <;> ring
        rw [h10]
        apply div_pos
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
            mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)
          ]
        all_goals positivity
      linarith
    linarith
  · -- Prove the upper bound: (b + c) / a + (c + a) / b + (a + b) / c - (a^3 + b^3 + c^3) / (a * b * c) ≤ 3
    have h7 : (b + c) / a + (c + a) / b + (a + b) / c - (a^3 + b^3 + c^3) / (a * b * c) ≤ 3 := by
      have h8 : (b + c) / a + (c + a) / b + (a + b) / c - (a^3 + b^3 + c^3) / (a * b * c) - 3 ≤ 0 := by
        have h9 : 0 < a * b * c := h₅
        have h10 : ( (b + c) / a + (c + a) / b + (a + b) / c - (a^3 + b^3 + c^3) / (a * b * c) - 3 ) =
            ( (b + c) * b * c + (c + a) * a * c + (a + b) * a * b - (a^3 + b^3 + c^3) - 3 * (a * b * c) ) / (a * b * c) := by
          field_simp
          <;> ring
        rw [h10]
        apply div_nonpos_of_nonpos_of_nonneg
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
            sq_nonneg (a * (a - b) + a * (a - c) + a * (b - c)), 
            sq_nonneg (b * (a - b) + b * (a - c) + b * (b - c)), 
            sq_nonneg (c * (a - b) + c * (a - c) + c * (b - c)), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
            mul_pos (sub_pos.mpr h') (sub_pos.mpr h'') 
          ]
        all_goals positivity
      linarith
    linarith