import Mathlib

open Real
open scoped BigOperators

theorem inequalities_58243 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  2 < (a + b)/c + (b + c)/a + (c + a)/b - (a^3 + b^3 + c^3)/(a*b*c) ∧
  (a + b)/c + (b + c)/a + (c + a)/b - (a^3 + b^3 + c^3)/(a*b*c) ≤ 3 := by
  constructor
  · -- Prove the lower bound: $2 < \frac{a+b}{c} + \frac{b+c}{a} + \frac{c+a}{b} - \frac{a^3+b^3+c^3}{abc}$
    have pos1 : 0 < a * b * c := by positivity
    have h1 : (a + b)/c + (b + c)/a + (c + a)/b - (a^3 + b^3 + c^3)/(a * b * c) - 2 > 0 := by
      have h2 : (a + b)/c + (b + c)/a + (c + a)/b - (a^3 + b^3 + c^3)/(a * b * c) - 2 =
          ( (a + b) * a * b + (b + c) * b * c + (c + a) * a * c - (a^3 + b^3 + c^3) - 2 * a * b * c ) / (a * b * c) := by
        field_simp
        ring
      rw [h2] at *
      apply div_pos
      · -- Prove that the numerator is positive
        nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
            mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)
        ]
      · -- Prove that the denominator is positive
        positivity
    linarith
  · -- Prove the upper bound: $\frac{a+b}{c} + \frac{b+c}{a  + \frac{c+a}{b} - \frac{a^3+b^3+c^3}{abc}\leq 3$
    have pos1 : 0 < a * b * c := by positivity
    have h1 : (a + b)/c + (b + c)/a + (c + a)/b - (a^3 + b^3 + c^3)/(a * b * c) - 3 ≤ 0 := by
      have h2 : (a + b)/c + (b + c)/a + (c + a)/b - (a^3 + b^3 + c^3)/(a * b * c) - 3 =
          ( (a + b) * a * b + (b + c) * b * c + (c + a) * a * c - (a^3 + b^3 + c^3) - 3 * a * b * c ) / (a * b * c) := by
        field_simp
        ring
      rw [h2] at *
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Prove that the numerator is non-positive
        nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
            mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
            sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)
        ]
      · -- Prove that the denominator is non-negative
        positivity
    linarith