import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_220961 :
  IsLeast {a^7 * b + b^7 * c + c^7 * a + a * b^3 + b * c^3 + c * a^3 |
    (a : ℝ) (b : ℝ) (c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 * b + b^2 * c + c^2 * a = 3)} 6 := by
  constructor
  · -- Show 6 is in the set
    use 1, 1, 1
    norm_num
  · -- Show 6 is minimal 
    intro x hx 
    rcases hx with ⟨a, b, c, ha, hb, hc, h, hx⟩
    have h1 : a^7 * b + a * b^3 ≥ 2 * (a^4 * b^2) := by
      nlinarith [sq_nonneg (a^3 - b), sq_nonneg (a^2 - b^2), sq_nonneg (a^4 - b^2 * a^2), sq_nonneg (a * b - 1), sq_nonneg (a^2 * b - 1), mul_pos ha hb, mul_pos (show 0 < a^2 by positivity) (show 0 < b^2 by positivity) ]
    have h2 : b^7 * c + b * c^3 ≥ 2 * (b^4 * c^2) := by
      nlinarith [sq_nonneg (b^3 - c), sq_nonneg (b^2 - c^2), sq_nonneg (b^4 - c^2 * b^2), sq_nonneg (b * c - 1), sq_nonneg (b^2 * c - 1), mul_pos hb hc, mul_pos (show 0 < b^2 by positivity) (show 0 < c^2 by positivity) ]
    have h3 : c^7 * a + c * a^3 ≥ 2 * (c^4 * a^2) := by
      nlinarith [sq_nonneg (c^3 - a), sq_nonneg (c^2 - a^2), sq_nonneg (c^4 - a^2 * c^2), sq_nonneg (c * a - 1), sq_nonneg (c^2 * a - 1), mul_pos hc ha, mul_pos (show 0 < c^2 by positivity) (show 0 < a^2 by positivity) ]
    have h4 : a^4 * b^2 = (a^2 * b) ^ 2 := by 
      ring
    have h5 : b^4 * c^2 = (b^2 * c) ^ 2 := by 
      ring
    have h6 : c^4 * a^2 = (c^2 * a) ^ 2 := by 
      ring
    have h7 : a^4 * b^2 + b^4 * c^2 + c^4 * a^2 = (a^2 * b) ^ 2 + (b^2 * c) ^ 2 + (c^2 * a) ^ 2 := by
      linarith [h4,h5,h6]
    have h9 : (a^2 * b) ^ 2 + (b^2 * c) ^ 2 + (c^2 * a) ^ 2 ≥ 3 := by
      nlinarith [sq_nonneg (a^2 * b - 1), sq_nonneg (b^2 * c - 1), sq_nonneg (c^2 * a - 1), sq_nonneg (a^2 * b - b^2 * c), sq_nonneg (b^2 * c - c^2 * a), sq_nonneg (c^2 * a - a^2 * b), h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    linarith [ h1, h2, h3, h7, h9, hx ]