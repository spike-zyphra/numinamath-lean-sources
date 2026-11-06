import Mathlib

open Real
open scoped BigOperators

theorem inequalities_80292 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  3 * (a ^ 4 + b ^ 4 + c ^ 4) / (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 +
  (b * c + c * a + a * b) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 := by
  have h0 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h1 : a + b + c > 0 := by
    linarith [show a > 0 by linarith, show b > 0 by linarith, show c > 0 by linarith]
  have h6 : (a^2 + b^2 + c^2) ^ 2 > 0 := by positivity
  have h8 : a^2 + b^2 + c^2 > 0 := by positivity
  have h3 : 3 * (a ^ 4 + b ^ 4 + c ^ 4) / (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 +
  (b * c + c * a + a * b) / (a ^ 2 + b ^ 2 + c ^ 2) - 2 ≥ 0 := by
    have h4 : 3 * (a ^ 4 + b ^ 4 + c ^ 4) / (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 +
      (b * c + c * a + a * b) / (a ^ 2 + b ^ 2 + c ^ 2) - 2 =
      (3 * (a ^ 4 + b ^ 4 + c ^ 4) + (b * c + c * a + a * b) * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ) / ((a ^ 2 + b ^ 2 + c ^ 2) ^ 2) := by 
      field_simp
      ring
      <;> nlinarith
    rw [h4]
    have h5 : 3 * (a ^ 4 + b ^ 4 + c ^ 4) + (b * c + c * a + a * b) * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          sq_nonneg (a * b + b * c + c * a - (a^2 + b^2 + c^2)), 
          sq_nonneg (a^2 + b^2 + c^2 - a * b - b * c - c * a), 
          mul_pos (show 0 < a + b - c by linarith) (show 0 < a + c - b by linarith), 
          mul_pos (show 0 < a + c - b by linarith) (show 0 < b + c - a by linarith), 
          mul_pos (show 0 < b + c - a by linarith) (show 0 < a + b - c by linarith) ]
    apply div_nonneg
    linarith
    positivity
  linarith