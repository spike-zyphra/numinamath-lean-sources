import Mathlib


theorem inequalities_43798 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 / b ^ 2 + b ^ 3 / c ^ 2 + c ^ 3 / a ^ 2 ≥ a ^ 2 / b + b ^ 2 / c + c ^ 2 / a := by

  have h1 : 0 < a ^ 2 * b ^ 2 * c ^ 2 := by
    positivity
  have h2 : a ^ 3 / b ^ 2 + b ^ 3 / c ^ 2 + c ^ 3 / a ^ 2 - (a ^ 2 / b + b ^ 2 / c + c ^ 2 / a) ≥ 0 := by
    have h3 : a ^ 3 / b ^ 2 + b ^ 3 / c ^ 2 + c ^ 3 / a ^ 2 - (a ^ 2 / b + b ^ 2 / c + c ^ 2 / a) =
        ( (a ^ 3 - a ^ 2 * b) * (a ^ 2 * c ^ 2) + (b ^ 3 - b ^ 2 * c) * (a ^ 2 * b ^ 2) + (c ^ 3 - c ^ 2 * a) * (b ^ 2 * c ^ 2) ) / (a ^ 2 * b ^ 2 * c ^ 2) := by
      field_simp
      ring
    rw [h3] 
    have h4 : (a ^ 3 - a ^ 2 * b) * (a ^ 2 * c ^ 2) + (b ^ 3 - b ^ 2 * c) * (a ^ 2 * b ^ 2) + (c ^ 3 - c ^ 2 * a) * (b ^ 2 * c ^ 2) ≥ 0 := by
      nlinarith [sq_nonneg (a ^ 2 * b - a * b * c), sq_nonneg (b ^ 2 * c - b * c * a), sq_nonneg (c ^ 2 * a - c * a * b), 
          sq_nonneg (a ^ 2 * c - b ^ 2 * a), sq_nonneg (b ^ 2 * a - c ^ 2 * b), sq_nonneg (c ^ 2 * b - a ^ 2 * c), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (mul_pos ha hb) hc
          ]
    have h5 : a ^ 2 * b ^ 2 * c ^ 2 > 0 := by positivity
    apply div_nonneg 
    · linarith
    · positivity

  linarith