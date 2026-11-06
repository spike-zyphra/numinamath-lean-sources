import Mathlib

open Real
open scoped BigOperators

theorem inequalities_55530 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a^2 * (b / c - 1) + b^2 * (c / a - 1) + c^2 * (a / b - 1) ≥ 0 := by

  have h1 : 0 < a * b * c := by
    positivity
  
  have eq1 : a^2 * (b / c - 1) + b^2 * (c / a - 1) + c^2 * (a / b - 1) =
      (a^2 * b / c + b^2 * c / a + c^2 * a / b) - (a^2 + b^2 + c^2) := by
    field_simp
    <;> ring
  
  rw [eq1]

  have h2 : a^2 * b / c + b^2 * c / a + c^2 * a / b ≥ a^2 + b^2 + c^2 := by

    have eq4 : a^2 * b / c + b^2 * c / a + c^2 * a / b - (a^2 + b^2 + c^2) ≥ 0 := by
      have h3' : 0 < a * b * c := h1
      have h4 : a^2 * b / c + b^2 * c / a + c^2 * a / b - (a^2 + b^2 + c^2) =
        ( (a^3 * b^2 ) + (b^3 * c^2 ) + (c^3 * a^2 ) - ( (a^2 + b^2 + c^2 ) * a * b * c ) ) / (a * b * c ) := by
        field_simp
        <;> ring_nf
        <;> field_simp
        all_goals ring
  
      rw [h4]

      have h5 : ( a^3 * b^2 + b^3 * c^2 + c^3 * a^2 ) ≥ ( (a^2 + b^2 + c^2 ) * a * b * c ) := by 

        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a + b - c by linarith) (show 0 < a + c - b by linarith),
          mul_pos (show 0 < a + b - c by linarith) (show 0 < b + c - a by linarith),
          mul_pos (show 0 < a + c - b by linarith) (show 0 < b + c - a by linarith) ]

      have denominators : 0 < a * b * c := h1
      apply div_nonneg
      linarith
      all_goals positivity
  
    linarith
  
  linarith
  all_goals linarith
  all_goals positivity
  all_goals linarith