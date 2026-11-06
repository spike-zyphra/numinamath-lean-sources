import Mathlib

open Real

theorem algebra_13036 (a b c : ℝ) (ha : 0 < c) (hc : c < b) (hb : b < a) :
    3 ≤ a - c + 1 / ((a - b) * (b - c)) := by
  have h1 : 0 < b - c := by linarith
  have h2 : 0 < a - b := by linarith
  have h3 : 0 < (a - b) * (b - c) := by
    apply mul_pos
    all_goals linarith
  have h4 : a - c = (a - b) + (b - c) := by linarith
  have h5 : a - c + 1 / ((a - b) * (b - c)) - 3 ≥ 0 := by
    have h6 : 0 < (a - b) * (b - c) := h3
    have h7 : a - c + 1 / ((a - b) * (b - c)) - 3 =
        ( (a - c) * (a - b) * (b - c) + 1 - 3 * (a - b) * (b - c) ) / ( (a - b) * (b - c) ) := by 
      field_simp
      <;> ring
    rw [h7]
    have h8 : (a - c) * (a - b) * (b - c) + 1 - 3 * (a - b) * (b - c) ≥ 0 := by
      nlinarith [sq_nonneg ( (a - b) - (b - c) ), sq_nonneg ( (a - b) * (b - c) - 1 ), sq_nonneg ( (a - b) + (b - c) ), 
        mul_pos h2 h1, 
        mul_pos h2 (show 0 < a - b by linarith),
        mul_pos h1 (show 0 < a - b by linarith)
      ]
    apply div_nonneg
    · linarith
    · positivity
  linarith