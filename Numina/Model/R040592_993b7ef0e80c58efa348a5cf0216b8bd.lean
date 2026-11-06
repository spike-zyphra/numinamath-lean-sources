import Mathlib
open Real

theorem algebra_291411 {a b : ℝ} (ha : a > 0) (hb : b > 0) (hab: a ≠ b) :
    sqrt ((2 * (a ^ 2 - a * b) / (35 * b)) * (10 * a / (7 * (a * b - b ^ 2)))) = 2*a / (7 * b) := by
  have h1 : a * b - b ^ 2 = b * (a - b) := by ring
  have h2 : a ^ 2 - a * b = a * (a - b) := by ring
  have h3 : a - b ≠ 0 := by
    intro h
    apply hab
    linarith
  have h4 : (2 * (a ^ 2 - a * b) / (35 * b)) * (10 * a / (7 * (a * b - b ^ 2))) = (2 * a / (7 * b)) ^ 2 := by
    rw [show a * b - b ^ 2 = b * (a - b) by linarith [h1], show a ^ 2 - a * b = a * (a - b) by linarith [h2]]
    have h5 : a - b ≠ 0 := h3
    field_simp [(show b ≠ 0 by linarith), h5, (show b * (a - b) ≠ 0 by
      apply mul_ne_zero
      · linarith
      · exact h5
    ), (show 7 * b ≠ 0 by
      apply mul_ne_zero
      · norm_num
      · linarith
    )
    ]
    <;> ring_nf <;> norm_num
  rw [h4]
  have h7 : sqrt ((2 * a / (7 * b)) ^ 2) = (2 * a / (7 * b)) := by
    rw [Real.sqrt_sq_eq_abs]
    have ha7 : (2 * a / (7 * b)) > 0 := by
      apply div_pos
      · -- Show 2 * a > 0
        nlinarith
      · -- Show 7 * b > 0
        positivity
    rw [abs_of_pos ha7]
  rw [h7]
  all_goals field_simp [(show b ≠ 0 by linarith)]
  <;> linarith