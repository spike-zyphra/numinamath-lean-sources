import Mathlib

theorem algebra_303065 {l w p : ℝ} (hl : l > 0) (hw : w > 0) (hp : p > 0)
    (h : l * w = (l * (1 + p / 100)) * (w * (1 - x / 100))) :
    x = 100 * p / (100 + p) := by
  have hw_eq : l * w > 0 := mul_pos hl hw
  have eq1 : 1 = (1 + p / 100) * (1 - x / 100) := by
    have hw_eq' : l * w ≠ 0 := by positivity
    apply (mul_left_inj' hw_eq').mp
    nlinarith
    all_goals linarith
  have eq2 : (100 + p) * x = 100 * p := by
    ring_nf at eq1
    nlinarith
    all_goals linarith
  have hp' : (100 + p) ≠ 0 := by linarith
  have hx : x = (100 * p) / (100 + p) := by
    field_simp [show 100 + p ≠ 0 by linarith]
    nlinarith
    all_goals linarith
  rw [hx]
  <;> field_simp [show 100 + p ≠ 0 by linarith]
  <;> nlinarith