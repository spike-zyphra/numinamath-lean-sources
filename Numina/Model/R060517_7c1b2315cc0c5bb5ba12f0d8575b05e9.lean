import Mathlib

theorem algebra_2447 {a : ℝ} (ha : a < 0) : √(a^2) + √((1 - a)^2) = 1 - 2 * a := by
  have h1 : √(a^2) = -a := by
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_neg ha]
    all_goals linarith
  have h2 : √((1 - a)^2) = 1 - a := by
    rw [Real.sqrt_sq_eq_abs]
    -- Show that 1 - a ≥ 0
    have h3 : 1 - a ≥ 0 := by linarith
    rw [abs_of_nonneg h3]
    all_goals linarith
  rw [h1, h2]
  ring