import Mathlib

open Real Set


theorem calculus_138156 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = 3 ^ x * (log 3 * sin (2 * x) - 2 * cos (2 * x)) / (log 3 ^ 2 + 4)) :
    deriv f = fun x => 3 ^ x * sin (2 * x) := by
  have eq1 : f = fun x => (3 ^ x * (log 3 * sin (2 * x) - 2 * cos (2 * x))) / (log 3 ^ 2 + 4) := by
    funext x
    exact h₀ x

  rw [eq1]
  funext x
  simp [deriv_div_const, deriv_mul, Real.rpow_def_of_pos, mul_comm]
  all_goals
    ring_nf
    <;> field_simp [Real.rpow_pos_of_pos, mul_pos (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3)]
  all_goals
    ring_nf
    <;> norm_num
    all_goals
      ring