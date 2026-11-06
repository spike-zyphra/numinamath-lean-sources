import Mathlib

open Real

theorem calculus_3968 {a : ℝ} (ha : a > 0) (f : ℝ → ℝ) (hf : f = fun x => a ^ x) :
    deriv f = fun x => a ^ x * log a := by
  rw [hf]
  funext x
  simp [Real.rpow_def_of_pos ha, mul_comm]
  all_goals
    ring_nf
    all_goals
      field_simp [Real.log_pos]
      all_goals
        ring