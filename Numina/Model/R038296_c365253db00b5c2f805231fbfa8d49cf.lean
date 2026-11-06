import Mathlib

theorem number_theory_291729 : ∃ k, Function.Periodic (fun n => (41 * 10 ^ n) % 61) k := by
  use 0
  all_goals simp [Function.Periodic]