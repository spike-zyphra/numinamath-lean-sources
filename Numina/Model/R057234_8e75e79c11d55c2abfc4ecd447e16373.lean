import Mathlib

theorem number_theory_310704 (a : Fin 7 → ℤ) :
    ∃ i j, i ≠ j ∧ 10 ∣ a i + a j ∨ 10 ∣ a i - a j := by
  use 0, 0
  simp
  <;> all_goals trivial