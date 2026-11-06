import Mathlib

theorem number_theory_90701 (f : Fin 1978 → Fin 6) :
    ∃ i, ∃ j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ f i = f j ∧ f i = f k ∧
      (i + 1) = (j + 1) + (k + 1) ∨ (i + 1) = 2 * (j + 1) := by
  use 3
  use 1
  use 2
  simp
  <;> try { tauto }
  all_goals try { native_decide }