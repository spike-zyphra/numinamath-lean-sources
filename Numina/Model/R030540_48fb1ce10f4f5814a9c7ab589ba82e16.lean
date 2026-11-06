import Mathlib

theorem number_theory_178039 (a : Fin 1978 → Fin 6) :
    ∃ i, ∃ j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ a i = a j ∧ a i = a k ∧
      i + 1 = j + 1 + k + 1 ∨ i + 1 = 2 * (j + 1) := by
  use (1 : Fin 1978)
  use (0 : Fin 1978)
  use (2 : Fin 1978)
  simp
  <;> aesop