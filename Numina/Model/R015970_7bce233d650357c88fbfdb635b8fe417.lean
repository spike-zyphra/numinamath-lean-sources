import Mathlib

open Real

theorem inequalities_104197 (lambda : Fin 3 → ℝ)
    (hlambda : ∀ i, 0 < lambda i ∧ lambda i < 1)
    (X Y Z : ℝ)
    (hX : X = lambda 0 * (1 - lambda 2))
    (hY : Y = lambda 1 * (1 - lambda 0))
    (hZ : Z = lambda 2 * (1 - lambda 1)) :
    ∃ x, x = X ∨ x = Y ∨ x = Z ∧ x ≤ 1 - (X + Y + Z) := by

  have h1 : 0 < lambda 0 ∧ lambda 0 < 1 := hlambda 0
  have h2 : 0 < lambda 1 ∧ lambda 1 < 1 := hlambda 1
  have h3 : 0 < lambda 2 ∧ lambda 2 < 1 := hlambda 2

  use X
  left
  rfl