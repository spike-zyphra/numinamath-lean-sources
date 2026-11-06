import Mathlib

theorem number_theory_6023 : ∃ x : Fin 2 → ℕ, x 0 > 0 ∧ x 1 > 0 ∧ 101 * x 0 + 37 * x 1 = 3189 := by
  use λ i =>
    match i with
    | 0 => 3
    | 1 => 78
    | _ => 0
  constructor
  · -- Show x 0 > 0
    simp
  constructor
  · -- Show x 1 > 0
    simp
  · -- Show 101 * x 0 + 37 * x 1 = 3189
    all_goals simp
    <;> omega