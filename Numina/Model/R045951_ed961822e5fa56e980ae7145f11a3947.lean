import Mathlib

theorem number_theory_198297 :
    ∃ s : Fin 100 → ℤ,
      (∀ i, s i = 1 ∨ s i = -1) ∧
      (∑ i, s i * (i + 1)) = 1982 := by
  use fun i =>
    if i ∈ ({53, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99} : Finset (Fin 100)) then
      -1
    else
      1
  constructor
  · -- Show that each entry is either 1 or -1
    intro i
    simp
    <;> omega
  · -- Show that the sum is 1982
    native_decide