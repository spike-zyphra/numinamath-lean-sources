import Mathlib

theorem algebra_16828 : IsLeast {x : ℕ | 1 < x ∧ x.Coprime 120} 7 := by
  constructor
  · -- Show that 7 is in the set
    constructor
    · norm_num
    · norm_num [Nat.Coprime]
  · -- Show that 7 is minimal
    intro y hy
    rcases hy with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    interval_cases y <;> norm_num [Nat.Coprime] at h2 <;> omega