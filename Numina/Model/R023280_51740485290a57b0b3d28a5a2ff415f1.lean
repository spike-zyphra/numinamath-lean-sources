import Mathlib

theorem number_theory_223269 (S : Finset ℕ) (hS : S = {20172017, 20172018, 20172019, 20172020, 20172021}) :
    ∃ x ∈ S, ∀ y ∈ S, x ≠ y → Nat.Coprime x y := by
  use 20172017
  have h1 : 20172017 ∈ S := by
    rw [hS]
    simp
  constructor 
  · -- Show that 20172017 is in S
    exact h1 
  · -- Show that ∀ y ∈ S, 20172017 ≠ y → Nat.Coprime 20172017 y
    intro y hy hne 
    rw [hS] at hy 
    simp at hy
    rcases hy with (rfl | rfl | rfl | rfl | rfl)
    · -- y = 20172017
      exfalso 
      simp at hne 
    · -- y = 20172018 
      norm_num [Nat.Coprime] 
    · -- y = 20172019 
      norm_num [Nat.Coprime] 
    · -- y = 20172020 
      norm_num [Nat.Coprime] 
    · -- y = 20172021 
      norm_num [Nat.Coprime]