import Mathlib

theorem number_theory_198790 :
    ∃ M : Finset ℕ, M.min = 1 ∧ M.max = 100 ∧ ∀ x ∈ M, x ≠ 1 → ∃ a b, a ∈ M ∧ b ∈ M ∧ x = a + b ∨ x = 2 * a := by
  use {1, 2, 3, 6, 12, 24, 25, 50, 100}
  constructor
  · -- Show that M.min = 1
    native_decide
  constructor
  · -- Show that M.max = 100
    native_decide
  · -- Show that ∀ x ∈ M, x ≠ 1 → ∃ a b, a ∈ M ∧ b ∈ M ∧ x = a + b ∨ x = 2 * a
    intro x hx hx1
    have hx2 : x = 2 ∨ x = 3 ∨ x = 6 ∨ x = 12 ∨ x = 24 ∨ x = 25 ∨ x = 50 ∨ x = 100 := by
      simp [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      omega
    rcases hx2 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- x = 2
      use 1, 1
      all_goals simp
    · -- x = 3
      use 1, 2
      all_goals simp
    · -- x = 6
      use 3, 3
      all_goals simp
    · -- x = 12
      use 6, 6
      all_goals simp
    · -- x = 24
      use 12, 12
      all_goals simp
    · -- x = 25
      use 1, 24
      all_goals simp
    · -- x = 50
      use 25, 0
      all_goals simp
    · -- x = 100
      use 50, 0
      all_goals simp