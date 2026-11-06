import Mathlib

theorem algebra_138138 {G : Type*} [Group G] : ∃! x : G, ∀ y : G, y * x = y := by
  use 1
  constructor
  · -- Show that 1 is the identity
    intro y
    simp
  · -- Show uniqueness
    intro x h
    have h1 := h 1
    simp at h1 ⊢
    all_goals try exact h1