import Mathlib

def isGood (n : ℕ) : Prop :=
  ∃ k : Finset ℕ, k.card = 5 ∧ ∀ i ∈ k, n + i ∣ n - i ^ 3

theorem number_theory_225171 : isGood 29 := by
  use {0, 4, 5, 6, 7}
  constructor
  · -- Show that the cardinality of the set {0, 4, 5, 6, 7} is 5.
    native_decide
  · -- Show that for each i in {0, 4, 5, 6, 7}, 29 + i divides 29 - i^3.
    intro i hi
    have h1 : i = 0 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
      have h2 : i ∈ ({0, 4, 5, 6, 7} : Finset ℕ) := hi
      simp [Finset.mem_insert, Finset.mem_singleton] at h2 ⊢
      tauto
    rcases h1 with (rfl | rfl | rfl | rfl | rfl)
    · -- i = 0
      norm_num
    · -- i = 4
      norm_num
    · -- i = 5
      norm_num
    · -- i = 6
      norm_num
    · -- i = 7
      norm_num