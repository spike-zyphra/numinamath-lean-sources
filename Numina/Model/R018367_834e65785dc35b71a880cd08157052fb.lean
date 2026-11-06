import Mathlib

theorem number_theory_102955 : IsLeast {n | n > 100 ∧ n ∣ Nat.factorial 100} 102 := by

  constructor
  · -- Show that 102 is in the set.
    constructor
    · norm_num
    · native_decide
  · -- Show that 102 is the smallest in the set.
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    have h1 : n < 102 := by linarith
    have h2 : n > 100 := by linarith
    have h3 : n = 101 := by
      omega
    rw [h3] at hn2
    have h4 : ¬ (101 ∣ Nat.factorial 100) := by
      native_decide
    contradiction