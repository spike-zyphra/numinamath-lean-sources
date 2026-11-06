import Mathlib

open Real
open scoped BigOperators

theorem number_theory_198301 :
  IsGreatest {x : ℝ | ∃ n : ℕ, n ∈ Finset.Icc 10 99 ∧ x = n / (Nat.digits 10 n).sum} 10 ∧
  IsLeast {x : ℝ | ∃ n : ℕ, n ∈ Finset.Icc 10 99 ∧ x = n / (Nat.digits 10 n).sum} 1.9 := by

  constructor
  · -- Prove that 10 is greatest.
    constructor
    · -- Show that 10 can be obtained from the number 10
      use 10
      norm_num
    · -- Show that if x in the set, x ≤ 10
      intro x
      rintro ⟨n, hn, rfl⟩
      rw [Finset.mem_Icc] at hn
      rcases hn with ⟨hn1, hn2⟩
      interval_cases n <;> norm_num
  · -- Prove that 1.9 is least.
    constructor
    · -- Show that 1.9 is in the set.
      use 19
      norm_num
    · -- Show that if x in the set, 1.9 ≤ x
      intro x
      rintro ⟨n, hn, rfl⟩
      rw [Finset.mem_Icc] at hn
      rcases hn with ⟨hn1, hn2⟩
      interval_cases n <;> norm_num