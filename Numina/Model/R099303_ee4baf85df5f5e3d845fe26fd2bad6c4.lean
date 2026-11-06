import Mathlib

open Finset

theorem number_theory_64517 {A : ℕ → ℕ}
    (hA : ∀ n, A n = ∏ k ∈ Icc 1 n, Nat.choose (k ^ 2) k) :
    IsLeast {n | 0 < n ∧ (A n) % 10 = 0} 4 := by
  constructor
  · -- Show $4$ is in the set.
    constructor
    · norm_num -- Show that 4 is positive
    · -- Show $A\ 4$ ends in 0
      rw [hA]
      have h1 : (∏ k in Icc 1 4, Nat.choose (k ^ 2) k) = 917280 := by 
        native_decide
      rw [h1]
      all_goals norm_num
  · -- Show that 4 is the smallest.
    intro n hn
    rcases hn with ⟨hn_pos, hn_10⟩
    by_contra h
    push_neg at h
    have h2 : n < 4 := by linarith 
    interval_cases n <;> norm_num [hA] at hn_10 <;> all_goals contradiction
    all_goals try { contradiction }
    all_goals try { linarith }
    all_goals contradiction