import Mathlib

open Finset

theorem number_theory_239316:
  ∃ S : List ℕ, ∃ p : ℕ, 
    S.length = 2005 ∧ (∀ n ∈ S, ∃ m : ℕ, n = m^2) ∧
  S.sum = p^2 := by

  use (List.replicate 2001 1) ++ (List.replicate 4 100)
  use 49
  constructor
  · -- Show the length is 2005
    native_decide
  constructor
  · -- Show all elements in the list are perfect squares.
    intro n hn
    rw [List.mem_append] at hn
    rcases hn with (hn | hn)
    · -- Case where n is in the first part (1s).
      rw [List.mem_replicate] at hn
      rcases hn with ⟨hn1, hn2⟩
      have hn3 : n = 1 := by
        omega
      rw [hn3]
      use 1
      all_goals
        norm_num
    · -- Case where n is in the second part (100s).
      rw [List.mem_replicate] at hn
      rcases hn with ⟨hn1, hn2⟩
      have hn3 : n = 100 := by
        omega
      rw [hn3]
      use 10
      all_goals
        norm_num
  · -- Show the sum is 49^2.
    native_decide