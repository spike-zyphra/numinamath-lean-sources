import Mathlib

open Nat

def is_perfect_square (n : ℕ) := ∃ m, m^2 = n

theorem number_theory_775 :
    IsGreatest {n | is_perfect_square n ∧ n ∣ 7 !} 144 := by
  constructor
  · -- Show 144 is in the set.
    constructor
    · -- Show 144 is a perfect square.
      use 12
      all_goals norm_num
    · -- Show 144 divides 7!.
      norm_num [Nat.factorial]
  · -- Show that no greater element is in the set.
    intro n hn
    rcases hn with ⟨h1, h2⟩
    rcases h1 with ⟨m, hm⟩
    by_contra h
    push_neg at h
    -- We have n > 144, so m > 12.
    have h3 : m > 12 := by
      by_contra h4
      push_neg at h4
      have : m ≤ 12 := by linarith
      have : m ^ 2 ≤ 144 := by
        nlinarith [show m ≤ 12 by linarith]
      nlinarith [hm, this, h]
    -- We have m^2 divides 7!.
    have h4 : m^2 ∣ 7! := by
      rw [show n = m ^ 2 by linarith [hm]] at h2
      exact h2
    -- We have m <= 71, since m^2 divides 7! = 5040
    have h5 : m ≤ 71 := by
      by_contra h
      push_neg at h
      have h6 : m ^ 2 > 7! := by
        have h8 : m ≥ 72 := by linarith
        have h9 : m ^ 2 ≥ 72^2 := by nlinarith [h8]
        norm_num [Nat.factorial] at *
        all_goals nlinarith
      have h9 : m ^ 2 ∣ 7! := h4
      have h10 : m ^ 2 ≤ 7! := by
        exact Nat.le_of_dvd (by positivity) h9
      linarith [h6, h10]
    -- Now find contradiction
    interval_cases m <;> norm_num [Nat.factorial] at h4 hm <;> omega