import Mathlib

theorem number_theory_3121 :
    IsGreatest {n | n ∈ Finset.Icc 100 999 ∧ 3 ∣ (Nat.divisors n).card} 996 := by
  constructor
  · -- Show 996 is in the set: it's in the range and 3 divides its number of divisors
    constructor
    · -- Show 996 is in the range [100, 999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show 3 divides the number of divisors of 996
      native_decide
  · -- Show that for any n in the set, n ≤ 996
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn3, hn4⟩
    by_contra h
    push_neg at h
    have h1 : n = 997 ∨ n = 998 ∨ n = 999 := by
      omega
    rcases h1 with (r | r | r)
    · -- Let's first compute the number of divisors of 997
      rw [r] at hn2
      have h2 : ¬ (3 ∣ (Nat.divisors 997).card) := by
        native_decide
      exact h2 hn2
    · -- Let's compute the number of divisors of 998
      rw [r] at hn2
      have h2 : ¬ (3 ∣ (Nat.divisors 998).card) := by
        native_decide
      exact h2 hn2
    · -- Let's compute the number of divisors of 999
      rw [r] at hn2
      have h2 : ¬ (3 ∣ (Nat.divisors 999).card) := by
        native_decide
      exact h2 hn2