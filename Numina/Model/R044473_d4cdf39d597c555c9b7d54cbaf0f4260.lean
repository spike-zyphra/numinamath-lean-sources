import Mathlib

theorem number_theory_14732 {n : ℕ} (hn : n ∈ Finset.Icc 900 950) :
    IsGreatest {p | p.Prime ∧ p ≤ Nat.sqrt n} 29 := by
  rw [Finset.mem_Icc] at hn
  rcases hn with ⟨hn1, hn2⟩
  constructor
  · -- Show 29 is in the set.
    constructor
    · -- Show 29 is prime
      norm_num
    · -- Show 29 ≤ Nat.sqrt n
      have h1 : n ≥ 900 := by linarith
      have h2 : n ≤ 950 := by linarith
      have h3 : n ≥ 900 := by linarith
      have h4 : Nat.sqrt n ≥ 30 := by
        have h5 : n ≥ 900 := by linarith
        have h6 : Nat.sqrt 900 = 30 := by norm_num [Nat.sqrt]
        have h7 : Nat.sqrt n ≥ Nat.sqrt 900 := by
          apply Nat.sqrt_le_sqrt
          linarith
        rw [h6] at h7
        linarith
      have h5 : (29 : ℕ) ≤ Nat.sqrt n := by
        have h6 : Nat.sqrt n ≥ 30 := h4
        omega
      exact h5
  · -- Show no greater element is in the set
    intro p hp
    rcases hp with ⟨h_prime, hp1⟩
    have h8 : n ≤ 950 := by linarith
    have h9 : Nat.sqrt n = 30 := by
      have h10 : n ≥ 900 := by linarith
      have h11 : n ≤ 950 := by linarith
      interval_cases n <;> norm_num [Nat.sqrt]
    rw [h9] at hp1
    by_contra h
    push_neg at h
    have h2 : p ≥ 30 := by omega
    have h3 : p = 30 := by omega
    rw [h3] at h_prime
    norm_num at h_prime