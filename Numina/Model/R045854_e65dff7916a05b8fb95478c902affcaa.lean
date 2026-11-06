import Mathlib

open Nat Finset

theorem number_theory_4494 :
    (IsLeast {n | 2 ≤ n ∧ ∀ i ∈ range 5, ¬ (n + i).Prime} 24) ∧ ∃ n, 2 ≤ n ∧ ∀ i ∈ range 1000000, ¬ (n + i).Prime := by
  constructor
  · -- Proof that 24 is the least element of the set
    constructor
    · -- Show 24 is in the set
      constructor
      · norm_num
      · -- Show that for all i in range 5, ¬ (24 + i).Prime
        intro i hi
        fin_cases hi <;> norm_num
    · -- Show minimality
      intro n hn
      rcases hn with ⟨hn2, h⟩
      by_contra h'
      push_neg at h'
      have h1 := h 0 (by simp)
      have h2 := h 1 (by simp)
      have h3 := h 2 (by simp)
      have h4 := h 3 (by simp)
      have h5 := h 4 (by simp)
      interval_cases n <;> norm_num at h1 h2 h3 h4 h5
  · -- Show existence of one million consecutive composites
    use ( (1000000 + 1 + 1).factorial + 2)
    constructor
    · -- Show 2 ≤ n
      have h1 : 1000000 + 1 + 1 ≥ 1 := by omega
      have h4 : (1000000 + 1 + 1).factorial ≥ 1 := by
        apply Nat.factorial_pos
      omega
    · -- Show that ∀ i ∈ range 1000000, ¬ (n + i).Prime
      intro i hi
      have h7 : i < 1000000 := by
        simpa using hi
      have h7' : i ≤ 999999 := by omega
      let N := ( (1000000 + 1 + 1).factorial + 2 )
      have h8 : N + i = (1000000 + 1 + 1).factorial + (2 + i) := by omega
      rw [h8]
      have h9 : 2 + i ≥ 2 := by linarith
      have h9' : 2 + i ≤ 1000001 := by
        omega
      have h10 : ¬ ( (1000000 + 1 + 1).factorial + (2 + i) ).Prime := by
        have h11 : ( (1000000 + 1 + 1).factorial + (2 + i) ) = (1000000 + 1 + 1).factorial + (i + 2) := by
          omega
        rw [h11]
        have h12 : (i + 2) ∣ (1000000 + 1 + 1).factorial := by
          apply Nat.dvd_factorial
          all_goals omega
        have h13 : (i + 2) ∣ (1000000 + 1 + 1).factorial + (i + 2) := by
          apply Nat.dvd_add
          · exact h12
          · exact Nat.dvd_refl (i + 2)
        have h14 : ¬ ( (1000000 + 1 + 1).factorial + (i + 2) ).Prime := by
          apply Nat.not_prime_of_dvd_of_lt h13
          all_goals
            nlinarith [ Nat.factorial_pos (1000000 + 1 + 1) ]
        exact h14
      exact h10