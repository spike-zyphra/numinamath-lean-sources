import Mathlib

theorem number_theory_106883 (n : ℕ) (hn : n ≠ 1) :
    n ∣ Nat.factorial (n - 1) + 1 → Nat.Prime n := by
  intro h
  by_contra h1
  push_neg at h1
  have h2 : n > 1 := by
    by_contra h3
    push_neg at h3
    have h4 : n = 0 ∨ n = 1 := by
      omega 
    rcases h4 with (h4 | h4)
    · -- n = 0 
      rw [h4] at h 
      norm_num at h
    · -- n = 1 
      have h4 : n = 1 := by 
        omega
      contradiction
  -- Now proven n > 1.
  have h4 : ¬Nat.Prime n := h1
  have h5 : ∃ p : ℕ, p ≤ n - 1 ∧ p > 1 ∧ p ∣ n := by
    have h6 : n > 1 := h2
    have h7 : ¬Nat.Prime n := h4
    have h9 : ∃ p, p ∣ n ∧ 1 < p ∧ p < n := by 
      rw [Nat.not_prime_iff_exists_dvd_lt (by linarith)] at h7 
      rcases h7 with ⟨p, hp1, hp2, hp3⟩
      refine' ⟨p, by omega, by omega, by omega⟩
    rcases h9 with ⟨p, hp1, hp2, hp3⟩
    refine' ⟨p, by omega, by omega, by omega⟩
  rcases h5 with ⟨p, hp1, hp2, hp3⟩
  have h6 : p ∣ n := hp3 
  have h7 : p ∣ Nat.factorial (n - 1) + 1 := by 
    exact dvd_trans h6 h 
  -- Now shown divisibility of p into factorial and actual expression 
  have h8 : p ∣ Nat.factorial (n - 1) := by 
    apply Nat.dvd_factorial 
    all_goals
      omega
  -- If p divides Nat.factorial (n-1) + 1 and Nat.factorial (n - 1) then p divides their difference.
  have h9 : p ∣ (Nat.factorial (n - 1) + 1) - Nat.factorial (n - 1) := by 
    apply Nat.dvd_sub' 
    · exact h7 
    · exact h8 
  -- The difference is trivial: expression becomes to 1, divisibility of 1 follows.
  have h10 : (Nat.factorial (n - 1) + 1) - Nat.factorial (n - 1) = 1 := by
    omega 
  rw [h10] at h9 
  -- Now divisibility of 1 by p. This is a contradiction: a prime number p divides 1. This is impossible. The inconsistency completes the theorem negating inequality transivity of prime divisibility and factorial part 
  have h11 : p > 1 := hp2 
  have h12 : p ≤ 1 := by 
    exact Nat.le_of_dvd (by linarith) h9 
  linarith