import Mathlib

theorem number_theory_128072 (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (hp4 : (p + 4).Prime) :
    p = 3 := by
  by_cases h3 : p ≤ 3
  · interval_cases p <;> norm_num at hp hp2 hp4 <;> omega
  · -- Assume p > 3, then p is not prime
    push_neg at h3
    have h1 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h1 with (h | h | h)
    · -- If p % 3 = 0
      have h5 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction
    · -- If p % 3 = 1
      have h6 : (p + 2) % 3 = 0 := by omega
      have h7 : ¬(p + 2).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 2) by omega)
        all_goals omega
      contradiction
    · -- If p % 3 = 2
      have h7 : (p + 4) % 3 = 0 := by omega
      have h8 : ¬(p + 4).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 4) by omega)
        all_goals omega
      contradiction