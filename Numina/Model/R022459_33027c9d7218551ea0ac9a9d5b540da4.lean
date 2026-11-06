import Mathlib

theorem number_theory_310230 (p : ℕ) (hp : p.Prime) (h : (8 * p ^ 2 + 1).Prime) :
    (8 * p ^ 2 - p + 2).Prime := by
  by_cases h1 : p ≤ 3
  · -- p ≤ 3, so p is 2 or 3.
    interval_cases p <;> norm_num at hp h ⊢ <;> tauto
  · -- p > 3
    have h2 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
      omega
    rcases h2 with (h2 | h2 | h2)
    · -- p % 3 = 0
      have h3 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction
    · -- p % 3 = 1
      have h3 : (8 * p ^ 2 + 1) % 3 = 0 := by
        have hp1 : p % 3 = 1 := h2
        simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, hp1]
        <;> omega
      have h4 : 3 < (8 * p ^ 2 + 1) := by
        have hp1 : p > 3 := by omega
        have hp2 : p ≥ 4 := by omega
        have h31 : 8 * p ^ 2 + 1 ≥ 8 * 4 ^ 2 + 1 := by
          have : p ^ 2 ≥ 16 := by
            nlinarith
          nlinarith
        nlinarith
      have h5 : ¬(8 * p ^ 2 + 1).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (8 * p ^ 2 + 1) by omega)
        all_goals nlinarith
      contradiction
    · -- p % 3 = 2
      have h3 : (8 * p ^ 2 + 1) % 3 = 0 := by
        have hp1 : p % 3 = 2 := h2
        simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, hp1]
        <;> omega
      have h4 : 3 < (8 * p ^ 2 + 1) := by
        have hp1 : p > 3 := by omega
        have hp2 : p ≥ 4 := by omega
        have h31 : 8 * p ^ 2 + 1 ≥ 8 * 4 ^ 2 + 1 := by
          have : p ^ 2 ≥ 16 := by
            nlinarith
          nlinarith
        nlinarith
      have h5 : ¬(8 * p ^ 2 + 1).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (8 * p ^ 2 + 1) by omega)
        all_goals nlinarith
      contradiction