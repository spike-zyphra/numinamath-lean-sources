import Mathlib

theorem number_theory_310844 (p : ℕ) (hp : Nat.Prime p) (h : 5 ≤ p)
    (h1 : Nat.Prime (2 * p + 1)) : ¬Nat.Prime (4 * p + 1) := by
  have hp1 : p % 3 = 1 ∨ p % 3 = 2 := by
    have h11 : p % 3 = 1 ∨ p % 3 = 2 := by
      by_contra h2
      push_neg at h2
      have h22 : p % 3 = 0 := by 
        omega
      have h222 : p > 3 := by 
        linarith
      have h33 : ¬Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals nlinarith
      contradiction 
    assumption
  rcases hp1 with (hp1 | hp1)
  · -- Assume p ≡ 1 (mod 3)
    have h2 : (2 * p + 1) % 3 = 0 := by
      omega
    have h3 : ¬ Nat.Prime (2 * p + 1) := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (2 * p + 1) by omega)
      all_goals
      omega
    contradiction
  · -- Assume p ≡ 2 (mod 3)
    have h2 : (4 * p + 1) % 3 = 0 := by
      omega
    have h4 : ¬Nat.Prime (4 * p + 1) := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (4 * p + 1) by omega)
      all_goals
      omega
    exact h4