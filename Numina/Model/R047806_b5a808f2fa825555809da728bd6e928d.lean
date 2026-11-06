import Mathlib

theorem number_theory_4241 (p : ℕ) (hp : p > 0) (h : Nat.Prime (p - 15)) (h' : Nat.Prime (p + 26)) (h'' : Nat.Prime (p + 42)) : p = 17 := by
  by_cases h1 : p ≤ 47
  · -- p ≤ 47
    interval_cases p <;> norm_num at h h' h'' ⊢ <;> all_goals tauto
  · -- p > 47
    have h2 : p % 2 = 0 ∨ p % 2 = 1 := by
      omega
    rcases h2 with (h2 | h2)
    · -- Assume p % 2 = 0
      have h3 : (p + 42) % 2 = 0 := by
        omega
      have h4 : p + 42 > 2 := by
        omega
      have h5 : ¬Nat.Prime (p + 42) := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (p + 42) by omega)
        all_goals omega
      contradiction
    · -- Assume p % 2 = 1
      have h9 : (p - 15 : ℕ) % 2 = 0 := by
        omega
      have h11 : p - 15 > 2 := by
        omega
      have h12 : ¬Nat.Prime (p - 15) := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (p - 15) by omega)
        all_goals omega
      contradiction