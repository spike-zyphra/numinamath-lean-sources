import Mathlib

theorem number_theory_234854 (p : ℕ) (hp : Nat.Prime p)
    (hp1 : Nat.Prime (p - 10)) (hp2 : Nat.Prime (p + 10)) :
    Nat.Prime (p - 2) := by
  have h1 : p ≥ 11 := by 
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at hp hp1 hp2 <;> tauto
  by_cases h : p ≤ 23
  · -- p ≤ 23
    interval_cases p <;> norm_num at hp hp1 hp2 ⊢ <;> tauto
  · -- p > 23
    have h2 : p > 23 := by
      omega
    by_cases h3 : p % 3 = 0
    · -- p is divisible by 3
      have h4 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction
    by_cases h4 : p % 3 = 1
    · -- p ≡ 1 (mod 3)
      have h5 : (p - 10) % 3 = 0 := by
        omega
      have h5 : p - 10 > 3 := by
        omega
      have h6 : ¬ Nat.Prime (p - 10) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p - 10) by omega)
        all_goals omega
      contradiction
    · -- p ≡ 2 (mod 3)
      have h5 : (p + 10) % 3 = 0 := by
        omega
      have h6 : p + 10 > 3 := by
        omega
      have h7 : ¬ Nat.Prime (p + 10) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 10) by omega)
        all_goals omega
      contradiction