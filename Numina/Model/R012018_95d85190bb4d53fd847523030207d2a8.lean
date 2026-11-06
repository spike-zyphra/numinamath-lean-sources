import Mathlib


theorem number_theory_178410 (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : q = p + 2) (hqr : r = q + 2) :
    (p, q, r) = (3, 5, 7) := by
  have h1 : r = p + 4 := by
    rw [hqr, hpq]
    all_goals omega
  by_cases h : p ≤ 7
  · -- if p ≤ 7
    interval_cases p <;> norm_num [hpq, h1] at hp hq hr ⊢ <;> tauto
  · -- p > 7
    have h2 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
      omega
    rcases h2 with (h2 | h2 | h2)
    · -- if p ≡ 0 [MOD 3]
      have h3 : ¬ p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction
    · -- if p ≡ 1 [MOD 3]
      have h4 : q % 3 = 0 := by
        have h4 : q = p + 2 := by 
          omega
        rw [h4]
        omega
      have h5 : ¬q.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
        all_goals 
        omega
      contradiction
    · -- if p ≡ 2 [MOD 3]
      have h6 : r % 3 = 0 := by
        have h6 : r = p + 4 := by 
          omega
        rw [h6]
        omega
      have h7 : ¬ r.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ r by omega)
        all_goals 
        omega
      contradiction