import Mathlib

theorem number_theory_201149 (p : ℕ) (hp : p.Prime) :
    (p^2 + 8).Prime ↔ p = 3 := by 
  constructor
  · -- Assume (p^2 + 8).Prime, prove p = 3
    intro h
    by_cases h1 : p ≤ 3
    · -- p must be 2 or 3
      interval_cases p <;> norm_num at hp h <;> tauto
    · -- p > 3
      have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
        have h3 : p % 3 ≠ 0 := by
          by_contra h4
          have h5 : 3 ∣ p := by omega
          have h6 : p ≠ 3 := by linarith
          have h7 : ¬p.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
          contradiction
        omega
      have h8 : (p^2) % 3 = 1 := by
        rcases h2 with (h9 | h10)
        · -- p ≡ 1 (mod 3)
          norm_num [Nat.pow_mod, h9] 
        · -- p ≡ 2 (mod 3)
          norm_num [Nat.pow_mod, h10]
      have h9 : (p^2 + 8) % 3 = 0 := by
        omega
      have h10 : 3 ∣ (p^2 + 8) := by
        omega
      have h11 : ¬(p^2 + 8).Prime := by
        apply Nat.not_prime_of_dvd_of_lt h10 (by nlinarith) (by nlinarith)
      contradiction
  · -- Assume p = 3, prove (p^2 + 8).Prime
    intro h
    rw [h]
    norm_num