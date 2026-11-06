import Mathlib

theorem number_theory_96872 (p : ℕ) (hp : Nat.Prime p) :
¬ Nat.Prime (p ^ 2 + 26) := by
  by_cases h : p ≤ 3
  · -- If p ≤ 3, then p must be 2 or 3
    interval_cases p <;> norm_num at hp ⊢ <;> tauto
  · -- p > 3
    have h1 : p > 3 := by
      by_contra h1
      push_neg at h1
      linarith
    -- Now p > 3, so p is not divisible by 2 or 3
    have h2 : p % 2 = 1 := by
      by_contra h2
      push_neg at h2
      have h2' : p % 2 = 0 := by omega
      have h2 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals nlinarith
      contradiction
    have h3 : p % 3 = 1 ∨ p % 3 = 2 := by 
      by_contra h3
      push_neg at h3
      have h3' : p % 3 = 0 := by omega
      have h3 : ¬ Nat.Prime p := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals nlinarith 
      contradiction 
    -- Now we show that p^2 + 26 is divisible by 3 
    -- So it's composite, since it's greater than 3 
    have h4 : (p ^ 2 + 26) % 3 = 0 := by 
      rcases h3 with (h3 | h3) 
      · -- p ≡ 1 (mod 3) 
        simp [Nat.add_mod, Nat.mul_mod, pow_two, h3] 
      · -- p ≡ 2 (mod 3) 
        simp [Nat.add_mod, Nat.mul_mod, pow_two, h3] 
    -- Now, since p > 3, we have p^2 + 26 > 3 
    have h5 : p ^ 2 + 26 > 3 := by 
      nlinarith [show p ≥ 4 from by nlinarith] 
    -- Therefore, p^2 + 26 is not prime 
    apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p ^ 2 + 26 by omega) 
    all_goals nlinarith