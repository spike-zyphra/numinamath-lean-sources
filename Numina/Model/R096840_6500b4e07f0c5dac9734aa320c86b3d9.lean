import Mathlib

theorem number_theory_139231 (p : ℕ) (hp : Nat.Prime p)
    (h : Nat.Prime (p^2 + 2)) : Nat.Prime (p^3 + 2) := by
  by_cases h1 : p ≤ 3
  · -- p is smaller than 4, so p can be 2 or 3
    interval_cases p <;> norm_num at hp h <;> norm_num at *
    <;> try trivial
    <;> contradiction
  · -- Now assume p > 3. Let's show that p^2 + 2 is composite.
    have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
      by_contra h
      push_neg at h
      have h3 : p % 3 = 0 := by
        omega
      have h4 : 3 ∣ p := by 
        omega
      have h5 : p > 3 := by
        linarith
      have h6 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt h4 (by norm_num) (by nlinarith)
      contradiction
    rcases h2 with (h2 | h2)
    · -- Case where p ≡ 1 (mod 3)
      have h3 : (p ^ 2) % 3 = 1 := by
        simp [Nat.pow_mod, h2]
      have h4 : (p^2 + 2) % 3 = 0 := by 
        omega
      have h5 : 3 ∣ (p^2 + 2) := by 
        omega
      have h6 : p > 3 := by 
        linarith
      have h8 : ¬ Nat.Prime (p^2 + 2) := by
        apply Nat.not_prime_of_dvd_of_lt h5 (by norm_num) (by nlinarith)
      contradiction
    · -- Case where p ≡ 2 (mod 3)
      have h3 : (p ^ 2) % 3 = 1 := by
        simp [Nat.pow_mod, h2]
      have h4 : (p^2 + 2) % 3 = 0 := by 
        omega
      have h5 : 3 ∣ (p^2 + 2) := by 
        omega
      have h6 : p > 3 := by 
        linarith
      have h8 : ¬ Nat.Prime (p^2 + 2) := by
        apply Nat.not_prime_of_dvd_of_lt h5 (by norm_num) (by nlinarith)
      contradiction