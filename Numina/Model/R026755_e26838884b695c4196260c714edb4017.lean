import Mathlib

theorem number_theory_160244 (a b n : ℕ) (_ : Nat.gcd a n = 1) (h₀ : Nat.gcd b n = 1) :
    Nat.gcd (a * b) n = 1 := by 
  have h3 : Nat.Coprime a n := by 
    rw [Nat.coprime_iff_gcd_eq_one] 
    exact ‹Nat.gcd a n = 1› 
  have h4 : Nat.Coprime b n := by 
    rw [Nat.coprime_iff_gcd_eq_one]
    exact h₀ 
  have h5 : Nat.Coprime (a * b) n := by 
    apply Nat.Coprime.mul 
    exact h3 
    exact h4 
  have h6 : Nat.gcd (a * b) n = 1 := by 
    rw [Nat.coprime_iff_gcd_eq_one] at h5 
    exact h5 
  exact h6