import Mathlib
open Nat Real Finset Set
noncomputable section

theorem number_theory_600014 (P : ℕ) (h : ∏ x ∈ (Nat.divisors (5^15)), x = 5^P) : P = 120 := by 
  have h1 : ∏ x in (Nat.divisors (5 ^ 15 : ℕ)), x = 5 ^ 120 := by
    rw [Nat.prod_divisors_prime_pow]
    all_goals native_decide

  rw [h1] at h
  
  have h2 : (5 : ℕ) ^ (120 : ℕ) = (5 : ℕ) ^ (P : ℕ) := by 
    exact_mod_cast h
  
  have h3 : (120 : ℕ) = P := by 
    exact Nat.pow_right_injective (by norm_num) h2
  
  omega