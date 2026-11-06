import Mathlib

theorem number_theory_192611 (k : ℕ) : 11 ∣ 5^(5*k+1) + 4^(5*k+2) + 3^(5*k) := by 
  induction' k with k ih
  . norm_num
  . norm_num [Nat.pow_add, Nat.pow_mul] at ih ⊢
    omega