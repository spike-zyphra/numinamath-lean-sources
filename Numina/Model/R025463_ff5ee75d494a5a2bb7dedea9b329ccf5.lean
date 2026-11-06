import Mathlib

theorem number_theory_169067 (n : ℕ) (h₀ : n + (Nat.digits 10 n).sum = 2021) :
    n = 2014 ∨ n = 1996 := by
  have h1 : n ≤ 2021 := by 
    have h2 : (Nat.digits 10 n).sum ≥ 0 := by
      simp
    omega
  interval_cases n <;> norm_num at h₀ ⊢ <;> tauto