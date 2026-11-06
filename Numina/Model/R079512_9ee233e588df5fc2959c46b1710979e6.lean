import Mathlib

theorem number_theory_116219 (n : ℕ) (h₀ : n > 0) (h₁ : (2 * n) < 100) (h₂ : (2 * n) > 9)
    (h₃ : Nat.digits 10 (2 * n) = List.reverse (Nat.digits 10 (n ^ 2))) :
    n ^ 2 = 81 := by
  have h4 : n < 50 := by
    omega
  interval_cases n <;> norm_num at h₃ ⊢ <;> try all_goals trivial
  all_goals
    try
      exfalso
      <;> norm_num at h₃ ⊢