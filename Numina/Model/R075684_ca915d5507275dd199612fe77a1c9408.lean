import Mathlib

theorem number_theory_257646 (n : ℕ) (h₀ : (Nat.digits 10 n).sum = 2006) :
    ¬ ∃ m, m^2 = n := by
  intro h
  rcases h with ⟨m, hm⟩
  have h1 : n % 9 = 8 := by
    have h2 : n % 9 = (Nat.digits 10 n).sum % 9 := by
      rw [Nat.modEq_nine_digits_sum]
      all_goals
      simp
    rw [h₀] at h2
    norm_num at h2 ⊢
    omega
  have h3 : m^2 % 9 = n % 9 := by 
    rw [hm]
  rw [h1] at h3
  -- Assume m exists such that m² = n, then m² ≡ 8 (mod 9)
  have h4 : m % 9 = 0 ∨ m % 9 = 1 ∨ m % 9 = 2 ∨ m % 9 = 3 ∨ m % 9 = 4 ∨ m % 9 = 5 ∨ m % 9 = 6 ∨ m % 9 = 7 ∨ m % 9 = 8 := by 
    omega
  rcases h4 with (h | h | h | h | h | h | h | h | h) <;> ( 
    simp [Nat.pow_mod, h] at h3
    <;> omega
  )
  all_goals
    omega