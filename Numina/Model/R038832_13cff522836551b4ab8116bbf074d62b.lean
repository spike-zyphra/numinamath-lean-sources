import Mathlib

theorem number_theory_2009 (n : ℕ) (hposn : n > 0) :
    (Nat.digits 10 (n ^ 3)).sum ≡ 1 [MOD 9] ∨
    (Nat.digits 10 (n ^ 3)).sum ≡ 8 [MOD 9] ∨
    (Nat.digits 10 (n ^ 3)).sum ≡ 9 [MOD 9] := by
  have h1 : (Nat.digits 10 (n ^ 3)).sum % 9 = n ^ 3 % 9 := by 
    rw [Nat.modEq_nine_digits_sum (n ^ 3)]
    <;> omega
  have h2 : n ^ 3 % 9 = 0 ∨ n ^ 3 % 9 = 1 ∨ n ^ 3 % 9 = 8 := by
    have h3 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> 
      simp [h3, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
    <;> omega
  have h3 : (Nat.digits 10 (n ^ 3)).sum % 9 = 0 ∨ (Nat.digits 10 (n ^ 3)).sum % 9 = 1 ∨ (Nat.digits 10 (n ^ 3)).sum % 9 = 8 := by
    omega
  rcases h3 with (h3 | h3 | h3)
  · -- (Nat.digits 10 (n ^ 3)).sum ≡ 9 [MOD 9]
    have h4 : (Nat.digits 10 (n ^ 3)).sum ≡ 9 [MOD 9] := by 
      simp [Nat.ModEq] at *
      all_goals omega
    right
    right 
    exact h4
  · -- (Nat.digits 10 (n ^ 3)).sum ≡ 1 [MOD 9]
    have h4 : (Nat.digits 10 (n ^ 3)).sum ≡ 1 [MOD 9] := by
      simp [Nat.ModEq] at *
      all_goals omega
    left
    exact h4
  · -- (Nat.digits 10 (n ^ 3)).sum ≡ 8 [MOD 9]
    have h4 : (Nat.digits 10 (n ^ 3)).sum ≡ 8 [MOD 9] := by
      simp [Nat.ModEq] at *
      all_goals omega
    right
    left
    exact h4