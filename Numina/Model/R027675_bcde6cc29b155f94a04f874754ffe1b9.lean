import Mathlib

theorem number_theory_134794 : ¬∃ n : ℕ, (Nat.digits 10 (n ^ 2)).sum = 2021 := by
  by_contra h
  rcases h with ⟨n, hn⟩
  have h1 : (n ^ 2) % 9 = 5 := by 
    have h2 : (n ^ 2) % 9 = (Nat.digits 10 (n ^ 2)).sum % 9 := by 
      rw [Nat.modEq_nine_digits_sum (n ^ 2)]
    have h3 : (Nat.digits 10 (n ^ 2)).sum = 2021 := by 
      linarith [hn]
    calc
      (n ^ 2) % 9 = (Nat.digits 10 (n ^ 2)).sum % 9 := by 
        rw [Nat.modEq_nine_digits_sum (n ^ 2)]
      _ = 2021 % 9 := by 
        rw [h3]
      _ = 5 := by 
        norm_num
  have h4 : (n ^ 2) % 9 = 0 ∨ (n ^ 2) % 9 = 1 ∨ (n ^ 2) % 9 = 4 ∨ (n ^ 2) % 9 = 7 := by 
    have h3 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> 
      simp [pow_two, Nat.mul_mod, h3, Nat.add_mod]
    <;> omega
  omega