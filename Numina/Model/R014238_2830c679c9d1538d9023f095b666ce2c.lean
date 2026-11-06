import Mathlib

theorem number_theory_104330 (a b c : ℤ) (h₀ : a + b + c ≡ 0 [ZMOD 6]) :
    a^5 + b^3 + c ≡ 0 [ZMOD 6] := by 
  have h1 : a ^ 5 % 6 = a % 6 := by
    have h2 : a % 6 = 0 ∨ a % 6 = 1 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4 ∨ a % 6 = 5 := by
      omega
    rcases h2 with (h | h | h | h | h | h) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
  
  have h2 : b ^ 3 % 6 = b % 6 := by
    have h3 : b % 6 = 0 ∨ b % 6 = 1 ∨ b % 6 = 2 ∨ b % 6 = 3 ∨ b % 6 = 4 ∨ b % 6 = 5 := by
      omega
    rcases h3 with (h | h | h | h | h | h) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h, Int.sub_emod]

  norm_num [Int.ModEq] at h₀ ⊢ 
  omega