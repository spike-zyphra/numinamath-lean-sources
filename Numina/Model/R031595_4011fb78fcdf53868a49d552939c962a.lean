import Mathlib

theorem number_theory_81392 (n : ℤ) (h : n ≡ 7 [ZMOD 8]) :
    ¬∃ a b c, n = a^2 + b^2 + c^2 := by
  rintro ⟨a, b, c, heq⟩
  have h8 : n % 8 = 7 := by 
    norm_num [Int.ModEq] at h
    omega
  have h9 : (a^2 + b^2 + c^2) % 8 = 7 := by
    omega
  have h10 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by 
    omega
  have h11 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by 
    omega
  have h12 : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by 
    omega
  rcases h10 with (h10 | h10 | h10 | h10 | h10 | h10 | h10 | h10) <;> rcases h11 with (h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11) <;> rcases h12 with (h12 | h12 | h12 | h12 | h12 | h12 | h12 | h12) <;> simp [Int.add_emod, Int.mul_emod, pow_two, h10, h11, h12] at h9 <;> omega