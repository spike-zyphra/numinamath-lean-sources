import Mathlib

theorem number_theory_5530 (a : ℤ) : a^37 ≡ a [ZMOD 1729] := by 
  norm_num [Int.ModEq]
  have h1 : a ^ 37 % 7 = a % 7 := by
    have h2 : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have h2 : a ^ 37 % 13 = a % 13 := by
    have h2 : a % 13 = 0 ∨ a % 13 = 1 ∨ a % 13 = 2 ∨ a % 13 = 3 ∨ a % 13 = 4 ∨ a % 13 = 5 ∨ a % 13 = 6 ∨ a % 13 = 7 ∨ a % 13 = 8 ∨ a % 13 = 9 ∨ a % 13 = 10 ∨ a % 13 = 11 ∨ a % 13 = 12 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have h3 : a ^ 37 % 19 = a % 19 := by
    have h2 : a % 19 = 0 ∨ a % 19 = 1 ∨ a % 19 = 2 ∨ a % 19 = 3 ∨ a % 19 = 4 ∨ a % 19 = 5 ∨ a % 19 = 6 ∨ a % 19 = 7 ∨ a % 19 = 8 ∨ a % 19 = 9 ∨ a % 19 = 10 ∨ a % 19 = 11 ∨ a % 19 = 12 ∨ a % 19 = 13 ∨ a % 19 = 14 ∨ a % 19 = 15 ∨ a % 19 = 16 ∨ a % 19 = 17 ∨ a % 19 = 18 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  omega