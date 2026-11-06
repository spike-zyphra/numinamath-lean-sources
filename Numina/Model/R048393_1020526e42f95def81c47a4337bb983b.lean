import Mathlib

theorem number_theory_235593 : ¬ ∃ x y : ℤ, x ^ 32 - y ^ 32 = 2016 := by
  intro h
  rcases h with ⟨x, y, h_eq⟩
  have h1 : x ^ 32 % 17 = 0 ∨ x ^ 32 % 17 = 1 := by
    have h1 : x % 17 = 0 ∨ x % 17 = 1 ∨ x % 17 = 2 ∨ x % 17 = 3 ∨ x % 17 = 4 ∨ x % 17 = 5 ∨ x % 17 = 6 ∨ x % 17 = 7 ∨ x % 17 = 8 ∨ x % 17 = 9 ∨ x % 17 = 10 ∨ x % 17 = 11 ∨ x % 17 = 12 ∨ x % 17 = 13 ∨ x % 17 = 14 ∨ x % 17 = 15 ∨ x % 17 = 16 := by
      omega
    rcases h1 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod] at *
  have h2 : y ^ 32 % 17 = 0 ∨ y ^ 32 % 17 = 1 := by
    have h2 : y % 17 = 0 ∨ y % 17 = 1 ∨ y % 17 = 2 ∨ y % 17 = 3 ∨ y % 17 = 4 ∨ y % 17 = 5 ∨ y % 17 = 6 ∨ y % 17 = 7 ∨ y % 17 = 8 ∨ y % 17 = 9 ∨ y % 17 = 10 ∨ y % 17 = 11 ∨ y % 17 = 12 ∨ y % 17 = 13 ∨ y % 17 = 14 ∨ y % 17 = 15 ∨ y % 17 = 16 := by
      omega
    rcases h2 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod] at *
  norm_num [Int.add_emod, Int.mul_emod, Int.sub_emod] at h_eq
  omega