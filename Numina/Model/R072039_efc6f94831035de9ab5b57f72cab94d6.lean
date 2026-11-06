import Mathlib

theorem number_theory_43339 (x y z : ℤ) :
    25 ∣ x^5 + y^5 + z^5 → 25 ∣ x^5 + y^5 ∨ 25 ∣ y^5 + z^5 ∨ 25 ∣ z^5 + x^5 := by
  intro h
  have h1 : x^5 % 25 = 0 ∨ x^5 % 25 = 1 ∨ x^5 % 25 = 7 ∨ x^5 % 25 = 18 ∨ x^5 % 25 = 24 := by
    have h1 : x % 25 = 0 ∨ x % 25 = 1 ∨ x % 25 = 2 ∨ x % 25 = 3 ∨ x % 25 = 4 ∨ x % 25 = 5 ∨ x % 25 = 6 ∨ x % 25 = 7 ∨ x % 25 = 8 ∨ x % 25 = 9 ∨ x % 25 = 10 ∨ x % 25 = 11 ∨ x % 25 = 12 ∨ x % 25 = 13 ∨ x % 25 = 14 ∨ x % 25 = 15 ∨ x % 25 = 16 ∨ x % 25 = 17 ∨ x % 25 = 18 ∨ x % 25 = 19 ∨ x % 25 = 20 ∨ x % 25 = 21 ∨ x % 25 = 22 ∨ x % 25 = 23 ∨ x % 25 = 24 := by 
      omega
    rcases h1 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.add_emod, Int.mul_emod, h] at *
  have h2 : y^5 % 25 = 0 ∨ y^5 % 25 = 1 ∨ y^5 % 25 = 7 ∨ y^5 % 25 = 18 ∨ y^5 % 25 = 24 := by
    have h2 : y % 25 = 0 ∨ y % 25 = 1 ∨ y % 25 = 2 ∨ y % 25 = 3 ∨ y % 25 = 4 ∨ y % 25 = 5 ∨ y % 25 = 6 ∨ y % 25 = 7 ∨ y % 25 = 8 ∨ y % 25 = 9 ∨ y % 25 = 10 ∨ y % 25 = 11 ∨ y % 25 = 12 ∨ y % 25 = 13 ∨ y % 25 = 14 ∨ y % 25 = 15 ∨ y % 25 = 16 ∨ y % 25 = 17 ∨ y % 25 = 18 ∨ y % 25 = 19 ∨ y % 25 = 20 ∨ y % 25 = 21 ∨ y % 25 = 22 ∨ y % 25 = 23 ∨ y % 25 = 24 := by 
      omega
    rcases h2 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.add_emod, Int.mul_emod, h] at *
  have h3 : z^5 % 25 = 0 ∨ z^5 % 25 = 1 ∨ z^5 % 25 = 7 ∨ z^5 % 25 = 18 ∨ z^5 % 25 = 24 := by
    have h3 : z % 25 = 0 ∨ z % 25 = 1 ∨ z % 25 = 2 ∨ z % 25 = 3 ∨ z % 25 = 4 ∨ z % 25 = 5 ∨ z % 25 = 6 ∨ z % 25 = 7 ∨ z % 25 = 8 ∨ z % 25 = 9 ∨ z % 25 = 10 ∨ z % 25 = 11 ∨ z % 25 = 12 ∨ z % 25 = 13 ∨ z % 25 = 14 ∨ z % 25 = 15 ∨ z % 25 = 16 ∨ z % 25 = 17 ∨ z % 25 = 18 ∨ z % 25 = 19 ∨ z % 25 = 20 ∨ z % 25 = 21 ∨ z % 25 = 22 ∨ z % 25 = 23 ∨ z % 25 = 24 := by 
      omega
    rcases h3 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.add_emod, Int.mul_emod, h] at *
  omega