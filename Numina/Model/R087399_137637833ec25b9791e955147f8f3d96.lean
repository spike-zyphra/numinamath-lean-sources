import Mathlib

theorem number_theory_6903
(a : ℤ) (h : ¬(2 ∣ a)) (h' : ¬(3 ∣ a)) : 24 ∣ a^2 + 23 := by
  have h1 : a % 2 ≠ 0 := by
    by_contra h2
    have : 2 ∣ a := by
      omega
    contradiction
  have h2 : a % 3 ≠ 0 := by
    by_contra h3
    have : 3 ∣ a := by
      omega
    contradiction
  have h3 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
    omega
  have h4 : a % 3 = 1 ∨ a % 3 = 2 := by 
    omega
  have h5 : a^2 % 8 = 1 := by
    rcases h3 with (h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
  have h6 : a^2 % 3 = 1 := by
    rcases h4 with (h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
  have h7 : a^2 % 24 = 1 := by
    omega
  omega