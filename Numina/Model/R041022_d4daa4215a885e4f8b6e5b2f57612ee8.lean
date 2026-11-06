import Mathlib

theorem number_theory_232047 (u v : ℤ) (h : 9 ∣ u^2 + u * v + v^2) :
    3 ∣ u ∧ 3 ∣ v := by
  have h1 : u % 9 = 0 ∨ u % 9 = 1 ∨ u % 9 = 2 ∨ u % 9 = 3 ∨ u % 9 = 4 ∨ u % 9 = 5 ∨ u % 9 = 6 ∨ u % 9 = 7 ∨ u % 9 = 8 := by
    omega
  have h2 : v % 9 = 0 ∨ v % 9 = 1 ∨ v % 9 = 2 ∨ v % 9 = 3 ∨ v % 9 = 4 ∨ v % 9 = 5 ∨ v % 9 = 6 ∨ v % 9 = 7 ∨ v % 9 = 8 := by
    omega
  have h3 : (u ^ 2 + u * v + v ^ 2) % 9 = 0 := by
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [h1, h2, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod] at h3 <;> omega