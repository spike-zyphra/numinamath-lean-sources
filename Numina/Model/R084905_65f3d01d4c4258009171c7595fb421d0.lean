import Mathlib

open Set

theorem number_theory_316034 {M : Set ℤ} (hM : M = {a | ∃ x y, a = x^2 - y^2}) :
    ∀ n, ¬(4 * n + 2 ∈ M) := by 
  intro n
  rw [hM]
  intro h
  rcases h with ⟨x, y, h_eq⟩ 
  have h1 : x^2 % 4 = 0 ∨ x^2 % 4 = 1 := by 
    have h2 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by 
      omega 
    rcases h2 with (h2 | h2 | h2 | h2) <;> norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h2] at *
  have h2 : y^2 % 4 = 0 ∨ y^2 % 4 = 1 := by 
    have h3 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by 
      omega 
    rcases h3 with (h3 | h3 | h3 | h3) <;> norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h3] at *
  omega 
  <;> nlinarith
  <;> omega 
  <;> nlinarith