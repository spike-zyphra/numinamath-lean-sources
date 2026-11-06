import Mathlib

theorem number_theory_114444 (a : ℤ) (n : ℤ) (h₀ : Even n) (h₁ : n = 4 * a + 2) :
    ¬∃ x y, n = x ^ 2 - y ^ 2 := by
  rw [h₁]
  intro h
  rcases h with ⟨x, y, h_eq⟩
  have h2 : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
    have h1 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
    rcases h1 with (h1 | h1 | h1 | h1) <;> norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, Int.emod, h1] at *
  have h3 : y ^ 2 % 4 = 0 ∨ y ^ 2 % 4 = 1 := by
    have h1 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
    rcases h1 with (h1 | h1 | h1 | h1) <;> norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, Int.emod, h1] at *
  have h4 : (x ^ 2 - y ^ 2) % 4 = 2 := by
    omega
  omega