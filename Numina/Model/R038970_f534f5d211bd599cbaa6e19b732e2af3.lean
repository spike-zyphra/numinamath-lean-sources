import Mathlib

theorem number_theory_101189 (a b c : ℤ) (h : 9 ∣ a^2 + b^2 + c^2) :
    9 ∣ a^2 - b^2 ∨ 9 ∣ b^2 - c^2 ∨ 9 ∣ a^2 - c^2 := by 
  have h1 : a^2 % 9 = 0 ∨ a^2 % 9 = 1 ∨ a^2 % 9 = 4 ∨ a^2 % 9 = 7 := by
    have h1 : a % 9 = 0 ∨ a % 9 = 1 ∨ a % 9 = 2 ∨ a % 9 = 3 ∨ a % 9 = 4 ∨ a % 9 = 5 ∨ a % 9 = 6 ∨ a % 9 = 7 ∨ a % 9 = 8 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> norm_num [h1, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod] at *
  have h2 : b^2 % 9 = 0 ∨ b^2 % 9 = 1 ∨ b^2 % 9 = 4 ∨ b^2 % 9 = 7 := by
    have h1 : b % 9 = 0 ∨ b % 9 = 1 ∨ b % 9 = 2 ∨ b % 9 = 3 ∨ b % 9 = 4 ∨ b % 9 = 5 ∨ b % 9 = 6 ∨ b % 9 = 7 ∨ b % 9 = 8 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> norm_num [h1, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod] at *
  have h3 : c^2 % 9 = 0 ∨ c^2 % 9 = 1 ∨ c^2 % 9 = 4 ∨ c^2 % 9 = 7 := by
    have h1 : c % 9 = 0 ∨ c % 9 = 1 ∨ c % 9 = 2 ∨ c % 9 = 3 ∨ c % 9 = 4 ∨ c % 9 = 5 ∨ c % 9 = 6 ∨ c % 9 = 7 ∨ c % 9 = 8 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> norm_num [h1, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod] at *
  have h4 : (a^2 + b^2 + c^2) % 9 = 0 := by
    omega
  have h5 : (a^2 - b^2) % 9 = 0 ∨ (b^2 - c^2) % 9 = 0 ∨ (a^2 - c^2) % 9 = 0 := by
    omega
  rcases h5 with (h5 | h5 | h5)
  · -- Case where (a^2 - b^2) % 9 = 0, so 9 divides a^2 - b^2
    exact Or.inl (by omega)
  · -- Case where (b^2 - c^2) % 9 = 0, so 9 divides b^2 - c^2
    exact Or.inr (Or.inl (by omega))
  · -- Case where (a^2 - c^2) % 9 = 0, so 9 divides a^2 - c^2
    exact Or.inr (Or.inr (by omega))