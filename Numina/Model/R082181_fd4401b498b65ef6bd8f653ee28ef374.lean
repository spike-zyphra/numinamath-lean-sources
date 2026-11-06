import Mathlib

theorem number_theory_45664 :
    ∀ n : ℕ, ∃ m : ℤ, m > n ∧ ¬∃ a b : ℤ, a^2 - b^2 = m := by 
  intro n 
  use 4 * (n : ℤ) + 2
  constructor
  · -- 证明 4n + 2 > n
    have h1 : (4 * (n : ℤ) + 2) > (n : ℤ) := by
      omega
    exact_mod_cast h1
  · -- 证明 4n + 2 不能写成两个平方的差
    intro h
    rcases h with ⟨a, b, h_eq⟩
    have h1 : a^2 % 4 = 0 ∨ a^2 % 4 = 1 := by 
      have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by 
        omega 
      rcases h1 with (h1 | h1 | h1 | h1) <;> 
        norm_num [pow_two, Int.add_emod, Int.mul_emod, h1, Int.sub_emod]
    have h2 : b^2 % 4 = 0 ∨ b^2 % 4 = 1 := by 
      have h2 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by 
        omega 
      rcases h2 with (h2 | h2 | h2 | h2) <;> 
        norm_num [pow_two, Int.add_emod, Int.mul_emod, h2, Int.sub_emod]
    have h3 : (a^2 - b^2) % 4 = 2 := by 
      omega 
    omega