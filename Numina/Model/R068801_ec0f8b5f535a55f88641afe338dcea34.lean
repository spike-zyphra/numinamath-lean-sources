import Mathlib

theorem algebra_132084 : ¬∃ a b c : ℤ, (b^2 - 4 * a * c) = 2019 := by 
  intro h
  rcases h with ⟨a, b, c, h⟩
  have h1 : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by 
    have h2 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by 
      omega 
    rcases h2 with (h2 | h2 | h2 | h2) <;> simp [pow_two, Int.mul_emod, Int.add_emod, h2]
    <;> omega 
  have h2 : (4 * a * c) % 4 = 0 := by 
    have h3 : (4 * a * c) % 4 = 0 := by 
      simp [Int.mul_emod] 
      <;> ring_nf <;> omega 
    omega 
  have h3 : b ^ 2 % 4 = 3 := by 
    omega 
  omega 
  all_goals omega
  all_goals omega
  all_goals omega
  all_goals omega
  all_goals omega