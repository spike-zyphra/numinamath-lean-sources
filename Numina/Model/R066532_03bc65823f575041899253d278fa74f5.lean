import Mathlib

theorem number_theory_122027 :
    ¬∃ a b : ℤ, a^2 - 3 * b^2 = 8 ∧
    ¬∃ a b c : ℤ, a > 0 ∧ b > 0 ∧ a^2 + b^2 = 3 * c^2 := by 
  rintro ⟨a, b, h₁, h₂⟩
  have h₃ : a^2 % 3 = 0 ∨ a^2 % 3 = 1 := by 
    have h4 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by 
      omega
    rcases h4 with (h | h | h)
    · 
      simp [pow_two, Int.mul_emod, h]
      <;> norm_num
    · 
      simp [pow_two, Int.mul_emod, h]
      <;> norm_num
    · 
      simp [pow_two, Int.mul_emod, h]
      <;> norm_num
  have h₄ : a^2 % 3 = 2 := by 
    omega 
  omega