import Mathlib

theorem number_theory_326570 (a b c : ℤ) (h₀ : 6 ∣ a + b + c) :
    0 = (a^3 + b^3 + c^3) % 6 := by 
  have h₁ : a % 6 = 0 ∨ a % 6 = 1 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4 ∨ a % 6 = 5 := by 
    omega
  have h₂ : b % 6 = 0 ∨ b % 6 = 1 ∨ b % 6 = 2 ∨ b % 6 = 3 ∨ b % 6 = 4 ∨ b % 6 = 5 := by 
    omega
  have h₃ : c % 6 = 0 ∨ c % 6 = 1 ∨ c % 6 = 2 ∨ c % 6 = 3 ∨ c % 6 = 4 ∨ c % 6 = 5 := by 
    omega
  have h₄ : a^3 % 6 = a % 6 := by
    rcases h₁ with (h₁ | h₁ | h₁ | h₁ | h₁ | h₁) <;> 
        simp [pow_succ, Int.add_emod, Int.mul_emod, h₁]
  have h₅ : b^3 % 6 = b % 6 := by 
    rcases h₂ with (h₂ | h₂ | h₂ | h₂ | h₂ | h₂) <;> 
        simp [pow_succ, Int.add_emod, Int.mul_emod, h₂]
  have h₆ : c^3 % 6 = c % 6 := by 
    rcases h₃ with (h₃ | h₃ | h₃ | h₃ | h₃ | h₃) <;> 
        simp [pow_succ, Int.add_emod, Int.mul_emod, h₃]
  have h₇ : (a^3 + b^3 + c^3) % 6 = (a + b + c) % 6 := by
    simp [Int.add_emod, h₄, h₅, h₆]
  have h₈ : (a + b + c) % 6 = 0 := by 
    omega
  rw [h₇, h₈]
  all_goals omega