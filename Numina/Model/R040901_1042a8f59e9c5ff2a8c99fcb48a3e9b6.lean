import Mathlib

theorem algebra_190071 (a b c : ℕ) (h₀ : a + b + c = 11) (h₁ : 3*a+7*b+14*c=108) :
    a=1 ∧ b=5 ∧ c=5 := by 
  have h2 : a = 1 ∧ b = 5 ∧ c = 5 := by
    have eq1 : 4 * b + 11 * c = 75 := by 
      omega
    have h3 : b = 5 := by
      omega
    have h4 : c = 5 := by
      omega
    have h5 : a = 1 := by
      omega
    exact ⟨h5, h3, h4⟩
  exact h2