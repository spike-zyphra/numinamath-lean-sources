import Mathlib

theorem number_theory_7690
    (n a b : ℤ)
    (h₀ : a ∣ n)
    (h₁ : b ∣ n)
    (h₂ : ∃ x y, a * x + b * y = 1) :
    a * b ∣ n := by
  rcases h₂ with ⟨x, y, h3⟩
  have h6 : IsCoprime a b := by 
    use x, y 
    linarith 
  have h7 : a * b ∣ n := by
    exact IsCoprime.mul_dvd h6 h₀ h₁
  exact h7