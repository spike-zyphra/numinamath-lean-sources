import Mathlib

theorem number_theory_8219 (a b c d : ℕ) (h₀ : a < 10) (h₁ : b < 10) (h₂ : c < 10) (h₃ : d < 10)
    (h₄ : Nat.factorial 34 = 295232799 * 1000000 + 100000 * a + 10000 * b + 1000 * c + 100 * d + 10 * 96041408476186096435 + 1000 * a + 100 * b) :
    a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 3 := by 
  norm_num [Nat.factorial] at h₄ 
  have h5 : a = 2 := by 
    omega 
  have h6 : b = 0 := by 
    omega 
  have h7 : c = 0 := by 
    omega 
  have h8 : d = 3 := by 
    omega 
  exact ⟨h5, h6, h7, h8⟩