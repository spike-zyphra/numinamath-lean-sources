import Mathlib

theorem algebra_169532 (a b c d e : ℝ) (h₀ : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e)
    (h₁ : (a + b + c + d) / 4 + e = 74) (h₂ : (a + b + c + e) / 4 + d = 80)
    (h₃ : (a + b + d + e) / 4 + c = 98) (h₄ : (a + c + d + e) / 4 + b = 116)
    (h₅ : (b + c + d + e) / 4 + a = 128) :
    e - a = 72 := by
  have eq1 : a + b + c + d + 4 * e = 296 := by
    linarith

  have eq2 : a + b + c + e + 4 * d = 320 := by 
    linarith
  
  have eq3 : a + b + d + e + 4 * c = 392 := by 
    linarith

  have eq4 : a + c + d + e + 4 * b = 464 := by 
    linarith

  have eq5 : b + c + d + e + 4 * a = 512 := by 
    linarith
  
  rcases h₀ with ⟨h₀1, h₀2, h₀3, h₀4⟩
  
  linarith