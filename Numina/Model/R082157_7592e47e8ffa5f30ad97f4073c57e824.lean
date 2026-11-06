import Mathlib

theorem number_theory_194462 (P B G : ℕ) (h₀ : P ≠ B) (h₁ : P ≠ G) (h₂ : B ≠ G)
    (h₃ : 1 ≤ P ∧ P ≤ 9) (h₄ : 0 ≤ B ∧ B ≤ 9) (h₅ : 0 ≤ G ∧ G ≤ 9)
    (h₆ : 100 * P + 10 * B + G = (P + B + G) * (P + B + G + 1)) :
    P = 1 ∧ B = 5 ∧ G = 6 := by 
  rcases h₃ with ⟨h₃₁, h₃₂⟩
  rcases h₄ with ⟨h₄₁, h₄₂⟩
  rcases h₅ with ⟨h₅₁, h₅₂⟩
  interval_cases P <;> interval_cases B <;> interval_cases G
  <;> omega