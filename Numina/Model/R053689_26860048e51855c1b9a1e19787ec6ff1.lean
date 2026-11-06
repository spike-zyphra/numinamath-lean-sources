import Mathlib

theorem number_theory_203376 :
    ¬∃ a b c : ℕ, a + b + c = 24 ∧ a * 10 + b * 15 + c * 20 = 5 * 20 ∧
    ¬∃ a b c : ℕ, a + b + c = 25 ∧ a * 10 + b * 15 + c * 20 = 5 * 20 := by 
  rintro ⟨a, b, c, h1, h2, h⟩
  omega