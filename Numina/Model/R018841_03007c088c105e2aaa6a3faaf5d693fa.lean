import Mathlib

theorem number_theory_163972 {a b c d e : ℕ} (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 0 ≤ b ∧ b ≤ 9)
    (h₂ : 1 ≤ c ∧ c ≤ 9) (h₃ : 0 ≤ d ∧ d ≤ 9) (h₄ : 0 ≤ e ∧ e ≤ 9)
    (h₅ : (10 * a + b) + (100 * c + 10 * d + e) = 1079) :
    a + b + c + d + e = 35 := by 
  rcases h₀ with ⟨ha1, ha2⟩
  rcases h₁ with ⟨hb1, hb2⟩
  rcases h₂ with ⟨hc1, hc2⟩
  rcases h₃ with ⟨hd1, hd2⟩
  rcases h₄ with ⟨he1, he2⟩
  omega