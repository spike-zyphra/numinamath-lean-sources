import Mathlib

theorem algebra_1512 (a b c d e f : ℕ) (h₀ : 0 ≤ a ∧ a ≤ 100) (h₁ : 0 ≤ b ∧ b ≤ 100)
    (h₂ : 0 ≤ c ∧ c ≤ 100) (h₃ : 0 ≤ d ∧ d ≤ 100) (h₄ : 0 ≤ e ∧ e ≤ 100) (h₅ : 0 ≤ f ∧ f ≤ 100)
    (h₆ : a > b ∧ b > c ∧ c > d ∧ d > e ∧ e > f) (h₇ : (a + b + c + d + e + f) / 6 = 91)
    (h₈ : f = 65) : c ≥ 95 := by
  rcases h₀ with ⟨ha0, ha100⟩
  rcases h₁ with ⟨hb0, hb100⟩
  rcases h₂ with ⟨hc0, hc100⟩
  rcases h₃ with ⟨hd0, hd100⟩
  rcases h₄ with ⟨he0, he100⟩
  rcases h₅ with ⟨hf0, hf100⟩
  rcases h₆ with ⟨h1, h2, h3, h4, h5⟩
  omega