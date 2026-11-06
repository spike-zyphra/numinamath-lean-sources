import Mathlib

theorem algebra_210984 (A B C D : ℕ) (h₀ : A ≠ 0) (h₁ : B ≠ 0) (h₂ : C ≠ 0)
    (h₃ : D ≠ 0) (h₄ : A ≠ B) (h₅ : A ≠ C) (h₆ : A ≠ D) (h₇ : B ≠ C) (h₈ : B ≠ D)
    (h₉ : C ≠ D) (h₁₀ : ∃ x, A * x ^ 2 + B * x + B * C = 0) (h₁₁ : ∃ x, A * x ^ 2 + B * x + B * D = 0)
    (h₁₂ : ∃ x, A * x ^ 2 + B * x + C * D = 0) :
    (A = 1 ∧ B = 9 ∧ C = 2 ∧ D = 0) ∨ (A = 2 ∧ B = 9 ∧ C = 1 ∧ D = 0) := by
  rcases h₁₀ with ⟨x, hx⟩
  have h1 : A * x ^ 2 + B * x + B * C = 0 := by
    linarith
  rcases h₁₁ with ⟨y, hy⟩
  have h2 : A * y ^ 2 + B * y + B * D = 0 := by
    linarith
  rcases h₁₂ with ⟨z, hz⟩
  have h3 : A * z ^ 2 + B * z + C * D = 0 := by
    linarith
  have h4 : A * x ^ 2 + B * x + B * C > 0 := by
    nlinarith [show 0 < A by omega, show 0 < B by omega, show 0 < C by omega, sq_pos_of_pos (show 0 < A by omega),
      sq_pos_of_pos (show 0 < B by omega), sq_nonneg x, sq_nonneg (x + 1)]
  linarith