import Mathlib

theorem number_theory_247102 {A B C D : ℕ} (h₀ : A ≠ B) (h₁ : A ≠ C) (h₂ : A ≠ D)
    (h₃ : B ≠ C) (h₄ : B ≠ D) (h₅ : C ≠ D) (h₆ : 1 ≤ A ∧ A ≤ 9) (h₇ : 1 ≤ B ∧ B ≤ 9)
    (h₈ : 1 ≤ C ∧ C ≤ 9) (h₉ : 1 ≤ D ∧ D ≤ 9) (h₁₀ : 10 * A + B ≠ 0) (h₁₁ : 10 * C + B ≠ 0)
    (h₁₂ : (10 * A + B) * (10 * C + B) = 100 * D + 10 * D + D) (h₁₃ : (10 * A + B) < (10 * C + B)) :
    A = 2 ∧ B = 7 ∧ C = 3 ∧ D = 9 := by

  rcases h₆ with ⟨h₆₁, h₆₂⟩
  rcases h₇ with ⟨h₇₁, h₇₂⟩
  rcases h₈ with ⟨h₈₁, h₈₂⟩
  rcases h₉ with ⟨h₉₁, h₉₂⟩
  interval_cases A <;> interval_cases B <;> interval_cases C <;> omega