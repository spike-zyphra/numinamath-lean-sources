import Mathlib

theorem number_theory_196602 (x y c : ℕ) (h₀ : 0 ≤ x ∧ x ≤ 9) (h₁ : 0 ≤ y ∧ y ≤ 9)
    (h₂ : 123400 + 10 * x + y ≡ 0 [MOD 8]) (h₃ : 123400 + 10 * x + y ≡ 0 [MOD 9])
    (h₄ : x + y = c) : c = 8 := by 
  norm_num [Nat.ModEq] at h₂ h₃
  rcases h₀ with ⟨hx₀, hx₁⟩
  rcases h₁ with ⟨hy₀, hy₁⟩
  omega