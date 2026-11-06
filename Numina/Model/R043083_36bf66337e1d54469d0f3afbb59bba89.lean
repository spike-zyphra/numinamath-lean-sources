import Mathlib

theorem number_theory_7381 {a b c d : ℤ} (h₀ : (a * d - b * c) ∣ a) (h₁ : (a * d - b * c) ∣ b) (h₂ : (a * d - b * c) ∣ c) (h₃ : (a * d - b * c) ∣ d) (h₄ : a * d - b * c ≠ 0) : a * d - b * c = 1 ∨ a * d - b * c = -1 := by
  set k := a * d - b * c with hk
  have hkne0 : k ≠ 0 := by
    intro h
    apply h₄
    all_goals
    linarith
  rcases h₀ with ⟨x, hx⟩
  rcases h₁ with ⟨y, hy⟩
  rcases h₂ with ⟨z, hz⟩
  rcases h₃ with ⟨w, hw⟩
  have eq1 : k = k ^ 2 * (x * w - y * z) := by
    have eq2 : a * d - b * c = k := by
      linarith
    rw [show a = k * x by linarith, show b = k * y by linarith, show c = k * z by linarith, show d = k * w by linarith] at eq2
    nlinarith
  have eq2 : k * (k * (x * w - y * z) - 1) = 0 := by
    nlinarith
  cases (mul_eq_zero.1 eq2) with
  | inl h =>
    exfalso
    apply hkne0
    linarith
  | inr h =>
    have h5 : k * (x * w - y * z) = 1 := by linarith
    have h6 : k = 1 ∨ k = -1 := by
      apply Int.eq_one_or_neg_one_of_mul_eq_one 
      exact h5
    cases h6 with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith