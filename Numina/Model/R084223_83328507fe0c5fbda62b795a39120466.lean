import Mathlib

theorem number_theory_210036 (f : ℕ → ℕ)
    (h₀ : f 1 = 1)
    (h₁ : f 2 = 1)
    (h₂ : ∀ n, f (3 * n) = f n + 2020)
    (h₃ : ∀ n, f (3 * n + 1) = 3 * f n + 2019)
    (h₄ : ∀ n, f (3 * n + 2) = 2019 * f n) :
    (∀ n, 0 < n → {i | 1 ≤ i ∧ i ≤ n ∧ Odd (f i)}.encard > {i | 1 ≤ i ∧ i ≤ n ∧ Even (f i)}.encard) ∧
    Even (f 2019) := by 
  have h1 := h₂ 0
  simp at h1
  all_goals linarith