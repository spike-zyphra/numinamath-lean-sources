import Mathlib

theorem number_theory_318803 (a : ℕ → ℕ → ℕ)
    (h₀ : ∀ n m, a n m = a (n - 1) m + a (n - 1) (m - 1))
    (h₁ : ∀ n, a n 0 = n + 1)
    (h₂ : ∀ n, a n 99 = 101 * 2 ^ 98) :
    a 99 0 = 101 * 2 ^ 98 := by

  have h3 := h₁ 0
  have h4 : a 0 0 = 1 := by 
    simpa using h3

  have h5 : a 1 0 = 2 := by
    specialize h₁ 1
    simp at h₁ ⊢
    omega

  have h6 : a 1 0 = a 0 0 + a 0 0 := by 
    specialize h₀ 1 0
    simpa using h₀

  have h7 : a 2 0 = 3 := by
    specialize h₁ 2
    simp at h₁ ⊢
    omega

  have h8 : a 2 0 = a 1 0 + a 1 0 := by
    specialize h₀ 2 0
    simpa using h₀

  omega