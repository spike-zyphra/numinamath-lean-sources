import Mathlib

theorem algebra_208886 (a : ℕ → ℝ) (h₀ : ∀ k, a k ≠ 0)
    (h₁ : ∀ k, a (k + 1) = ⌊a k⌋ * (a k % 1)) :
    ∃ N, ∀ k, N ≤ k → a k = a (k + 2) := by 
  have h3 : a 1 = 0 := by
    have h1 := h₁ 0
    norm_num at h1 ⊢
    nlinarith
  have h4 : a 1 ≠ 0 := h₀ 1
  exfalso 
  contradiction