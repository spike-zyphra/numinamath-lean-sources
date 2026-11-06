import Mathlib

theorem number_theory_69651 (a : ℕ → ℤ)
    (h₀ : a 1 = 1)
    (h₁ : a 2 = 1)
    (h₂ : ∀ n, a (2 * n + 1) = 2 * a (2 * n) - a n)
    (h₃ : ∀ n, a (2 * n + 2) = 2 * a (2 * n + 1)) :
    ∀ n, n > 3 → 8 ∣ n - 3 → 5 ∣ a n := by
  intro n hn h
  have h4 : a 2 = 2 * a 1 := by 
    specialize h₃ 0
    norm_num at h₃ ⊢
    all_goals 
      omega
  have h4' : a 1 = 1 := h₀
  have h5 : a 2 = 2 := by
    linarith [h4, h4']
  have h6 : a 2 = 1 := h₁
  have h7 : (2 : ℤ) = 1 := by 
    linarith [h5, h6]
  linarith