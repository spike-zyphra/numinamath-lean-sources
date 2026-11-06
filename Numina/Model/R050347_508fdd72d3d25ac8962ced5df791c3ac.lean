import Mathlib

theorem number_theory_124244 (a : ℕ → ℕ)
    (h₀ : a 0 = 0)
    (h₁ : a 1 = 1)
    (h₂ : a 2 = 1)
    (h₃ : ∀ n ≥ 1, a (3 * n) = a n)
    (h₄ : ∀ n ≥ 1, a (3 * n + 1) = a n + 1)
    (h₅ : ∀ n ≥ 1, a (3 * n + 2) = a n + 1) :
    a 2021 = 6 := by
  have h3 : a 2021 = a 673 + 1 := by
    specialize h₅ 673 (by norm_num)
    norm_num at h₅ ⊢
    omega
  have h4 : a 673 = a 224 + 1 := by
    specialize h₄ 224 (by norm_num)
    norm_num at h₄ ⊢
    omega
  have h5 : a 224 = a 74 + 1 := by
    specialize h₅ 74 (by norm_num)
    norm_num at h₅ ⊢
    omega
  have h6 : a 74 = a 24 + 1 := by
    specialize h₅ 24 (by norm_num)
    norm_num at h₅ ⊢
    omega
  have h7 : a 24 = a 8 := by
    specialize h₃ 8 (by norm_num)
    norm_num at h₃ ⊢
    omega
  have h8 : a 8 = a 2 + 1 := by
    specialize h₅ 2 (by norm_num)
    norm_num at h₅ ⊢
    omega
  have h9 : a 2 = 1 := h₂
  rw [h3]
  rw [h4]
  rw [h5]
  rw [h6]
  rw [h7]
  rw [h8]
  rw [h9]
  all_goals omega