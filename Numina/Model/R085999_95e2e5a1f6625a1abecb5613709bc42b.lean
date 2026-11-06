import Mathlib

theorem algebra_206446 (a : ℕ → ℤ) (h₀ : ∀ n, a (n + 2) = a n + a (n + 1))
    (h₁ : a 4 = 53) (h₂ : a 7 = 225) :
    a 0 = 7 := by
  have h₃ : a 2 = a 0 + a 1 := by
    specialize h₀ 0
    norm_num at h₀ ⊢
    exact h₀

  have h₄ : a 3 = a 1 + a 2 := by
    specialize h₀ 1
    norm_num at h₀ ⊢
    exact h₀

  have h₅ : a 3 = a 0 + 2 * a 1 := by
    rw [h₃] at h₄
    linarith

  have h₆ : a 4 = a 2 + a 3 := by
    specialize h₀ 2
    norm_num at h₀ ⊢
    exact h₀

  have h₇ : a 4 = 2 * a 0 + 3 * a 1 := by
    rw [h₃, h₅] at h₆
    linarith

  have h₈ : a 5 = a 3 + a 4 := by
    specialize h₀ 3
    norm_num at h₀ ⊢
    exact h₀

  have h₉ : a 5 = 3 * a 0 + 5 * a 1 := by
    rw [h₅, h₇] at h₈
    linarith

  have h₁₀ : a 6 = a 4 + a 5 := by
    specialize h₀ 4
    norm_num at h₀ ⊢
    exact h₀

  have h₁₁ : a 6 = 5 * a 0 + 8 * a 1 := by
    rw [h₇, h₉] at h₁₀
    linarith

  have h₁₂ : a 7 = a 5 + a 6 := by
    specialize h₀ 5
    norm_num at h₀ ⊢
    exact h₀

  have h₁₃ : a 7 = 8 * a 0 + 13 * a 1 := by
    rw [h₉, h₁₁] at h₁₂
    linarith

  rw [h₇] at h₁
  rw [h₁₃] at h₂

  omega