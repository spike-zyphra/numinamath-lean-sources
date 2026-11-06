import Mathlib

theorem algebra_301942 {f : ℕ → ℕ} (h₀ : ∀ n, 0 < n → f (f n) = 4 * n + 3)
    (h₁ : ∀ k, f (2 ^ k) = 2 ^ (k + 1) + 1) :
    f 2303 = 4607 := by
  have h1 : f (8) = 17 := by
    specialize h₁ 3
    norm_num at h₁ ⊢
    exact h₁
  have h2 : f (17) = 35 := by
    have h17 : f (f 8) = 4 * 8 + 3 := h₀ 8 (by norm_num)
    rw [h1] at h17
    norm_num at h17 ⊢
    exact h17
  have h3 : f (35) = 71 := by
    have h17 : f (f 17) = 4 * 17 + 3 := h₀ 17 (by norm_num)
    rw [h2] at h17
    norm_num at h17 ⊢
    exact h17
  have h4 : f (71) = 143 := by
    have h17 : f (f 35) = 4 * 35 + 3 := h₀ 35 (by norm_num)
    rw [h3] at h17
    norm_num at h17 ⊢
    exact h17
  have h5 : f (143) = 287 := by
    have h17 : f (f 71) = 4 * 71 + 3 := h₀ 71 (by norm_num)
    rw [h4] at h17
    norm_num at h17 ⊢
    exact h17
  have h6 : f (287) = 575 := by
    have h17 : f (f 143) = 4 * 143 + 3 := h₀ 143 (by norm_num)
    rw [h5] at h17
    norm_num at h17 ⊢
    exact h17
  have h7 : f (575) = 1151 := by
    have h17 : f (f 287) = 4 * 287 + 3 := h₀ 287 (by norm_num)
    rw [h6] at h17
    norm_num at h17 ⊢
    exact h17
  have h8 : f (1151) = 2303 := by
    have h17 : f (f 575) = 4 * 575 + 3 := h₀ 575 (by norm_num)
    rw [h7] at h17
    norm_num at h17 ⊢
    exact h17
  have h9 : f (2303) = 4607 := by
    have h17 : f (f 1151) = 4 * 1151 + 3 := h₀ 1151 (by norm_num)
    rw [h8] at h17
    norm_num at h17 ⊢
    exact h17
  exact h9