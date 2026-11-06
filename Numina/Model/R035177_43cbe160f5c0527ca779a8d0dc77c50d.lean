import Mathlib

theorem algebra_21695 (a b c : ℕ → ℝ)
    (h₀ : ∃ d, ∀ n, a n = a 0 + d * n)
    (h₁ : ∃ r, ∀ n, b n = b 0 * r ^ n)
    (h₂ : ∀ n, c n = a n + b n)
    (h₃ : c 0 = 1)
    (h₄ : c 1 = 4)
    (h₅ : c 2 = 15)
    (h₆ : c 3 = 2) :
    c 4 = 61 := by
  rcases h₀ with ⟨d, ha⟩
  rcases h₁ with ⟨r, hb⟩
  have h7 : c 0 = a 0 + b 0 := h₂ 0
  rw [h7] at h₃
  have h8 : c 1 = a 1 + b 1 := h₂ 1
  rw [h8] at h₄
  have h9 : a 1 = a 0 + d := by 
    specialize ha 1
    norm_num at ha
    linarith
  have h10 : b 1 = b 0 * r ^ 1 := hb 1
  rw [h9, h10] at h₄
  have h11 : c 2 = a 2 + b 2 := h₂ 2
  rw [h11] at h₅
  have h12 : a 2 = a 0 + 2 * d := by 
    specialize ha 2
    norm_num at ha
    linarith
  have h13 : b 2 = b 0 * r ^ 2 := hb 2
  rw [h12, h13] at h₅
  have h14 : c 3 = a 3 + b 3 := h₂ 3
  rw [h14] at h₆
  have h15 : a 3 = a 0 + 3 * d := by 
    specialize ha 3
    norm_num at ha
    linarith
  have h16 : b 3 = b 0 * r ^ 3 := hb 3
  rw [h15, h16] at h₆
  have h17 : c 4 = a 4 + b 4 := h₂ 4
  have h18 : a 4 = a 0 + 4 * d := by 
    specialize ha 4
    norm_num at ha
    linarith
  have h19 : b 4 = b 0 * r ^ 4 := hb 4
  rw [h17, h18, h19]
  nlinarith [sq_nonneg (r + 3), sq_nonneg (b 0 - 1 / 2), sq_nonneg (d - 5), sq_nonneg (a 0 - 1 / 2)]
  all_goals linarith