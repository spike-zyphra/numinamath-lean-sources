import Mathlib

theorem algebra_299215 (f : ℝ → ℝ) (h₀ : f 0 = 0)
    (h₁ : ∀ x, f (x + 4) - f x ≤ x ^ 2) (h₂ : ∀ x, f (x + 16) - f x ≥ 4 * x ^ 2 + 48 * x + 224) :
    f 64 = 19840 := by
  have h3 : f 64 ≤ 19840 := by
    have h4 := h₁ 0
    have h8 := h₁ 4
    have h12 := h₁ 8
    have h16 := h₁ 12
    have h20 := h₁ 16
    have h24 := h₁ 20
    have h28 := h₁ 24
    have h32 := h₁ 28
    have h36 := h₁ 32
    have h40 := h₁ 36
    have h44 := h₁ 40
    have h48 := h₁ 44
    have h52 := h₁ 48
    have h56 := h₁ 52
    have h60 := h₁ 56
    have h64 := h₁ 60
    norm_num [h₀] at h4 h8 h12 h16 h20 h24 h28 h32 h36 h40 h44 h48 h52 h56 h60 h64
    linarith

  have h4 : f 64 ≥ 19840 := by
    have h16_0 := h₂ 0
    have h32_0 := h₂ 16
    have h48_0 := h₂ 32
    have h64_0 := h₂ 48
    norm_num [h₀] at h16_0 h32_0 h48_0 h64_0
    linarith

  linarith [h3, h4]