import Mathlib

theorem algebra_197302 {a b : ℝ} (ha : a ≠ 0) (h : ∀ x : ℝ, (2 * x ^ 3 - 5 * x ^ 2 + 7 * x - 8) * (a * x ^ 2 + b * x + 11) = 8 * x ^ 5 - 17 * x ^ 2 - 3 * x - 88) :
    a = 4 ∧ b = 10 := by
  have h₁ := h 0
  ring_nf at h₁
  have h₂ := h 1
  ring_nf at h₂
  have h₃ := h 2
  ring_nf at h₃
  have h₄ := h 3
  ring_nf at h₄
  have h₅ := h 4
  ring_nf at h₅
  have h₆ := h 5
  ring_nf at h₆
  constructor
  · -- Show $a = 4$
    nlinarith
  · -- Show $b = 10$
    nlinarith