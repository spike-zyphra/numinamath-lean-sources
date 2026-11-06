import Mathlib

theorem algebra_177579 {a b c : ℝ} (p : ℝ → ℝ)
    (h₀ : ∀ x, p x = (x - a) * (x - b) + (x - b) * (x - c) + (x - c) * (x - a)) :
    (∀ x, p x ≥ 0) ↔ a = b ∧ b = c := by
  constructor
  · -- Assume that ∀ x, p x ≥ 0, need to prove a = b ∧ b = c
    intro h
    have h1 := h ((a + b + c) / 3)
    rw [h₀] at h1
    have h1a : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg ((a + b + c) / 3 - a), sq_nonneg ((a + b + c) / 3 - b), sq_nonneg ((a + b + c) / 3 - c)]
    have h2a : a - b = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have h3a : b - c = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    constructor
    · -- a = b
      linarith
    · -- b = c
      linarith
  · -- Assume a = b ∧ b = c, need to prove ∀ x, p x ≥ 0
    rintro ⟨hb, hc⟩
    intro x
    rw [h₀]
    have hb' : b = a := by
      linarith
    have hc' : c = a := by
      linarith
    rw [hb', hc']
    nlinarith [sq_nonneg (x - a), sq_nonneg (x - b), sq_nonneg (x - c)]