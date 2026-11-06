import Mathlib

theorem algebra_243107 (a b c d : ℝ) (h₀ : a^2 + b^2 = 1) (h₁ : c^2 + d^2 = 4) :
    a * d + b * c ∈ Set.Icc (-2) 2 := by
  have h2 : -2 ≤ a * d + b * c ∧ a * d + b * c ≤ 2 := by
    have h3 : (a * d + b * c) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
      nlinarith [sq_nonneg (a * c - b * d)]
    have h4 : (a * d + b * c) ^ 2 ≤ 4 := by
      rw [h₀, h₁] at h3
      nlinarith
    constructor
    · nlinarith [sq_nonneg (a * d + b * c), h4]
    · nlinarith [sq_nonneg (a * d + b * c), h4]
  simp [Set.mem_Icc]
  constructor <;> linarith [h2.1, h2.2]