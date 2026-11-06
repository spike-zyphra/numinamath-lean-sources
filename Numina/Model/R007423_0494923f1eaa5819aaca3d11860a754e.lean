import Mathlib

  theorem inequalities_214887 (a b c d : ℝ) (h₀ : a^2 + b^2 = 1) (h₁ : c^2 + d^2 = 1) :
    |a * c - b * d| ≤ 1 := by
    have h : (a * c - b * d) ^ 2 ≤ 1 := by
      have h2 : (a^2 + b^2) * (c^2 + d^2) = 1 := by 
        rw [h₀, h₁]
        all_goals norm_num
      have h3 : (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
        ring_nf
      rw [h2] at h3
      nlinarith [sq_nonneg (a * d + b * c)]
    have h4 : -1 ≤ a * c - b * d ∧ a * c - b * d ≤ 1 := by 
      constructor
      · -- Proof that -1 ≤ a * c - b * d
        nlinarith [sq_nonneg (a * c - b * d)]
      · -- Proof that a * c - b * d ≤ 1
        nlinarith [sq_nonneg (a * c - b * d)]
    apply abs_le.mpr
    constructor <;> linarith