import Mathlib

theorem inequalities_80786 (a : ℕ → ℝ) (d : ℝ) (h₀ : ∀ n < 5, a n = a 0 + d * n)
    (h₁ : 0 < d) (h₂ : ∀ n < 5, 0 < a n) :
    (a 2)^3 ≤ (1 / 10) * ((a 0)^3 + 4 * (a 1)^3 + 4 * (a 3)^3 + (a 4)^3) := by 
  have a1 : a 1 = a 0 + d := by
    specialize h₀ 1 (by norm_num)
    rw [h₀]
    ring
  have a2 : a 2 = a 0 + 2 * d := by
    specialize h₀ 2 (by norm_num)
    rw [h₀]
    ring
  have a3 : a 3 = a 0 + 3 * d := by 
    specialize h₀ 3 (by norm_num)
    rw [h₀]
    ring
  have a4 : a 4 = a 0 + 4 * d := by 
    specialize h₀ 4 (by norm_num)
    rw [h₀]
    ring
  rw [a2, a1, a3, a4]
  have pos0 : 0 < a 0 := by
    have h00 := h₂ 0 (by norm_num)
    linarith
  have pos1 : 0 < a 0 + d := by
    have h11 := h₂ 1 (by norm_num)
    nlinarith
  have pos3 : 0 < a 0 + 3 * d := by 
    have h33 := h₂ 3 (by norm_num)
    nlinarith
  have pos4 : 0 < a 0 + 4 * d := by 
    have h44 := h₂ 4 (by norm_num)
    nlinarith
  nlinarith [sq_nonneg (a 0 - (a 0 + d)), sq_nonneg (a 0 - (a 0 + 2 * d)), sq_nonneg (a 0 - (a 0 + 3 * d)), sq_nonneg (a 0 - (a 0 + 4 * d)), sq_nonneg (d), sq_nonneg (a 0), sq_nonneg (a 0 + d), sq_nonneg (a 0 + 3 * d), sq_nonneg (a 0 + 4 * d), mul_pos h₁ pos0, mul_pos h₁ pos1, mul_pos h₁ pos3, mul_pos h₁ pos4]