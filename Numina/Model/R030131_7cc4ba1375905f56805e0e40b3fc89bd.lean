import Mathlib

open Real

theorem inequalities_1478 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (_ : 0 < c)
    (h : a + b + c = 3) :
    sqrt (a^2 + a - b - c + 2) + sqrt (b^2 + b - a - c + 2) +
    sqrt (c^2 + c - a - b + 2) ≤ 3 * sqrt 2 := by

  have h₁ : a + b + c = 3 := h

  have h₁₁ : a^2 + a - b - c + 2 = a^2 + 2 * a - 1 := by
    nlinarith

  have h₂₂ : b^2 + b - a - c + 2 = b^2 + 2 * b - 1 := by
    nlinarith

  have h₃₃ : c^2 + c - a - b + 2 = c^2 + 2 * c - 1 := by
    nlinarith

  rw [h₁₁, h₂₂, h₃₃]

  have h6 : sqrt (a^2 + 2 * a - 1) ≤ sqrt 2 * a := by
    have h7 : a^2 + 2 * a - 1 ≤ 2 * a^2 := by
      nlinarith [sq_nonneg (a - 1)]
    have h8 : sqrt (a^2 + 2 * a - 1) ≤ sqrt (2 * a^2) := Real.sqrt_le_sqrt (by linarith)
    have h9 : sqrt (2 * a^2) = sqrt 2 * a := by
      have h11 : 0 ≤ a := by linarith
      have h12 : 2 * a^2 = (sqrt 2 * a) ^ 2 := by
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
        all_goals linarith
      rw [h12]
      simp [h11]
    linarith

  have h7 : sqrt (b^2 + 2 * b - 1) ≤ sqrt 2 * b := by
    have h8 : b^2 + 2 * b - 1 ≤ 2 * b^2 := by
      nlinarith [sq_nonneg (b - 1)]
    have h9 : sqrt (b^2 + 2 * b - 1) ≤ sqrt (2 * b^2) := Real.sqrt_le_sqrt (by linarith)
    have h10 : sqrt (2 * b^2) = sqrt 2 * b := by
      have h11 : 0 ≤ b := by linarith
      have h12 : 2 * b^2 = (sqrt 2 * b) ^ 2 := by
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
        all_goals linarith
      rw [h12]
      simp [h11]
    linarith

  have h8 : sqrt (c^2 + 2 * c - 1) ≤ sqrt 2 * c := by
    have h9 : c^2 + 2 * c - 1 ≤ 2 * c^2 := by
      nlinarith [sq_nonneg (c - 1)]
    have h10 : sqrt (c^2 + 2 * c - 1) ≤ sqrt (2 * c^2) := Real.sqrt_le_sqrt (by linarith)
    have h11 : sqrt (2 * c^2) = sqrt 2 * c := by
      have h12 : 0 ≤ c := by linarith
      have h13 : 2 * c^2 = (sqrt 2 * c) ^ 2 := by
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
        all_goals linarith
      rw [h13]
      simp [h12]
    linarith

  have h9 : sqrt (a^2 + 2 * a - 1) + sqrt (b^2 + 2 * b - 1) + sqrt (c^2 + 2 * c - 1) ≤ sqrt 2 * (a + b + c) := by
    linarith [h6, h7, h8]

  have h10 : a + b + c = 3 := h

  rw [h10] at h9

  have h11 : sqrt 2 * (3 : ℝ) = 3 * sqrt 2 := by
    ring_nf

  linarith [h9, h11]