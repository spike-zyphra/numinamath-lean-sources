import Mathlib

theorem algebra_314950 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = (x ^ 2 - 1) * (x ^ 2 + a * x + b))
    (h : ∀ x, f x = f (4 - x)) :
    IsLeast (Set.image f {x | ∃ y, x = y}) (-16) := by

  have h1 := h 0
  rw [hf, hf] at h1

  have h2 := h 1
  rw [hf, hf] at h2

  have h3 := h 2
  rw [hf, hf] at h3

  have h4 := h 3
  rw [hf, hf] at h4

  have h5 := h 4
  rw [hf, hf] at h5

  have h6 := h 5
  rw [hf, hf] at h6

  ring_nf at h1 h2 h3 h4 h5 h6

  have ha : a = -8 := by
    nlinarith

  have hb : b = 15 := by
    nlinarith

  constructor
  · -- First, show -16 is in the image
    use 2 + Real.sqrt 5
    constructor
    · -- Show it exists
      use 2 + Real.sqrt 5
    · -- Show it equals -16
      have h7 : ∀ x, f x = (x ^ 2 - 1) * (x ^ 2 - 8 * x + 15) := by
        intro x
        rw [hf x]
        rw [ha, hb]
        all_goals ring
      rw [h7 (2 + Real.sqrt 5)]
      have h8 : (2 + Real.sqrt 5 : ℝ) ^ 2 = 4 + 4 * Real.sqrt 5 + (Real.sqrt 5) ^ 2 := by
        ring
      have h9 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      rw [h8, h9]
      ring_nf
      <;> norm_num [Real.sqrt_pos.mpr, h9]
  · -- Now, show it's minimum
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h7 : ∀ x, f x = (x ^ 2 - 1) * (x ^ 2 - 8 * x + 15) := by
      intro x
      rw [hf x]
      rw [ha, hb]
      all_goals ring
    rw [show y = f x by linarith [hx]]
    rw [h7 x]
    nlinarith [ sq_nonneg (x ^ 2 - 5), sq_nonneg (x - 2 - Real.sqrt 5), sq_nonneg (x - 2 + Real.sqrt 5), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]