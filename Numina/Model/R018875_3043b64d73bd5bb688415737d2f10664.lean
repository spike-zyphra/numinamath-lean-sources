import Mathlib

theorem algebra_199962 {g : ℤ → ℤ} (h1 : g 1 > 1) (h2 : ∀ x y, g (x + y) + x * g y + y * g x = g x * g y + x + y + x * y)
    (h3 : ∀ x, 3 * g x = g (x + 1) + 2 * x - 1) : g 5 = 248 := by
  have h4 : g 0 = 0 ∨ g 0 = 1 := by 
    have h5 := h2 0 0
    simp at h5
    have : g 0 * (g 0 - 1) = 0 := by linarith
    cases' (mul_eq_zero.mp this) with h6 h7
    · left
      linarith
    · right
      linarith
  cases h4 with
  | inl h4 =>
    exfalso
    have h5 := h2 1 0
    simp [h4] at h5
    linarith [show g 1 > 1 by linarith, h5]
  | inr h4 =>
    -- Now that we have g(0) = 1, we can compute g(1).
    have h5 : g 0 = 1 := h4
    have h6 : 3 * g 0 = g 1 + 2 * 0 - 1 := h3 0
    rw [h5] at h6
    have h7 : g 1 = 4 := by linarith
    -- Compute g(2) using recurrence
    have h8 : 3 * g 1 = g 2 + 2 * 1 - 1 := h3 1
    rw [h7] at h8
    have h9 : g 2 = 11 := by linarith
    -- Compute g(3) using recurrence
    have h10 : 3 * g 2 = g 3 + 2 * 2 - 1 := h3 2
    rw [h9] at h10
    have h11 : g 3 = 30 := by linarith
    -- Compute g(4) using recurrence
    have h12 : 3 * g 3 = g 4 + 2 * 3 - 1 := h3 3
    rw [h11] at h12
    have h13 : g 4 = 85 := by linarith
    -- Compute g(5) using recurrence
    have h14 : 3 * g 4 = g 5 + 2 * 4 - 1 := h3 4
    rw [h13] at h14
    linarith