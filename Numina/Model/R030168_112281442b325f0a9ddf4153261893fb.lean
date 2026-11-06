import Mathlib

theorem algebra_239974 (f : ℝ → ℝ) :
    (∀ x y, f (x * y + 1) = f x * f y - f y - x + 2) ↔ ∀ x, f x = x + 1 := by
  constructor
  · -- Assume ∀ x y, f (x * y + 1) = f x * f y - f y - x + 2 prove ∀ x, f x = x + 1
    intro h
    have h1 : f 1 = f 0 ^ 2 - f 0 + 2 := by
      specialize h 0 0
      norm_num at h
      linarith
    -- substituting x = 0 and y =1
    have h2 : f 1 = f 0 * f 1 - f 1 + 2 := by
      specialize h 0 1
      norm_num at h
      linarith
    have h3 : f 0 = 1 := by
      have h4 : f 1 = f 0 ^ 2 - f 0 + 2 := h1
      rw [h4] at h2
      have h5 : f 0 ^ 3 - 3 * f 0 ^ 2 + 4 * f 0 - 2 = 0 := by
        nlinarith [sq_nonneg (f 0), sq_nonneg (f 1), sq_pos_of_pos (show (3 : ℝ) > 0 by linarith)]
      have h6 : (f 0 - 1) * (f 0 ^ 2 - 2 * f 0 + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h6) with h7 h8
      · 
        linarith
      · 
        have h9 : f 0 ^ 2 - 2 * f 0 + 2 = 0 := by linarith
        have h10 : f 0 ^ 2 - 2 * f 0 + 2 > (0 : ℝ) := by
          nlinarith [sq_nonneg (f 0 - 1)]
        nlinarith [h10, sq_nonneg (f 0 - 1)]
    intro x
    have h4 : f 1 = 2 := by
      rw [show f 0 = 1 by linarith [h3]] at h1
      nlinarith
    have h10 := h x 0
    simp [h3] at h10
    rw [h4] at h10
    have hx : f x = x + 1 := by
      nlinarith
    exact hx
  · -- Assume ∀ x, f x = x + 1 prove ∀ x y, f (x * y + 1) = f x * f y - f y - x + 2
    intro h x y
    rw [h, h, h]
    ring