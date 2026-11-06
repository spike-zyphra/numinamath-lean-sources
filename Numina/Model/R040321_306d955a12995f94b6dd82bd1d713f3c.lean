import Mathlib

theorem algebra_310262 (f : ℝ → ℝ) (h : ∀ x y z, f (x + y) + f (y + z) + f (z + x) ≥ 3 * f (x + 2 * y + z)) :
    f 1 - f 0 = 0 := by
  have h11 : f 0 ≥ f 1 := by 
    have h8 := h 1 0 0
    norm_num at h8 ⊢ 
    linarith
  -- Prove f 1 ≥ f 0.
  have h14 : f 1 ≥ f 0 := by
    have h15 := h (1 / 2) (-1 / 2) (1 / 2)
    norm_num at h15 ⊢
    linarith 
  -- From h11 and h14, prove f 0 = f 1.
  have h01 : f 0 = f 1 := by 
    linarith [h11, h14]
  -- Final goal.
  linarith [h01]