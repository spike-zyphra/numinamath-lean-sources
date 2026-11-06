import Mathlib

theorem algebra_197627 {f : ℝ → ℝ → ℝ} (hf1 : ∀ x, f x 0 = 1)
    (hf2 : ∀ x y z, f (f x y) z = f z (x * y) + z) (c : ℝ)
    (hc : f 1 2004 = c) : c = 2005 := by
  have h1 : f 0 0 = 1 := hf1 0
  have h2 : ∀ z : ℝ, f 1 z = 1 + z := by
    intro z
    have h3 : f (f 0 0) z = f z (0 * 0) + z := hf2 0 0 z
    have h4 : f 0 0 = 1 := h1
    simp [h4] at h3
    have h5 : f z 0 = 1 := hf1 z
    simp [h5] at h3
    linarith
  have h3 : f 1 2004 = 1 + 2004 := by 
    apply h2 2004 
  linarith [hc, h3]