import Mathlib

theorem algebra_132915 {f : ℝ → ℝ} (h0 : f 0 = 1)
    (hf : ∀ x y, f (x * y + 1) = f x * f y - f y - x + 2) :
    ∀ x, f x = x + 1 := by 
  have h1 := hf 0 0
  simp [h0] at h1
  have h2 := hf (0:ℝ) 
  simp [h0] at h2
  intro x
  have h3 := hf x 0
  simp [h0, h1] at h3
  linarith