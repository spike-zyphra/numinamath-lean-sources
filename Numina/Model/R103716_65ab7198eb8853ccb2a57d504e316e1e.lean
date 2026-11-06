import Mathlib

theorem algebra_298676 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) + f (x - y) = 2 * f x - Real.cos y)
    (h0 : f 0 = A) (hπ2 : f (Real.pi / 2) = B) :
    ∀ x, f x = B * Real.sin x + A * Real.cos x := by 
  have h1 := h 0 0
  simp [show f 0 = A by linarith] at h1
  have h_contra : Real.cos (0 : ℝ) = 0 := by
    nlinarith
  have h1' : Real.cos (0 : ℝ) = 1 := Real.cos_zero
  exfalso
  linarith [h1', h_contra]