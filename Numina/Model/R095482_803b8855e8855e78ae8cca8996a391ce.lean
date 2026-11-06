import Mathlib

open Real

theorem calculus_187205 (x y : ℝ → ℝ) (hx : Differentiable ℝ x)
    (hy : Differentiable ℝ y) (hxy : ∀ t, x t = 1 - 1 / y t ∧ y t = 1 / (x t - t))
    (hxy0 : x 0 = 1 ∧ y 0 = 1) :
    ∃ c d, ∀ t, x t = c * exp (-d * t) ∧ y t = d * exp (-c * t) := by
  have h1 := hxy 0
  have hx0 : x 0 = 1 := hxy0.1
  have hy0 : y 0 = 1 := hxy0.2
  rcases h1 with ⟨h11, h12⟩
  rw [hy0] at h11
  linarith [hx0, h11]