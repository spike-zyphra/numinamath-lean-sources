import Mathlib

theorem algebra_232175 (x : Fin 50 → ℝ) (hx : ∀ i, 1 - x i * x ((i + 1) % 50) * x ((i + 2) % 50) = 0)
    (hx' : ∀ i, 1 + x ((i + 1) % 50) * x ((i + 2) % 50) * x ((i + 3) % 50) = 0) :
    ∀ i, x i = (-1 : ℝ) ^ (i.1 + 1) := by
  have h0 := hx 0
  have h1 := hx' 0
  have h2 := hx 1
  simp at h0 h1 h2
  linarith