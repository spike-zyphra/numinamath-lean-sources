import Mathlib

theorem algebra_250538 (a b : Fin 3 → ℝ) (x : ℝ → ℝ)
    (hroots : ∀ i, x 0 ^ 2 + a i * x 0 + b i = 0) :
    (x 0) ^ 2 + (a 0 + a 1 + a 2) / 3 * x 0 + (b 0 + b 1 + b 2) / 3 = 0 := by
  have h₁ := hroots 0
  have h₂ := hroots 1
  have h₃ := hroots 2
  simp [Fin.succ] at h₁ h₂ h₃ ⊢
  linarith