import Mathlib

theorem algebra_4456 {f : ℝ → ℝ} (hf : ∀ x, f x + (1 - x) * f (-x) = x ^ 2) :
    ∀ x, f (-x) + (1 + x) * f x = x ^ 2 := by
  intro x
  have h := hf (-x)
  simp [show (-(-x : ℝ)) = x by ring] at h ⊢
  <;> linarith