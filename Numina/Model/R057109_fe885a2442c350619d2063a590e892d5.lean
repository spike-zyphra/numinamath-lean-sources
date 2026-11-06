import Mathlib

theorem algebra_2497 {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 180) (h : 90 - θ = (180 - θ) / 7 + 6) : θ = 68 := by
  rcases hθ with ⟨hθ1, hθ2⟩
  linarith