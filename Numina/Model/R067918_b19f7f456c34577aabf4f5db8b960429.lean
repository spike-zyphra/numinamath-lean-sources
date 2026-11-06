import Mathlib

theorem algebra_227801 {x y : ℝ} (h₀ : x + y = 135) (h₁ : 0.35 * x = 0.28 * y) :
    x = 60 ∧ y = 75 := by
  have eq2 : 35 * x = 28 * y := by
    calc
      35 * x = (0.35 * x) * 100 := by ring_nf
      _ = (0.28 * y) * 100 := by rw [h₁]
      _ = 28 * y := by ring_nf
  have hx : x = 60 := by
    linarith [h₀, eq2]
  have hy : y = 75 := by
    linarith [h₀, hx]
  exact ⟨hx, hy⟩