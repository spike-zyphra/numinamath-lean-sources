import Mathlib

theorem algebra_4324 {x y : ℝ} (h₀ : x + y = 620) (h₁ : (1 + 20 / 100) * x = 168)
    (h₂ : (1 + 30 / 100) * y = z) :
    z = 624 := by
  have hx : x = 140 := by
    nlinarith
  have hy : y = 480 := by
    linarith [h₀, hx]
  have hz : z = 624 := by
    nlinarith [h₂, hy]
  exact hz