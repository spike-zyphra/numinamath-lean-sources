import Mathlib

theorem algebra_181791 {x y : ℝ} (hxy : x > 0 ∧ y > 0)
    (h1 : x * 3 = y * 6) (h2 : x * 2 = y * 3) :
    x * 54 = y * 12 := by
  rcases hxy with ⟨hx, hy⟩
  nlinarith