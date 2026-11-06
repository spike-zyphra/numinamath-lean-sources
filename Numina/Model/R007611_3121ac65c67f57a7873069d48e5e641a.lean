import Mathlib

theorem algebra_14198 (e b k : ℝ)
    (h₀ : e = 4)
    (h₁ : b = (2 / 3) * e)
    (h₂ : k = (7 / 5) * b) :
    k = 56 / 15 := by
  have hb : b = 8 / 3 := by
    rw [h₀] at h₁ -- substitute e = 4 into b = (2/3) * e
    linarith
  rw [hb] at h₂ -- substitute b = 8/3 into k = (7/5) * b
  linarith -- compute (7/5) * (8/3) = 56/15 and verify equality