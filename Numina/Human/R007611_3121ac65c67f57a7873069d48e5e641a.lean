import Mathlib

/- Eugene, Brianna, and Katie are going on a run. Eugene runs at a rate of 4 miles per hour. If Brianna runs $\frac{2}{3}$ as fast as Eugene, and Katie runs $\frac{7}{5}$ as fast as Brianna, how fast does Katie run? -/
theorem algebra_14198 (e b k : ℝ)
    (h₀ : e = 4)
    (h₁ : b = (2 / 3) * e)
    (h₂ : k = (7 / 5) * b) :
    k = 56 / 15 := by
  rw [h₁, h₀] at h₂
  linarith