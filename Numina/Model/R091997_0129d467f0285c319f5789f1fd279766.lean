import Mathlib

theorem algebra_132277 (x y z : ℝ) (h1 : 2*x+3*y+z+6=0) (h2 : x-3*y-2*z+3=0) :
    (x+3)/(-3)=y/5 ∧ y/5=z/(-9) := by
  constructor
  · -- Prove (x + 3)/(-3) = y/5
    field_simp at *
    linarith [h1, h2]
  · -- Prove y/5 = z/(-9)
    field_simp at *
    linarith [h1, h2]