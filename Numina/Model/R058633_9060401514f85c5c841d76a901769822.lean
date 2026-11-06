import Mathlib

theorem algebra_211782 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x * y = 1) (p : ℝ) (hp : 0 < p) :
    (1 + p / 100) * x * (y * (1 - p / (100 + p))) = 1 := by
  have h1 : (1 + p / 100) * x * (y * (1 - p / (100 + p))) =
           ( (1 + p / 100) * (1 - p / (100 + p)) ) * (x * y) := by
    ring
  rw [h1, hxy]
  field_simp
  <;> ring