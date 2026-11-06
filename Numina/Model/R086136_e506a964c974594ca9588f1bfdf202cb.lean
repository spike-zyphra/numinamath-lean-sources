import Mathlib

theorem algebra_177880 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : (1 + 3 / 100) * x - (1 + 11 / 100) * y = 3) (h2 : x - y = 3.8) :
    x = 15.225 ∧ y = 11.425 := by
  have eq1 : x = y + 3.8 := by
    linarith
  rw [eq1] at h1
  have h3 : y = 11.425 := by
    norm_num at h1 ⊢
    linarith
  have h4 : x = 15.225 := by
    rw [h3] at eq1
    linarith
  constructor
  · exact h4
  · exact h3