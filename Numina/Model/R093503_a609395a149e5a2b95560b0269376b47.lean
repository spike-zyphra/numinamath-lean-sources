import Mathlib

theorem algebra_212641 {x y z : ℝ} (h1 : x + y = z) (h2 : y = 4 * x) (h3 : x > 0) (h4 : y > 0) (h5 : z > 0)
    (h6 : x * 10000 + y * 20000 = z * 60000) (h7 : y * 42000 ≤ z * 60000 ∧ z * 60000 ≤ y * 60000) :
    12.5 ≤ y / (x + y + z) * 100 ∧ y / (x + y + z) * 100 ≤ 15 := by 
  have h8 : x = 0 := by
    nlinarith [h1, h2, h6]
  linarith