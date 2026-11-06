import Mathlib

theorem algebra_212698 {x y z : ℝ} (h1 : x + y = z) (h2 : y = 3 * x) (h3 : x > 0) (h4 : y > 0) (h5 : z > 0)
    (h6 : 10000 < x - y ∧ x - y < 18000) (h7 : 18000 < y ∧ y < 42000) :
    15 ≤ y / (x + y + z) * 100 ∧ y / (x + y + z) * 100 ≤ 25 := by
  have h8 : x - y < 0 := by
    have h9 : y = 3 * x := h2
    linarith
  linarith