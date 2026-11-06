import Mathlib

theorem inequalities_224272 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    12 * x * y ≤ 4 * x * (1 - y) + 9 * y * (1 - x) := by
  have h1 : 4 * x * (1 - y) + 9 * y * (1 - x) = 4 * x + 9 * y - 13 * x * y := by 
    ring 
  have h3 : 12 * x * y ≤ 4 * x + 9 * y - 13 * x * y := by 
    have h4 : 0 ≤ 4 * x + 9 * y - 25 * x * y := by 
      nlinarith [sq_nonneg (x - 3 / 5), sq_nonneg (y - 2 / 5), 
        sq_nonneg (x - y), 
        mul_nonneg hx hy, 
        mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ 1 - y by linarith), 
        sq_nonneg (x + y - 1), 
        mul_nonneg hx (show 0 ≤ 1 - x by linarith), 
        mul_nonneg hy (show 0 ≤ 1 - y by linarith),
        mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith)
      ]
    linarith 
  linarith [h1, h3]