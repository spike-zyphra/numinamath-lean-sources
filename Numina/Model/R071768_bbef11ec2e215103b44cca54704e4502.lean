import Mathlib

theorem algebra_118558 (x y : ℝ) (hx : 4 ≤ x ∧ x ≤ 100) (hy : 4 ≤ y ∧ y ≤ 100)
    (hxy : x > 0 ∧ y > 0) :
    |(x + y) / 2 - ((x + y + y) / 3)| ≤ 16 := by
  have h1 : -16 ≤ (x + y) / 2 - (x + y + y) / 3 := by
    linarith [hx.left, hy.right]
  have h2 : (x + y) / 2 - (x + y + y) / 3 ≤ 16 := by
    linarith [hx.right, hy.left]
  apply abs_le.mpr
  constructor <;> linarith [h1, h2]