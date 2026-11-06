import Mathlib

theorem algebra_286609 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : (x + y) ^ 2 = 2500 ∧ x * y = 500) :
    x ^ 3 + y ^ 3 = 50000 := by
  rcases h with ⟨h1, h2⟩
  have h3 : x + y = 50 := by
    have h4 : 0 < x + y := by
      linarith
    nlinarith [sq_nonneg (x + y - 50)]
  have h4 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by
    ring
  rw [h4]
  rw [h3, h2]
  norm_num