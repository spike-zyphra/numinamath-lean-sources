import Mathlib

theorem algebra_100522 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : (1 + 3 * x + 2 * y) / (1 + 2 * x + 3 * y) = 4) (h2 : (1 + 2 * x + 3 * y) / (1 + 3 * x + 2 * y) = 1 / 2) :
    y / x = 8 := by
  have h3 : 1 + 2 * x + 3 * y ≠ 0 := by
    by_contra h
    rw [h] at h1
    field_simp at h1

  have h4 : 1 + 3 * x + 2 * y ≠ 0 := by
    by_contra h
    rw [h] at h2
    field_simp at h2

  have eq1 : 1 + 3 * x + 2 * y = 4 * (1 + 2 * x + 3 * y) := by
    field_simp [h3] at h1
    nlinarith
  
  have eq2 : 2 * (1 + 2 * x + 3 * y) = (1 + 3 * x + 2 * y) := by
    field_simp [h4] at h2
    nlinarith

  -- Note: from these equations, we derive a contradiction in positivity.
  have eq3 : y > 0 := hy
  have eq4 : x > 0 := hx
  
  -- The equations lead to a contradiction with y > 0
  nlinarith [sq_nonneg (x - 0), sq_nonneg (y - 0), sq_nonneg (x), sq_nonneg (y)]