import Mathlib

theorem algebra_177207 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (hxy : x = y + 75) (h : x * y - 1000 = 227 * x + 113 * y) :
    x = 159234 ∧ y = 158469 := by
  have h1 : x * y ≥ 1000 := by
    by_contra h1
    push_neg at h1
    have h2 : x * y < 1000 := by linarith
    have h3 : x * y - 1000 = 0 := by
      omega
    rw [h3] at h
    nlinarith [hxy]
  have eq1 : x * y = 227 * x + 113 * y + 1000 := by
    omega
  rw [show x = y + 75 by linarith [hxy]] at eq1
  have eq2 : y ≤ 321 := by
    nlinarith [sq_nonneg (y : ℕ)]
  interval_cases y <;> omega