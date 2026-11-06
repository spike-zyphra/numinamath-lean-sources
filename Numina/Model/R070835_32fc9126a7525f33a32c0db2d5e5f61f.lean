import Mathlib

theorem algebra_276642 {p q : ℝ} (hp : p ≠ 0) (h : ∀ x y, p * x + 2 * y = 7 → 3 * x + q * y = 5) :
    p = 21 / 5 := by
  have h1 := h 0 (7 / 2) (by
    -- Verify that (0, 7/2) satisfies px + 2y = 7
    field_simp
    <;> linarith
  )
  have h2 := h (7 / p) 0 (by
    -- Verify that (7/p, 0) satisfies px + 2y = 7
    field_simp [hp]
    <;> linarith
  )
  field_simp [hp] at h2
  linarith