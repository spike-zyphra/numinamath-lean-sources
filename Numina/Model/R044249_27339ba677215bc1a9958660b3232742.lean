import Mathlib

theorem algebra_113301 {a b : ℝ} (h : (a + b + a) * (a + b + b) = 9) : a * b ≤ 1 := by
  -- Expanding the given equation $(2a + b)(a + 2b) = 9$ into $2a^2 + 5ab + 2b^2 = 9$.
  have eq1 : 2 * a^2 + 5 * a * b + 2 * b^2 = 9 := by
    ring_nf at h ⊢
    linarith
  -- Now relate a^2 + b^2 with ab. Using that (a - b)^2 ≥ 0, we have a^2 + b^2 ≥ 2ab
  nlinarith [sq_nonneg (a - b)]