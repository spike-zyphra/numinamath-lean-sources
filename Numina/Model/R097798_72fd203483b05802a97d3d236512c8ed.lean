import Mathlib

theorem algebra_277679 {a r : ℚ} (hr : r ≠ 0) :
    ∃ d, ∀ n, a * r ^ n - a * r ^ (n + 1) = d * r ^ n := by
  use a * (1 - r)
  intro n
  have h1 : a * r ^ n - a * r ^ (n + 1) = (a * (1 - r)) * r ^ n := by
    ring_nf
  rw [h1]
  <;> ring