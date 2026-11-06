import Mathlib

theorem algebra_9185 (m : ℝ)
    (h : ∀ x, 2 * x ^ 2 + 4 * x + m ≠ 3 * x ^ 2 - 2 * x + 6) : m < -3 := by
  by_contra hm
  push_neg at hm
  have hne : ∃ x, 2 * x ^ 2 + 4 * x + m = 3 * x ^ 2 - 2 * x + 6 := by
    have h1 : 3 + m ≥ 0 := by linarith
    use 3 + Real.sqrt (3 + m)
    nlinarith [Real.sqrt_nonneg (3 + m), Real.sq_sqrt (show (3 + m) ≥ 0 by linarith)]
  rcases hne with ⟨x, hx⟩
  specialize h x
  contradiction