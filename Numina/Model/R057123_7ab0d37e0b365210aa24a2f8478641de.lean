import Mathlib

theorem algebra_307108 {a : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (h : -a m < 0) (h' : ∑ i in Finset.range (m + 1), a i < 0) :
    m > 0 := by
  by_contra h1
  have h2 : m = 0 := by
    omega
  rw [h2] at h h'
  simp at h h'
  all_goals linarith