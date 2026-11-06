import Mathlib

theorem algebra_239991 (a : ℕ → ℕ → ℕ) (ha : ∀ n, a n 0 = n + 1)
    (h : ∀ n m, a n (m + 1) = a n m + a n (m + 2)) :
    a 2015 0 = 2 ^ 2014 * 2017 := by
  have h1 := h 0 0
  simp [ha] at h1
  have h2 := h 0 1
  simp [show a 0 0 = 1 by linarith [ha 0], h1] at h2
  all_goals
    omega