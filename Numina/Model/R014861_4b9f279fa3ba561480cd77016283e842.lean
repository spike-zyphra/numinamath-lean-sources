import Mathlib

theorem algebra_316932 {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (h1 : a 1 = 0) (h2 : ∀ n, (a (n + 1)) ^ 2 + a (n + 1) - 1 = a n ^ 2)
    (S T : ℕ → ℝ) (hS : ∀ n, S n = ∑ i in Finset.Icc 1 n, a i)
    (hT : ∀ n, T n = ∑ k in Finset.Icc 1 n, 1 / (∏ j in Finset.Icc 1 k, (1 + a j))) :
    ∀ n, 0 < n → a n * n - 2 < 0 ∧ T n < 3 := by

  have h3 := h2 0
  simp [h1] at h3
  have h4 : a 0 ^ 2 ≥ 0 := by
    nlinarith [ha 0]

  nlinarith