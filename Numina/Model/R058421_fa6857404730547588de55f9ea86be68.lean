import Mathlib

theorem algebra_9077 {f g : ℝ → ℝ} (hf : ∀ x, f x = (x ^ 2 + 3) ^ 2) (hg : ∀ x, g x = 4 * x * (x ^ 2 + 3 * x + 4)) (n : ℝ) (hn : n > 0) (h : f n + g (n - 1) = 10 ^ 8) : n = 99 := by
  have h1 : f n = (n ^ 2 + 3) ^ 2 := hf n
  have h2 : g (n - 1) = 4 * (n - 1) * ((n - 1) ^ 2 + 3 * (n - 1) + 4) := by
    apply hg
  rw [h1, h2] at h
  have h_eq : (n + 1) ^ 4 = 10 ^ 8 := by
    nlinarith [sq_nonneg (n ^ 2), sq_nonneg (n - 1), sq_nonneg (n + 1), sq_nonneg (n * (n - 1)), sq_nonneg (n * (n + 1)), sq_nonneg ((n - 1) * (n + 1))]
  have h_eq1 : (n + 1) ^ 4 - 10 ^ 8 = 0 := by linarith
  have h5 : n + 1 = 100 := by
    nlinarith [sq_nonneg ((n + 1) ^ 2 - 10000), sq_nonneg ((n + 1) - 100), sq_nonneg ((n + 1) + 100), sq_nonneg (n - 99), sq_pos_of_pos (show 0 < n by linarith), sq_nonneg ((n + 1) ^ 2)]
  linarith