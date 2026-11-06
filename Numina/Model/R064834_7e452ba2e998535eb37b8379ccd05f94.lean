import Mathlib

theorem algebra_9199 {t : ℝ} (ht : t > 0) (a b : ℕ → ℝ)
(ha : a 1 = 1) (hsum : ∀ n, 3 * t * ∑ i ∈ Finset.range n, a i - (2 * t + 3) * ∑ i ∈ Finset.range (n - 1), a i = 3 * t)
(hb1 : b 1 = 1) (hbn : ∀ n ≥ 2, b n = (2 / 3) * (2 / 3) * b (n - 1) + 1 / 3) :
∀ n, b n = (2 / 3) * n + 1 / 3 := by
  have h0 := hsum 0
  simp [Finset.sum_range_zero] at h0
  nlinarith