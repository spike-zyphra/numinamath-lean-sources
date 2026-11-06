import Mathlib

theorem algebra_283534 {a S : ℕ → ℝ} (hS : ∀ n, S n = ∑ i in Finset.range n, a i)
    (ha : ∃ r, ∀ n, a n = a 0 * r ^ n) (hS10 : S 10 = 10) (hS30 : S 30 = 70) :
    S 40 = 150 := by
  rcases ha with ⟨r, hr⟩
  have h10 : S 10 = a 0 * (1 + r + r^2 + r^3 + r^4 + r^5 + r^6 + r^7 + r^8 + r^9) := by
    rw [hS 10]
    simp [Finset.sum_range_succ, hr 1, hr 2, hr 3, hr 4, hr 5, hr 6, hr 7, hr 8, hr 9]
    ring
  have h30 : S 30 = a 0 * (1 + r + r^2 + r^3 + r^4 + r^5 + r^6 + r^7 + r^8 + r^9 + r^10 + r^11 + r^12 + r^13 + r^14 + r^15 + r^16 + r^17 + r^18 + r^19 + r^20 + r^21 + r^22 + r^23 + r^24 + r^25 + r^26 + r^27 + r^28 + r^29) := by
    rw [hS 30]
    simp [Finset.sum_range_succ, hr 1, hr 2, hr 3, hr 4, hr 5, hr 6, hr 7, hr 8, hr 9, hr 10, hr 11, hr 12, hr 13, hr 14, hr 15, hr 16, hr 17, hr 18, hr 19, hr 20, hr 21, hr 22, hr 23, hr 24, hr 25, hr 26, hr 27, hr 28, hr 29]
    ring
  have h40 : S 40 = a 0 * (1 + r + r^2 + r^3 + r^4 + r^5 + r^6 + r^7 + r^8 + r^9 + r^10 + r^11 + r^12 + r^13 + r^14 + r^15 + r^16 + r^17 + r^18 + r^19 + r^20 + r^21 + r^22 + r^23 + r^24 + r^25 + r^26 + r^27 + r^28 + r^29 + r^30 + r^31 + r^32 + r^33 + r^34 + r^35 + r^36 + r^37 + r^38 + r^39) := by
    rw [hS 40]
    simp [Finset.sum_range_succ, hr 1, hr 2, hr 3, hr 4, hr 5, hr 6, hr 7, hr 8, hr 9, hr 10, hr 11, hr 12, hr 13, hr 14, hr 15, hr 16, hr 17, hr 18, hr 19, hr 20, hr 21, hr 22, hr 23, hr 24, hr 25, hr 26, hr 27, hr 28, hr 29, hr 30, hr 31, hr 32, hr 33, hr 34, hr 35, hr 36, hr 37, hr 38, hr 39]
    ring
  rw [h10] at hS10
  rw [h30] at hS30
  rw [h40]
  ring_nf at hS10 hS30 ⊢
  nlinarith [sq_nonneg (r ^ 10 + 3), sq_nonneg (r ^ 5 - 1), sq_nonneg (r ^ 5 + 1), sq_nonneg (a 0), sq_nonneg (r - 1), sq_nonneg (r + 1)]