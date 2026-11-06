import Mathlib

theorem algebra_10532 {a : ℕ → ℝ} {r : ℝ} (ha : ∀ n, a n = a 0 * r ^ n)
    (h1 : ∑ i in Finset.range 10, a i = 10) (h2 : ∑ i in Finset.range 30, a i = 70) :
    ∑ i in Finset.range 40, a i = 150 := by 
  have h3 : ∀ i, a i = a 0 * r ^ i := by
    intro i
    specialize ha i
    simpa using ha
  have h10 : ∑ i in Finset.range 10, a i = a 0 * (1 + r + r^2 + r^3 + r^4 + r^5 + r^6 + r^7 + r^8 + r^9) := by
    simp [Finset.sum_range_succ, h3 1, h3 2, h3 3, h3 4, h3 5, h3 6, h3 7, h3 8, h3 9]
    <;> ring
  have h30 : ∑ i in Finset.range 30, a i = a 0 * (1 + r + r^2 + r^3 + r^4 + r^5 + r^6 + r^7 + r^8 + r^9 + r^10 + r^11 + r^12 + r^13 + r^14 + r^15 + r^16 + r^17 + r^18 + r^19 + r^20 + r^21 + r^22 + r^23 + r^24 + r^25 + r^26 + r^27 + r^28 + r^29) := by
    simp [Finset.sum_range_succ, h3 1, h3 2, h3 3, h3 4, h3 5, h3 6, h3 7, h3 8, h3 9, h3 10, h3 11, h3 12, h3 13, h3 14, h3 15, h3 16, h3 17, h3 18, h3 19, h3 20, h3 21, h3 22, h3 23, h3 24, h3 25, h3 26, h3 27, h3 28, h3 29]
    <;> ring
  have h40 : ∑ i in Finset.range 40, a i = a 0 * (1 + r + r^2 + r^3 + r^4 + r^5 + r^6 + r^7 + r^8 + r^9 + r^10 + r^11 + r^12 + r^13 + r^14 + r^15 + r^16 + r^17 + r^18 + r^19 + r^20 + r^21 + r^22 + r^23 + r^24 + r^25 + r^26 + r^27 + r^28 + r^29 + r^30 + r^31 + r^32 + r^33 + r^34 + r^35 + r^36 + r^37 + r^38 + r^39) := by
    simp [Finset.sum_range_succ, h3 1, h3 2, h3 3, h3 4, h3 5, h3 6, h3 7, h3 8, h3 9, h3 10, h3 11, h3 12, h3 13, h3 14, h3 15, h3 16, h3 17, h3 18, h3 19, h3 20, h3 21, h3 22, h3 23, h3 24, h3 25, h3 26, h3 27, h3 28, h3 29, h3 30, h3 31, h3 32, h3 33, h3 34, h3 35, h3 36, h3 37, h3 38, h3 39]
    <;> ring
  rw [h10] at h1
  rw [h30] at h2
  rw [h40]
  nlinarith [sq_nonneg (r^10 - 2), sq_nonneg (r^5), sq_nonneg (r^2 - 1), sq_nonneg (r + 1), sq_nonneg (a 0), sq_nonneg (r^4 - 1), sq_nonneg (r^5 - 1), sq_nonneg (r^5 + 1)]