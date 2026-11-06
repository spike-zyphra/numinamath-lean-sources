import Mathlib

theorem algebra_163805 {a : ℕ → ℝ} {r : ℝ} (ha : ∀ n, a n = a 0 * r ^ n)
    (hsum : ∑ i in Finset.range 10, a i = 10) (hsum' : ∑ i in Finset.range 30, a i = 70) :
    ∑ i in Finset.range 40, a i = 150 := by

  have eq1 : ∑ i in Finset.range 10, a i = a 0 * (1 + r + r^2 + r^3 + r^4 + r^5 + r^6 + r^7 + r^8 + r^9) := by
    simp [Finset.sum_range_succ, ha 1, ha 2, ha 3, ha 4, ha 5, ha 6, ha 7, ha 8, ha 9]
    all_goals ring

  have eq2 : ∑ i in Finset.range 30, a i = a 0 * (1 + r + r^2 + r^3 + r^4 + r^5 + r^6 + r^7 + r^8 + r^9 + r^10 + r^11 + r^12 + r^13 + r^14 + r^15 + r^16 + r^17 + r^18 + r^19 + r^20 + r^21 + r^22 + r^23 + r^24 + r^25 + r^26 + r^27 + r^28 + r^29) := by
    simp [Finset.sum_range_succ, ha 1, ha 2, ha 3, ha 4, ha 5, ha 6, ha 7, ha 8, ha 9, ha 10, ha 11, ha 12, ha 13, ha 14, ha 15, ha 16, ha 17, ha 18, ha 19, ha 20, ha 21, ha 22, ha 23, ha 24, ha 25, ha 26, ha 27, ha 28, ha 29]
    all_goals ring

  have eq3 : ∑ i in Finset.range 40, a i = a 0 * (1 + r + r^2 + r^3 + r^4 + r^5 + r^6 + r^7 + r^8 + r^9 + r^10 + r^11 + r^12 + r^13 + r^14 + r^15 + r^16 + r^17 + r^18 + r^19 + r^20 + r^21 + r^22 + r^23 + r^24 + r^25 + r^26 + r^27 + r^28 + r^29 + r^30 + r^31 + r^32 + r^33 + r^34 + r^35 + r^36 + r^37 + r^38 + r^39) := by
    simp [Finset.sum_range_succ, ha 1, ha 2, ha 3, ha 4, ha 5, ha 6, ha 7, ha 8, ha 9, ha 10, ha 11, ha 12, ha 13, ha 14, ha 15, ha 16, ha 17, ha 18, ha 19, ha 20, ha 21, ha 22, ha 23, ha 24, ha 25, ha 26, ha 27, ha 28, ha 29, ha 30, ha 31, ha 32, ha 33, ha 34, ha 35, ha 36, ha 37, ha 38, ha 39]
    all_goals ring

  rw [eq1] at hsum
  rw [eq2] at hsum'
  rw [eq3] at *

  have eq5 : r ^ 10 = 2 := by
    nlinarith [sq_nonneg (r ^ 5), sq_nonneg (r ^ 10 - 2), sq_nonneg (r ^ 15 - r ^ 5), sq_nonneg (r ^ 10 - 1), sq_nonneg (r ^ 30 - r ^ 10), sq_nonneg (r ^ 10 * (r ^ 10 + 1) - 6), sq_pos_of_pos (show 0 < (2 : ℝ) by norm_num)]

  have eq6 : r ^ 40 = 16 := by
    calc
      r ^ 40 = (r ^ 10) ^ 4 := by ring
      _ = 2 ^ 4 := by rw [eq5]
      _ = (16 : ℝ) := by norm_num

  nlinarith [sq_nonneg (r ^ 5), sq_nonneg (r ^ 10 - 1), sq_pos_of_pos (show 0 < (2 : ℝ) by norm_num), sq_nonneg (r ^ 20 - 4)]