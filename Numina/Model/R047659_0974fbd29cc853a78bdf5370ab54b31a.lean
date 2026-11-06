import Mathlib

theorem algebra_144533 {x y : ℝ} (hx : x + Real.sqrt (x + 2 * y) - 2 * y = 7 / 2) (hy : x ^ 2 + x + 2 * y - 4 * y ^ 2 = 27 / 2) :
    (x, y) = (19 / 4, 17 / 8) := by
  have h1 : 0 ≤ x + 2 * y := by
    by_contra h
    push_neg at h
    have h2 : Real.sqrt (x + 2 * y) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      linarith
      all_goals linarith
    have h3 : x + Real.sqrt (x + 2 * y) - 2 * y = 7 / 2 := hx
    rw [h2] at h3
    nlinarith [sq_nonneg (x + 2 * y), sq_nonneg (y), sq_nonneg (x - 19 / 4), sq_nonneg (y - 17 / 8)]
  have ht_def : Real.sqrt (x + 2 * y) ≥ 0 := by positivity
  set t := Real.sqrt (x + 2 * y) with ht
  have ht2 : t ^ 2 = x + 2 * y := by
    rw [ht]
    rw [Real.sq_sqrt]
    linarith
  have ht_eq : x + t - 2 * y = 7 / 2 := by
    nlinarith [hx, ht]
  have eq1 : x = t ^ 2 - 2 * y := by
    nlinarith [ht2]
  have eq2 : (t ^ 2 - 2 * y) ^ 2 + (t ^ 2 - 2 * y) + 2 * y - 4 * y ^ 2 = 27 / 2 := by
    rw [show x = t ^ 2 - 2 * y by linarith [eq1]] at hy
    linarith
  have ht_eq1 : 4 * y = t ^ 2 + t - 7 / 2 := by
    nlinarith [ht_eq, ht2]
  have ht_eq2 : y = (t ^ 2 + t - 7 / 2) / 4 := by
    nlinarith [ht_eq1]
  have ht_eq6 : t = 3 := by
    nlinarith [sq_nonneg (t - 3), sq_nonneg (y - 17 / 8), sq_nonneg (x - 19 / 4), sq_nonneg (t ^ 2 - 9)]
  have ht_eq7 : x + 2 * y = 9 := by
    nlinarith [ht_eq6, ht2]
  have ht_eq8 : x - 2 * y = 1 / 2 := by
    nlinarith [ht_eq6, ht_eq]
  have ht9 : x = 19 / 4 := by
    nlinarith [ht_eq7, ht_eq8]
  have ht10 : y = 17 / 8 := by
    nlinarith [ht_eq7, ht_eq8]
  simp [Prod.ext_iff, ht9, ht10]