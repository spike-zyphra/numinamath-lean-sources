import Mathlib

open Real

theorem algebra_149577 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    ⌊sqrt (1 + a^2) + sqrt (1 + 2 * b)⌋ = 2 := by
  have hb_eq : b = 1 - a := by linarith
  -- √(1 + a^2) + √(1 + 2(1 -a)) ≥ 2
  have h1 : 2 ≤ sqrt (1 + a^2) + sqrt (1 + 2 * (1 - a)) := by
    have h1 : 0 < a := ha
    have h2 : a < 1 := by nlinarith [h, hb]
    have h3 : sqrt (1 + a^2) > 1 := by
      have h4 : 1 + a^2 > 1 := by nlinarith [sq_pos_of_pos h1]
      have h5 : sqrt (1 + a^2) > sqrt 1 := Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
      rw [show sqrt 1 = 1 by rw [Real.sqrt_one]] at h5
      linarith
    have h4 : sqrt (1 + 2 * (1 - a)) > 1 := by
      have h5 : 1 + 2 * (1 - a) > 1 := by nlinarith [h2]
      have h6 : sqrt (1 + 2 * (1 - a)) > sqrt 1 := Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
      rw [show sqrt 1 = 1 by rw [Real.sqrt_one]] at h6
      linarith
    linarith
  -- √ (1 + a^2) + √(1 + 2(1 -a)) < 3, combinwith the above inequality we get the conclusion.
  have h2 : sqrt (1 + a^2) + sqrt (1 + 2 * (1 - a)) < 3 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + a^2 by nlinarith), Real.sq_sqrt (show 0 ≤ 1 + 2 * (1 - a) by nlinarith),
      sq_nonneg (a - 1 / 2), sq_nonneg (a - 1 / 3), sq_nonneg (a - 1 / 4), sq_nonneg (a - 1 / 5),
      sq_nonneg (sqrt (1 + a^2) - 1), sq_nonneg (sqrt (1 + 2 * (1 - a)) - 1)]
  have h3 : ⌊sqrt (1 + a^2) + sqrt (1 + 2 * (1 - a))⌋ = 2 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> (try norm_num) <;> linarith
  simp [hb_eq] at h3 ⊢
  exact h3