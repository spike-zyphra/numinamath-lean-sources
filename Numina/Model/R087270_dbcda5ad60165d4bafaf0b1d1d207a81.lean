import Mathlib

open Real Set

theorem algebra_308637 (a b c : ℝ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) :
    2 + sqrt 2 ≤ sqrt (a - 2) + sqrt (b + 1) + abs (1 - sqrt (c - 1)) := by

  have ha2 : 1 ≤ a - 2 := by linarith
  have hha : sqrt (a - 2) ≥ 1 := by
    have h1 : sqrt (a - 2) ≥ sqrt 1 := Real.sqrt_le_sqrt (by linarith)
    have h2 : sqrt 1 = 1 := Real.sqrt_one
    linarith

  have hb2 : 4 ≤ b + 1 := by linarith
  have hhb : sqrt (b + 1) ≥ 2 := by
    have h1 : sqrt (b + 1) ≥ sqrt 4 := Real.sqrt_le_sqrt (by linarith)
    have h2 : sqrt 4 = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    linarith

  have hc2 : 2 ≤ c - 1 := by linarith
  have hsqc : sqrt (c - 1) ≥ sqrt 2 := Real.sqrt_le_sqrt (by linarith)

  have h_1_le_sqrc1 : 1 ≤ sqrt (c - 1) := by
    have h1 : 1 ≤ sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
    have h2 : sqrt 2 ≤ sqrt (c - 1) := hsqc
    linarith

  have h_abs : abs (1 - sqrt (c - 1)) = sqrt (c - 1) - 1 := by
    have h_neg : 1 - sqrt (c - 1) ≤ 0 := by
      nlinarith [Real.sqrt_nonneg (c - 1), Real.sqrt_nonneg 2, hsqc]
    rw [abs_of_nonpos h_neg]
    ring

  have h_abs2 : sqrt (c - 1) - 1 ≥ sqrt 2 - 1 := by
    have h1 : sqrt (c - 1) ≥ sqrt 2 := hsqc
    linarith

  rw [h_abs]
  linarith [hha, hhb, h_abs2, Real.sqrt_nonneg 2, Real.sqrt_nonneg (c - 1)]