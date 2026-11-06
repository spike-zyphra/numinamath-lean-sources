import Mathlib

theorem algebra_287686 (x y : ℝ) (hx : x = 25 + 10 * Real.sqrt 5) (hy : y = 25 - 10 * Real.sqrt 5) :
    x ^ ((1 : ℝ) / 3) + y ^ ((1 : ℝ) / 3) = 5 := by

  have h1 : 0 ≤ (5 : ℝ) := by norm_num
  have h2 : 0 ≤ (Real.sqrt 5 : ℝ) := Real.sqrt_nonneg 5

  have hx1 : 0 ≤ x := by
    rw [hx]
    nlinarith [Real.sqrt_nonneg 5, Real.mul_self_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]

  have hy1 : 0 ≤ y := by
    rw [hy]
    nlinarith [Real.sqrt_nonneg 5, Real.mul_self_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 5]

  have h3 : x ^ ((1 : ℝ) / 3) ≥ 0 := by positivity
  have h4 : y ^ ((1 : ℝ) / 3) ≥ 0 := by positivity

  have h5 : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith

  have h6 : (y ^ ((1 : ℝ) / 3)) ^ 3 = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith

  have h7 : (x ^ ((1 : ℝ) / 3)) ^ 3 + (y ^ ((1 : ℝ) / 3)) ^ 3 = 50 := by
    rw [h5, h6, hx, hy]
    nlinarith [Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

  have h8 : (x ^ ((1 : ℝ) / 3)) * (y ^ ((1 : ℝ) / 3)) = 5 := by
    have h9 : (x ^ ((1 : ℝ) / 3)) * (y ^ ((1 : ℝ) / 3)) = ((x ) * (y )) ^ ((1 : ℝ) / 3) := by
      rw [← Real.mul_rpow]
      all_goals nlinarith
    rw [h9]
    have h10 : (x ) * (y ) = 125 := by
      rw [hx, hy]
      nlinarith [Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    rw [h10]
    have h11 : (125 : ℝ) ^ ((1 : ℝ) / 3) = (5 : ℝ) := by
      have h111 : (125 : ℝ) = (5 : ℝ) ^ (3 : ℝ) := by norm_num
      rw [h111]
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith
    rw [h11]
    all_goals nlinarith

  have h20 : (x ^ ((1 : ℝ) / 3) + y ^ ((1 : ℝ) / 3)) ^ 3 = 50 + 15 * (x ^ ((1 : ℝ) / 3) + y ^ ((1 : ℝ) / 3)) := by
    calc
      (x ^ ((1 : ℝ) / 3) + y ^ ((1 : ℝ) / 3)) ^ 3
          = (x ^ ((1 : ℝ) / 3)) ^ 3 + (y ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((x ^ ((1 : ℝ) / 3)) * (y ^ ((1 : ℝ) / 3))) * (x ^ ((1 : ℝ) / 3) + y ^ ((1 : ℝ) / 3)) := by
            ring
      _ = (x ^ ((1 : ℝ) / 3)) ^ 3 + (y ^ ((1 : ℝ) / 3)) ^ 3 + 3 * 5 * (x ^ ((1 : ℝ) / 3) + y ^ ((1 : ℝ) / 3)) := by
          rw [h8]
          all_goals nlinarith
      _ = 50 + 15 * (x ^ ((1 : ℝ) / 3) + y ^ ((1 : ℝ) / 3)) := by
          rw [h7]
          all_goals ring_nf
          <;> nlinarith

  have h21 : (x ^ ((1 : ℝ) / 3) + y ^ ((1 : ℝ) / 3) - 5) * ((x ^ ((1 : ℝ) / 3) + y ^ ((1 : ℝ) / 3)) ^ 2 + 5 * (x ^ ((1 : ℝ) / 3) + y ^ ((1 : ℝ) / 3)) + 10) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h21) with h22 h23
  · -- When $A + b -5 =0$, then $a + b =5$
    linarith
  · -- When the quadratic equals 0
    nlinarith [sq_nonneg ((x ^ ((1 : ℝ) / 3) + y ^ ((1 : ℝ) / 3)) + 5 / 2), sq_nonneg ((x ^ ((1 : ℝ) / 3) - y ^ ((1 : ℝ) / 3))), Real.sqrt_nonneg 5]