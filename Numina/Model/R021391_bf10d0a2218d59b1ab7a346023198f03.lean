import Mathlib

open Polynomial

theorem algebra_14231 {a b : ℝ} (ha : a ^ 4 - 4 * a - 1 = 0) (hb : b ^ 4 - 4 * b - 1 = 0)
    (hab : a ≠ b) : a * b + a + b = 1 := by

  have h1 : a ^ 4 - b ^ 4 - 4 * (a - b) = 0 := by
    nlinarith

  have h2 : (a - b) * ((a + b) * (a ^ 2 + b ^ 2) - 4) = 0 := by
    ring_nf at h1 ⊢
    nlinarith

  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case where a - b = 0
    exfalso
    apply hab
    linarith
  · -- Case where the second factor is zero
    have eq1 : (a + b) * (a ^ 2 + b ^ 2) = 4 := by linarith
    have eq2 : a ^ 4 + b ^ 4 = 4 * (a + b) + 2 := by 
      nlinarith [ha, hb]

    have h3 : (a + b) ^ 2 - 2 * (a * b) = a ^ 2 + b ^ 2 := by
      nlinarith

    have eq4 : (a + b) * ((a + b) ^ 2 - 2 * (a * b)) = 4 := by
      nlinarith [eq1, h3]

    have eq5 : (a ^ 2 + b ^ 2) ^ 2 - 2 * (a * b) ^ 2 = 4 * (a + b) + 2 := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a + b), ha, hb, eq1]

    -- Now, we can solve for `a * b + a + b = 1` using `eq4` and `eq5`. This involves squaring.
    have h4' : a * b + a + b = 1 := by
      have eq6 : (a + b) ^ 2 = 2 := by
        nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_pos_of_ne_zero (show (a - b: ℝ) ≠ 0 by 
          intro h'
          apply hab
          linarith
        ), sq_nonneg (a * b), eq1, eq4, eq2, sq_nonneg (a ^ 2 - b ^ 2)]

      nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), eq6, eq4, sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_pos_of_ne_zero (show (a - b : ℝ) ≠ 0 by
        intro h'
        apply hab
        linarith
      ), sq_nonneg (a ^ 2 - b ^ 2)]
    linarith [h4']