import Mathlib

theorem algebra_211432 (x : ℝ) (hx : 0 ≤ x) (h : 5 * x ^ 2 + x - x * Real.sqrt (5 * x ^ 2 - 1) - 2 = 0) :
    x = Real.sqrt 10 / 5 := by

  have h1 : 0 ≤ 5 * x ^ 2 - 1 := by
    by_contra h1
    push_neg at h1
    have h2 : Real.sqrt (5 * x ^ 2 - 1) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      linarith
    rw [h2] at h
    nlinarith [sq_nonneg (x)]

  have eq1 : 5 * x ^ 2 + x - 2 = x * Real.sqrt (5 * x ^ 2 - 1) := by
    nlinarith

  have h2 : (5 * x ^ 2 + x - 2) ^ 2 = (x * Real.sqrt (5 * x ^ 2 - 1)) ^ 2 := by
    rw [eq1]

  have h3 : (x * Real.sqrt (5 * x ^ 2 - 1)) ^ 2 = x ^ 2 * (Real.sqrt (5 * x ^ 2 - 1) ^ 2) := by
    ring

  have h4 : Real.sqrt (5 * x ^ 2 - 1) ^ 2 = 5 * x ^ 2 - 1 := Real.sq_sqrt (show 0 ≤ (5 * x ^ 2 - 1 : ℝ) by linarith)

  rw [h3, h4] at h2

  have h6 : 20 * x ^ 4 + 10 * x ^ 3 - 18 * x ^ 2 - 4 * x + 4 = 0 := by
    nlinarith [h2]

  have h8 : (5 * x ^ 2 - 2) * (4 * x ^ 2 + 2 * x - 2) = 0 := by
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2)]

  cases' (mul_eq_zero.1 h8) with h9 h10

  · -- Case 5 * x ^ 2 - 2 = 0
    have h11 : 5 * x ^ 2 = 2 := by
      linarith

    have h13 : x = Real.sqrt 10 / 5 := by
      have h14 : x ≥ 0 := by linarith [hx]
      have h33 : x ^ 2 = (2 / 5 : ℝ) := by
        nlinarith
      have h15 : x = Real.sqrt (2 / 5 : ℝ) := by
        have h16 : x ≥ 0 := by linarith [hx]
        have h17 : x ^ 2 = (2 / 5 : ℝ) := by
          nlinarith
        rw [← h17]
        field_simp [Real.sqrt_nonneg]

      have h18 : Real.sqrt (2 / 5 : ℝ) = Real.sqrt 10 / 5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      rw [h18] at h15
      linarith

    linarith

  · -- Case 4 * x ^ 2 + 2 * x - 2 = 0
    have eq4 : 4 * x ^ 2 + 2 * x - 2 = 0 := by
      linarith

    have eq5 : x = (1 / 2 : ℝ) := by
      nlinarith [sq_nonneg (x - (1 / 2 : ℝ)), sq_nonneg (x + 1), hx]

    rw [eq5] at eq1
    nlinarith [Real.sqrt_nonneg (5 * ( (1 / 2 : ℝ) ) ^ 2 - 1), Real.sq_sqrt (show 0 ≤ (5 * ( (1 / 2 : ℝ) ) ^ 2 - 1 : ℝ) by nlinarith), Real.sqrt_nonneg 10, Real.sqrt_nonneg (5 * ( (1 / 2 : ℝ) ) ^ 2 - 1)]