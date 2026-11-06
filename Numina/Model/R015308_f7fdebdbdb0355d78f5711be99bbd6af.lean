import Mathlib
open Real

theorem algebra_879 {x y : ℝ} (hx : 2 * x ^ 2 - 6 * x + 5 = sqrt (4 * y - 3)) (hy : x ^ 2 = y ^ 4 - 2 * y ^ 3 + 5 * y ^ 2 - 4 * y + 4) :
    (x, y) = (2, 1) := by

  have h1 : 4 * y - 3 ≥ 0 := by
    by_contra h
    push_neg at h
    have h2 : sqrt (4 * y - 3) = 0 := by
      rw [sqrt_eq_zero']
      all_goals nlinarith
    rw [h2] at hx
    nlinarith [sq_nonneg (x ^ 2 - (y ^ 2 - y + 2) ^ 2), sq_nonneg ((y) ^ 2 - (y) + 1), sq_nonneg ((y) - (1) ), sq_nonneg ((y ^ 2 - y + 2) - 2), sq_nonneg (x - 2)]
  have h1y1 : sqrt (4 * y - 3) ≥ 0 := by positivity
  have h2 : x ^ 2 = (y ^ 2 - y + 2) ^ 2 := by
    nlinarith
  have h3 : x = y ^ 2 - y + 2 ∨ x = - (y ^ 2 - y + 2) := by
    have h4 : x ^ 2 - (y ^ 2 - y + 2) ^ 2 = 0 := by linarith
    have h5 : (x - (y ^ 2 - y + 2)) * (x + (y ^ 2 - y + 2)) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h5) with h6 h7
    · left
      linarith
    · right
      linarith

  rcases h3 with (h3 | h3)
  · -- Assume x = y ^ 2 - y + 2
    have eq2 : sqrt (4 * y - 3) = 2 * (y ^ 2 - y + 2) ^ 2 - 6 * (y ^ 2 - y + 2) + 5 := by
      rw [show x = y ^ 2 - y + 2 by linarith [h3]] at hx
      linarith [hx]

    have h8 : y = 1 := by
      have h51 : (sqrt (4 * y - 3)) ^ 2 = 4 * y - 3 := by
        rw [Real.sq_sqrt]
        linarith [h1]
      nlinarith [ Real.sqrt_nonneg (4 * y - 3), sq_nonneg (sqrt (4 * y - 3) - 1), sq_nonneg ((y - 1) ), sq_nonneg ((y) ^ 2 - y + 2 - 2), sq_nonneg (y * (y - 1) ), sq_nonneg ( (y ^ 2 - (y - 1) ^ 2) ), sq_nonneg (y^2 - 2 * y + 1) ]

    have h9 : x = 2 := by
      rw [show y = 1 by linarith [h8] ] at h3
      nlinarith
    simp [h9, h8]

  · -- Assume x = - (y ^ 2 - y + 2)
    have eq3 : sqrt (4 * y - 3) = 2 * (-(y ^ 2 - y + 2)) ^ 2 - 6 * (-(y ^ 2 - y + 2)) + 5 := by
      rw [show x = - (y ^ 2 - y + 2) by linarith [h3]] at hx
      linarith [hx]

    -- Substitute y = 1 in eq3 and in hx to get sqrt (4 * 1 - 3) = 1 and 25 = 1 for a contradiction
    have eq6 : y = 1 := by
      have h51 : (sqrt (4 * y - 3)) ^ 2 = 4 * y - 3 := by
        rw [Real.sq_sqrt]
        linarith [h1]
      nlinarith [ Real.sqrt_nonneg (4 * y - 3), sq_nonneg (sqrt (4 * y - 3) - 1), sq_nonneg ((y - 1) ), sq_nonneg ((y) ^ 2 - y + 2 - 2), sq_nonneg (y ^ 2 * (y - 1) ), sq_nonneg (y ^ 2 - 2 * y + 1) ]
    have h10 : x = -2 := by
      rw [show y = 1 by linarith [eq6] ] at h3
      nlinarith
    exfalso
    have h11 : (2 * x ^ 2 - 6 * x + 5) = sqrt (4 * y - 3) := hx
    rw [show x = -2 by linarith [h10], show y = 1 by linarith [eq6] ] at h11
    all_goals
      nlinarith [Real.sqrt_nonneg (4 * (1 : ℝ) - 3), Real.sq_sqrt (show 0 ≤ (4 * (1 : ℝ) - 3) by norm_num), h1y1]