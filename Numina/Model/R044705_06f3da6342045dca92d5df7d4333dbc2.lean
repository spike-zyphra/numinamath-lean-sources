import Mathlib

theorem algebra_3267 {n : ℝ} (hn : n > 0) (h : Real.sqrt (1625 + n) - Real.sqrt (1625 - n) = 10) : n = 400 := by
  have h1 : 0 ≤ 1625 + n := by
    linarith

  have h2 : 0 ≤ 1625 - n := by
    by_contra h3
    push_neg at h3
    have h4 : Real.sqrt (1625 - n) = 0 := by
      rw [Real.sqrt_eq_zero']
      linarith
    have h5 : Real.sqrt (1625 + n) = 10 := by 
      linarith [h, h4]
    have h6 : 1625 + n = (10 : ℝ) ^ 2 := by
      calc
        1625 + n = (Real.sqrt (1625 + n)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (10 : ℝ) ^ 2 := by 
          rw [h5]
    have h7 : n = -1525 := by 
      nlinarith
    linarith

  have h10 : Real.sqrt (1625 + n) = Real.sqrt (1625 - n) + 10 := by
    linarith [h]

  have h11 : (Real.sqrt (1625 + n)) ^ 2 = (Real.sqrt (1625 - n) + 10) ^ 2 := by
    rw [h10]

  have h12 : (Real.sqrt (1625 + n)) ^ 2 = (1625 + n) := by
    apply Real.sq_sqrt
    linarith

  have h13 : (Real.sqrt (1625 - n)) ^ 2 = (1625 - n) := by
    apply Real.sq_sqrt
    linarith

  have h14 : (Real.sqrt (1625 - n) + 10) ^ 2 = (Real.sqrt (1625 - n)) ^ 2 + 20 * Real.sqrt (1625 - n) + 100 := by
    ring

  rw [h12, h14] at h11
  rw [h13] at h11

  have h15 : n - 50 = 10 * Real.sqrt (1625 - n) := by
    nlinarith [Real.sqrt_nonneg (1625 - n)]

  have h17 : (n - 50) ^ 2 = 100 * (Real.sqrt (1625 - n)) ^ 2 := by 
    calc
      (n - 50) ^ 2 = (10 * Real.sqrt (1625 - n)) ^ 2 := by 
        rw [show 10 * Real.sqrt (1625 - n) = (n - 50) by linarith [h15]]
      _ = 100 * (Real.sqrt (1625 - n)) ^ 2 := by 
        ring_nf

  have h18 : (Real.sqrt (1625 - n)) ^ 2 = (1625 - n) := by 
    apply Real.sq_sqrt
    linarith

  rw [h18] at h17

  have h19 : n ^ 2 = 160000 := by 
    nlinarith

  have h20 : n = 400 := by 
    nlinarith [sq_pos_of_pos (show 0 < n by linarith)]

  exact h20