import Mathlib

theorem algebra_186847 (x : ℝ) (hx : x ≥ 0) (h : (24 + Real.sqrt x) ^ ((1 : ℝ) / 3) - (5 + Real.sqrt x) ^ ((1 : ℝ) / 3) = 1) :
    x = 9 := by
  have h1 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  set a := (24 + Real.sqrt x) ^ ((1 : ℝ) / 3) with ha
  set b := (5 + Real.sqrt x) ^ ((1 : ℝ) / 3) with hb
  have h2 : a - b = 1 := by 
    linarith [h]
  have h3 : a ^ 3 = 24 + Real.sqrt x := by
    rw [ha]
    have h4 : ((24 + Real.sqrt x : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (24 + Real.sqrt x) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      norm_num
      all_goals nlinarith [show (24 + Real.sqrt x) ≥ 0 by nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]]
    nlinarith
  have h4 : b ^ 3 = 5 + Real.sqrt x := by
    rw [hb]
    have h5 : ((5 + Real.sqrt x : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (5 + Real.sqrt x) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      norm_num
      all_goals nlinarith [show (5 + Real.sqrt x) ≥ 0 by nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]]
    nlinarith
  have h5 : a ^ 3 - b ^ 3 = 19 := by
    nlinarith [h3, h4, Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
  have h6 : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by
    ring_nf
  rw [h6] at h5
  rw [show a - b = 1 by linarith [h2]] at h5
  have h7 : a ^ 2 + a * b + b ^ 2 = 19 := by
    linarith [h5]
  -- Now, since $a - b = 1$, we can write $a = b + 1$.
  have h8 : a = b + 1 := by 
    linarith [h2]
  rw [h8] at h7
  have h8' : 3 * b ^ 2 + 3 * b - 18 = 0 := by
    nlinarith [h7]
  have h9 : b ^ 2 + b - 6 = 0 := by 
    nlinarith [h8']
  have hb_pos : b > 0 := by
    have h4_pos : b ^ 3 > 0 := by
      nlinarith [h4, Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
    by_contra h
    push_neg at h
    have : b ≤ 0 := by nlinarith
    have : b ^ 3 ≤ 0 := by
      nlinarith [sq_nonneg (b ^ 2), sq_nonneg (b), sq_nonneg (b + 1)]
    linarith
  have hb2 : b = 2 := by
    have h : b ^ 2 + b - 6 = 0 := h9
    have h10 : (b + 3) * (b - 2) = 0 := by
      nlinarith [h]
    cases' (mul_eq_zero.1 h10) with h10 h10
    · -- b + 3 = 0
      linarith [hb_pos]
    · -- b - 2 = 0
      linarith
  have ha3 : a = 3 := by 
    linarith [h8, hb2]
  have h11 : Real.sqrt x = 3 := by
    have h4 : b ^ 3 = 5 + Real.sqrt x := h4
    rw [hb2] at h4
    nlinarith [h4, Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
  -- Now $\sqrt{x} = 3$ implies $x = 9$.
  have h12 : x = 9 := by 
    have h11' : Real.sqrt x = 3 := h11
    have h11_sq : (Real.sqrt x) ^ 2 = 9 := by 
      rw [h11']
      norm_num
    have h13 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (show x ≥ 0 by linarith)
    nlinarith [h13, h11_sq]
  exact h12