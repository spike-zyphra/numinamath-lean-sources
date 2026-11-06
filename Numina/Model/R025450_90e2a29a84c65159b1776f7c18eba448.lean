import Mathlib

theorem algebra_214872 (x : ℝ) (hx : x^2 - 5 = Real.sqrt (5 - x)) :
    x = (-1 - Real.sqrt 21) / 2 ∨ x = (1 + Real.sqrt 17) / 2 := by
  have h1 : 5 - x ≥ 0 := by 
    by_contra h
    push_neg at h
    have h2 : Real.sqrt (5 - x) = 0 := by 
      rw [Real.sqrt_eq_zero']
      all_goals linarith
    rw [h2] at hx
    nlinarith
  have h2 : x ^ 2 - 5 ≥ 0 := by 
    by_contra h
    push_neg at h
    have h3 : Real.sqrt (5 - x) < 0 := by 
      nlinarith [Real.sqrt_nonneg (5 - x), Real.sq_sqrt (show 0 ≤ 5 - x by linarith), sq_nonneg (x ^ 2 - 5), h, sq_nonneg (Real.sqrt (5 - x) - (x ^ 2 - 5))]
    have h4 : Real.sqrt (5 - x) ≥ 0 := Real.sqrt_nonneg (5 - x)
    linarith
  have h3 : Real.sqrt (5 - x) ≥ 0 := Real.sqrt_nonneg (5 - x)
  have h4 : (Real.sqrt (5 - x)) ^ 2 = 5 - x := Real.sq_sqrt (show 0 ≤ 5 - x by linarith)
  have h5 : (x^2 - 5) ^ 2 = 5 - x := by
    have h_eq : x^2 - 5 = Real.sqrt (5 - x) := by linarith [hx]
    have h6 : (x^2 - 5) ^ 2 = (Real.sqrt (5 - x) ) ^ 2 := by 
      rw [h_eq]
    have h7 : (Real.sqrt (5 - x)) ^ 2 = 5 - x := Real.sq_sqrt (show 0 ≤ 5 - x by linarith)
    rw [h7] at h6
    linarith
  have h4 : x^4 - 10 * x^2 + x + 20 = 0 := by
    nlinarith [sq_nonneg (x^2 - 5), sq_nonneg (x), sq_nonneg (Real.sqrt (5 - x) - x^2 + 5)]
  have h6 : (x^2 + x - 5) * (x^2 - x - 4) = 0 := by
    ring_nf
    nlinarith [h4]
  have h7 : x^2 + x - 5 = 0 ∨ x^2 - x - 4 = 0 := by 
    cases (mul_eq_zero.mp h6) with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith
  cases h7 with
  | inl h8 =>
    have h8' : x^2 + x - 5 = 0 := h8
    have h9 : x = (-1 - Real.sqrt 21) / 2 ∨ x = (-1 + Real.sqrt 21) / 2 := by 
      have h10 : (x - (-1 - Real.sqrt 21) / 2) * (x - (-1 + Real.sqrt 21) / 2) = 0 := by 
        nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num), Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), h8']
      cases (mul_eq_zero.mp h10) with
      | inl h11 =>
        left
        linarith
      | inr h12 =>
        right
        linarith
    cases h9 with
    | inl h10 =>
      left
      linarith
    | inr h11 =>
      have h11' : x = (-1 + Real.sqrt 21) / 2 := h11
      have h11'' : x ^ 2 - 5 = (1 - Real.sqrt 21) / 2 := by
        rw [h11']
        nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
      have sqrt_21_gt_1 : Real.sqrt 21 > 1 := by
        nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
      have h11''' : (1 - Real.sqrt 21) / 2 < (0 : ℝ) := by
        nlinarith [sqrt_21_gt_1]
      nlinarith [h11'', h11''', h2]
  | inr h8 =>
    have h8' : x^2 - x - 4 = 0 := h8
    have h9 : x = (1 + Real.sqrt 17) / 2 ∨ x = (1 - Real.sqrt 17) / 2 := by
      have h10 : (x - (1 + Real.sqrt 17) / 2) * (x - (1 - Real.sqrt 17) / 2) = 0 := by 
        nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num), h8']
      cases (mul_eq_zero.mp h10) with
      | inl h11 =>
        left
        linarith
      | inr h12 =>
        right
        linarith
    cases h9 with
    | inl h10 =>
      right
      linarith
    | inr h11 =>
      have h11' : x = (1 - Real.sqrt 17) / 2 := h11
      have h11'' : x ^ 2 - 5 = (-1 - Real.sqrt 17) / 2 := by 
        rw [h11']
        nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
      have sqrt_17_gt_1 : Real.sqrt 17 > 1 := by
        nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
      have h11''' : (-1 - Real.sqrt 17) / 2 < (0 : ℝ) := by 
        nlinarith [sqrt_17_gt_1]
      nlinarith [h11'', h11''', h2]