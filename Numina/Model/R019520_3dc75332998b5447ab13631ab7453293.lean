import Mathlib

theorem algebra_253189 (x : ℝ) :
  abs (x^4 - x^2 - 6) = abs (x^4 - 4) - abs (x^2 + 2) ↔
  abs x ≥ Real.sqrt 3 := by
  constructor
  · -- Assume equation prove abs x ≥ Real.sqrt 3
    intro h
    have h1 : abs (x^2 + 2) = x^2 + 2 := by
      apply abs_of_nonneg
      nlinarith [sq_nonneg x]
    rw [h1] at h
    by_contra h2
    push_neg at h2
    have hx2 : x ^ 2 < (3 : ℝ) := by
      cases le_or_lt 0 x with
      | inl h_nonneg =>
        have h3 : abs x = x := abs_of_nonneg (by linarith)
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h3, h2]
      | inr h_neg =>
        have h3 : abs x = -x := abs_of_neg (by linarith)
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h3, h2]
    -- have hx2_nonneg : x^2 ≥ 0 := sq_nonneg x
    cases le_or_lt 0 (x^4 - 4) with
    | inl h_nonneg =>
      have h3 : abs (x^4 - 4) = x^4 - 4 := abs_of_nonneg (by linarith)
      rw [h3] at h
      cases le_or_lt 0 (x^4 - x^2 - 6) with
      | inl h_nonneg2 =>
        have h4 : abs (x^4 - x^2 - 6) = x^4 - x^2 - 6 := abs_of_nonneg (by linarith)
        rw [h4] at h
        nlinarith [sq_nonneg (x^2 - 3), sq_nonneg (x^2 - 2), sq_nonneg (x^2), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      | inr h_neg2 =>
        have h4 : abs (x^4 - x^2 - 6) = -(x^4 - x^2 - 6) := abs_of_neg (by linarith)
        rw [h4] at h
        nlinarith [sq_nonneg (x^2 - 3), sq_nonneg (x^2 - 2), sq_nonneg (x^2), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    | inr h_neg =>
      have h3 : abs (x^4 - 4) = -(x^4 - 4) := abs_of_neg (by linarith)
      rw [h3] at h
      cases le_or_lt 0 (x^4 - x^2 - 6) with
      | inl h_nonneg2 =>
        have h4 : abs (x^4 - x^2 - 6) = x^4 - x^2 - 6 := abs_of_nonneg (by linarith)
        rw [h4] at h
        nlinarith [sq_nonneg (x^2 - 3), sq_nonneg (x^2 - 2), sq_nonneg (x^2), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      | inr h_neg2 =>
        have h4 : abs (x^4 - x^2 - 6) = -(x^4 - x^2 - 6) := abs_of_neg (by linarith)
        rw [h4] at h
        nlinarith [sq_nonneg (x^2 - 3), sq_nonneg (x^2 - 2), sq_nonneg (x^2), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  · -- Assume abs x ≥ Real.sqrt 3 prove equation
    intro h
    have h1 : abs (x^2 + 2) = x^2 + 2 := by
      apply abs_of_nonneg
      nlinarith [sq_nonneg x]
    have h2 : x^2 ≥ 3 := by
      cases le_or_lt 0 x with
      | inl h_nonneg =>
        have h3 : abs x = x := abs_of_nonneg (by linarith)
        rw [h3] at h
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h]
      | inr h_neg =>
        have h3 : abs x = -x := abs_of_neg (by linarith)
        rw [h3] at h
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h]
    have h4 : abs (x^4 - x^2 - 6) = x^4 - x^2 - 6 := by
      have h5 : x^4 - x^2 - 6 ≥ 0 := by
        nlinarith [sq_nonneg (x^2 - 3), sq_nonneg (x^2), Real.sqrt_nonneg 3, sq_nonneg (x - 0)]
      rw [abs_of_nonneg h5]
    have h5 : abs (x^4 - 4) = x^4 - 4 := by
      have h6 : x^4 - 4 ≥ 0 := by
        nlinarith [sq_nonneg (x^2 - 3), sq_nonneg (x^2 - 2), sq_nonneg (x - 0), Real.sqrt_nonneg 3, sq_nonneg (x ^ 2 - 3)]
      rw [abs_of_nonneg h6]
    rw [h1, h4, h5]
    all_goals nlinarith [sq_nonneg (x^2 - 3), sq_nonneg (x - 0)]