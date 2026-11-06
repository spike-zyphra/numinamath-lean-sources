import Mathlib

open Real Set

theorem algebra_95732 {f : ℝ → ℝ} (hf : f = λ x => logb 2 x)
    (Ax Bx : ℝ) (hAx : Ax > 0) (hBx : Bx > 0) (hABx : (Ax + Bx) / 2 = 6) (hABy : (f Ax + f Bx)/2 = 2) :
    abs (Bx - Ax) = 4 * sqrt 5 := by
  have h1 : f Ax = logb 2 Ax := by rw [hf]
  have h2 : f Bx = logb 2 Bx := by rw [hf]
  rw [h1] at hABy
  rw [h2] at hABy
  have h3 : logb 2 Ax + logb 2 Bx = 4 := by linarith
  have h4 : logb 2 Ax + logb 2 Bx = logb 2 (Ax * Bx) := by
    rw [← logb_mul (by linarith) (by linarith)]
  have h5 : logb 2 (Ax * Bx) = 4 := by linarith [h3, h4]
  have h6 : Ax * Bx = 16 := by
    have h7 : logb 2 (Ax * Bx) = 4 := h5
    have h9 : Ax * Bx > 0 := by positivity
    have h8 : Ax * Bx = (2 : ℝ) ^ (4 : ℝ) := by
      rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) h9] at h7
      · linarith
      all_goals linarith
    have h10 : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
    rw [h10] at h8
    linarith
  have h7 : Ax + Bx = 12 := by linarith
  have h8 : Bx - Ax = 4 * Real.sqrt 5 ∨ Bx - Ax = - (4 * Real.sqrt 5) := by
    have h9 : (Bx - Ax) ^ 2 = 80 := by
      nlinarith
    have h10 : (80 : ℝ) = (4 * (Real.sqrt 5)) ^ 2 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith)]
    have h11 : (Bx - Ax) ^ 2 = (4 * Real.sqrt 5) ^ 2 := by
      linarith [h9, h10]
    have h12 : (Bx - Ax) = 4 * Real.sqrt 5 ∨ (Bx - Ax) = - (4 * Real.sqrt 5) := by
      have h13 : (Bx - Ax) ^ 2 - (4 * Real.sqrt 5) ^ 2 = 0 := by
        nlinarith [h11]
      have h14 : (Bx - Ax - 4 * Real.sqrt 5) * (Bx - Ax + 4 * Real.sqrt 5) = 0 := by
        nlinarith [h13]
      cases (mul_eq_zero.mp h14) with
      | inl h15 =>
        left
        linarith
      | inr h16 =>
        right
        linarith
    cases h12 with
    | inl h13 =>
      left
      linarith
    | inr h14 =>
      right
      linarith
  cases h8 with
  | inl h9 =>
    rw [h9]
    have h10 : abs (4 * Real.sqrt 5) = 4 * Real.sqrt 5 := by
      apply abs_of_nonneg
      positivity
    rw [h10]
  | inr h9 =>
    rw [h9]
    have h11 : abs (- (4 * Real.sqrt 5)) = 4 * Real.sqrt 5 := by
      have h12 : Real.sqrt 5 > 0 := by
        apply Real.sqrt_pos.mpr
        norm_num
      have h13 : - (4 * Real.sqrt 5) < (0 : ℝ) := by
        nlinarith [show Real.sqrt 5 > 0 by apply Real.sqrt_pos.mpr (by norm_num)]
      rw [abs_of_neg h13]
      all_goals nlinarith
    rw [h11]