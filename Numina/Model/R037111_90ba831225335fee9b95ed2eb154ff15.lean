import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_274386 {f : ℝ → ℝ}
  (hf : f = λ x => 2 * (logb (1/2) x)^2 - 2 * logb (1/2) x + 1) :
  StrictMonoOn f (Ici (sqrt 2 / 2)) := by
  intro x hx y hy hxy
  have h1 : x ≥ sqrt 2 / 2 := by
    simpa using hx
  have h2 : y ≥ sqrt 2 / 2 := by
    simpa using hy
  have h3 : x < y := hxy
  have hx4 : x > 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have hy4 : y > 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h4 : f x = 2 * (logb (1 / 2) x) ^ 2 - 2 * (logb (1 / 2) x) + 1 := by
    rw [hf]
  have h5 : f y = 2 * (logb (1 / 2) y) ^ 2 - 2 * (logb (1 / 2) y) + 1 := by
    rw [hf]
  have h6 : logb (1 / 2) x = logb 2 x / logb 2 (1 / 2) := by
    field_simp [logb]
  have h7 : logb (1 / 2) y = logb 2 y / logb 2 (1 / 2) := by
    field_simp [logb]
  have h8 : logb 2 (1 / 2 : ℝ) = -1 := by
    rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
  have h9 : logb (1 / 2) x = - logb 2 x := by
    rw [h6, h8]
    <;> ring_nf
  have h10 : logb (1 / 2) y = - logb 2 y := by
    rw [h7, h8]
    <;> ring_nf
  rw [h4, h9]
  rw [h5, h10]
  have h11 : Real.logb (2 : ℝ) x < Real.logb (2 : ℝ) y := by
    apply Real.logb_lt_logb
    all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h12 : Real.logb (2 : ℝ) x - Real.logb (2 : ℝ) y < 0 := by
    linarith
  have h13 : Real.logb (2 : ℝ) x + Real.logb (2 : ℝ) y > -1 := by
    have h14 : Real.logb (2 : ℝ) x + Real.logb (2 : ℝ) y = Real.logb (2 : ℝ) (x * y) := by
      rw [Real.logb_mul (by positivity) (by positivity)]
    have h15 : x * y > (1 / 2 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_pos (show (0 : ℝ) < x by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]) (show (0 : ℝ) < y by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)])]
    have h16 : Real.logb (2 : ℝ) (x * y) > -1 := by
      have h17 : Real.logb (2 : ℝ) (x * y) > Real.logb (2 : ℝ) (1 / 2 : ℝ) := by
        apply Real.logb_lt_logb
        all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h18 : Real.logb (2 : ℝ) (1 / 2 : ℝ) = -1 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      linarith [h17, h18]
    linarith [h14, h16]
  have h17 : (Real.logb (2 : ℝ) x - Real.logb (2 : ℝ) y) * (Real.logb (2 : ℝ) x + Real.logb (2 : ℝ) y + 1) < 0 := by
    apply mul_neg_of_neg_of_pos
    · linarith
    ·
      linarith
  nlinarith