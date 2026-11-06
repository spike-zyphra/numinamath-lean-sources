import Mathlib

theorem algebra_21180 {P : ℝ → ℝ} (hP : P = fun x => x ^ 2 + 6 * x - 4) :
    P (Real.sqrt 13 - 3) = 0 := by 
  rw [hP]
  have h2 : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by
    exact Real.sq_sqrt (by norm_num)
  simp [h2]
  <;> ring_nf
  <;> norm_num [Real.sqrt_nonneg, Real.sq_sqrt]
  <;> nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]