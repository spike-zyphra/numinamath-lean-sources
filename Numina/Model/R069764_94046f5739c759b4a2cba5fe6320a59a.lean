import Mathlib

theorem algebra_247085 (f : ℝ → ℝ) (hf : f = fun x => 3 * x ^ 2 + 6 * Real.sqrt 3 * x - 18)
    (A : ℝ × ℝ) (hA : A = (Real.sqrt 3, 9)) :
    f A.1 = A.2 := by
  rw [hA] at *
  rw [hf]
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  simp [h1]
  <;> linarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]