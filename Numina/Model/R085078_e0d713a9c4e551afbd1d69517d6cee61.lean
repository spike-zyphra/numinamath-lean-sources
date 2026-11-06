import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem calculus_281088 (a : ℝ) (z : ℂ) (hz : z = a + I)
  (hzz : z.re < 0 ∧ z.im > 0) (hzz' : abs (z * (1 + I)) > 2) :
  a < -1 := by
  have h1 : z.re = a := by
    simp [hz]
  have h2 : z.im = 1 := by
    simp [hz]
  have ha1 : a < 0 := by 
    linarith [h1, hzz.left]
  have h3 : z * (1 + I) = (a - 1) + (a + 1) * I := by 
    rw [hz]
    simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    <;> ring
  have h4 : abs (z * (1 + I)) = Real.sqrt ((a - 1) ^ 2 + (a + 1) ^ 2) := by
    rw [h3]
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [h4] at hzz'
  have h5 : (a - 1) ^ 2 + (a + 1) ^ 2 > 4 := by 
    by_contra h
    push_neg at h
    have h6 : Real.sqrt ((a - 1) ^ 2 + (a + 1) ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
    have h7 : Real.sqrt 4 = 2 := by
      rw [Real.sqrt_eq_cases]
      norm_num
    linarith [h6, h7, hzz']
  nlinarith [h5, sq_nonneg (a), ha1]