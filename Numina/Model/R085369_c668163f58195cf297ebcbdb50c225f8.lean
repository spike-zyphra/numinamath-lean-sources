import Mathlib

theorem algebra_203869 (a : ℝ) (ha : a > 0) (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 2 - Real.sqrt 2)
    (h : f (f (Real.sqrt 2)) = -Real.sqrt 2) :
    a = Real.sqrt 2 / 2 := by
  have h1 : f (Real.sqrt 2) = 2 * a - Real.sqrt 2 := by
    rw [hf]
    have h2 : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    rw [h2]
    ring
  have h3 : f (f (Real.sqrt 2)) = a * (2 * a - Real.sqrt 2) ^ 2 - Real.sqrt 2 := by
    rw [h1]
    apply hf
  rw [h3] at h
  have h4 : a * (2 * a - Real.sqrt 2) ^ 2 = 0 := by
    linarith [h]
  have h5 : (2 * a - Real.sqrt 2) ^ 2 = 0 := by
    nlinarith [h4, show 0 < a by linarith]
  have h6 : 2 * a - Real.sqrt 2 = 0 := by
    rw [sq_eq_zero_iff] at h5
    exact h5
  have h7 : 2 * a = Real.sqrt 2 := by linarith
  linarith