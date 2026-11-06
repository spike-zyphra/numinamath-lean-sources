import Mathlib

theorem number_theory_7924 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : Real.sqrt (x % 1 + y % 1) = Real.sqrt (x % 1) + Real.sqrt (y % 1)) :
    x % 1 = 0 ∨ y % 1 = 0 := by
  have h1 : Real.sqrt (x % 1 + y % 1) = Real.sqrt (x % 1) + Real.sqrt (y % 1) := h

  have h2 : x % 1 ≥ 0 := by
    norm_num
    all_goals omega
  have h3 : y % 1 ≥ 0 := by
    norm_num
    all_goals omega
  have h4 : (Real.sqrt (x % 1 + y % 1)) ^ 2 = (Real.sqrt (x % 1) + Real.sqrt (y % 1)) ^ 2 := by
    rw [h1]
  have h5 : (Real.sqrt (x % 1 + y % 1)) ^ 2 = x % 1 + y % 1 := Real.sq_sqrt (show x % 1 + y % 1 ≥ 0 by positivity)
  have h6 : (Real.sqrt (x % 1) + Real.sqrt (y % 1)) ^ 2 = (Real.sqrt (x % 1)) ^ 2 + (Real.sqrt (y % 1)) ^ 2 + 2 * (Real.sqrt (x % 1)) * (Real.sqrt (y % 1)) := by
    ring
  have h7 : (Real.sqrt (x % 1)) ^ 2 = x % 1 := by
    exact Real.sq_sqrt (show x % 1 ≥ 0 by positivity)
  have h8 : (Real.sqrt (y % 1)) ^ 2 = y % 1 := by
    exact Real.sq_sqrt (show y % 1 ≥ 0 by positivity)
  rw [h5, h6, h7, h8] at h4
  have h9 : (Real.sqrt (x % 1)) * (Real.sqrt (y % 1)) = 0 := by
    linarith
  cases' (mul_eq_zero.mp h9) with h10 h11
  · -- Real.sqrt (x % 1) = 0
    have h12 : x % 1 = 0 := by
      have : Real.sqrt (x % 1) = 0 := by
        linarith
      rw [Real.sqrt_eq_zero (by positivity)] at this
      linarith
    left
    exact h12
  · -- Real.sqrt (y % 1) = 0
    have h13 : y % 1 = 0 := by
      have : Real.sqrt (y % 1) = 0 := by
        linarith
      rw [Real.sqrt_eq_zero (by positivity)] at this
      linarith
    right
    exact h13