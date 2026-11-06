import Mathlib

open Real

theorem inequalities_255378 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 2 * Real.sqrt (a * b * c)) : b * c ≥ b + c := by
  by_cases h4 : b * c > 0
  ·
    have h1 : 0 ≤ a * b * c := by
      apply mul_nonneg
      apply mul_nonneg
      all_goals nlinarith
    have h2 : (Real.sqrt (a * b * c)) ^ 2 = a * b * c := by
      rw [Real.sq_sqrt]
      positivity
    have h3 : (a + b + c) ^ 2 = 4 * (a * b * c) := by
      calc
        (a + b + c) ^ 2 = (2 * Real.sqrt (a * b * c)) ^ 2 := by rw [h]
        _ = 4 * (Real.sqrt (a * b * c) ^ 2) := by ring
        _ = 4 * (a * b * c) := by rw [h2]

    by_cases ha' : a > 0
    ·
      have h4' : (a + b + c) ^ 2 ≥ 4 * a * (b + c) := by
        nlinarith [sq_nonneg (a - (b + c)), sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c)]
      have h5 : 4 * (a * b * c) ≥ 4 * a * (b + c) := by
        nlinarith [h3, h4']
      have h7 : b * c ≥ b + c := by
        nlinarith
      linarith
    ·
      have h10 : a = 0 := by linarith
      have h11 : b + c = 0 := by
        rw [show a = 0 by linarith [h10]] at h3
        nlinarith [sq_nonneg (b * c), sq_nonneg (b + c), sq_nonneg (b - c)]
      have h12 : b = 0 := by nlinarith [h11, hb, hc]
      have h13 : c = 0 := by nlinarith [h11, hb, hc]
      rw [h12, h13]
      all_goals nlinarith
  ·
    have h4' : b * c = 0 := by nlinarith
    have h5 : Real.sqrt (a * b * c) = 0 := by
      have h8 : a * b * c = 0 := by
        nlinarith [h4']
      rw [h8]
      simp
    have h10 : a + b + c = 0 := by
      nlinarith [h, h5]
    have h11 : a = 0 := by nlinarith [h10, ha, hb, hc]
    have h12 : b = 0 := by nlinarith [h10, ha, hb, hc]
    have h13 : c = 0 := by nlinarith [h10, ha, hb, hc]
    rw [h12, h13]
    all_goals nlinarith