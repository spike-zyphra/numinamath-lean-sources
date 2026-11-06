import Mathlib

theorem inequalities_125949 (p q : ℝ) (mp : p > 0) (hq : q > 0)
    (h : p + q = 1) (m n : ℕ) :
    p ^ m * q ^ n ≤ 1 := by
  have hp1 : p ≤ 1 := by linarith
  have h10 : q = 1 - p := by nlinarith
  rw [ h10 ]
  have hp2 : p ≥ 0 := by linarith
  have hp3 : (1 - p) ≥ 0 := by nlinarith
  have hp4 : p ≤ 1 := hp1
  have hp5 : (1 - p) ≤ 1 := by nlinarith
  have h6 : p ^ m ≥ 0 := by positivity
  have h7 : ( (1 - p) ) ^ n ≥ 0 := by positivity

  have h8 : p ^ m ≤ 1 := by
    have h2 : p ≥ 0 := by linarith
    have h3 : p ≤ 1 := hp1
    have h9 : p ^ m ≤ 1 := by
      apply pow_le_one
      all_goals nlinarith

    linarith

  have h9 : ( (1 - p) ) ^ n ≤ 1 := by
    have h12 : (1 - p) ≥ 0 := by nlinarith
    have h11 : (1 - p) ≤ 1 := by nlinarith
    have h12 : ( (1 - p) ) ^ n ≤ 1 := by
      apply pow_le_one
      all_goals nlinarith

    linarith

  nlinarith [mul_nonneg (show 0 ≤ (p) by linarith) (show 0 ≤ (1 - p) by nlinarith), sq_nonneg (p - (1 - p)), sq_nonneg (p), sq_nonneg (1 - p) ]