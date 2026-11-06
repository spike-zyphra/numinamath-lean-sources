import Mathlib

theorem algebra_310116 (x : ℝ) (h : 0 ≤ 7 * x ^ 2 + 9 * x + 13 ∧ 0 ≤ 7 * x ^ 2 - 5 * x + 13)
    (h' : Real.sqrt (7 * x ^ 2 + 9 * x + 13) + Real.sqrt (7 * x ^ 2 - 5 * x + 13) = 7 * x) :
    x = 12 / 7 := by
  have h1 : 0 ≤ 7 * x ^ 2 + 9 * x + 13 := h.1
  have h2 : 0 ≤ 7 * x ^ 2 - 5 * x + 13 := h.2
  have eq1 : Real.sqrt (7 * x ^ 2 + 9 * x + 13) ≥ 0 := by positivity
  have eq2 : Real.sqrt (7 * x ^ 2 - 5 * x + 13) ≥ 0 := by positivity
  have h_eq1 : Real.sqrt (7 * x ^ 2 + 9 * x + 13) + Real.sqrt (7 * x ^ 2 - 5 * x + 13) = 7 * x := h'
  have h_eq2 : (Real.sqrt (7 * x ^ 2 + 9 * x + 13) + Real.sqrt (7 * x ^ 2 - 5 * x + 13)) ^ 2 = (7 * x) ^ 2 := by
    rw [h_eq1]
  have h_eq3 : (Real.sqrt (7 * x ^ 2 + 9 * x + 13) + Real.sqrt (7 * x ^ 2 - 5 * x + 13)) ^ 2 =
    (Real.sqrt (7 * x ^ 2 + 9 * x + 13)) ^ 2 + (Real.sqrt (7 * x ^ 2 - 5 * x + 13)) ^ 2 + 2 * (Real.sqrt (7 * x ^ 2 + 9 * x + 13)) * (Real.sqrt (7 * x ^ 2 - 5 * x + 13)) := by ring
  have h_eq4 : (7 * x) ^ 2 = 49 * x^2 := by ring
  rw [h_eq3] at h_eq2
  rw [h_eq4] at h_eq2
  have h_eq5 : (Real.sqrt (7 * x ^ 2 + 9 * x + 13)) ^ 2 = 7 * x ^ 2 + 9 * x + 13 := by
    rw [Real.sq_sqrt]
    linarith
  have h_eq6 : (Real.sqrt (7 * x ^ 2 - 5 * x + 13)) ^ 2 = 7 * x ^ 2 - 5 * x + 13 := by
    rw [Real.sq_sqrt]
    linarith
  rw [h_eq5, h_eq6] at h_eq2
  have h_eq3 : 2 * (Real.sqrt (7 * x ^ 2 + 9 * x + 13)) * (Real.sqrt (7 * x ^ 2 - 5 * x + 13)) = 35 * x^2 - 4 * x - 26 := by
    nlinarith
  have h_eq4 : 4 * ((7 * x ^ 2 + 9 * x + 13) * (7 * x ^ 2 - 5 * x + 13)) = (35 * x ^ 2 - 4 * x - 26) ^ 2 := by
    have h_eq5 : (2 * (Real.sqrt (7 * x ^ 2 + 9 * x + 13)) * (Real.sqrt (7 * x ^ 2 - 5 * x + 13))) ^ 2 = (35 * x ^ 2 - 4 * x - 26) ^ 2 := by
      rw [h_eq3]
    have h_eq6 : (2 * (Real.sqrt (7 * x ^ 2 + 9 * x + 13)) * (Real.sqrt (7 * x ^ 2 - 5 * x + 13))) ^ 2 = 4 * ((7 * x ^ 2 + 9 * x + 13) * (7 * x ^ 2 - 5 * x + 13)) := by
      calc
        (2 * (Real.sqrt (7 * x ^ 2 + 9 * x + 13)) * (Real.sqrt (7 * x ^ 2 - 5 * x + 13))) ^ 2
        = 4 * ((Real.sqrt (7 * x ^ 2 + 9 * x + 13)) ^ 2 * (Real.sqrt (7 * x ^ 2 - 5 * x + 13)) ^ 2) := by ring_nf
        _ = 4 * ((7 * x ^ 2 + 9 * x + 13) * (7 * x ^ 2 - 5 * x + 13)) := by
          rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    rw [h_eq6] at h_eq5
    linarith
  have h_eq5 : x ^ 2 * (21 * x ^ 2 - 8 * x - 48) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h_eq5) with h_eq6 h_eq7
  · 
    have h_eq8 : x ^ 2 = 0 := by 
      nlinarith
    have h_eq9 : x = 0 := by
      nlinarith
    rw [h_eq9] at h_eq1
    norm_num [Real.sqrt_nonneg, h_eq9] at h_eq1
  · 
    have h_eq8 : 21 * x ^ 2 -8 * x -48 = 0 := by
      nlinarith
    have h_eq9 : (x - 12 / 7) * (x + 4 / 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h_eq9) with h_eq10 h_eq11
    · 
      linarith
    · 
      have h_eq14 : x = -4 / 3 := by
        linarith
      rw [h_eq14] at h_eq1
      nlinarith [Real.sqrt_nonneg (7 * (-4 / 3) ^ 2 + 9 * (-4 / 3) + 13), Real.sqrt_nonneg (7 * (-4 / 3) ^ 2 - 5 * (-4 / 3) + 13), Real.sq_sqrt (show (0: ℝ) ≤ 7 * (-4 / 3) ^ 2 + 9 * (-4 / 3) + 13 by nlinarith), Real.sq_sqrt (show (0: ℝ) ≤ 7 * (-4 / 3) ^ 2 - 5 * (-4 / 3) + 13 by nlinarith)]