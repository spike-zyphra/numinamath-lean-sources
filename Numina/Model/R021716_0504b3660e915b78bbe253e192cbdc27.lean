import Mathlib

theorem algebra_239584 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a - 4 * Real.sqrt (b * c) + 2 * b = 2 * Real.sqrt (a * c) - 3 * c) :
    a = b ∧ b = c := by 
  have h3 : Real.sqrt (b * c) = Real.sqrt b * Real.sqrt c := by
    rw [Real.sqrt_mul]
    all_goals nlinarith
  have h4 : Real.sqrt (a * c) = Real.sqrt a * Real.sqrt c := by
    rw [Real.sqrt_mul]
    all_goals nlinarith
  rw [h3] at h
  rw [h4] at h
  have h5 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith)
  have h6 : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt (by linarith)
  have h7 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
  have h11 : Real.sqrt b = Real.sqrt c := by
    nlinarith [sq_nonneg (Real.sqrt b - Real.sqrt c), sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a - Real.sqrt c), 
      Real.sqrt_nonneg b, Real.sqrt_nonneg c, Real.sqrt_nonneg a, 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      Real.sq_sqrt (show 0 ≤ b by linarith), 
      Real.sq_sqrt (show 0 ≤ c by linarith), 
      Real.sq_sqrt (show 0 ≤ a by linarith)]
  have hbc : b = c := by
    have h13 : Real.sqrt b = Real.sqrt c := h11
    have h14 : (Real.sqrt b) ^ 2 = b := h5
    have h15 : (Real.sqrt c) ^ 2 = c := h6
    have h16 : b = c := by
      have h17 : (Real.sqrt b) ^ 2 = (Real.sqrt c) ^ 2 := by
        rw [h13]
      rw [h14, h15] at h17
      linarith
    linarith
  have h18 : a = b := by
    have h17 : b = c := hbc
    have eq1 : a - 4 * (Real.sqrt b * Real.sqrt c) + 2 * b = 2 * (Real.sqrt a * Real.sqrt c) - 3 * c := h
    have h11' : Real.sqrt c = Real.sqrt b := by linarith [h11]
    rw [h11'] at eq1
    have eq2 : a + b = 2 * (Real.sqrt a * Real.sqrt b) := by
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c]
    have h15 : (Real.sqrt a) ^ 2 = a := h7
    have h14 : (Real.sqrt b) ^ 2 = b := h5
    have eq7 : (a - b) ^ 2 = 0 := by
      nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sqrt_nonneg a, Real.sqrt_nonneg b, sq_nonneg (a - b)]
    have eq8 : a - b = 0 := by
      nlinarith
    linarith
  constructor
  · linarith [h18]
  · linarith [hbc]