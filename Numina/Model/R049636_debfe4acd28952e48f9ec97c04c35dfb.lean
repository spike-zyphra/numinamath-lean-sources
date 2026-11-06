import Mathlib

theorem algebra_250534 {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : Real.sqrt (a * c) + Real.sqrt (b * d) = Real.sqrt ((a + b) * (c + d))) : a * d = b * c := by
  have h1 : Real.sqrt (a * c) + Real.sqrt (b * d) = Real.sqrt ((a + b) * (c + d)) := h
  have h2 : (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 = (Real.sqrt ((a + b) * (c + d))) ^ 2 := by
    rw [h1]
  have h3 : (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 = (Real.sqrt (a * c)) ^ 2 + (Real.sqrt (b * d)) ^ 2 + 2 * (Real.sqrt (a * c) * Real.sqrt (b * d)) := by ring
  have h4 : (Real.sqrt ((a + b) * (c + d))) ^ 2 = (a + b) * (c + d) := by
    apply Real.sq_sqrt
    positivity
  rw [h3, h4] at h2
  have h5 : (Real.sqrt (a * c)) ^ 2 = a * c := by
    apply Real.sq_sqrt
    positivity
  have h6 : (Real.sqrt (b * d)) ^ 2 = b * d := by
    apply Real.sq_sqrt
    positivity
  rw [h5, h6] at h2
  have h7 : 2 * (Real.sqrt (a * c) * Real.sqrt (b * d)) = a * d + b * c := by
    linarith
  have h8 : (2 * (Real.sqrt (a * c) * Real.sqrt (b * d))) ^ 2 = (a * d + b * c) ^ 2 := by 
    rw [h7]
  have h9 : (2 * (Real.sqrt (a * c) * Real.sqrt (b * d))) ^ 2 = 4 * (a * c * b * d) := by
    calc
      (2 * (Real.sqrt (a * c) * Real.sqrt (b * d))) ^ 2 
        = 4 * ((Real.sqrt (a * c) * Real.sqrt (b * d)) ^ 2) := by ring
      _ = 4 * ((Real.sqrt (a * c)) ^ 2 * (Real.sqrt (b * d)) ^ 2) := by ring
      _ = 4 * ((a * c) * (b * d)) := by 
        rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      _ = 4 * (a * c * b * d) := by ring
  rw [h9] at h8
  have h10 : (a * d + b * c) ^ 2 = a^2 * d^2 + 2 * a * b * c * d + b^2 * c^2 := by ring
  rw [h10] at h8
  have h11 : (a * d - b * c) ^ 2 = 0 := by
    nlinarith
  have h12 : a * d - b * c = 0 := by
    rw [sq_eq_zero_iff] at h11
    linarith
  linarith