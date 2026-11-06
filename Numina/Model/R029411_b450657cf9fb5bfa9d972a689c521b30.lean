import Mathlib

theorem inequalities_604174 (a b c d e : ℝ) (h₀ : a + b + c + d + e = 0)
    (A B : ℝ) (hA : A = a * b + b * c + c * d + d * e + e * a)
    (hB : B = a * c + c * e + e * b + b * d + d * a) :
    2005 * A + B ≤ 0 ∨ A + 2005 * B ≤ 0 := by
  by_contra h
  push_neg at h
  have h1 : 2005 * A + B > 0 := by linarith [h.1]
  have h2 : A + 2005 * B > 0 := by linarith [h.2]
  have h_sq_zero : (a + b + c + d + e) ^ 2 = 0 := by
    rw [h₀]
    norm_num
  have h3 : (2005 * A + B) + (A + 2005 * B) ≤ 0 := by
    have h_eq1 : A + B = (a * b + b * c + c * d + d * e + e * a) + (a * c + c * e + e * b + b * d + d * a) := by 
      rw [hA, hB]
    have h_eq2 : A + B ≤ 0 := by
      have h4 : (a + b + c + d + e) ^ 2 = 0 := h_sq_zero
      have h5 : (a + b + c + d + e) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + 2 * (A + B) := by
        rw [hA, hB]
        ring_nf
      rw [h5] at h4
      nlinarith [sq_nonneg (a + b + c + d + e), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (d - e)]
    have h7 : (2005 * A + B) + (A + 2005 * B) = 2006 * (A + B) := by
      linarith
    nlinarith [h_eq2, h7]
  have h4 : (2005 * A + B) + (A + 2005 * B) > 0 := by
    linarith [h1, h2]
  linarith [h4, h3]