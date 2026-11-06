import Mathlib

theorem algebra_21257 {a r : ℝ} (ha : a = 7) (hr : r ≠ 0) (h7 : a * r^6 = 5103) :
    a * r^4 = 567 := by
  rw [ha] at h7 ⊢
  have h8 : (7 : ℝ) * r ^ 6 = 5103 := by
    simpa using h7
  have h9 : r ^ 6 = 729 := by
    nlinarith
  have h10 : r ^ 2 = 9 := by 
    have h11 : r ^ 6 - 729 = 0 := by linarith
    have h12 : r ^ 6 - 729 = (r ^ 2 - 9) * (r ^ 4 + 9 * r ^ 2 + 81) := by
      ring_nf
    rw [h12] at h11
    cases' (mul_eq_zero.1 h11) with h13 h14
    · -- Case r^2 - 9 = 0
      linarith
    · -- Case r^4 + 9 * r^2 + 81 = 0
      nlinarith [sq_nonneg (r ^ 2), sq_nonneg (r ^ 2 - 9)]
  have h12 : r ^ 4 = 81 := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring_nf
      _ = 9 ^ 2 := by rw [h10]
      _ = (81 : ℝ) := by norm_num
  nlinarith