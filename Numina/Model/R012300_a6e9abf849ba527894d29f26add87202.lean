import Mathlib

theorem algebra_93893 (d t : ℝ) (ht : t > 0) (h : d = 16 * t ^ 2) (h' : t + d / 1120 = 7.7) :
    d = 784 := by
  have h1 : d = 16 * t ^ 2 := h
  have h2 : t + d / 1120 = 7.7 := h'
  rw [h1] at h2
  have eq1 : 16 * t ^ 2 / (1120 : ℝ) = (1/70) * t ^ 2 := by
    ring_nf
  have eq2 : t + (16 * t ^ 2 / (1120 : ℝ)) = 7.7 := by
    linarith
  rw [eq1] at eq2
  have eq3 : (1/70 : ℝ) * t ^ 2 + t - 7.7 = 0 := by
    linarith
  have eq4 : t ^ 2 + 70 * t - 539 = 0 := by
    have eq5 : ( (1/70 : ℝ) * t ^ 2 + t - 7.7 = 0 ) := eq3
    ring_nf at eq5 ⊢
    linarith
  have eq5 : (t + 77) * (t - 7) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 eq5) with h6 h7
  · -- Case where t + 77 = 0, which implies t = -77, contradicting t > 0
    have h8 : t = -77 := by linarith
    nlinarith -- Contradicts t > 0
  · -- Case where t - 7 = 0, so t = 7.
    have ht_eq : t = 7 := by linarith
    rw [ht_eq] at h1
    nlinarith