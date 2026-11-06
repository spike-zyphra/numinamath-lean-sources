import Mathlib

theorem algebra_319592 {a b : ℝ} (h : ∀ n ∈ Finset.range 3, a^3 + b^3 = a^n + b^n) :
    a + b ≤ 2 := by
  have h0 := h 0 (by simp)
  have h1 := h 1 (by simp)
  have h2 := h 2 (by simp)
  have h4 : a^3 + b^3 = 2 := by
    simp [pow_zero] at h0
    nlinarith
  have h5 : a + b = 2 := by
    have eq2 : a^3 + b^3 = a + b := by 
      simp [pow_one] at h1
      linarith
    nlinarith [h4, eq2]
  linarith [h5]