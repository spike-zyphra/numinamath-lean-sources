import Mathlib

/- Let $x>0$, and ${{x}^{2}}+\frac{1}{{{x}^{2}}}=7$, then ${{x}^{5}}+\frac{1}{{{x}^{5}}}=$ ___          ___. -/
theorem algebra_11298 {x : ℝ} (hx : x > 0) (h : x ^ 2 + 1 / x ^ 2 = 7) :
    x ^ 5 + 1 / x ^ 5 = 123 := by
  
  have h1 : x + 1 / x = 3 := by
    have h2 : (x + 1 / x) ^ 2 = x ^ 2 + 1 / x ^ 2 + 2 := by
      field_simp
      ring
    rw [h] at h2
    have h3 : (x + 1 / x) ^ 2 = 9 := by
      linarith
    have h4 : x + 1 / x > 0 := by
      positivity
    have h5 : x + 1 / x = 3 := by
      nlinarith
    exact h5
  
  have h6 : x ^ 3 + 1 / x ^ 3 = 18 := by
    have h7 : x ^ 3 + 1 / x ^ 3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
      field_simp
      ring
    rw [h1] at h7
    nlinarith
  
  have h8 : x ^ 4 + 1 / x ^ 4 = 47 := by
    have h9 : x ^ 4 + 1 / x ^ 4 = (x ^ 2 + 1 / x ^ 2) ^ 2 - 2 := by
      field_simp
      ring
    rw [h] at h9
    nlinarith
  
  have h10 : x ^ 5 + 1 / x ^ 5 = (x + 1 / x) * (x ^ 4 + 1 / x ^ 4) - (x ^ 3 + 1 / x ^ 3) := by
    field_simp
    ring
  
  rw [h1, h8, h6] at h10
  nlinarith