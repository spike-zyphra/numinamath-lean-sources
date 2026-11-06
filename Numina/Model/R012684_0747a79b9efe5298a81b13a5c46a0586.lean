import Mathlib

theorem algebra_93041 (m r d : ℝ) (hm : 0 < m) (hr : 0 < r) (hd : 0 < d)
    (h : 1 / m / d = 1 / (m + r) / x) :
    x = m * d / (m + r) := by
  have h1 : x ≠ 0 := by
    by_contra h1
    rw [h1] at h
    field_simp [(show m ≠ 0 by linarith), (show d ≠ 0 by linarith), (show m + r ≠ 0 by nlinarith)] at h 
  have h2 : m * d ≠ 0 := by
    apply mul_ne_zero
    linarith
    linarith
  have h3 : m + r ≠ 0 := by
    linarith
  field_simp [(show m ≠ 0 by linarith), (show d ≠ 0 by linarith), 
      (show m + r ≠ 0 by linarith), h1] at h ⊢
  <;> nlinarith