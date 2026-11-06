import Mathlib

theorem algebra_15605 {m : ℝ} 
    (hm₁ : 0 < m - 2) (hm₂ : 0 < 2 * m + 7) 
    (h : (2 * m + 7) * (m - 2) = 51) : m = 5 := by
  have h1 : (2 * m + 7) * (m - 2) = 2 * m ^ 2 + 3 * m - 14 := by
    ring
  rw [h1] at h
  have h2 : 2 * m ^ 2 + 3 * m - 65 = 0 := by
    linarith
  have h3 : (m - 5) * (2 * m + 13) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case $m - 5 = 0$, so $m = 5$ 
    linarith 
  · -- Case $2m + 13 = 0$, so $m = -13/2$
    -- However, $m = -13/2$ contradicts $0 < m - 2$
    nlinarith