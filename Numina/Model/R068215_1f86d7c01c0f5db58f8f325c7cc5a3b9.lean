import Mathlib

theorem algebra_327497 {m n : ℝ} (h : m ≠ n) (h' : (m + 6) * (m + 5) - (n + 6) * (n + 5) = 2006 * m * (m - 1) - 2006 * n * (n - 1)) :
    m + n = 2017 / 2005 := by
  have eq1 : (m + 6) * (m + 5) - (n + 6) * (n + 5) = m^2 - n^2 + 11 * (m - n) := by ring
  have eq2 : 2006 * m * (m - 1) - 2006 * n * (n - 1) = 2006 * (m^2 - n^2) - 2006 * (m - n) := by 
    ring
  rw [eq1, eq2] at h'

  have eq4 : (m - n) * (-2005 * (m + n) + 2017) = 0 := by
    nlinarith [h']

  cases' (mul_eq_zero.1 eq4) with h4 h5

  -- Case 1: h4 : m - n = 0, which contradicts h : m ≠ n
  · -- h4 : m - n = 0
    exfalso
    apply h
    linarith

  -- Case 2: h5 : -2005 * (m + n) + 2017 = 0, solving for m + n
  · -- h5 : -2005 * (m + n) + 2017 = 0
    linarith