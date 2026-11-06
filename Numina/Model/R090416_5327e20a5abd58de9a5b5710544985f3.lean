import Mathlib

theorem algebra_901 {m n : ℝ} (h₀ : m ≠ n) (h₁ : m^2 = n + 2) (h₂ : n^2 = m + 2) : m^3 - 2 * m * n + n^3 = -2 := by
  have eq1 : m^2 - n^2 = n - m := by
    linarith
  have eq2 : (m - n) * (m + n) = (n - m) := by 
    nlinarith [eq1]
  have eq3 : (m - n) * (m + n) = -(m - n) := by 
    nlinarith [eq2]
  have h3 : m - n ≠ 0 := by 
    intro h
    apply h₀
    linarith
  have h4 : m + n + 1 = 0 := by 
    apply (mul_left_inj' h3).mp
    linarith
  have h5 : m + n = -1 := by
    linarith
  have h6 : m * n = -1 := by 
    nlinarith [h₁, h₂, h5]
  have h3' : m^3 + n^3 = (m + n)^3 - 3 * (m * n) * (m + n) := by
    ring
  nlinarith [h3', h5, h6]