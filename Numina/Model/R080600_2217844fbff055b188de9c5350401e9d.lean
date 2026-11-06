import Mathlib

theorem algebra_308858 {m n : ℝ} (hmn : m ≠ n) (h1 : m^2 = n + 2) (h2 : n^2 = m + 2) :
    m^3 - 2 * m * n + n^3 = -2 := by
  have eq3 : m + n = -1 := by
    have eq1 : m^2 - n^2 = n - m := by linarith
    have eq2 : m^2 - n^2 = (m - n) * (m + n) := by
      ring
    rw [eq2] at eq1
    have eq4 : (m - n) * (m + n + 1) = 0 := by
      linarith
    cases (mul_eq_zero.mp eq4) with
    | inl h => 
      exfalso
      apply hmn
      linarith
    | inr h => 
      linarith
  have hmn_eq : m * n = -1 := by
    have h_sum_sq : m^2 + n^2 = (m + n)^2 - 2 * (m * n) := by
      ring
    have h_mn : m^2 + n^2 = m + n + 4 := by 
      have h1' : m^2 = n + 2 := by linarith
      have h2' : n^2 = m + 2 := by linarith
      have h3 : m^2 + n^2 = (n + 2) + (m + 2) := by 
        linarith [h1', h2']
      linarith [h3]
      all_goals nlinarith
    rw [eq3] at h_mn
    rw [eq3] at h_sum_sq
    nlinarith
  have eq4 : m^3 + n^3 = (m + n)^3 - 3 * (m * n) * (m + n) := by 
    ring
  have eq5 : m^3 - 2 * m * n + n^3 = (m^3 + n^3) - 2 * (m * n) := by
    ring
  rw [eq5]
  rw [eq4]
  rw [eq3, hmn_eq]
  norm_num
  all_goals nlinarith