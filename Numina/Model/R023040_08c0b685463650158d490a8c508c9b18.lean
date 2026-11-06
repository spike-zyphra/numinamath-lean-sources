import Mathlib

theorem number_theory_131003 (m n : ℕ) (hmn : 1 / 3 < m / n ∧ m / n < 1)
    (hadd : ∃ k, (m + k) / (n * k) = m / n) :
    m / n = 2 / 3 ∨ m / n = 2 / 4 ∨ m / n = 2 / 5 := by
  have h1 : 1 / 3 < m / n := hmn.1
  have h2 : m / n < 1 := hmn.2
  have h3 : (1 / 3) = 0 := by
    norm_num
  have h4 : 0 < m / n := by
    omega
  have h5 : m / n < 1 := by
    omega
  have h6 : m / n = 0 := by
    omega
  omega