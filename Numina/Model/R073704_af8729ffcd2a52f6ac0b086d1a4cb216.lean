import Mathlib

theorem number_theory_298129 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmn : 24 * m = n ^ 4) :
    m ≥ 54 := by
  have h1 : n ≥ 6 := by
    by_contra h
    push_neg at h
    have h2 : n < 6 := by linarith
    interval_cases n <;> omega
  have h2 : n ^ 4 ≥ 1296 := by
    have h3 : n ≥ 6 := h1
    have h4 : (n : ℕ) ^ 4 ≥ 6 ^ 4 := by
      apply Nat.pow_le_pow_of_le_left h3 4
    norm_num at h4 ⊢
    linarith
  have h3 : 24 * m ≥ 1296 := by
    linarith
  have h4 : m ≥ 54 := by
    omega
  linarith