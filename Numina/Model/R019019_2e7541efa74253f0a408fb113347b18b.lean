import Mathlib

theorem algebra_306671 {a b : ℕ} (h : ∃ m n, m ≠ n ∧ m^2 + a * m + 1 = b ∧ n^2 + a * n + 1 = b) :
    ¬Prime (a^2 + b^2) := by
  rcases h with ⟨m, n, hneq, hm, hn⟩
  have h1 : m^2 + a * m + 1 = n^2 + a * n + 1 := by
    linarith
  have h2 : m^2 + a * m = n^2 + a * n := by
    linarith
  have h4 : m < n ∨ n < m := by
    by_contra h
    push_neg at h
    have h5 : m = n := by
      omega
    contradiction
  rcases h4 with h4 | h4
  · -- Assume m < n
    have h5 : m < n := h4
    have h6 : m ^ 2 + a * m < n ^ 2 + a * n := by
      nlinarith [show m < n by linarith, sq_pos_of_pos (show 0 < (n - m : ℕ) by omega)]
    nlinarith
  · -- Assume n < m
    have h5 : n < m := by
      omega
    have h6 : n ^ 2 + a * n < m ^ 2 + a * m := by
      nlinarith [show n < m by linarith, sq_pos_of_pos (show 0 < (m - n : ℕ) by omega)]
    nlinarith