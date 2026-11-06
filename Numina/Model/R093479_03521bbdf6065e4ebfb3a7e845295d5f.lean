import Mathlib

theorem number_theory_447 (n : ℕ) (hn : n ≠ 0) :
    ¬ ∃ x, x^2 = n * (n + 1) * (n + 2) * (n + 3) := by
  rintro ⟨x, hx⟩
  have h1 : x ^ 2 = n * (n + 1) * (n + 2) * (n + 3) := hx
  have h2 : x ^ 2 > (n^2 + 3 * n) ^ 2 := by
    nlinarith [h1, sq_nonneg (x - n^2 - 3 * n), sq_nonneg (n + 1), sq_nonneg (x - n^2 - 3 * n - 1), sq_pos_of_ne_zero (show n ≠ 0 by exact hn), sq_nonneg (n + 3)]
  have h3 : x ^ 2 < (n^2 + 3 * n + 1) ^ 2 := by
    nlinarith [h1, sq_nonneg (x - n^2 - 3 * n), sq_nonneg (n + 1), sq_nonneg (n - 1), sq_nonneg (x - n^2 - 3 * n - 1), sq_pos_of_ne_zero (show n ≠ 0 by exact hn), sq_nonneg (n + 3)]
  have h4 : x > n^2 + 3 * n := by
    have h5 : x ^ 2 > (n^2 + 3 * n) ^ 2 := h2
    nlinarith [sq_nonneg (x - (n^2 + 3 * n))]
  have h7 : x < n^2 + 3 * n + 1 := by
    have h8 : x ^ 2 < (n^2 + 3 * n + 1) ^ 2 := h3
    nlinarith [sq_nonneg (x - (n^2 + 3 * n + 1))]
  omega