import Mathlib

theorem number_theory_269994 (M N : ℕ) (hM : M < 10) (hN : N < 10)
    (h : (100 * M + 10 * N + 1) - (10 * M + N) = 13) :
    M + N = 13 := by
  have h1 : 100 * M + 10 * N + 1 ≥ 10 * M + N := by
    omega
  have h2 : (100 * M + 10 * N + 1) = (10 * M + N) + 13 := by
    omega
  have h3 : 90 * M + 9 * N = 12 := by
    omega
  omega