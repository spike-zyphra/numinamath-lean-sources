import Mathlib

theorem algebra_137690 {N : ℕ} (hN : N < 40) (havg : (N * 66 + 5 * N) / (N + 5 * N) = 67)
    (havg' : (N * 71 + 5 * N) / (N + 5 * N) = 75) (havg'' : (N * 56 + 5 * N) / (N + 5 * N) = 59) :
    N = 12 ∨ N = 24 ∨ N = 36 := by
  interval_cases N <;> omega