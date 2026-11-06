import Mathlib

theorem algebra_115613 {N : ℕ} (hN : N < 40) (havg : (66 * N + 5 * (N - 65)) / (N + 1) = 71)
    (havg' : (56 * N + 5 * (N - 56)) / (N + 1) = 59) :
    N = 12 ∨ N = 24 ∨ N = 36 := by 
  interval_cases N <;> norm_num at havg havg' <;> tauto