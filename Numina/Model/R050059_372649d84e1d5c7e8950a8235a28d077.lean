import Mathlib

theorem algebra_249838 {M H : ℕ} (hM : M > 0) (hH : H > 0)
    (h1 : 15 * H = M * 2 + 45 * M) (h2 : 45 * H = M * 5 + 5 * H) :
    M = 40 ∧ H = 50 := by 
  omega