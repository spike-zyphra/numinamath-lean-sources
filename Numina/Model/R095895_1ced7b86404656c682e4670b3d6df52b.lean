import Mathlib

theorem algebra_215364 (M N : ℝ) (hMN : M = 1.5 * N) (hM : M > 0) (hN : N > 0)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hA' : A = 1 / 5) (hB' : B = 1 / 5)
    (hC' : C = 1 / 6) (hABC : A * 5 + B * 5 + C * 6 = 1) :
    B * 5 = 15 / 8 := by
  rw [hA'] at hABC
  rw [hB'] at hABC
  rw [hC'] at hABC
  linarith