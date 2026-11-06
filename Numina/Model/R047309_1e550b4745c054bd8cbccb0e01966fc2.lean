import Mathlib

theorem algebra_249570 (M W : ℕ) (hM : M > 0) (hW : W > 0)
    (hM1 : M * 3 = W * 2) (hM2 : M * 37 + W * 42 = (M + W) * x) :
    x = 40 := by
  nlinarith [hM1, hM2, mul_pos hM (show 0 < 1 by omega), mul_pos hW (show 0 < 1 by omega)]