import Mathlib

theorem algebra_17037 {x y : ℕ} (hx : x = Nat.factorization 144 2) (hy : y = Nat.factorization 144 3) :
    (1 / 5 : ℝ) ^ (y - x : ℤ) = 25 := by
  have hx2 : x = 4 := by 
    rw [hx]
    native_decide
  have hy2 : y = 2 := by 
    rw [hy]
    native_decide
  rw [hx2, hy2]
  norm_num