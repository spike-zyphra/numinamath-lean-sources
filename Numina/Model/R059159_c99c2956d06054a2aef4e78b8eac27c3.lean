import Mathlib

theorem algebra_21430 {p q : ℝ → ℝ} (hp : p = fun x => 2 - x ^ 2) (hq : q = fun x => 6 / x) :
    p (q 2) = -7 := by 
  rw [hq, hp]
  norm_num