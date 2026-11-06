import Mathlib

theorem algebra_20095 {P Q : ℝ → ℝ} (hP : P = fun x => 4 * x ^ 3 - 2 * x ^ 2 + 7 * x - 1)
    (hQ : Q = fun x => (P x) ^ 2) :
    Q 0 = 1 := by
  rw [hQ]
  rw [hP]
  norm_num