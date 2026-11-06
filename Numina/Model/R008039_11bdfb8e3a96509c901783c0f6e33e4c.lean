import Mathlib

theorem calculus_22746 {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.det A = 4) (hB : Matrix.det B = -5) :
    Matrix.det (A * B) = -20 := by
  rw [Matrix.det_mul]
  rw [hA, hB]
  all_goals norm_num