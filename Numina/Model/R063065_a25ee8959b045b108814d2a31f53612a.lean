import Mathlib

theorem calculus_17260 {M : Matrix (Fin 2) (Fin 2) ℝ} (hMN : Matrix.det M = -2) :
    Matrix.det (M ^ 4) = 16 := by
  have h1 : Matrix.det (M ^ 4) = (Matrix.det M) ^ 4 := by
    simp [Matrix.det_pow]
  rw [h1, hMN]
  norm_num