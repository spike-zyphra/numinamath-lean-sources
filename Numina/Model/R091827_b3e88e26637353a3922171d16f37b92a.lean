import Mathlib

theorem algebra_132239 {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : A.det ≠ 0)
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B = fun i j => A.adjugate i j)
    (hAB : ∀ i j, A i j ≠ 0 → B i j ≠ 0) :
    (B.det = A.det ^ 3) := by
  rw [hB]
  simp [Matrix.det_adjugate]
  all_goals tauto