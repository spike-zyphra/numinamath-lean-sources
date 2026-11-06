import Mathlib

theorem algebra_117963 :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A ≠ 1 ∧ B ≠ 1 ∧ A * B = 1 := by
  use !![2, 0; 0, 3], !![1 / 2, 0; 0, 1 / 3]
  constructor
  · -- Show A ≠ 1
    intro h
    have h1 := congr_arg (fun M => M 0 0) h
    simp [Matrix.of_apply, Matrix.one_fin_two] at h1
    all_goals norm_num at h1
  constructor
  · -- Show B ≠ 1
    intro h
    have h1 := congr_arg (fun M => M 0 0) h
    simp [Matrix.of_apply, Matrix.one_fin_two] at h1
    all_goals norm_num at h1
  · -- Show A * B = 1
    simp [Matrix.mul_apply, Matrix.of_apply, Matrix.one_fin_two]
    all_goals norm_num