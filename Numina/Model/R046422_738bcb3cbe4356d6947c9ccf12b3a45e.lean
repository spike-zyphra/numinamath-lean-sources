import Mathlib

open Matrix Real

theorem calculus_16136 {a d : ℝ} (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A = !![a, 1; -2, d]) (hA' : A + A⁻¹ = 0) :
    A.det = 1 := by
  have h1 := congr_arg (fun X => X 0 0) hA'
  have h2 := congr_arg (fun X => X 0 1) hA'
  have h3 := congr_arg (fun X => X 1 0) hA'
  have h4 := congr_arg (fun X => X 1 1) hA'
  simp [hA, Matrix.inv, Matrix.det_fin_two, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at h1 h2 h3 h4
  have h5 : a * d = -1 := by
    have eq1 := h2
    have eq2 := h3
    field_simp [(show a * d + 2 ≠ 0 by
      by_contra h
      have h6 : a * d + 2 = 0 := by linarith
      rw [h6] at eq1 eq2
      norm_num at eq1 eq2
      all_goals nlinarith
    )] at eq1 eq2
    nlinarith
  rw [hA]
  simp [Matrix.det_fin_two]
  nlinarith [h5]