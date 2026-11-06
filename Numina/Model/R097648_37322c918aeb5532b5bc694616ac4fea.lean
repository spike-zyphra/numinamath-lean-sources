import Mathlib

theorem calculus_22908 {x y z : ℝ} (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A = !![1, x; y, -9/5]) (hB : B = !![12/5, 1/10; 5, z])
    (hAB : A + B = A * B) : x + y + z = 56/5 := by
  rw [hA, hB] at hAB
  have eq1 := congr_arg (fun M => M 0 0) hAB
  simp [Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add] at eq1
  norm_num at eq1
  have eq2 := congr_arg (fun M => M 0 1) hAB
  simp [Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add] at eq2
  norm_num at eq2
  have eq3 := congr_arg (fun M => M 1 0) hAB
  simp [Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add] at eq3
  norm_num at eq3
  have eq4 := congr_arg (fun M => M 1 1) hAB
  simp [Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add] at eq4
  norm_num at eq4
  have hx : x = 1/5 := by
    linarith
  have hy : y = 10 := by
    linarith
  have hz : z = 1 := by
    nlinarith [show y = 10 from by linarith]
  linarith [show x = 1/5 from by linarith, show y = 10 from by linarith, show z = 1 from by linarith]