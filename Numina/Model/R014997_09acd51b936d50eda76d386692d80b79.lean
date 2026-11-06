import Mathlib

theorem calculus_22302 {a b d : ℝ} (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M = !![a, b; 0, d]) (hM3 : M^3 = !![8, -57; 0, 27]) :
    M = !![2, -3; 0, 3] := by 
  rw [hM] at hM3
  have eq1 := congr_arg (fun x => x 0 0) hM3
  have eq2 := congr_arg (fun x => x 0 1) hM3
  have eq3 := congr_arg (fun x => x 1 0) hM3
  have eq4 := congr_arg (fun x => x 1 1) hM3
  simp [pow_three, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at eq1 eq2 eq3 eq4
  have ha : a^3 = 8 := by linarith
  have hd : d^3 = 27 := by linarith
  have h1 : a = 2 := by 
    have h2 : a^3 - 8 = 0 := by linarith
    have h3 : (a - 2) * (a^2 + 2 * a + 4) = 0 := by 
      ring_nf at h2 ⊢
      nlinarith
    cases' (mul_eq_zero.1 h3) with h4 h5
    · linarith 
    · -- a^2 + 2 * a + 4 = 0 
      have h6 : a^2 + 2 * a + 4 > 0 := by 
        nlinarith [sq_nonneg (a + 1)]
      nlinarith 
  have h2 : d = 3 := by
    have h7 : d^3 - 27 = 0 := by linarith
    have h8 : (d - 3) * (d^2 + 3 * d + 9) = 0 := by 
      ring_nf at h7 ⊢
      nlinarith
    cases' (mul_eq_zero.1 h8) with h9 h10
    · linarith 
    · -- d^2 + 3 * d + 9 = 0 
      have h11 : d^2 + 3 * d + 9 > 0 := by
        nlinarith [sq_nonneg (d + 3 / 2)]
      nlinarith 
  have h3 : b = -3 := by 
    rw [show a = 2 by linarith, show d = 3 by linarith] at eq2
    nlinarith 
  ext i j 
  fin_cases i <;> fin_cases j <;> simp [hM, h1, h3, h2] <;> norm_num
  all_goals norm_num