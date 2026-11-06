import Mathlib

open Real
open scoped BigOperators

theorem algebra_122278 (A B C : EuclideanSpace ℝ (Fin 3))
  (hA : A = ![ -4, 0, 4 ])
  (hB : B = ![ -1, 6, 7 ])
  (hC : C = ![ 1, 10, 9 ]) :
  cos (arccos ((inner (B - A) (C - A)) / (dist A B * dist A C))) = 1 := by
  rw [hA, hB, hC]
  simp [dist_eq_norm, EuclideanSpace.norm_eq, inner, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have h1 : √54 * √150 = 90 := by 
    calc 
      √54 * √150 = √(54 * 150 : ℝ) := by rw [Real.sqrt_mul (by norm_num)]
      _ = √(8100 : ℝ) := by norm_num 
      _ = √(81 * 100 : ℝ) := by norm_num 
      _ = √81 * √100 := by rw [Real.sqrt_mul (by norm_num)]
      _ = (9 : ℝ) * (10 : ℝ) := by 
        have h13 : √81 = (9 : ℝ) := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        have h14 : √100 = (10 : ℝ) := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        rw [h13, h14] 
      _ = (90 : ℝ) := by norm_num 
  have ha : ( ((-1 + 4 : ℝ) * (1 + 4) + 6 * 10 + (7 - 4) * (9 - 4)) / (√((-4 + 1) ^ 2 + 6 ^ 2 + (4 - 7) ^ 2) * √((-4 - 1) ^ 2 + 10 ^ 2 + (4 - 9) ^ 2)) ) = (1 : ℝ) := by 
    have hb_eq : ( (-1 + 4 : ℝ) * (1 + 4) + 6 * 10 + (7 - 4) * (9 - 4) ) = 90 := by norm_num 
    have hc_eq : √((-4 + 1) ^ 2 + 6 ^ 2 + (4 - 7) ^ 2) = √54 := by 
      norm_num 
    have hd_eq : √((-4 - 1) ^ 2 + 10 ^ 2 + (4 - 9) ^ 2) = √150 := by 
      norm_num 
    rw [hb_eq, hc_eq, hd_eq] 
    rw [show √54 * √150 = 90 by linarith [h1]]
    all_goals norm_num 
  rw [ha] 
  have ha1 : cos (arccos (1 : ℝ)) = 1 := by 
    rw [cos_arccos] 
    all_goals norm_num 
  simpa using ha1