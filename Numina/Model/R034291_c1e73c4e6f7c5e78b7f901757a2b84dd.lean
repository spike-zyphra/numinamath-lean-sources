import Mathlib

open Matrix

theorem calculus_12687 {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A = !![-1, 2; 3, 4]) :
    {x : ℝ × ℝ | A ^ 6 = x.1 • A + x.2 • 1} = {(2223, 4510)} := by
  ext ⟨p, q⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Forward direction: if (p, q) satisfies the equation, then (p, q) = (2223, 4510)
    rintro h
    rw [hA] at h
    simp [pow_succ, Matrix.mul_apply, Matrix.of_apply, Matrix.one_fin_two] at h
    have eq1 := congr_arg (fun x => x 0 0) h
    have eq2 := congr_arg (fun x => x 0 1) h
    have eq3 := congr_arg (fun x => x 1 0) h
    have eq4 := congr_arg (fun x => x 1 1) h
    norm_num [Fin.sum_univ_succ, Fin.sum_univ_zero] at eq1 eq2 eq3 eq4 
    have eq1' : p = 2223 := by 
      linarith 
    have eq1q : q = 4510 := by 
      linarith 
    simp [eq1', eq1q]
  · -- Backward direction: (2223, 4510) satisfies the equation
    rintro hpq 
    rcases hpq with ⟨rfl, rfl⟩
    rw [hA]
    simp [pow_succ, Matrix.mul_apply, Matrix.of_apply, Matrix.one_fin_two]
    all_goals norm_num [Fin.sum_univ_succ, Fin.sum_univ_zero]