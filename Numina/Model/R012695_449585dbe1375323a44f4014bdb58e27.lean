import Mathlib
open Real

theorem algebra_2935 {n : ℕ} {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A = !![cos x, -sin x; sin x, cos x]) :
    A ^ n = !![cos (n * x), -sin (n * x); sin (n * x), cos (n * x)] := by

  have h1 : ∀ n : ℕ, A ^ n = !![cos (n * x), -sin (n * x); sin (n * x), cos (n * x)] := by 
    intro n 
    induction n with 
    | zero =>
      rw [hA]
      simp [pow_zero]
      all_goals
        ext i j 
        fin_cases i <;> fin_cases j <;> simp [cos_zero, sin_zero]
        all_goals norm_num
    | succ n ih =>
      simp [pow_succ, ih]
      simp [hA, Matrix.mul_apply, Matrix.ext_iff]
      funext i j 
      fin_cases i <;> fin_cases j <;> simp [cos_add, sin_add, mul_add, add_mul]
      <;> ring
  exact h1 n