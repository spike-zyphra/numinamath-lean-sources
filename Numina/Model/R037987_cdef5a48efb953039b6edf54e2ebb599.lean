import Mathlib

open Real

theorem calculus_158942 {y : ℝ → ℝ} (hy : y = fun x => (exp (2 * x + 1)) ^ ((1 : ℝ) / 3)) (n : ℕ) :
    iteratedDeriv n y = fun x => (2 / 3) ^ n * (exp (2 * x + 1)) ^ ((1 : ℝ) / 3) := by 
  rw [hy]
  have eq1 : ∀ (n : ℕ), (iteratedDeriv n (fun (x : ℝ) => (exp (2 * x + 1)) ^ ((1 : ℝ) / 3)) ) 
              = fun x => (2 / 3) ^ n * ((exp (2 * x + 1)) ^ ((1 : ℝ) / 3)) := by 
    intro n
    induction n with
    | zero =>
      funext x
      all_goals simp
      <;> ring_nf
      <;> norm_num
      <;> norm_num
    | succ k ih =>
      have eq2 : iteratedDeriv (k + 1) (fun (x : ℝ) => (exp (2 * x + 1)) ^ ((1 : ℝ) / 3)) 
                = deriv (iteratedDeriv k (fun (x : ℝ) => (exp (2 * x + 1)) ^ ((1 : ℝ) / 3)) ) := by 
        simp [iteratedDeriv_succ]
      rw [eq2]
      rw [ih]
      funext x
      simp [deriv_const_mul, deriv_pow, deriv_id'', mul_comm, mul_assoc, add_assoc]
      <;> ring_nf
      <;> simp [exp_mul, Real.rpow_def_of_pos, mul_add, add_mul, mul_assoc, exp_ne_zero]
      <;> ring_nf
      <;> field_simp [exp_mul, Real.rpow_def_of_pos, mul_add, add_mul, mul_assoc, exp_ne_zero]
      <;> ring_nf
      <;> norm_num
      <;> field_simp [exp_mul, Real.rpow_def_of_pos, mul_add, add_mul, mul_assoc, exp_ne_zero]
      <;> ring_nf
      <;> norm_num
      all_goals try {field_simp}
      all_goals try {norm_num}
      all_goals try {linarith}
  apply eq1 n
  all_goals try {linarith}