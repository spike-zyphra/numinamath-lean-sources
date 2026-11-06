import Mathlib

open Real

theorem calculus_139605 (y : ℝ → ℝ) (hy : y = fun x => 2^(3 * x + 5)) (n : ℕ) :
    iteratedDeriv n y = fun x => 2^(3 * x + 5) * 3^n * (log 2)^n := by 
  rw [hy]
  have eq : ∀ (n : ℕ), iteratedDeriv n (fun (x : ℝ) => (2 : ℝ) ^ (3 * x + 5)) = fun x => (2 : ℝ) ^ (3 * x + 5) * 3 ^ n * (log 2) ^ n := by
    intro n 
    induction n with
    | zero =>
      funext x 
      simp [iteratedDeriv_zero]
      <;> norm_num
    | succ n ih =>
      have eq1 : iteratedDeriv (n + 1) (fun (x : ℝ) => (2 : ℝ) ^ (3 * x + 5)) = deriv (iteratedDeriv n (fun (x : ℝ) => (2 : ℝ) ^ (3 * x + 5))) := by 
        simp [iteratedDeriv_succ]
      rw [eq1, ih]
      funext x
      simp [deriv_mul, deriv_pow, deriv_id'', mul_comm]
      <;> field_simp [Real.rpow_def_of_pos, mul_add, add_mul, Real.rpow_pos_of_pos]
      <;> ring
      all_goals 
        field_simp [Real.rpow_def_of_pos, mul_comm]
        <;> ring
  exact eq n