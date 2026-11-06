import Mathlib

open Real

theorem calculus_124002 {y : ℝ → ℝ} (hy : y = fun x => sqrt (exp (3 * x + 1))) (n : ℕ) :
    iteratedDeriv n y = fun x => ((3 / 2) ^ n) * sqrt (exp (3 * x + 1)) := by 
  rw [hy]
  have eq1 : ∀ x : ℝ, sqrt (exp (3 * x + 1)) = exp ((3 * x + 1) / 2) := by
    intro x
    have eq1' : sqrt (exp (3 * x + 1)) = (exp (3 * x + 1)) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    have eq2' : exp ((3 * x + 1) / 2) = (exp (3 * x + 1)) ^ (1 / 2 : ℝ) := by
      have h1 : exp ((3 * x + 1) / 2) = exp ((3 * x + 1) * (1 / 2 : ℝ)) := by 
        ring_nf 
      rw [h1]
      rw [← Real.exp_mul]
      all_goals norm_num 
      all_goals ring 
      all_goals norm_num 
    linarith [eq1', eq2']
  have eq2 : (fun x : ℝ => sqrt (exp (3 * x + 1))) = fun x => exp ((3 * x + 1) / 2) := by 
    funext x 
    exact eq1 x 
  rw [eq2]
  have h1 : ∀ n : ℕ, iteratedDeriv n (fun x : ℝ => exp ((3 * x + 1) / 2)) = 
    fun x => ((3 / 2) ^ n) * exp ((3 * x + 1) / 2) := by
    intro n
    induction n with 
    | zero =>
      funext x
      simp [iteratedDeriv_zero]
    | succ n ih =>
      have eq3 : iteratedDeriv (n + 1) (fun x : ℝ => exp ((3 * x + 1) / 2)) =
        deriv (iteratedDeriv n (fun x : ℝ => exp ((3 * x + 1) / 2)))
        := by 
          simp [iteratedDeriv_succ]
      rw [eq3]
      rw [ih]
      funext x
      simp [deriv_mul, deriv_id'', deriv_const, mul_comm]
      all_goals field_simp 
      all_goals ring_nf 
      all_goals field_simp 
      all_goals ring_nf 
      all_goals norm_num 
      all_goals field_simp 
      all_goals linarith
  rw [h1 n]
  have eq3 : ∀ x : ℝ, exp ((3 * x + 1) / 2) = sqrt (exp (3 * x + 1)) := by 
    intro x 
    linarith [eq1 x] 
  funext x 
  have eq4' : exp ((3 * x + 1) / 2) = sqrt (exp (3 * x + 1)) := by 
    apply eq3 
  simp [eq4']
  all_goals ring_nf 
  all_goals simp [deriv_mul, deriv_id'', mul_comm]
  all_goals field_simp 
  all_goals ring 
  all_goals norm_num 
  all_goals ring_nf 
  all_goals field_simp 
  all_goals ring_nf 
  all_goals norm_num 
  all_goals field_simp 
  all_goals ring_nf 
  all_goals norm_num