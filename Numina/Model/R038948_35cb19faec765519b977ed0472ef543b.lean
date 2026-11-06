import Mathlib

open Real

theorem calculus_124551 {f : ℝ → ℝ} (hf : f = fun x => 7^(5*x)) (n : ℕ) :
    iteratedDeriv n f = fun x => 5^n * (log 7)^n * 7^(5*x) := by
  rw [hf]
  have eq1 : ∀ (n : ℕ), iteratedDeriv n (fun (x : ℝ) => (7 : ℝ) ^ (5 * x)) = fun x => 5 ^ n * (log 7) ^ n * (7 : ℝ) ^ (5 * x) := by
    intro n
    induction n with
    | zero =>
      funext x
      simp [iteratedDeriv_zero]
      all_goals norm_num
      all_goals linarith
    | succ n ih =>
      have eq2 : (iteratedDeriv (n + 1) (fun (x : ℝ) => (7 : ℝ) ^ (5 * x))) =
        deriv (iteratedDeriv n (fun (x : ℝ) => (7 : ℝ) ^ (5 * x))) := by
          simp [iteratedDeriv_succ]
          all_goals linarith
      rw [eq2]
      rw [ih]
      funext x
      have h1 : deriv (fun y => (5 : ℝ) ^ n * (log 7 : ℝ) ^ n * (7 : ℝ) ^ (5 * y)) x = (5 : ℝ) ^ (n + 1) * (log 7 : ℝ) ^ (n + 1) * (7 : ℝ) ^ (5 * x) := by
        simp [deriv_const_mul, deriv_pow, deriv_id'', mul_comm]
        all_goals field_simp [Real.rpow_def_of_pos (show (7 : ℝ) > 0 by norm_num), mul_comm]
        all_goals ring_nf
        all_goals field_simp [Real.rpow_def_of_pos (show (7 : ℝ) > 0 by norm_num), mul_comm]
        all_goals ring_nf
        all_goals norm_num
        all_goals field_simp
        all_goals norm_num
        all_goals linarith
      have h2 : (fun y => (5 : ℝ) ^ n * (log 7 : ℝ) ^ n * (7 : ℝ) ^ (5 * y)) = (fun y => (5 : ℝ) ^ n * (log 7 : ℝ) ^ n * (7 : ℝ) ^ (5 * y)) := by rfl
      rw [h1]
      all_goals ring_nf
      all_goals norm_num
      all_goals linarith

  specialize eq1 n
  simpa using eq1