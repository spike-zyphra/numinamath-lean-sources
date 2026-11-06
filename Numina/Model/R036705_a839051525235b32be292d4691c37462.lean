import Mathlib


open Real


theorem calculus_124803 {f : ℝ → ℝ} (hf : f = fun x => (exp (7 * x - 1)) ^ ((1 : ℝ) / 5)) (n : ℕ) :
    iteratedDeriv n f = fun x => (7 / 5) ^ n * (exp (7 * x - 1)) ^ ((1 : ℝ) / 5) := by

  have h1 : ∀ (n : ℕ), iteratedDeriv n f = fun x => (7 / 5 : ℝ) ^ n * (exp (7 * x - 1)) ^ ((1 : ℝ) / 5) := by
    intro n
    induction n with
    | zero =>
      funext x
      simp [hf]
    | succ n ih =>
      have eq1 : iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f) := by
        simp [iteratedDeriv_succ]
      rw [eq1, ih]
      funext x
      simp [deriv_const_mul, deriv_pow, deriv_mul, deriv_id'', mul_comm]
      all_goals
        try field_simp [Real.rpow_def_of_pos, mul_pos, Real.exp_pos]
        <;> ring_nf <;> field_simp [Real.rpow_def_of_pos, mul_pos, Real.exp_pos]

  specialize h1 n
  simpa using h1