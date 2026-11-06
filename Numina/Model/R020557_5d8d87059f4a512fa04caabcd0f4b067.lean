import Mathlib

open Real

theorem calculus_158618 (a : ℝ) (ha : a > 0) (f : ℝ → ℝ) (hf : f = fun x => a^(3*x)) :
    ∀ n, iteratedDeriv n f = fun x => (a^(3*x))*3^n * (log a)^n := by
  intro n
  induction n with
  | zero =>
    simp [hf, iteratedDeriv_zero]
  | succ n ih =>
    have eq2 : iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f) := by
      simp [iteratedDeriv_succ]
    rw [eq2, ih]
    funext x
    simp [deriv_mul, mul_comm, mul_assoc, Real.rpow_def_of_pos ha, mul_assoc, mul_comm, mul_assoc]
    all_goals
      ring_nf