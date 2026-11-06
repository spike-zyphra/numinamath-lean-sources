import Mathlib

theorem calculus_162175 (y : ℝ → ℝ) (hy : y = fun x => x^2 + 3 * x + 2) :
    iteratedDeriv 3 y = 0 := by
  have eq6 : deriv y = fun x => 2 * x + 3 := by
    rw [hy]
    funext x
    simp [deriv_pow, deriv_const, deriv_add, deriv_mul, mul_comm]
    all_goals ring
  have eq7 : deriv (deriv y) = fun x => (2 : ℝ) := by
    rw [eq6]
    funext x 
    simp [deriv_pow, deriv_const, deriv_add, deriv_mul, mul_comm]
    all_goals ring
  have eq8 : deriv (deriv (deriv y)) = fun x => (0 : ℝ) := by
    rw [eq7]
    funext x
    simp [deriv_pow, deriv_const, deriv_add, deriv_mul, mul_comm]
  have eq9 : iteratedDeriv 3 y = deriv (deriv (deriv y)) := by
    simp [iteratedDeriv_succ, eq6, eq7]
  rw [eq9]
  exact_mod_cast eq8