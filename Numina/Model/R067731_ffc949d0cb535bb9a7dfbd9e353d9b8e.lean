import Mathlib

open Real

theorem calculus_165701 {y : ℝ → ℝ} (hy : y = fun x => exp (2 * x)) :
    ∀ x, iteratedDeriv 3 y x - 8 * y x = 0 := by
  intro x
  have h_eq : ∀ n, iteratedDeriv n y = fun x => (2^(n : ℕ)) * exp (2 * x) := by
    intro n
    induction n with 
    | zero =>
      simp [hy]
      <;> ring
    | succ n ih =>
      have eq1 : iteratedDeriv (n + 1) y = deriv (iteratedDeriv n y) := by
        simp [iteratedDeriv_succ]
      rw [eq1]
      rw [ih]
      funext x
      simp [deriv_mul, deriv_id'', mul_comm]
      <;> ring_nf <;> simp [exp_ne_zero]
      <;> ring
  have h3 : iteratedDeriv 3 y x = 8 * exp (2 * x) := by
    rw [h_eq 3]
    simp
    <;> ring_nf
  have hy_x : y x = exp (2 * x) := by 
    rw [hy]
  rw [h3, hy_x]
  <;> ring_nf <;> simp [exp_ne_zero]
  <;> ring