import Mathlib

open Real

theorem calculus_158283 (k : ℝ) (y : ℝ → ℝ) (hy : y = fun x => 2 ^ (k * x)) (n : ℕ) :
    iteratedDeriv n y = fun x => 2 ^ (k * x) * k ^ n * (log 2) ^ n := by
  rw [hy]
  have h1 : ∀ (n : ℕ), iteratedDeriv n (fun x : ℝ => (2 : ℝ) ^ (k * x)) =
      fun x => (2 : ℝ) ^ (k * x) * k ^ n * (log 2) ^ n := by
    intro n
    induction n with
    | zero =>
      funext x
      simp
    | succ n ih =>
      have eq2 : iteratedDeriv (Nat.succ n) (fun x : ℝ => (2 : ℝ) ^ (k * x)) =
          deriv (iteratedDeriv n (fun x : ℝ => (2 : ℝ) ^ (k * x)))
        := by simp [iteratedDeriv_succ]
      rw [eq2, ih]
      funext x
      simp [deriv_mul, deriv_pow, mul_comm, mul_assoc, Real.rpow_def_of_pos, mul_add, add_mul]
      all_goals
        field_simp [Real.rpow_def_of_pos, mul_comm]
        all_goals
          ring_nf
  apply h1 n