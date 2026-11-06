import Mathlib
open Real

theorem algebra_96057 {u : ℕ → ℤ} (hu1 : u 1 = 5)
(hun : ∀ n, 1≤n → u (n+1) - u n = 3+4*(n-1)):
∀ n, 1≤n → u n = 2*n*n-3*n+6 := by
  intro n hn
  induction n with
  | zero =>
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      rw [hu1]
      norm_num 
    | succ k =>
      have eq1 := hun (k+1) (by omega)
      simp [show k + 1 + 1 = k + 2 by omega] at eq1
      have eq2 : u (k + 2) = u (k+1) + 3 + 4 * (k : ℕ) := by
        omega
      have eq3 := ih (by omega)
      rw [eq2]
      rw [eq3]
      simp [pow_two]
      ring_nf
      all_goals
        omega