import Mathlib

/- Exercise 2. Show that there are infinitely many pairs ( $m, n$ ) of distinct strictly positive integers such that $m!n!$ is a perfect square. -/
theorem number_theory_293532 :
    ∀ N : ℕ, ∃ m n : ℕ,
      m > N ∧ n > N ∧ m ≠ n ∧ IsSquare ((Nat.factorial m) * (Nat.factorial n)) := by
  rintro N
  -- we'll use (N+2)^2 = m and (N+2)^2-1 = n, generally any N + k with k > 1 will work
  use (N+2)^2, (N+2)^2 - 1
  and_intros
  -- first two inequalities are easy to prove
  . simp
    calc
    N ≤ N^2 := by exact Nat.le_self_pow (by norm_num) N
    _ < (N+2)^2 := by gcongr; linarith
  . suffices N + 1 < (N + 2)^2 by omega
    calc
    N + 1 ≤ (N + 1)^2 := by exact Nat.le_self_pow (by norm_num) (N+1)
    _ < (N + 2)^2 := by gcongr; linarith
  -- distinction is also easy to prove, but have to show (N+2)^2 is larger than 1 due to how nat subtraction works
  . by_contra h
    have : 2^2 ≤ (N + 2)^2 := by gcongr; linarith
    omega
  -- finally show the expression is square of (N+2)(((N+2)^2 - 1)!)
  . use (N+2) * (Nat.factorial ((N+2)^2 - 1))
    rw [← Nat.mul_factorial_pred (by simp)]
    ring