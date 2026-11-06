import Mathlib

/- Show that if \( u_{n+1} \) and \( u_{n+2} \) are consecutive terms of the Fibonacci sequence, then the Euclidean algorithm requires exactly \( n \) divisions to demonstrate that the greatest common divisor \( (u_{n+1}, u_{n+2}) = 1 \).-/
theorem number_theory_4532 {u : ℕ → ℕ} (hu0 : u 0 = 1) (hu1 : u 1 = 1)
    (hun : ∀ n, u (n + 2) = u (n + 1) + u n) (n : ℕ) :
    Nat.gcd (u (n + 1)) (u n) = 1 := by
  -- use mathematical induction
  induction' n with n ih
  -- check the base case
  . simp [hu1, hu0]
  -- use the fact that `gcd(u_{n+1}, u_n+u_{n+1})` = `gcd(u_{n+1}, u_n)`
  -- and induction hypothesis. It's easy to draw a conlusion.
  . rw [show n+1+1=n+2 by omega, hun, Nat.gcd_comm, Nat.add_comm (u (n + 1)),
    Nat.gcd_add_self_right (u (n + 1)) (u n), ih]
