import Mathlib

/- Example 5 The Fibonacci sequence is defined as follows: $F_{1}=F_{2}=1, F_{n+2}=F_{n+1}+F_{n}, n=1$, $2, \cdots$ Prove: For any positive integers $m$ and $n$, we have $\left(F_{m}, F_{n}\right)=F_{(m, n)}$. -/
theorem number_theory_7857 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : (Nat.fib m).gcd (Nat.fib n) = Nat.fib (m.gcd n) := by
  clear hm hn
  -- Let's use induction on the gcd
  -- To prove P(x, y) for all x, y : ℕ, it suffices to prove:
  -- 1. P(0, n) holds for all n : ℕ
  -- 2. Assuming P(n % m, m) holds for some positive m, we have P(m, n)
  induction m, n using Nat.gcd.induction with
  | H0 => simp -- Trivial case
  | H1 m n _ h' =>
    -- Use the definition of gcd
    rw [← Nat.gcd_rec m n] at h'
    -- Write n as m * (n / m) + n % m
    conv_lhs => rw [← Nat.mod_add_div' n m]
    -- Use the induction hypothesis with the lemma `Nat.gcd_fib_add_mul_self`, which states that `(Nat.fib m).gcd (Nat.fib (n + k * m)) = (Nat.fib m).gcd (Nat.fib n)`
    rwa [Nat.gcd_fib_add_mul_self m (n % m) (n / m), Nat.gcd_comm (Nat.fib m) _]
