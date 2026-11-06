import Mathlib


/-Let $m$ be a positive integer. Let $a$ be an integer such that $a$ and $m$ are coprime. Let $N$ and $k$ be positive integers such that $k$ divides $N$. If the order of $a$ modulo $m$ is $N$, show that the order of $a^k$ modulo $m$ is $N/k$.-/
theorem order_of_pow_is_div
  (m : ℕ)
  (hm : 0 < m)
  (a : ℤ)
  (ha : a.natAbs.Coprime m)
  (N k : ℕ)
  (hN : 0 < N)
  (hk : 0 < k)
  (hkN : k ∣ N)
  (h_order_a : orderOf (a : ZMod m) = N) :
  orderOf ((a : ZMod m) ^ k) = N / k :=
by
  -- The theorem `orderOf_pow` gives a direct formula for the order of an element raised to a power.
  -- The formula is: `orderOf (x ^ k) = orderOf x / Nat.gcd (orderOf x) k`.
  -- This theorem is applicable because `ZMod m` forms a finite monoid, and `a` is a unit.
  calc
    orderOf ((a : ZMod m) ^ k)
    -- Apply the `orderOf_pow` theorem.
    = orderOf (a : ZMod m) / Nat.gcd (orderOf (a : ZMod m)) k := by exact orderOf_pow' (a : ZMod m) (by omega)
    -- Substitute `h_order_a`, which states `orderOf (a : ZMod m) = N`.
    _ = N / Nat.gcd N k := by rw [h_order_a]
    -- Since `k` divides `N` (`hkN`), their greatest common divisor is `k` itself.
    -- We use the `Nat.gcd_eq_right_of_dvd` lemma, which states `gcd(n,k) = k` if `k ∣ n`.
    _ = N / k := by rw [Nat.gcd_eq_right hkN]
    