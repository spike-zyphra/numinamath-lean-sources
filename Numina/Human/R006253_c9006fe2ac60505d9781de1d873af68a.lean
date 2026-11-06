import Mathlib

/- Let $k$ and $n$ be positive integers. Given that $3^k \equiv 1 \pmod{1000}$, determine the last three digits of $3^{kn}$. Show the answer is $001$. -/
theorem number_theory_635173 (k n : ℕ) (hk : 0 < k) (hn : 0 < n) (h : 3 ^ k ≡ 1 [MOD 1000]) :
    3 ^ (k * n) % 1000 = 001 := by
  simp only [Nat.ModEq, Nat.one_mod] at h
  -- 3 ^ (k * n) = (3 ^ k) ^ n ≡ 1 ^ n ≡ 1 [MOD 1000]
  rw [pow_mul, Nat.pow_mod, h, Nat.one_pow, Nat.one_mod]
