import Mathlib

/- Given that $p$ and $q$ are both prime numbers, and there exist two positive integers $m$ and $n$ such that $p=m+n$ and $q=mn$, then the value of $\frac{{{p}^{p}}+{{q}^{q}}}{{{m}^{n}}+{{n}^{m}}}$ is ___          ___ . -/
theorem number_theory_627675 (p q m n : ℕ)
    (hp₁ : Nat.Prime p) (hq₂ : Nat.Prime q)
    (hp₂ : p = m + n) (hq₃ : q = m * n) :
    (p ^ p + q ^ q) / (m ^ n + n ^ m : ℚ) = 31 / 3 := by
  -- We substitute `p` and `q` with their expressions in terms of `m` and `n`.
  subst p q
  -- Since `m * n` is prime, we have `m = 1` or `n = 1` and the other is prime.
  rw [Nat.prime_mul_iff] at hq₂
  -- We consider the two cases.
  rcases hq₂ with ⟨h₁, rfl⟩ | ⟨h₁, rfl⟩
  . -- If `n = 1`, then `m` and `m + 1` are both prime.
    -- But one of them is even
    obtain hm | hm : Even m ∨ Even (m + 1) := Nat.even_mul.mp (Nat.even_mul_succ_self m)
    -- We clearly have `m = 2`.
    . obtain rfl : m = 2 := (Nat.Prime.even_iff h₁).mp hm
      norm_num
    . obtain hm₂ : m + 1 = 2 := (Nat.Prime.even_iff hp₁).mp hm
      obtain rfl : m = 1 := by omega
      norm_num at h₁
  . -- The same argument works for `m = 1`.
    rw [add_comm] at hp₁
    obtain hn | hn : Even n ∨ Even (n + 1) := Nat.even_mul.mp (Nat.even_mul_succ_self n)
    . obtain rfl : n = 2 := (Nat.Prime.even_iff h₁).mp hn
      norm_num
    . obtain hn₂ : n + 1 = 2 := (Nat.Prime.even_iff hp₁).mp hn
      obtain rfl : n = 1 := by omega
      norm_num at h₁
