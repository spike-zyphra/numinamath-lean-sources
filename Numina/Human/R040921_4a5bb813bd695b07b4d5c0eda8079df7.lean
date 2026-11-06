import Mathlib

/-- 51. $a, b$ and $n$ are fixed natural numbers. It is known that for any natural $k (k \neq b)$,
the number $a-k^{n}$ is divisible without remainder by $b-k$. Prove that $a=b^{n}$. -/
theorem number_theory_276366 (a b : ℤ) (n : ℕ) (ha : a > 0) (hb : b > 0) (hn : n > 0) (h : ∀ k, k ≠ b → (b-k) ∣ (a - k^n)) :
    a = b^n := by
  -- Since k^n - b^n = (k-b) (k^(n-1) + k^(n-2) b + ... + b^(n-1)),
  -- k^n - b^n is divisible by b-k.
  have : ∀ k, k ≠ b → b - k ∣ k^n - b^n := by
    intro k ne
    rw[← neg_dvd, neg_sub]
    apply sub_dvd_pow_sub_pow
  -- Thus, a - b^n =
  have : ∀ k, k ≠ b → b - k ∣ a - b^n := by
    intro k ne
    -- (a-k^n) + (k^n-b^n) is divisble by b-k for any k ≠ b.
    convert_to _ ∣ (a - k^n) + (k^n - b^n)
    · ring
    apply dvd_add
    · exact h _ ne
    · exact this _ ne
  -- but this can only be true when a = b^n:
  have : a - b^n = 0 := by
    -- If a - b^n ≠ 0,
    by_contra! neq
    apply neq
    -- a-b^n must be divisble by b-(b-2|a-b^n|) = 2|a^b-n|, since b-|a-b^n| ≠ b.
    apply Int.eq_zero_of_abs_lt_dvd (m := 2 * |a-b^n|) ?h1 (lt_two_mul_self $ abs_pos.mpr neq)
    have ne : b - 2 * |a - b ^ n| ≠ b := by
      intro h
      rw[sub_eq_self] at h
      have : |a - b^n| > 0 := by simp[neq]
      omega
    -- Hence a-b^n = 0, contradiction.
    specialize this (b - 2 * |a - b ^ n|) ne
    convert this using 1
    · ring
  linarith