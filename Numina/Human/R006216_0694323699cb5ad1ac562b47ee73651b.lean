import Mathlib

/- Lemma 1: For $a > 1$, we have $a^c - 1 \equiv a^{c \mod b} - 1 \pmod{a^b - 1}$. -/
lemma pow_sub_one_mod_pow_sub_one (a b c : ℕ) (ha1 : 1 < a) : (a ^ c - 1) % (a ^ b - 1) = a ^ (c % b) - 1 := by
  have ha0 : 0 < a := Nat.zero_lt_of_lt ha1
  -- We first consider the case where `b = 0`.
  rcases eq_zero_or_pos b with rfl | hb0
  · simp
  -- Let's consider whether `c < b` or `c ≥ b`.
  rcases lt_or_le c b with h | h
  · -- If c < b, then a ^ c - 1 < a ^ b - 1, so the result is trivial.
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt h]
    rwa [Nat.sub_lt_sub_iff_right (Nat.one_le_pow c a ha0), Nat.pow_lt_pow_iff_right ha1]
  · -- If c ≥ b, then we rewrite a ^ c - 1 as a ^ (c - b) * (a ^ b - 1) + (a ^ (c - b) - 1).
    suffices a ^ (c - b + b) - 1 = a ^ (c - b) * (a ^ b - 1) + (a ^ (c - b) - 1) by
      rw [← Nat.sub_add_cancel h, Nat.add_mod_right, this, Nat.add_mod, Nat.mul_mod, Nat.mod_self,
        Nat.mul_zero, Nat.zero_mod, Nat.zero_add, Nat.mod_mod, pow_sub_one_mod_pow_sub_one _ _ _ ha1] -- -- We use recursion on the lemma itself. The recursion terminates because `c - b < c`.
    rw [← Nat.add_sub_assoc (Nat.one_le_pow (c - b) a ha0), ← Nat.mul_add_one, Nat.pow_add,
      Nat.sub_add_cancel (Nat.one_le_pow b a ha0)]

/- Lemma 2: For $a > 1$, we have $\gcd(a^b - 1, a^c - 1) = a^{\gcd(b, c)} - 1$. -/
lemma pow_sub_one_gcd_pow_sub_one (a b c : ℕ) (ha1 : 1 < a) :
    Nat.gcd (a ^ b - 1) (a ^ c - 1) = a ^ Nat.gcd b c - 1 := by
  -- Let's just use the same technique as in the Euclidean algorithm.
  -- First, we consider the case where `b = 0`.
  rcases eq_zero_or_pos b with rfl | hb
  · simp
  -- If `b > 0`, then we use the recursion on the Euclidean algorithm.
  -- The recursion terminates because `c % b < b`.
  replace hb : c % b < b := Nat.mod_lt c hb
  rw [Nat.gcd_rec, pow_sub_one_mod_pow_sub_one _ _ _ ha1, pow_sub_one_gcd_pow_sub_one _ _ _ ha1, ← Nat.gcd_rec]

/- Let $a$ be a natural number greater than 1. For strictly positive natural numbers $m$ and $n$, show that the greatest common divisor of $a^m-1$ and $a^n-1$ is equal to $a^{\operatorname{GCD}(m,n)}-1$. -/
theorem number_theory_634717 (a m n : ℕ) (ha : 1 < a) (hm : 0 < m) (hn : 0 < n) :
    Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1 := by
  -- We apply the lemma.
  exact pow_sub_one_gcd_pow_sub_one a m n ha
