import Mathlib
/- Let $b$ be a positive integer, $n$ and $m$ be positive natural numbers, and $c$ and $d$ be positive integers. An integer $a > 0$ has the property that for any integer $k$ such that $k \neq b$, the expression $b-k$ divides $a-(ck^n + dk^m)$. Determine the value of $a$ in terms of $b, c, d, n, m$. Show that $a = cb^n + db^m$. -/
theorem algebra_638078 (a b c d n m : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (hn : n > 0) (hm : m > 0) (h : ∀ k : ℤ, k ≠ b → (b - k) ∣ a - (c * k ^ n + d * k ^ m)) : a = c * b ^ n + d * b ^ m:= by
  -- Transform the hypothesis to work with integer arithmetic
  -- Replace the original divisibility condition with a modular equivalence
  replace h : ∀ k : ℤ, k ≠ ↑b → ↑b - k ∣ ↑a - (↑c * b ^ n + ↑d * b ^ m):= by
    intro k hk
    specialize h k hk
    -- Show that a is congruent to c*b^n + d*b^m modulo (b-k)
    suffices a ≡ c * b ^ n + d * b ^ m [ZMOD b - k] by exact Int.ModEq.dvd (id (Int.ModEq.symm this))
    -- Convert divisibility to modular equivalence
    replace h : a ≡ c * k ^ n + d * k ^ m [ZMOD b - k]:= by exact Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) h)
    -- Show that k is congruent to b modulo (b-k)
    have g1 : k ≡ b [ZMOD b - k]:= by
      suffices b - k ∣ b - k by exact Int.ModEq.symm (Int.modEq_sub (↑b) k)
      simp
    -- Use the congruence to show k^n ≡ b^n [ZMOD b-k]
    have g2 : k ^ n ≡ b ^ n [ZMOD b - k]:= by exact Int.ModEq.pow n g1
    -- Similarly, k^m ≡ b^m [ZMOD b-k]
    replace g1:= Int.ModEq.pow m g1
    -- Multiply both sides by c: c*k^n ≡ c*b^n [ZMOD b-k]
    replace g2 : c * k ^ n ≡ c * b ^ n [ZMOD b - k]:= by exact Int.ModEq.mul_left (↑c) g2
    -- Multiply both sides by d: d*k^m ≡ d*b^m [ZMOD b-k]
    replace g1 : d * k ^ m ≡ d * b ^ m [ZMOD b - k]:= by exact Int.ModEq.mul_left (↑d) g1
    -- Add the congruences: c*k^n + d*k^m ≡ c*b^n + d*b^m [ZMOD b-k]
    replace g1:= Int.ModEq.add g2 g1
    -- Transitivity gives us the desired result
    exact Int.ModEq.trans h g1
  -- Convert natural numbers to integers for the rest of the proof
  zify
  -- Define t as the difference between a and the target expression
  set t:= (↑a : ℤ) - (↑c * ↑b ^ n + ↑d * ↑b ^ m) with ht
  clear_value t
  -- Show that t = 0, which implies a = c*b^n + d*b^m
  suffices t = 0 by linarith
  -- Proof by contradiction: assume t ≠ 0
  by_contra H
  -- Convert to natural number absolute value
  replace H : t.natAbs ≠ 0:= by exact Int.natAbs_ne_zero.mpr H
  -- Choose a specific value for k to get a contradiction
  specialize h (b - t.natAbs - 1) ?_
  .
    -- Show that the chosen k is not equal to b
    by_contra H1
    replace H1 : t.natAbs + 1 = 0:= by
      zify
      linarith
    omega
  .
    -- Simplify the expression and show that 1 + t.natAbs divides t.natAbs
    ring_nf at h
    replace h : 1 + t.natAbs ∣ t.natAbs:= by
      zify
      simp at h
      exact (dvd_abs (1 + |t|) t).mpr h
    -- This leads to a contradiction since t.natAbs > 0
    apply Nat.le_of_dvd (by omega) at h
    omega
