import Mathlib

open scoped Nat

/- 15. Given $a_{1}=1, a_{2}=3, a_{n+2}=(n+3) a_{n+1}-(n+2) a_{n}$. If for $m \geqslant n$, the value of $a_{m}$ is always divisible by 9, find the minimum value of $n$.

When $m \geqslant n$, $a_{m}$'s value can be divided by 9, find the smallest $n$. -/
theorem algebra_255980 {a : ℕ → ℤ} (ha1 : a 1 = 1) (ha2 : a 2 = 3)
    (han : ∀ n > 0, a (n + 2) = (n + 3) * a (n + 1) - (n + 2) * a n) :
    IsLeast {n | ∀ m ≥ n, 9 ∣ a m} 5 := by
  -- Show that a(n + 2) = a(n + 1) + (n + 2)! for all n.
  have h n : a (n + 2) = a (n + 1) + (n + 2)! := by
    -- Proof by induction.
    induction n with
    -- 3 = a(2) = 1 + 2! = a(1) + (0 + 2)!.
    | zero => simp [ha2, ha1]
    | succ n ih =>
      -- For a(n + 1 + 2) we have:
      -- a(n + 1 + 2) = (n + 3) * a(n + 2) - (n + 2) * a(n + 1).
      simp_rw [han (n + 1) (by omega), Nat.cast_add, add_assoc]
      norm_num
      -- The goal simplifies to (n + 3) * (a(n + 2) - a(n + 1)) = (n + 3)!.
      suffices (n + 3) * (a (n + 2) - a (n + 1)) = (n + 3)! by
        linear_combination this
      -- We have a(n + 2) = a(n + 1) + (n + 2)! (from the induction hypothesis),
      -- so (n + 3) * (a(n + 2) - a(n + 1)) = (n + 3) * (n + 2)! = (n + 3)!.
      rw [ih, add_sub_cancel_left]
      norm_cast
  simp only [IsLeast, ge_iff_le, Set.mem_setOf_eq, lowerBounds]
  constructor
  -- We need to show that for all m ≥ 5, 9 ∣ a(m).
  · intro m hm
    rw [show m = (m - 5) + 5 by omega]
    -- It is enough to show that 9 ∣ a(n + 5) for all n ≥ 0.
    generalize m - 5 = n
    -- Proof by induction.
    induction n with
    -- a(0 + 5) = 153, and 9 ∣ 153.
    | zero => norm_num [h, Nat.factorial, ha1]
    | succ n ih =>
      -- We have a(n + 1 + 5) = a(n + 5) + (n + 6)!.
      rw [show n + 1 + 5 = (n + 5) + 1 by ring, h, show n + 4 + 1 = n + 5 by ring]
      -- 9 divides a(n + 5) (by the induction hypothesis), so
      -- it is left to show that 9 ∣ (n + 6)!.
      apply dvd_add ih
      norm_cast
      -- (n + 6)! = 6! * x = 720 * x.
      rw [show n + 4 + 2 = 6 + n by ring, ← Nat.factorial_mul_ascFactorial]
      -- 720 = 9 * 80 so 9 divides 720 * x.
      use 80 * (7).ascFactorial n
      norm_num [Nat.factorial]
      ring
  -- We need to show that if for some n we have 9 ∣ a(m) for all m ≥ n, then n ≥ 5.
  · intro n hn
    -- Consider a(4) = 33. 9 does not divide 33 = a(4), so n > 4.
    specialize hn 4
    norm_num [h, ha2, ha1, Nat.factorial] at hn
    linarith