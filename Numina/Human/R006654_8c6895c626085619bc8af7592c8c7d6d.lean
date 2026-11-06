import Mathlib

/-!
Let `b m a : ℤ` with `0 < m` and `b ≡ -1 [ZMOD m]`.  If the integer with base‑`b` digits
`[1,2,3,4,5]` differs from `a` by a multiple of `m`, then `a = 3 % m`.
-/


theorem digit_congruence {b : ℤ} {m a : ℕ}
  (h_b     : (b : ZMod m) = -1)
  (a_lt    : a < m)
  (hN      : ((1 * b ^ 4 + 2 * b ^ 3 + 3 * b ^ 2 + 4 * b + 5 : ℤ) : ZMod m) = a) :
  a = 3 % m :=
by
  -- The proof proceeds in two main steps.
  -- 1. We show that `a % m = 3 % m`. This is done by showing that `a` and `3` are congruent
  --    modulo `m`, which means they are equal as elements of the type `ZMod m`.
  -- 2. We use the fact that `a < m` to show that `a % m = a`, which allows us to conclude
  --    that `a = 3 % m`.

  have cast_ZMod: (h_eq : (a : ZMod m) = 3) -> (h_lt : a < m) -> a = 3 % m := by
      intro h_eq h_lt
      -- The equality in ZMod m implies that the natural numbers are congruent modulo m.
      have h_mod_eq : a ≡ 3 [MOD m] := (ZMod.natCast_eq_natCast_iff
    a 3 m).mp h_eq

      -- The definition of Nat.ModEq is that their modulo operations are equal.
      have h_val_eq : a % m = 3 % m := h_mod_eq

      -- Given that a < m, we know that a % m is just a.
      -- This is the theorem Nat.mod_eq_of_lt.
      have h_a_mod_a : a % m = a := Nat.mod_eq_of_lt h_lt

      -- We can now substitute a for a % m in our equality.
      rw [h_a_mod_a] at h_val_eq

      -- The goal is now exactly what h_val_eq states.
      exact h_val_eq


  have h1 : ((1 * b ^ 4 + 2 * b ^ 3 + 3 * b ^ 2 + 4 * b + 5 : ℤ) : ZMod m) = 3 := by
      calc
        -- The initial expression from `hN`.
        ((1 * b ^ 4 + 2 * b ^ 3 + 3 * b ^ 2 + 4 * b + 5 : ℤ) : ZMod m)

        -- First, we use the fact that casting from integers to `ZMod m` is a ring homomorphism.
        -- This means the cast `(↑)` can be distributed over addition and multiplication.
        -- The `push_cast` tactic automates this process. `rfl` confirms the result is identical.
        _ = (1 * (b : ZMod m) ^ 4 + 2 * (b : ZMod m) ^ 3 + 3 * (b : ZMod m) ^ 2 + 4 * (b : ZMod m) + 5) := by
            push_cast
            rfl

        -- Next, we substitute `(b : ZMod m)` with `-1` using our hypothesis `h_b`.
        _ = (1 * (-1) ^ 4 + 2 * (-1) ^ 3 + 3 * (-1) ^ 2 + 4 * (-1) + 5) := by
            rw [h_b]

        -- The final step is to compute the sum of these numbers.
        -- The `ring` tactic is designed to solve polynomial and ring equalities.
        _ = 3 := by
            ring

  have h2: (a : ZMod m) = 3 := by
      rw [← h1, ← hN]


  exact cast_ZMod h2 a_lt
