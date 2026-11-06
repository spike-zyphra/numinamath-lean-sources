import Mathlib


/--
For any natural number `n`, prove that the greatest common divisor of `fib n` and `fib (n + 1)` is `1`.
-/
theorem gcd_fib_succ (n : Nat) :
  Nat.gcd (Nat.fib n) (Nat.fib (n + 1)) = 1 := by
  -- Induction on `n`
  induction n with
  | zero =>
    -- base case: n = 0, fib 0 = 0, fib 1 = 1, gcd 0 1 = 1
    simp [Nat.fib_zero, Nat.fib_one]
  | succ k ih =>
    -- induction hypothesis: Nat.gcd (fib k) (fib (k + 1)) = 1
    -- prove: Nat.gcd (fib (k + 1)) (fib (k + 2)) = 1
    cases k with
    | zero =>
      -- k = 0: prove gcd(fib 1, fib 2) = gcd(1, 1) = 1
      norm_num [Nat.fib_one, Nat.fib_two]
    | succ k' =>
      cases k' with
      | zero =>
        -- k = 1: prove gcd(fib 2, fib 3) = gcd(1, 2) = 1
        calc
          Nat.gcd (Nat.fib 2) (Nat.fib 3)
            = Nat.gcd 1 2 := by norm_num [Nat.fib_two]
            _ = 1 := by norm_num
      | succ k'' =>
        -- k ≥ 2: use general modulo operation
        have hmod : Nat.fib (Nat.succ (Nat.succ k'') + 2) % Nat.fib (Nat.succ (Nat.succ k'') + 1) = Nat.fib (Nat.succ (Nat.succ k'')) := by
          calc
            Nat.fib (Nat.succ (Nat.succ k'') + 2) % Nat.fib (Nat.succ (Nat.succ k'') + 1)
              = (Nat.fib (Nat.succ (Nat.succ k'') + 1) + Nat.fib (Nat.succ (Nat.succ k''))) % Nat.fib (Nat.succ (Nat.succ k'') + 1) := by simp [Nat.fib_add_two]
            _ = Nat.fib (Nat.succ (Nat.succ k'')) := by
              rw [Nat.add_comm, Nat.add_mod_right]
              exact Nat.mod_eq_of_lt (Nat.fib_lt_fib_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k''))))

        calc
          Nat.gcd (Nat.fib (Nat.succ (Nat.succ k'') + 1)) (Nat.fib (Nat.succ (Nat.succ k'') + 2))
            = Nat.gcd (Nat.fib (Nat.succ (Nat.succ k'') + 2) % Nat.fib (Nat.succ (Nat.succ k'') + 1)) (Nat.fib (Nat.succ (Nat.succ k'') + 1)) := by rw [Nat.gcd_rec]
            _ = Nat.gcd (Nat.fib (Nat.succ (Nat.succ k''))) (Nat.fib (Nat.succ (Nat.succ k'') + 1)) := by simp [hmod]
            _ = 1 := ih
