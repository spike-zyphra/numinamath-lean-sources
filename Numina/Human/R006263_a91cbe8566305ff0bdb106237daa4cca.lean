import Mathlib

/- Let $N$ be a positive integer. We are interested in the value of $26^N \pmod{14}$.
Show that $26^N \pmod{14}$ is equal to:
- $12$, if $N \equiv 1 \pmod 6$
- $4$, if $N \equiv 2 \pmod 6$
- $6$, if $N \equiv 3 \pmod 6$
- $2$, if $N \equiv 4 \pmod 6$
- $10$, if $N \equiv 5 \pmod 6$
- $8$, if $N \equiv 0 \pmod 6$ -/
theorem number_theory_635265 (N : ℕ) (hN : 0 < N) :
    26 ^ N % 14 = match N % 6 with
    | 0 => 8
    | 1 => 12
    | 2 => 4
    | 3 => 6
    | 4 => 2
    | 5 => 10
    | _ => 0 -- Unreachable
    := by
  -- We induct on N.
  induction N, hN using Nat.le_induction with
  | base => simp -- For the base case, we check that 26 ^ 1 % 14 = 12.
  | succ N hN ih =>
    -- For the inductive step, we use the fact that 26 ^ (N + 1) = 26 ^ N * 26.
    -- We split into the cases where N % 6 = 0, 1, 2, 3, 4, 5.
    mod_cases N % 6
    all_goals
      -- We calculate (N + 1) % 6 = (N % 6 + 1) % 6.
      simp only [Nat.ModEq, Nat.reduceMod] at H
      -- We use the inductive hypothesis to simplify 26 ^ N % 14.
      simp only [pow_succ, Nat.mul_mod, ih, H, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, Nat.add_mod]