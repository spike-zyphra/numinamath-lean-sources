import Mathlib

/-- Let $P$ be the product of any three consecutive positive odd integers. The largest integer
dividing all such $P$ is:

$\text{(A) } 15\quad \text{(B) } 6\quad \text{(C) } 5\quad \text{(D) } 3\quad \text{(E) } 1$ -/
theorem number_theory_95493 :
    IsGreatest {n : ℕ | ∀ P, (∃ k, Odd k ∧ P = k * (k + 2) * (k + 4)) → n ∣ P} 3 := by

  -- Let $s$ be the set of all such positive integers $n$.
  set s := {n : ℕ | ∀ P, (∃ k, Odd k ∧ P = k * (k + 2) * (k + 4)) → n ∣ P}

  -- Now, let's show that $3$ is the greatest element of $s$.
  constructor

  -- First, let's show that $3$ is an element of $s$.
  · simp [s]
    -- Let $P$ be a product of three consecutive odd numbers. Write $P = k (k + 2) (k + 4)$.
    intro P k hk hPk
    -- We will show that $P$ is 0 modulo 3.
    suffices P ≡ 0 [MOD 3] by exact Nat.dvd_of_mod_eq_zero this

    -- Let $r$ be the remainder of $k$ modulo $3$.
    let r := k % 3

    -- Let's analyze the possible values of $r$.
    have : r < 3 := by omega
    interval_cases h : r

    -- If $r = 0$, then
    -- P = k (k + 2) (k + 4)
    · calc _ ≡ k * (k + 2) * (k + 4) [MOD 3] := by rw [hPk]
    --   = r (r + 2) (r + 1)
           _ ≡ r * (r + 2) * (r + 1) [MOD 3] := by simp [Nat.ModEq, r, Nat.mul_mod, Nat.add_mod]
    --   = 0
           _ ≡ 0 [MOD 3] := by simp [h]; rfl

    -- If $r = 1$, then
    · calc _ ≡ k * (k + 2) * (k + 4) [MOD 3] := by rw [hPk]
    --   = r (r + 2) (r + 1)
           _ ≡ r * (r + 2) * (r + 4) [MOD 3] := by simp [Nat.ModEq, r, Nat.mul_mod, Nat.add_mod]
    --   = 0
           _ ≡ 15 [MOD 3] := by simp [h]; rfl
           _ ≡ 0 [MOD 3] := by decide

    -- If $r = 2$, then
    · calc _ ≡ k * (k + 2) * (k + 4) [MOD 3] := by rw [hPk]
    --   = r (r + 2) (r + 1)
           _ ≡ r * (r + 2) * (r + 4) [MOD 3] := by simp [Nat.ModEq, r, Nat.mul_mod, Nat.add_mod]
    --   = 0
           _ ≡ 48 [MOD 3] := by simp [h]; rfl
           _ ≡ 0 [MOD 3] := by decide

    -- In each case, $P$ is divisible by $3$. Therefore, $P$ is in $s$.

  -- Let $n$ be an element of $s$. We will show that $n$ is less than or equal to $3$.
  · intro n hn
    simp [s] at hn

    -- 15 is a product of three consecutive odd numbers, namely $1$, $3$, and $5$. Therefore, $n$ divides $15$.
    have : n ∣ 15 := hn 15 1 (by norm_num) (by norm_num)

    -- Divisors of $15$ are $1$, $3$, $5$, and $15$. Therefore, $n$ is one of these numbers.
    have : n ∈ (15).divisors := by
      rw [Nat.mem_divisors]
      exact ⟨this, by norm_num⟩
    have : n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 15 := by
      suffices n ∈ ({1, 3, 5, 15} : Finset ℕ) from by simpa using this
      convert this using 1

    -- Let's analyze each case.
    rcases this with (rfl | rfl | rfl | rfl)

    -- There is no problem about $n = 1$, it is less than or equal to $3$.
    · norm_num

    -- Again, there is no problem about $n = 3$, it is equal to $3$.
    · norm_num

    -- For $n = 5$, we will show that this is impossible.
    · exfalso
      -- Let $P = 7 * 9 * 11$. By assumption, $n$ divides $P$. However, $5$ does not divide $P$.
      -- This is a contradiction.
      suffices 5 ∣ 7 * 9 * 11 by norm_num at this
      apply hn _ 7 (by decide) (by norm_num)

    -- For $n = 15$, we will show that this is impossible.
    · exfalso
      -- Let $P = 7 * 9 * 11$. By assumption, $n$ divides $P$. $5$ divides $n$. However, $15$ does
      -- not divide $P$. This is a contradiction.
      suffices 15 ∣ 7 * 9 * 11 by norm_num at this
      apply hn _ 7 (by decide) (by norm_num)

    -- Either way, $n$ is less than or equal to $3$. Therefore, $3$ is the greatest element of $s$.