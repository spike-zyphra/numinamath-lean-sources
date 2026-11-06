import Mathlib
/- Find the largest number $n$ such that (2004!)! is divisible by (( $n!)!)!$. -/
theorem algebra_611224 : IsGreatest {n : ℕ | Nat.factorial (Nat.factorial (Nat.factorial n)) ∣ Nat.factorial (Nat.factorial 2004)} 6:= by
  -- Helper lemma: For positive natural numbers n and m, n! divides m! if and only if n ≤ m
  have h1 : ∀ n m : ℕ, n > 0 → m > 0 → (Nat.factorial n ∣ Nat.factorial m ↔ n ≤ m):= by
    intro n m _ hm
    constructor
    -- Forward direction: if n! divides m!, then n ≤ m
    .
      intro h
      by_contra H
      simp at H
      -- If n > m, then m! divides n!
      have h1 : m.factorial ∣ n.factorial:= by exact Nat.factorial_dvd_factorial (by omega)
      -- If m! divides n! and n! divides m!, then m! = n!
      replace h1 : m.factorial = n.factorial:= by exact Nat.dvd_antisymm h1 h
      -- But if m < n, then m! < n!, contradiction
      replace H : m.factorial < n.factorial:= by exact Nat.factorial_lt_of_lt hm H
      linarith
    -- Reverse direction: if n ≤ m, then n! divides m!
    .
      intro h
      exact Nat.factorial_dvd_factorial h

  -- Proving that 6 is in the set {n : ℕ | (n!)!! divides (2004!)!}
  constructor
  .
    simp
    -- We need to show that (6!)!! divides (2004!)!
    -- It's sufficient to show that (2004!) ≥ (6!)!
    suffices Nat.factorial 2004 ≥ (Nat.factorial 6).factorial by exact Nat.factorial_dvd_factorial this
    -- It's sufficient to show that 2004 ≥ 6!
    suffices 2004 ≥ Nat.factorial 6 by exact Nat.factorial_le this
    -- Expand 6! = 6 × 5 × 4 × 3 × 2 × 1 = 720
    repeat rw [Nat.factorial_succ]
    simp

  -- Proving that 6 is the greatest element in the set
  .
    intro n h
    simp at h
    -- Case analysis: either n = 0 or n > 0
    by_cases hn : n = 0
    -- Case n = 0: trivially n ≤ 6
    .
      omega
    -- Case n > 0
    .
      -- From h, we know (n!)!! divides (2004!)!
      -- Using the helper lemma, this means (n!)! ≤ (2004!)
      replace h:= (h1 (n.factorial.factorial) (Nat.factorial 2004) (Nat.factorial_pos (n.factorial)) (Nat.factorial_pos (2004))).1 h
      -- This implies n! ≤ 2004
      replace h : n.factorial ≤ 2004:= by
        by_contra H
        simp at H
        -- If n! > 2004, then (n!)! > (2004)!
        have g1 : n.factorial.factorial > Nat.factorial 2004:= by exact (Nat.factorial_lt (by omega)).2 H
        linarith
      -- Proof by contradiction: assume n > 6
      by_contra H
      simp at H
      -- If n > 6, then n ≥ 7
      replace H : n ≥ 7:= by omega
      -- Then n! ≥ 7!
      replace H : n.factorial ≥ Nat.factorial 7:= by exact Nat.factorial_le H
      -- Expand 7! = 7 × 6 × 5 × 4 × 3 × 2 × 1 = 5040
      repeat rw [Nat.factorial_succ] at H
      simp at H
      -- But 5040 > 2004, contradiction with n! ≤ 2004
      linarith
