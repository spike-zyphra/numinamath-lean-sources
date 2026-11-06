import Mathlib
/- Compute the unique positive integer $n$ such that $\frac{n^{3}-1989}{n}$ is a perfect square. -/
theorem number_theory_610686 (n : ℕ) (hn : n > 0) : (∃ k : ℕ, ((↑n : ℝ) ^ 3 - 1989) / (↑n : ℝ) = (↑k : ℝ) ^ 2) ↔ n = 13:= by
  constructor
  -- Forward direction: if (n³-1989)/n is a perfect square, then n = 13
  .
    intro h
    rcases h with ⟨k, hk⟩
    -- Simplify the field expression
    field_simp at hk
    -- Rewrite the equation to get n³ = 1989 + n·k²
    replace hk : n ^ 3 = 1989 + n * k ^ 2:= by
      rify
      linarith
    -- Prove that n divides n³
    have h1 : n ∣ n ^ 3:= by exact Dvd.intro_left (n.pow 2) rfl
    rw [hk] at h1
    -- Prove that n divides n·k²
    have h2 : n ∣ n * k ^ 2:= by simp
    -- Since n divides n³ and n divides n·k², n must divide 1989
    replace h1 : n ∣ 1989:= by exact (Nat.dvd_add_iff_left h2).mpr h1
    set m:= 1989 with hm
    clear_value m
    -- Express that n is a divisor of 1989
    replace h1 : n ∈ Nat.divisors m:= by refine Nat.mem_divisors.mpr ⟨h1, (by linarith)⟩
    -- Factor 1989 as 9 * 13 * 17
    rw [show 1989 = 9 * 13 * 17 by omega] at hm
    -- List all divisors of 1989
    have h3 : Nat.divisors m = {1, 3, 9, 13, 17, 39, 51, 117, 153, 221, 663, 1989}:= by
      rw [hm]
      simp
      native_decide
    rw [h3] at h1
    clear h3
    subst m
    simp at hk
    -- Prove that n > 12 using the equation n³ = 1989 + n·k²
    have hk1 : n > 12:= by
      by_contra H
      simp at H
      replace H : n ^ 3 ≤ 12 ^ 3:= by exact Nat.pow_le_pow_of_le_left H 3
      have g1 : n * k ^ 2 ≥ 0:= by positivity
      linarith
    -- Check each possible divisor of 1989 that is greater than 12
    fin_cases h1
    -- Case n = 1
    .
      linarith
    -- Case n = 3
    .
      linarith
    -- Case n = 9
    .
      linarith
    -- Case n = 13
    .
      simp
    -- Case n = 17: Show that no integer k can satisfy the equation
    .
      simp at hk
      -- Prove that k > 13
      have hk1 : k > 13:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 13 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      -- Prove that k < 14
      have hk2 : k < 14:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 14 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      -- This is a contradiction since no integer can be both > 13 and < 14
      linarith
    -- Case n = 39: Similar contradiction for k
    .
      simp at hk
      have hk1 : k > 38:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 38 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 39:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 39 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case n = 51: Similar contradiction for k
    .
      simp at hk
      have hk1 : k > 50:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 50 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 51:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 51 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case n = 117: Similar contradiction for k
    .
      simp at hk
      have hk1 : k > 116:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 116 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 117:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 117 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case n = 153: Similar contradiction for k
    .
      simp at hk
      have hk1 : k > 152:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 152 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 153:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 153 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case n = 221: Similar contradiction for k
    .
      simp at hk
      have hk1 : k > 220:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 220 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 221:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 221 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case n = 663: Similar contradiction for k
    .
      simp at hk
      have hk1 : k > 662:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 662 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 663:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 663 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case n = 1989: Similar contradiction for k
    .
      simp at hk
      have hk1 : k > 1988:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 1988 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 1989:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 1989 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
  -- Reverse direction: if n = 13, then (n³-1989)/n is a perfect square
  .
    intro h
    subst n
    simp
    norm_num
    -- Show that when n = 13, k = 4 satisfies the equation
    use 4
    simp
    linarith
