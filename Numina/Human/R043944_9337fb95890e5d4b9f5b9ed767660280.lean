import Mathlib
/- Determine the second smallest positive integer $n$ such that $n^{3}+n^{2}+n+1$ is a perfect square. -/
theorem number_theory_610023 (a : ℕ) (ha : IsLeast {n : ℕ | n > 0 ∧ ∃ k : ℕ, n ^ 3 + n ^ 2 + n + 1 = k ^ 2} a) : IsLeast {n : ℕ | n > a ∧ ∃ k : ℕ, n ^ 3 + n ^ 2 + n + 1 = k ^ 2} 7:= by
  -- First, prove that a = 1 is the smallest positive integer with the property
  have h1 : a = 1:= by
    rcases ha with ⟨⟨h1, h2⟩, h3⟩
    simp [lowerBounds] at h3
    specialize h3 (show 0 < 1 by omega) 2 (by omega)
    omega
  -- Substitute a = 1 and clear the hypothesis ha
  subst a
  clear ha
  -- Prove that 7 is the second smallest positive integer with the property
  constructor
  -- First part: Prove that 7 satisfies the property (7^3 + 7^2 + 7 + 1 = 20^2)
  .
    simp
    use 20
    simp
  -- Second part: Prove that no integer between 1 and 7 satisfies the property
  .
    simp [lowerBounds]
    intro n hn k hk
    by_contra H
    -- If n < 7 and n > 1, then n must be one of {2,3,4,5,6}
    replace H : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6:= by omega
    rcases H with H | H | H | H | H
    -- Case n = 2: Show that 2^3 + 2^2 + 2 + 1 = 15 is not a perfect square
    .
      subst n
      simp at hk
      -- Prove that if k^2 = 15, then 3 < k < 4, which is impossible for integer k
      have hk1 : k > 3:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 3 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 4:= by
        by_contra H
        simp at H
        replace H : 4 ^ 2 ≤ k ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case n = 3: Show that 3^3 + 3^2 + 3 + 1 = 40 is not a perfect square
    .
      subst n
      simp at hk
      -- Prove that if k^2 = 40, then 6 < k < 7, which is impossible for integer k
      have hk1 : k > 6:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 6 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 7:= by
        by_contra H
        simp at H
        replace H : 7 ^ 2 ≤ k ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case n = 4: Show that 4^3 + 4^2 + 4 + 1 = 85 is not a perfect square
    .
      subst n
      simp at hk
      -- Prove that if k^2 = 85, then 9 < k < 10, which is impossible for integer k
      have hk1 : k > 9:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 9 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 10:= by
        by_contra H
        simp at H
        replace H : 10 ^ 2 ≤ k ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case n = 5: Show that 5^3 + 5^2 + 5 + 1 = 156 is not a perfect square
    .
      subst n
      simp at hk
      -- Prove that if k^2 = 156, then 12 < k < 13, which is impossible for integer k
      have hk1 : k > 12:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 12 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 13:= by
        by_contra H
        simp at H
        replace H : 13 ^ 2 ≤ k ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case n = 6: Show that 6^3 + 6^2 + 6 + 1 = 259 is not a perfect square
    .
      subst n
      simp at hk
      -- Prove that if k^2 = 259, then 16 < k < 17, which is impossible for integer k
      have hk1 : k > 16:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 16 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 17:= by
        by_contra H
        simp at H
        replace H : 17 ^ 2 ≤ k ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
