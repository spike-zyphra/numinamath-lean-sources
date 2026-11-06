import Mathlib
/- Find all positive integers $n>1$ for which $\frac{n^{2}+7 n+136}{n-1}$ is the square of a positive integer. -/
theorem number_theory_611486 : {n : ℕ | n > 1 ∧ ∃ k : ℕ, ((↑n : ℝ) ^ 2 + 7 * n + 136) / (n - 1) = k ^ 2} = {5, 37}:= by
  ext n
  constructor
  -- Forward direction: if n satisfies the condition, then n is either 5 or 37
  .
    intro h
    simp at h
    rcases h with ⟨h1, h2⟩
    rcases h2 with ⟨k, hk⟩
    -- Rearranging the equation to get (n-1)*k² = n²+7n+136
    replace hk : (n - 1) * k ^ 2 = n ^ 2 + 7 * n + 136:= by
      rify
      field_simp
      rify at h1
      replace h1 : (↑n : ℝ) - 1 > 0:= by linarith
      field_simp at hk
      linarith
    -- Proving that (n-1) divides 144
    have h2 : n - 1 ∣ 144:= by
      set m:= n - 1 with hm
      clear_value m
      replace hm : n = m + 1:= by omega
      subst n
      ring_nf at hk
      replace hk : m ∣ 144 + m * 9 + m ^ 2:= by rw [←hk] ; simp
      have g1 : m ∣ m ^ 2:= by exact Dvd.intro_left (m.pow 1) rfl
      have g2 : m ∣ m * 9:= by simp
      replace hk : m ∣ 144 + m * 9:= by exact (Nat.dvd_add_iff_left g1).mpr hk
      replace hk : m ∣ 144:= by exact (Nat.dvd_add_iff_left g2).mpr hk
      exact hk
    -- Setting m = n-1 to simplify calculations
    set m:= n - 1 with hm
    clear_value m
    replace hm : n = m + 1:= by omega
    subst n
    ring_nf at hk
    -- Listing all divisors of 144
    have h3 : Nat.divisors 144 = {1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144}:= by decide
    replace h2 : m ∈ Nat.divisors 144:= by refine Nat.mem_divisors.mpr ⟨h2, by omega⟩
    rw [h3] at h2
    -- Checking each possible value of m (which is n-1)
    fin_cases h2
    -- Case m = 1 (n = 2)
    .
      simp at hk
      have hk1 : k > 12:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 12 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 13:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 13 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case m = 2 (n = 3)
    .
      simp at hk
      have hk1 : k > 9:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 9 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 10:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 10 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case m = 3 (n = 4)
    .
      simp at hk
      have hk1 : k > 7:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 7 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 8:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 8 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case m = 4 (n = 5) - This is a valid solution
    .
      simp
    -- Case m = 6 (n = 7)
    .
      simp at hk
      have hk1 : k > 6:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 6 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 7:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 7 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case m = 8 (n = 9)
    .
      simp at hk
      have hk1 : k > 5:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 5 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 6:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 6 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case m = 9 (n = 10)
    .
      simp at hk
      have hk1 : k > 5:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 5 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 6:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 6 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case m = 12 (n = 13)
    .
      simp at hk
      have hk1 : k > 5:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 5 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 6:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 6 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case m = 16 (n = 17)
    .
      simp at hk
      have hk1 : k > 5:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 5 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 6:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 6 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case m = 18 (n = 19)
    .
      simp at hk
      have hk1 : k > 5:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 5 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 6:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 6 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case m = 24 (n = 25)
    .
      simp at hk
      have hk1 : k > 6:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 6 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 7:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 7 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case m = 36 (n = 37) - This is a valid solution
    .
      simp
    -- Case m = 48 (n = 49)
    .
      simp at hk
      have hk1 : k > 7:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 7 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 8:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 8 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case m = 72 (n = 73)
    .
      simp at hk
      have hk1 : k > 9:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 9 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 10:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 10 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case m = 144 (n = 145)
    .
      simp at hk
      have hk1 : k > 12:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≤ 12 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have hk2 : k < 13:= by
        by_contra H
        simp at H
        replace H : k ^ 2 ≥ 13 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
  -- Reverse direction: if n is 5 or 37, then it satisfies the condition
  .
    intro h
    simp at h
    rcases h with h | h
    all_goals
      subst n
      simp
      norm_num
      use 7
      simp
      linarith
