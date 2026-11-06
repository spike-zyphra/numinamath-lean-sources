import Mathlib
/- Find all integers $n$ for which $\frac{n^{3}+8}{n^{2}-4}$ is an integer. -/
theorem number_theory_609246 : {n : ℤ | n ^ 2 - 4 ≠ 0 ∧ (∃ k : ℤ, (n ^ 3 + 8) / ((↑n : ℝ) ^ 2 - 4) = k)} = {0, 1, 3, 4, 6}:= by
  -- We use extensionality to prove equality of sets
  ext n
  constructor
  -- Forward direction: if (n^3+8)/(n^2-4) is an integer, then n is in {0,1,3,4,6}
  .
    intro h
    simp at h
    rcases h with ⟨h1, ⟨k, h2⟩⟩
    rify at h1
    field_simp at h2
    -- Rewrite the equation to get n^3+8 = k*(n^2-4)
    replace h2 : n ^ 3 + 8 = k * (n ^ 2 - 4):= by rify ; linarith
    -- Factor the equation to get (n+2)*(n^2-2n+4-k*(n-2)) = 0
    replace h2 : (n + 2) * (n ^ 2 - 2 * n + 4 - k * (n - 2)) = 0:= by linarith
    -- We know n^2-4 ≠ 0 from our assumption
    replace h1 : n ^ 2 - 4 ≠ 0:= by rify ; exact h1
    -- Factor n^2-4 as (n-2)*(n+2)
    rw [show n ^ 2 - 4 = (n - 2) * (n + 2) by ring] at h1
    simp at h1
    -- Since n+2 ≠ 0, we can simplify our equation
    simp [h1] at h2
    -- Rearrange to get 4 = (k-n)*(n-2)
    replace h2 : 4 = (k - n) * (n - 2):= by linarith
    -- This means n-2 divides 4
    replace h2 : n - 2 ∣ 4:= by rw [h2] ; simp
    -- Let m = n-2 to simplify our work
    set m:= n - 2
    have hm : n = m + 2:= by omega
    clear_value m
    subst n
    ring_nf at h1
    -- The absolute value of m divides 4
    replace h2 : m.natAbs ∣ 4:= by
      zify
      exact (abs_dvd m 4).mpr h2
    -- m.natAbs is a divisor of 4
    replace h2 : m.natAbs ∈ Nat.divisors 4:= by refine Nat.mem_divisors.mpr ⟨h2, (by omega)⟩
    -- The divisors of 4 are 1, 2, and 4
    have h3 : Nat.divisors 4 = {1, 2, 4}:= by decide
    rw [h3] at h2
    simp at h2
    zify at h2
    -- Case analysis on the possible values of m
    rcases h2 with h2 | h2 | h2
    -- Case: |m| = 1
    .
      replace h2 : m = 1 ∨ m = -1:= by exact abs_eq_abs.mp h2
      rcases h2 with h2 | h2
      all_goals
        subst m
        simp
    -- Case: |m| = 2
    .
      replace h2 : m = 2 ∨ m = -2:= by exact abs_eq_abs.mp h2
      rcases h2 with h2 | h2
      all_goals
        subst m
        simp
    -- Case: |m| = 4
    .
      replace h2 : m = 4 ∨ m = -4:= by exact abs_eq_abs.mp h2
      rcases h2 with h2 | h2
      .
        subst m
        simp
      .
        subst m
        simp at h1
  -- Reverse direction: if n is in {0,1,3,4,6}, then (n^3+8)/(n^2-4) is an integer
  .
    intro h
    simp at h
    -- Case analysis for each possible value of n
    rcases h with h | h | h | h | h
    all_goals
      subst n
      simp
      norm_num
    -- For n = 0, the result is -2
    .
      use -2
      simp
    -- For n = 1, the result is -3
    .
      use -3
      simp
    -- For n = 3, the result is 7
    .
      use 7
      simp
    -- For n = 4, the result is 6
    .
      use 6
      simp
    -- For n = 6, the result is 7
    .
      use 7
      simp
