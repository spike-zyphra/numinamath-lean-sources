import Mathlib

/- Jax bought exactly enough trees to plant eight equal rows. Then one tree died and couldn't be planted, but he still had enough trees left to plant exactly nine equal rows. After that, a tree was stolen, but he still had enough trees left to plant exactly ten equal rows. If he bought the least number of trees satisfying these three conditions, how many trees did he buy? -/
theorem number_theory_19288 : IsLeast {n : ℤ | n > 0 ∧ 8 ∣ n ∧ 9 ∣ n - 1 ∧ 10 ∣ n - 2} 352 := by
  -- Prove two subgoals
  -- 1. 352 is in the set
  -- 2. 352 is the least element in the set
  constructor
  . -- Prove by simplification
    trivial
  . -- Suppose n > 0 satisfies the conditions 8 ∣ n ∧ 9 ∣ n - 1 ∧ 10 ∣ n - 2
    rintro n ⟨h0, h1, h2, h3⟩
    -- First, we prove 90 ∣ n - 82
    have h4 : 90 ∣ n - 82 := by
      -- Prove 9 ∣ n - 82 and 10 ∣ n - 82
      have k1 : 9 ∣ n - 82 := by
        rw [show n - 82 = n - 1 - 81 by ring]
        exact Int.dvd_sub h2 (by trivial)
      have k2 : 10 ∣ n - 82 := by
        rw [show n - 82 = n - 2 - 80 by ring]
        exact Int.dvd_sub h3 (by trivial)
      -- Thus the least common multiple of 9 and 10 is a divisor of n - 82
      exact lcm_dvd k1 k2
    clear h2 h3
    -- Next, we prove 360 ∣ n - 352
    have h5 : 360 ∣ n - 352 := by
      -- Prove 90 ∣ n - 352 and 8 ∣ n - 352
      have k1 : 90 ∣ n - 352 := by
        rw [show n - 352 = n - 82 - 270 by ring]
        exact Int.dvd_sub h4 (by trivial)
      have k2 : 8 ∣ n - 352 := by
        exact Int.dvd_sub h1 (by trivial)
      -- Thus the least common multiple of 90 and 8 is a divisor of n - 352
      exact lcm_dvd k1 k2
    -- Now we have 360 ∣ n - 352, so n - 352 = 360k for some integer k
    rcases h5 with ⟨k, hk⟩
    -- We have k ≥ 0 because n > 0
    have : k ≥ 0 := by omega
    -- So we have n ≥ 352
    omega
