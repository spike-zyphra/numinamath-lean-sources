import Mathlib
/- Find all integers $m$ such that $m^{2}+6 m+28$ is a perfect square. -/
theorem algebra_611164 : {m : ℤ | ∃ k : ℤ, k ^ 2 = m ^ 2 + 6 * m + 28} = {6, -12}:= by
  ext m
  constructor
  -- Forward direction: if m²+6m+28 is a perfect square, then m is either 6 or -12
  .
    intro h
    simp at h
    rcases h with ⟨k, hk⟩
    -- Rearrange the equation to get (k+m+3)(k-m-3) = 19
    replace hk : (k + m + 3) * (k - m - 3) = 19:= by linarith
    have h:= hk
    -- Prove that 19 is prime
    have h1 : Nat.Prime 19:= by norm_num
    -- Convert to natural numbers using absolute value
    replace hk : ((k + m + 3) * (k - m - 3)).natAbs = 19:= by rw [hk]; simp
    rw [show ((k + m + 3) * (k - m - 3)).natAbs = (k + m + 3).natAbs * (k - m - 3).natAbs by exact Int.natAbs_mul (k + m + 3) (k - m - 3)] at hk
    -- Use divisibility properties of prime numbers
    have h2 : (k + m + 3).natAbs ∣ 19:= by exact Dvd.intro (k - m - 3).natAbs hk
    -- Since 19 is prime, the absolute value must be either 1 or 19
    replace h2 : (k + m + 3).natAbs = 1 ∨ (k + m + 3).natAbs = 19:= by exact (Nat.dvd_prime h1).mp h2
    rcases h2 with h2 | h2
    -- Case where absolute value is 1
    .
      replace h2 : k + m + 3 = 1 ∨ k + m + 3 = -1:= by exact Int.natAbs_eq_natAbs_iff.mp h2
      rcases h2 with h2 | h2
      -- Subcase: k + m + 3 = 1
      .
        rw [h2] at h
        replace h : m = -12:= by linarith
        subst m
        simp
      -- Subcase: k + m + 3 = -1
      .
        rw [h2] at h
        replace h : m = 6:= by linarith
        subst m
        simp
    -- Case where absolute value is 19
    .
      replace h2 : k + m + 3 = 19 ∨ k + m + 3 = -19:= by exact Int.natAbs_eq_natAbs_iff.mp h2
      rcases h2 with h2 | h2
      -- Subcase: k + m + 3 = 19
      .
        rw [h2] at h
        replace h : m = 6:= by linarith
        subst m
        simp
      -- Subcase: k + m + 3 = -19
      .
        rw [h2] at h
        replace h : m = -12:= by linarith
        subst m
        simp
  -- Reverse direction: prove that both 6 and -12 satisfy the equation
  .
    intro h
    simp at h
    rcases h with h | h
    -- Case: m = 6
    .
      subst m
      simp
      use 10
      simp
    -- Case: m = -12
    .
      subst m
      simp
      use 10
      simp
