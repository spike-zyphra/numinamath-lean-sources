import Mathlib

/- Show that $n^{n}+(n+1)^{n+1}$ is composite for infinitely many positive integers $n$. -/
theorem number_theory_604738 :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ ¬Nat.Prime ((n ^ n) + (n + 1) ^ (n + 1)) := by
    intro N
    use 6 * N + 4 -- we' ll show that 6t+4 is as desired --
    constructor
    . omega
    . let n:= 6 * N + 4
      have hn: 6 * N + 4 = n := by simp [n]
      simp [hn]

      -- indeed 3 ∣ n ^ n + (n + 1) ^ (n + 1) --
      have dvd3: 3 ∣ n ^ n + (n + 1) ^ (n + 1) := by
        have mod3: n % 3 = 1 := by
          simp [n]
          omega
        have mod3_2: (n + 1) % 3 = 2 := by
          simp [n]
          omega
        have mod5: n % 6 = 4 := by
          simp [n]
          omega
        have nmod: n ^ n % 3 = 1 := by
          rw [Nat.pow_mod]
          rw[mod3]
          simp
        have n1mod: (n + 1) ^ (n + 1) % 3 = 2 := by
            rw [Nat.pow_mod]
            rw [mod3_2]
            simp [n]
            have eq: 2 ^ (6 * N + 4 + 1) = 4 ^ (3 * N + 2) * 2 := by
                rw [Nat.pow_add_one]
                simp
                nth_rewrite 2[show 4 = 2 ^ 2 by omega]
                rw [← Nat.pow_mul]
                rw [show 2 * (3 * N + 2) = 6 * N + 4  by omega]

            rw [eq]
            rw [← Nat.mod_mul_mod]
            rw [Nat.pow_mod]
            rw [show 4%3 = 1 by simp]
            simp
        apply Nat.dvd_of_mod_eq_zero
        rw [Nat.add_mod]
        rw [nmod]
        rw [n1mod]
      by_contra! p
      have l: n ^ n + (n + 1) ^ (n + 1) = 3 := by
        rw [← Nat.Prime.dvd_iff_eq]
        exact dvd3
        exact p
        omega
    -- classify according to n=0 or not --
      by_cases o: n = 0
      -- n = 0 --
      . rw [o] at l
        omega
      -- n ≠ 0 --
      . replace o: n ≥ 1 := by omega
        have ineq2: 2 ^ 2 ≤ 2 ^ (n + 1) := by
            apply Nat.pow_le_pow_of_le_right
            omega
            omega
        have ineq: 5 ≤ 1 + 2 ^ (n + 1) := by
            calc 5 = 1 + 2 ^ 2 := by ring
                 _ ≤ 1 + 2 ^ (n + 1) := by apply Nat.add_le_add_left;exact ineq2
        have no: 3 ≥  5 := by
            calc 3 = n ^ n + (n + 1) ^ (n + 1) := by simp [l]
                 _ ≥ 1 ^ n + (n + 1) ^ (n + 1) := by simp; rw [show 1 = 1^ n by ring];apply Nat.pow_le_pow_left;omega
                 _ ≥ 1 + 2 ^ (n + 1) := by simp; apply Nat.pow_le_pow_left;omega
                 _ ≥ 1 + 2 ^ 2 := by simp; exact ineq
        tauto