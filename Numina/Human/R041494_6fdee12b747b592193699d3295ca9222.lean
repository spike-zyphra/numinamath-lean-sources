import Mathlib

/- The sum of two positive integers $a$ and $b$ is 1001.  What is the largest possible value of $\gcd(a,b)$? -/
theorem number_theory_13190 : IsGreatest { x : ℕ | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ a + b = 1001 ∧ x = a.gcd b } 143 := by
  -- Two goals: show 143 satisfies the conditions and is the largest
  constructor
  . -- Show 143 satisfies the conditions
    -- Set a = 143 and b = 858
    use 143, 858
    -- Lean can compute this
    simp
  . -- Show 143 is the largest
    rintro x ⟨a, b, ha, hb, h, rfl⟩
    -- gcd(a, b) ∣ a + b, because gcd(a, b) ∣ a and gcd(a, b) ∣ b
    -- We get some k such that 1001 = gcd(a, b) * k
    have ⟨k, H⟩ : a.gcd b ∣ a + b := Nat.dvd_add (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
    rw [h] at H

    -- k must not be 0 (easy to prove)
    -- If k = 1, it contradicts the fact that a and b are positive
    -- Thus k ≥ 2
    have hk : 2 ≤ k := by
      -- Prove by contradiction
      by_contra! hk
      -- Case analysis on k
      interval_cases k
      . simp at H
      . simp at H
        have k : a.gcd b ≤ a := Nat.gcd_le_left b ha
        omega

    -- the least prime divisor of 1001 is 7
    replace hk : 7 ≤ k := by
      -- The usage of native_decide is necessary here, and it can be replaced by easy hand calculation
      rw [← show Nat.minFac 1001 = 7 by native_decide]
      -- 2 ≤ k, k ∣ 1001
      -- So Nat.minFac 1001 ≤ k
      apply Nat.minFac_le_of_dvd hk
      exact Dvd.intro_left (a.gcd b) H.symm

    -- Trivial inequality
    nlinarith
