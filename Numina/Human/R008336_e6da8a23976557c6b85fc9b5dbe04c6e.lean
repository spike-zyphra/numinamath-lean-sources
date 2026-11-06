import Mathlib

/- Alicia has $n$ candies, where $n$ is a positive integer with three digits. If she buys $5$ more, she will have a multiple of $8$. If she loses $8$, she will have a multiple of $5$. What is the smallest possible value of $n$? -/
theorem number_theory_12589 : IsLeast {n : ℕ | 100 ≤ n ∧ n < 1000 ∧ (n + 5) % 8 = 0 ∧ (n - 8) % 5 = 0} 123 := by
  -- Two goals: show 123 satisfies the conditions and is the smallest
  constructor
  . -- Show 123 satisfies the conditions
    -- Lean can compute this
    simp
  . -- Show 123 is the smallest
    intro n ⟨h1, h2, h3, h4⟩

    -- We have n ≡ -5 ≡ 3 [MOD 8]
    -- 8 ∣ n - 3
    replace h3 : 8 ∣ n - 3 := by
      apply Nat.dvd_of_mod_eq_zero at h3
      have h := Nat.dvd_sub (show 8 ≤ n + 5 by omega) h3 (by simp)
      simp at h
      exact h

    -- We have n ≡ 8 ≡ 3 [MOD 5]
    -- 5 ∣ n - 3
    replace h4 : 5 ∣ n - 3 := by
      apply Nat.dvd_of_mod_eq_zero at h4
      have h := Nat.dvd_add h4 (show 5 ∣ 5 by simp)
      rw [show n - 8 + 5 = n - 3 by omega] at h
      exact h

    -- n - 3 is divisible by 8 and 5
    -- Thus n - 3 is divisible by 40
    have h : 40 ∣ n - 3 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h3 h4

    -- Omega can solve this
    rcases h with ⟨k, hk⟩
    clear h2 h3 h4
    omega
