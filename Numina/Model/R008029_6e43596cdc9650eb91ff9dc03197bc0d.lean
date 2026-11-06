import Mathlib

theorem number_theory_22738 {a : ℕ} (ha : 0 < a) (h : Nat.lcm (a + 1) (a - 5) = 10508) :
    a^2 - 4 * a + 1 = 21022 := by 
  have h1 : a ≤ 10513 := by
    by_cases h2 : a + 1 ≤ a - 5
    · omega
    · -- If a - 5 < a + 1, then gcd(a+1, a-5) divides 6.
      have h3 : a - 5 ∣ 10508 := by
        rw [← h]
        exact Nat.dvd_lcm_right _ _
      have h4 : a - 5 ≤ 10508 := by
        exact Nat.le_of_dvd (by norm_num) h3
      omega

  interval_cases a <;> norm_num [Nat.lcm] at h <;> omega