import Mathlib

theorem algebra_199529 {x : ℤ} (hx : x / 2 * 7 - 1001 > 0) (hxp : Prime (x / 2 * 7 - 1001)) :
    (x / 8)^2 - 1001 = 295 := by
  have h1 : x / 2 * 7 - 1001 > 0 := hx
  have h2 : x / 2 * 7 - 1001 = 7 := by
    by_cases h : x / 2 * 7 - 1001 > 7
    · -- Assume p > 7
      have h3 : Prime (x / 2 * 7 - 1001) := hxp
      have h5 : ¬Prime (x / 2 * 7 - 1001) := by
        rw [Int.prime_iff_natAbs_prime]
        have h6 : (x / 2 * 7 - 1001).natAbs % 7 = 0 := by
          omega
        have h7 : ¬ (x / 2 * 7 - 1001).natAbs.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 7 ∣ (x / 2 * 7 - 1001).natAbs by omega)
          all_goals
            omega
        tauto
      contradiction
    · -- Case x / 2 * 7 - 1001 ≤ 7
      have h4 : x / 2 * 7 - 1001 ≤ 7 := by
        omega
      have : x / 2 * 7 - 1001 = 7 := by
        interval_cases h8 : x / 2 * 7 - 1001 <;> norm_num at h8 hxp ⊢
        <;> omega
      assumption
  have h3 : x / 2 * 7 = 1008 := by
    omega
  have h4 : x / 2 = 144 := by
    omega
  have h6 : x = 288 ∨ x = 289 := by
    omega
  rcases h6 with (r | r)
  · -- Case x = 288
    rw [r]
    all_goals
      norm_num
  · -- Case x = 289
    rw [r]
    all_goals
      norm_num