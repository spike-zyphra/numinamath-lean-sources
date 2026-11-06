import Mathlib

/- What is the largest number $k$ less than 1000 such that the remainder is 1 when $k$ is divided by each of 3, 4, 5, 6, and 7? -/
theorem number_theory_19616  :
    IsGreatest {k : ℕ | k < 1000 ∧ k % 3 = 1 ∧ k % 4 = 1 ∧ k % 5 = 1 ∧ k % 6 = 1 ∧ k % 7 = 1} 841 := by
        -- 分两步证明：能取等 + 最大值
        constructor <;>
        simp [upperBounds]
        intro k hk h3 h4 h5 h6 h7
        by_cases H : k ≤ 1
        -- 能取等
        .
            omega
        -- 最大值
        .
            simp at H
            -- k % p = 1 ↔ p ∣ k - 1
            replace h3 : 3 ∣ k - 1:= by refine Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h3)
            replace h4 : 4 ∣ k - 1:= by refine Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h4)
            replace h5 : 5 ∣ k - 1:= by refine Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h5)
            replace h6 : 6 ∣ k - 1:= by refine Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h6)
            replace h7 : 7 ∣ k - 1:= by refine Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h7)
            -- p ∣ k - 1 ∧ q ∣ k - 1 → Nat.lcm p q ∣ k - 1
            replace h3 : Nat.lcm 3 4 ∣ k - 1:= by exact Nat.lcm_dvd h3 h4
            rw [show Nat.lcm 3 4 = 12 by decide] at h3
            replace h3 : Nat.lcm 12 5 ∣ k - 1:= by exact Nat.lcm_dvd h3 h5
            rw [show Nat.lcm 12 5 = 60 by decide] at h3
            replace h3 : Nat.lcm 60 7 ∣ k - 1:= by exact Nat.lcm_dvd h3 h7
            -- 得到 420 ∣ k - 1
            rw [show Nat.lcm 60 7 = 420 by decide] at h3
            clear h4 h5 h6 h7
            replace h3 : ∃ a : ℕ, k - 1 = a * 420:= by exact exists_eq_mul_left_of_dvd h3
            rcases h3 with ⟨a, h⟩
            have _ : a ≤ 2:= by
                by_contra!
                replace this : a ≥ 3:= by omega
                have _ : k - 1 ≥ 1260:= by omega
                omega
            omega
