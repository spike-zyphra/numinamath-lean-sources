import Mathlib

/- What is the smallest integer greater than 200 for which the greatest common divisor of that integer and 36 is 18? -/
theorem algebra_20530 :
   IsLeast {n : ℕ| n > 200 ∧ Nat.gcd n 36 = 18 } 234 := by
      constructor <;>
      simp [lowerBounds]
      .
         intro a h1 h2

         -- h3：如果a和36的最大公约数是18，那么18整除a
         have h3 : a.gcd 36 ∣ a := (Nat.gcd_dvd a 36).1
         rw [h2] at h3
         -- h4：存在某个自然数k，使得a = 18k
         have h4 : ∃ (k : ℕ), a = 18 * k := h3
         rcases h4 with ⟨k, hk⟩
         rw [hk] at h1
         -- 由于a > 200，所以 18k > 200，即 k > 200/18
         replace h1 : 200 / 18 < k := by omega
         simp at h1
         -- h5：证明k必须大于12
         have h5 : 12 < k := by
            -- 反证法：假设k ≤ 12
            by_contra h6
            simp at h6
            -- 如果k ≤ 12，那么k必须等于12
            replace h6 : k = 12 := by omega
            rw [h6] at hk
            simp at hk
            rw [hk] at h2
            -- 但是216和36的最大公约数是36，不是18
            have _ : Nat.gcd 216 36 = 36 := by decide
            trivial
         -- 因此k ≥ 13
         replace h1 : 13 ≤ k := by omega
         -- 最终证明234是满足条件的最小值
         linarith
