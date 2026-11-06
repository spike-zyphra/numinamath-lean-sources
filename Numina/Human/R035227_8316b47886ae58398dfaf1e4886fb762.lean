import Mathlib

open Nat

/-A whole number larger than 2 leaves a remainder of 2 when divided by each of the numbers 3, 4, 5, and 6.  What is the smallest such number?-/
theorem algebra_19929 :
    IsLeast {n | 2 < n ∧ 2 ≡ n [MOD 3] ∧ 2 ≡ n [MOD 4] ∧ 2 ≡ n [MOD 5] ∧ 2 ≡ n [MOD 6]} 62 := by
      refine' ⟨by norm_num [Nat.modEq_iff_dvd], fun a h => _⟩
      -- We have noted that the desired number is 2 greater than a number that is a multiple of 3, 4, 5, and 6.  Therefore, it is 2 greater than the least common multiple of 3, 4, 5, and 6.  The least common multiple of 3, 4, 5, and 6 is $2^2\cdot 3\cdot 5 = 60$, so the smallest number that fits the problem is $60 + 2 = \boxed{62}$.
      simp [Nat.modEq_iff_dvd ] at h
      norm_cast at h
      rw [Int.subNatNat_of_le (by omega)] at h
      norm_cast at h
      have : ((((3).lcm 4).lcm 5).lcm 6) = 60 := by norm_num
      have : 60 ∣ a - 2 := by
        rw [←this]
        apply Nat.lcm_dvd
        apply Nat.lcm_dvd
        apply Nat.lcm_dvd
        all_goals tauto
      have := le_of_dvd (by omega) this
      omega
