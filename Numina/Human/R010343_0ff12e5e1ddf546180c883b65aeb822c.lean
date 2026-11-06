import Mathlib

/-
The Fermat number $ F_{5} = 2^{2^{5}} + 1 $ is divisible by 641.
-/
theorem number_theory_4601 : 641 ∣ 2^(2^5) + 1 := by
  -- Showing that 2^(2^5)+1 = 641*k, we can deduce 641 | 2^(2^5)+1.
  have : 2 ^ (2 ^ 5) + 1 = 641 * (2 ^ 28 - 641 ^ 3 + 4 * 641 ^ 2 - 6 * 641 + 4) := by
    calc 2 ^ (2 ^ 5) + 1
      _ = 2 ^ 32 + 1 := by norm_num
      _ = (641 - 5 ^ 4) * 2 ^ 28 + 1:= by norm_num
      _ = 641 * 2 ^ 28 - (5 * 2 ^ 7) ^ 4 + 1 := by norm_num
      _ = 641 * 2 ^ 28 - (641 - 1) ^ 4 + 1 := by norm_num
      _ = 641 * 2 ^ 28 - (641 ^ 4 - 4 * 641 ^ 3 + 6 * 641 ^ 2 - 4 * 641 + 1) + 1 := by norm_num
      _ = 641 * (2 ^ 28 - 641 ^ 3 + 4 * 641 ^ 2 - 6 * 641 + 4) := by norm_num
  exact Dvd.intro _ this.symm
