import Mathlib

/- What is the last digit of $17^{103}+5$ ?-/
theorem number_theory_610865 : 17^103 + 5 ≡ 8 [MOD 10] := by
  -- Use Euler's theorem, 17 ^ 4 % 10 = 1 to simplify calculation.
  have h₀ := @Nat.ModEq.pow_totient 17 10 (by norm_num)
  rw [show Nat.totient 10 = 4 by decide] at h₀
  -- Raise both sides to the power of 25.
  apply Nat.ModEq.pow 25 at h₀
  rw [<-Nat.pow_mul] at h₀
  -- Multiply both sides by 17 ^ 3.
  replace h₀ := @Nat.ModEq.mul _ _ _ (17 ^ 3) (17 ^ 3) h₀ (by rfl)
  rw [<-Nat.pow_add, show 4 * 25 + 3 = 103 by norm_num] at h₀
  -- Add both sides by 5.
  replace h₀ := @Nat.ModEq.add _ _ _ 5 5 h₀ (by rfl)
  calc
    17 ^ 103 + 5 ≡ 1 ^ 25 * 17 ^ 3 + 5 [MOD 10] := h₀
    _ ≡ 8 [MOD 10] := by
      symm
      rw [Nat.modEq_iff_dvd']
      all_goals
        norm_num
