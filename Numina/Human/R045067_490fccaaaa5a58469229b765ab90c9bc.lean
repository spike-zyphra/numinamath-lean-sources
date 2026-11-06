import Mathlib

/- Find the greatest common divisor of the numbers $2002+2,2002^{2}+2,2002^{3}+2, \ldots$.-/
theorem number_theory_610974 :
    IsGreatest {x : ℕ | ∀ n > 0, x ∣ (2002 ^ n + 2)} 6 := by
  -- Simplify the goal into two parts.
  simp [IsGreatest, upperBounds]
  refine ⟨?_, ?_⟩
  . -- First show that 6 divides every element in the sequence.
    intro n hn
    -- It suffices to show that both 2 and 3 divides 2002 ^ n + 2.
    rw [show 6 = 2 * 3 by norm_num]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    . -- Show that 2 divides 2002 ^ n + 2.
      apply Nat.dvd_of_mod_eq_zero
      simp [Nat.add_mod, Nat.pow_mod]
      norm_num [Nat.zero_pow hn]
    . -- Show that 3 divides 2002 ^ n + 2.
      apply Nat.dvd_of_mod_eq_zero
      simp [Nat.add_mod, Nat.pow_mod]
  . -- Show that 6 is the greatest possible such number, and hence the greatest common divisor.
    intro d hd
    have hd₁ := hd 1 (by norm_num)
    have hd₂ := hd 2 (by norm_num)
    -- Note that d ∣ 2002 ^ 2 - 4 = (2002 ^ 1 + 2)(2002 ^ 1 - 2).
    replace hd₁ : d ∣ 2002 ^ 2 - 4 := by
      calc
        _ ∣ 2002 ^ 1 + 2 := hd₁
        _ ∣ 2002 ^ 2 - 4 := by norm_num
    -- We have d ∣ 6 by considering the difference of hd₁ and hd₂.
    have hd₃ : d ∣ (2002 ^ 2 + 2) - (2002 ^ 2 - 4) := by
      apply Nat.dvd_sub (by norm_num) hd₂ hd₁
    apply Nat.le_of_dvd (by norm_num) at hd₃
    simp_all
