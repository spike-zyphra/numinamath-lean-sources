import Mathlib

/- What is the largest factor of 130000 that does not contain the digit 0 or 5 ?-/
theorem number_theory_609879 :
    IsGreatest {x : ℕ | x ∣ 130000 ∧ ∀ d ∈ Nat.digits 10 x, (d ≠ 0 ∧ d ≠ 5)} 26 := by
  -- Simplify the goal intwo two parts.
  simp [IsGreatest, upperBounds]
  refine ⟨?_, ?_⟩
  . -- First show that 26 is indeed a divisor of 130000 satisfying the condition.
    norm_num
  . -- Show that 26 is the greatest such divisor.
    intro h h₀ h₁
    -- Note that in order that the digits of d contains no 0 or 5, d must be not be a multiple of 5.
    have h₂ : ¬5 ∣ h := by
      by_contra!
      -- Assume on the contrary, then the unit digit is either 0 or 5.
      have h₂ := @Nat.head!_digits 10 h (by norm_num)
      have h₃ : h % 10 = 0 ∨ h % 10 = 5 := by
        omega
      rw [<-h₂] at h₃
      specialize h₁ (Nat.digits 10 h).head! (List.head!_mem_self (Nat.digits_ne_nil_iff_ne_zero.mpr (by by_contra!; simp [this] at h₀)))
      tauto
    -- Now h must be a divisor of 208, because 130000 = 208 * 5⁴.
    have h₃ : h ∣ 208 := by
      rw [show 130000 = 208 * 5 ^ 4 from rfl] at h₀
      apply Nat.Coprime.dvd_of_dvd_mul_right at h₀
      exact h₀
      apply Nat.Coprime.pow_right
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Nat.prime_five)).mpr h₂)
    -- List the divisors of 208, and h is one of them.
    replace h₃ : h ∈ ({1, 2, 4, 8, 13, 16, 26, 52, 104, 208} : Finset ℕ) := by
      rw [show {1, 2, 4, 8, 13, 16, 26, 52, 104, 208} = Nat.divisors 208 by decide, Nat.mem_divisors]
      exact ⟨h₃, by norm_num⟩
    -- Show that h₃ could not be 52, 104 nor 208.
    have h₄ : h ≠ 52 ∧ h ≠ 104 ∧ h ≠ 208 := by
      refine ⟨?_, ?_, ?_⟩
      all_goals
        by_contra!
        simp [this] at h₁
    simp [h₄] at h₃
    omega
