import Mathlib

/- Determine the number of solutions in $x$ of the congruence $64x\equiv 2\pmod {66}$ such that $0< x\le 100$. -/
theorem number_theory_22766 :
    Set.ncard {x : ℕ | 0 < x ∧ x ≤ 100 ∧ 64 * x ≡ 2 [MOD 66]} = 3 := by
  have h₀ : Set.ncard {32, 65, 98} = 3 := by
    -- Prove that the set {32, 65, 98} has cardinality of 3.
    rw [show ({32, 65, 98} : Set ℕ) = ({32, 65, 98} : Finset ℕ) by simp]
    rw [Set.ncard_coe_Finset]
    rw [Finset.card_insert_of_not_mem]
    rw [Finset.card_insert_of_not_mem]
    all_goals
      simp
  have h₁ : {x : ℕ | 0 < x ∧ x ≤ 100 ∧ 64 * x ≡ 2 [MOD 66]} = {32, 65, 98} := by
    -- Prove that the set required is the same as {32, 65, 98}.
    ext x
    apply Iff.intro
    <;> intro h
    <;> simp at h ⊢
    . obtain ⟨h₁, h₂, h₃⟩ := h
      -- Replace the modular congruence to -x ≡ 1 [MOD 33].
      rw [Nat.modEq_iff_dvd, <-Int.modEq_iff_dvd] at h₃
      replace h₃ := (show (64 * x : ℤ) ≡ -2 * (x : ℤ) [ZMOD 66] by rw [show 64 * x = -2 * (x : ℤ) + 66 * (x : ℤ) by omega]; apply Int.modEq_add_fac_self).symm.trans h₃
      rw [show (2 : ℕ) = (2 : ℤ) * 1 by norm_num, Int.neg_mul, <-Int.mul_neg] at h₃
      apply Int.ModEq.cancel_left_div_gcd (show 0 < 66 by norm_num) at h₃
      norm_num at h₃
      simp [Int.modEq_iff_dvd] at h₃
      rw [dvd_iff_exists_eq_mul_left] at h₃
      obtain ⟨c, h₃⟩ := h₃
      have h₄ : c ≤ 3 := by
        omega
      have h₅ : c ≥ 1 := by
        omega
      interval_cases c
      all_goals
        omega
    . -- For each of the numbers 32, 65, 98, show that the condition is satisfied.
      obtain h | h | h := h
      all_goals
        rw [h]
        norm_num
        rw [Nat.modEq_iff_dvd]
        omega
  calc
    Set.ncard {x : ℕ | 0 < x ∧ x ≤ 100 ∧ 64 * x ≡ 2 [MOD 66]} = Set.ncard {32, 65, 98} := by rw [h₁]
    _ = 3 := h₀
