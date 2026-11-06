import Mathlib

set_option maxHeartbeats 500000
/- How many two-digit positive integers have at least one 7 as a digit? -/
theorem algebra_12833 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).contains 7} = 18 := by
  have h₀ : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).contains 7} = {17, 27, 37, 47, 57, 67, 77, 87, 97, 70, 71, 72, 73, 74, 75, 76, 78, 79} := by
    ext n
    simp
    -- Break the iff into two implications.
    apply Iff.intro <;> intro h
    . obtain ⟨⟨h₀, h₁⟩, h₂⟩ := h
      -- Prove that n has exactly two digits.
      have h₃ : (Nat.digits 10 n).length = 2 := by
        rw [Nat.digits_len]
        simp
        apply @Nat.log_mono_right 10 10 n at h₀
        rw [show Nat.log 10 10 = 1 by native_decide] at h₀
        apply @Nat.log_mono_right 10 n 99 at h₁
        rw [show Nat.log 10 99 = 1 by native_decide] at h₁
        omega
        norm_num
        omega
      rw [List.length_eq_two] at h₃
      obtain ⟨n₀, ⟨n₁, h₃⟩⟩ := h₃
      simp [h₃] at h₂
      obtain h₂ | h₂ := h₂
      . -- If unit digit is 7.
        rw [h₂.symm] at h₃
        have h₄ : n = 7 + n₁ * 10 := by
          rw [<-@Nat.ofDigits_digits 10 n, h₃, Nat.ofDigits_eq_sum_mapIdx]
          simp
        replace h₁ : n₁ ≤ 9 := by
          omega
        replace h₀ : n₁ ≥ 1 := by
          omega
        interval_cases n₁
        rw [h₄]
        all_goals
          tauto
      . -- If tens digit is 7.
        rw [h₂.symm] at h₃
        have h₄ : n = n₀ + 7 * 10 := by
          rw [<-@Nat.ofDigits_digits 10 n, h₃, Nat.ofDigits_eq_sum_mapIdx]
          simp
        have h₅ : n₀ < 10 := by
          apply @Nat.digits_lt_base 10 n n₀
          norm_num
          simp [h₃]
        interval_cases n₀
        rw [h₄]
        all_goals
          tauto
    . obtain h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h := h
      all_goals
        rw [h]
        norm_num
  calc
    {n | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).contains 7}.ncard = Set.ncard {17, 27, 37, 47, 57, 67, 77, 87, 97, 70, 71, 72, 73, 74, 75, 76, 78, 79} := by rw [h₀]
    _ = ({17, 27, 37, 47, 57, 67, 77, 87, 97, 70, 71, 72, 73, 74, 75, 76, 78, 79} : Finset ℕ).toSet.ncard := by simp
    _ = Finset.card {17, 27, 37, 47, 57, 67, 77, 87, 97, 70, 71, 72, 73, 74, 75, 76, 78, 79} := Set.ncard_coe_Finset _
    _ = 18 := by simp
