import Mathlib

theorem algebra_292043 (x : ℕ) :
    (2^(x-5)=2 ↔ x=6) ∧ (2^x=512 ↔ x=9) ∧ (x^5=243 ↔ x=3) ∧ (x^4=625 ↔ x=5) := by
  constructor
  · -- Proof of (2^(x-5)=2 ↔ x=6)
    apply Iff.intro
    · -- Forward direction: If 2^(x-5) = 2, then x = 6
      intro h
      have h1 : x ≥ 5 := by
        by_contra h2
        push_neg at h2
        interval_cases x <;> simp at h <;> omega
      have h2 : x - 5 = 1 := by
        have h3 : 2 ^ (x - 5) = 2 ^ 1 := by
          rw [h]
          all_goals norm_num
        have h4 : x - 5 = 1 := by
          exact Nat.pow_right_injective (by norm_num) h3
        exact h4
      omega
    · -- Backward direction: If x = 6, then 2^(x-5) = 2
      intro h
      rw [h]
      all_goals norm_num
  constructor
  · -- Proof of (2^x=512 ↔ x=9)
    apply Iff.intro
    · -- Forward direction: If 2^x = 512, then x = 9
      intro h
      have h1 : 2 ^ x = 2 ^ 9 := by
        rw [h]
        all_goals norm_num
      have h2 : x = 9 := by
        exact Nat.pow_right_injective (by norm_num) h1
      exact h2
    · -- Backward direction: If x = 9, then 2^x = 512
      intro h
      rw [h]
      all_goals norm_num
  constructor
  · -- Proof of (x^5=243 ↔ x=3)
    apply Iff.intro
    · -- Forward direction: If x^5 = 243, then x = 3
      intro h
      have h1 : x ≤ 3 := by
        by_contra h2
        push_neg at h2
        have h3 : x ≥ 4 := by omega
        have h4 : x ^ 5 ≥ 4 ^ 5 := by
          apply Nat.pow_le_pow_of_le_left
          omega
        norm_num at h4
        linarith
      interval_cases x <;> norm_num at h <;> tauto
    · -- Backward direction: If x = 3, then x^5 = 243
      intro h
      rw [h]
      all_goals norm_num
  · -- Proof of (x^4=625 ↔ x=5)
    apply Iff.intro
    · -- Forward direction: If x^4 = 625, then x = 5
      intro h
      have h1 : x ≤ 5 := by
        by_contra h2
        push_neg at h2
        have h3 : x ≥ 6 := by omega
        have h4 : x ^ 4 ≥ 6 ^ 4 := by
          apply Nat.pow_le_pow_of_le_left
          omega
        norm_num at h4
        linarith
      interval_cases x <;> norm_num at h <;> tauto
    · -- Backward direction: If x = 5, then x^4 = 625
      intro h
      rw [h]
      all_goals norm_num