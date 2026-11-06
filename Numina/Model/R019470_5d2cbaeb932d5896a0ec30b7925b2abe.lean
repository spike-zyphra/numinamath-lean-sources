import Mathlib

theorem number_theory_208561 :
    {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 25 ∣ n ∧ (Nat.digits 10 n).sum = 25} =
    {9925, 4975, 5875, 6775, 7675, 8575, 9475} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
            and_imp]
  constructor
  · -- First direction: Show that each number in the set is one of 9925, 4975, 5875, 6775, 7675, 8575, 9475
    rintro ⟨⟨hn1, hn2⟩, h25, hsum⟩
    interval_cases n <;> norm_num at h25 hsum <;> omega
  · -- Second direction: Show that each of the given numbers satisfies the conditions
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- 9925 is a four-digit number divisible by 25 with digit sum 25
      norm_num
    · -- 4975 is a four-digit number divisible by 25 with digit sum 25
      norm_num
    · -- 5875 is a four-digit number divisible by 25 with digit sum 25
      norm_num
    · -- 6775 is a four-digit number divisible by 25 with digit sum 25
      norm_num
    · -- 7675 is a four-digit number divisible by 25 with digit sum 25
      norm_num
    · -- 8575 is a four-digit number divisible by 25 with digit sum 25
      norm_num
    · -- 9475 is a four-digit number divisible by 25 with digit sum 25
      norm_num