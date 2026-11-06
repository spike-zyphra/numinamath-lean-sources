import Mathlib

theorem number_theory_281767 :
    {n : ℕ | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).sum = 3 * (Nat.digits 10 (n + 3)).sum} = {207, 117, 108} := by 
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Proof of forward direction: If n ∈ {three-digit numbers and digit sum condition}, then n ∈ {207, 117, 108}
    rintro ⟨⟨hn1, hn2⟩, h⟩
    interval_cases n <;> norm_num at h hn1 hn2 ⊢
    <;> omega
  · -- Proof of reverse direction: If n ∈ {207, 117, 108}, then n ∈ {three-digit numbers and digit sum condition}
    rintro (rfl | rfl | rfl)
    · -- Check n = 207
      constructor
      · -- Show 207 is in the range 100 ≤ n ≤ 999
        norm_num
      · -- Check the digit sum condition
        all_goals norm_num
    · -- Check n = 117
      constructor
      · -- Show 117 is in the range 100 ≤ n ≤ 999
        norm_num
      · -- Check the digit sum condition
        all_goals norm_num
    · -- Check n = 108
      constructor
      · -- Show 108 is in the range 100 ≤ n ≤ 999
        norm_num
      · -- Check the digit sum condition
        all_goals norm_num