import Mathlib

theorem number_theory_128944 :
    {n : ℕ | n ∈ Finset.Icc 100 999 ∧ (n / 100) % 10 ≠ 0 ∧ (n / 100) ^ 2 + (n % 100 / 10) ^ 2 + (n % 100 % 10) ^ 2 ∣ 26} =
    {100, 110, 101, 302, 320, 230, 203, 431, 413, 314, 341, 134, 143, 510, 501, 150, 105} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- First direction: if n is in the left set, it is in the finite set.
    intro h
    rcases h with ⟨⟨hn1, hn2⟩, hn3, hndiv⟩
    interval_cases n <;> norm_num at *
    <;> omega
  · -- Second direction: each element in the finite set is in the left set.
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      constructor
      · norm_num
      all_goals
        constructor
        · norm_num
        · norm_num