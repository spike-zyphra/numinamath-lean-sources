import Mathlib

theorem number_theory_196003 :
    ∃ k, {i | i ∈ Finset.range 10 ∧ (Nat.digits 10 (k + i)).length = 6 ∧
      (Nat.digits 10 (k + i))[0]! + (Nat.digits 10 (k + i))[1]! + (Nat.digits 10 (k + i))[2]! =
        (Nat.digits 10 (k + i))[3]! + (Nat.digits 10 (k + i))[4]! + (Nat.digits 10 (k + i))[5]!}.ncard = 2 := by
  use 111111
  have h1 : {i | i ∈ Finset.range 10 ∧ (Nat.digits 10 (111111 + i)).length = 6 ∧
      (Nat.digits 10 (111111 + i))[0]! + (Nat.digits 10 (111111 + i))[1]! + (Nat.digits 10 (111111 + i))[2]! =
        (Nat.digits 10 (111111 + i))[3]! + (Nat.digits 10 (111111 + i))[4]! + (Nat.digits 10 (111111 + i))[5]!} = {0, 9} := by
    ext i
    simp only [Finset.mem_range, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First direction: if i in the set, then i = 0 or 9
      intro h
      rcases h with ⟨h1, h2, h3⟩
      interval_cases i <;> norm_num at h1 h2 h3 <;> tauto
    · -- Second direction: if i in {0, 9}, then in the set
      rintro (rfl | rfl)
      · -- i = 0
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- i = 9
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_pair]
  all_goals norm_num