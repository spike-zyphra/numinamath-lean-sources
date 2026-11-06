import Mathlib

theorem number_theory_6358 :
    ∑ᶠ n ∈ {n : ℕ | 0 < n ∧ 2020 % n = 1}, n = 2695 := by 
  have h1 : {n : ℕ | 0 < n ∧ 2020 % n = 1} = {3, 673, 2019} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n is a positive integer such that 2020 % n = 1, prove n ∈ {3, 673, 2019}
      intro h
      rcases h with ⟨hn_pos, hn_mod⟩
      have h2 : n ≤ 2020 := by
        by_contra h
        push_neg at h
        have h3 : 2020 % n = 2020 := by
          rw [Nat.mod_eq_of_lt]
          omega
        omega
      interval_cases n <;> norm_num at hn_mod hn_pos ⊢
      <;> omega
      <;> try { trivial }
    · -- Assume n ∈ {3, 673, 2019}, prove 0 < n ∧ 2020 % n = 1
      rintro (rfl | rfl | rfl)
      · -- Show that 3 is in the set
        constructor
        · norm_num
        · norm_num
      · -- Show that 673 is in the set
        constructor
        · norm_num
        · norm_num
      · -- Show that 2019 is in the set
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [finsum_mem_insert, finsum_mem_insert, finsum_mem_singleton]
  all_goals norm_num
  <;> try { native_decide }
  <;> try { trivial }
  <;> try { native_decide }
  <;> try { native_decide }
  <;> try { native_decide }
  <;> try { native_decide }
  <;> try { native_decide }
  <;> try { trivial }
  all_goals try { native_decide }
  <;> try { native_decide }
  <;> try { trivial }
  <;> try { native_decide }
  <;> try { trivial }
  <;> try { native_decide }
  all_goals try { native_decide }