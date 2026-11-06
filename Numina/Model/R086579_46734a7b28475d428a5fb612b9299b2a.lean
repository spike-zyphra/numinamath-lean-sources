import Mathlib

theorem number_theory_12817 :
    Set.ncard {x | ∃ n, x = n^2 ∧ x ∣ 180} = 4 := by
  have h1 : {x | ∃ n, x = n^2 ∧ x ∣ 180} = {1, 4, 9, 36} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
              Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x is a perfect square dividing 180, prove x ∈ {1, 4, 9, 36}
      rintro ⟨n, rfl, hn⟩
      have h2 : n^2 ≤ 180 := by exact Nat.le_of_dvd (by norm_num) hn
      have h3 : n ≤ 13 := by nlinarith [h2]
      interval_cases n <;> norm_num at *
      <;> tauto
    · -- Assume x ∈ {1, 4, 9, 36}, prove x is a perfect square dividing 180
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 1
        exact ⟨1, by norm_num, by norm_num⟩
      · -- x = 4
        exact ⟨2, by norm_num, by norm_num⟩
      · -- x = 9
        exact ⟨3, by norm_num, by norm_num⟩
      · -- x = 36
        exact ⟨6, by norm_num, by norm_num⟩
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]