import Mathlib

theorem number_theory_5046 : {x | x ∣ 61200 ∧ ∃ n, n^2 = x}.encard = 12 := by
  have h1 : {x | x ∣ 61200 ∧ ∃ n, n^2 = x} = 
    {1, 4, 9, 16, 25, 36, 100, 144, 225, 400, 900, 3600} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x divides 61200 and is a perfect square
      intro h
      rcases h with ⟨hx1, ⟨n, hxn⟩⟩
      have h2 : n^2 ∣ 61200 := by 
        rw [show n ^ 2 = x by linarith [hxn]]
        all_goals exact hx1
      have h4 : n^2 ≤ 61200 := by 
        exact Nat.le_of_dvd (by norm_num) h2
      have h5 : n ≤ 247 := by 
        by_contra h6
        push_neg at h6
        have h7 : n ≥ 248 := by omega
        have h8 : n ^ 2 ≥ 248 ^ 2 := by nlinarith 
        nlinarith
      have h5' : n ≤ 247 := h5
      have eq1 : n^2 = x := by linarith
      interval_cases n <;> norm_num [eq1] at hx1 ⊢
      <;> omega 
    · -- Assume x in the right side set, then x divides 61200 and perfect square.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 1
        constructor
        · norm_num
        · use 1
          all_goals norm_num
      · -- x = 4
        constructor
        · norm_num
        · use 2
          all_goals norm_num
      · -- x = 9
        constructor
        · norm_num
        · use 3
          all_goals norm_num
      · -- x = 16
        constructor
        · norm_num
        · use 4
          all_goals norm_num
      · -- x = 25
        constructor
        · norm_num
        · use 5
          all_goals norm_num
      · -- x = 36
        constructor
        · norm_num
        · use 6
          all_goals norm_num
      · -- x = 100
        constructor
        · norm_num
        · use 10
          all_goals norm_num
      · -- x = 144
        constructor
        · norm_num
        · use 12
          all_goals norm_num
      · -- x = 225
        constructor
        · norm_num
        · use 15
          all_goals norm_num
      · -- x = 400
        constructor
        · norm_num
        · use 20
          all_goals norm_num
      · -- x = 900
        constructor
        · norm_num
        · use 30
          all_goals norm_num
      · -- x = 3600
        constructor
        · norm_num
        · use 60
          all_goals norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try native_decide